#include "realtime_combat.h"

#include "actions.h"
#include "animation.h"
#include "art.h"
#include "combat.h"
#include "combat_ai.h"
#include "critter.h"
#include "game.h"
#include "game_mouse.h"
#include "interface.h"
#include "input.h"
#include "item.h"
#include "kb.h"
#include "map.h"
#include "mouse.h"
#include "object.h"
#include "platform_compat.h"
#include "scripts.h"
#include "tile.h"
#include "worldmap.h"

namespace fallout {

static constexpr unsigned int kMoveFrameDelayMs = 75;
static constexpr int kMovePixelsPerFrame = 4;
static constexpr unsigned int kAttackCooldownMs = 650;

static unsigned int gLastMoveFrameTime = 0;
static unsigned int gLastAttackTime = 0;
static bool gWasMoving = false;
static bool gRangedAimActive = false;
static bool gCursorModeActive = false;
static int gSavedMouseCursor = MOUSE_CURSOR_NONE;
static bool gSavedMouseObjectsVisible = false;

static bool realTimeCombatIsTempleStart()
{
    if (gMapHeader.index == MAP_ARROYO_TEMPLE) {
        return true;
    }

    return compat_strnicmp(gMapHeader.name, "ARTEMPLE", 8) == 0;
}

bool realTimeCombatIsEnabled()
{
    return gGameLoaded
        && !gameUiIsDisabled()
        && gameGetState() == GAME_STATE_0
        && interfaceBarEnabled()
        && !isoIsDisabled()
        && realTimeCombatIsTempleStart();
}

static void realTimeCombatEnterCursorMode()
{
    bool enteringCursorMode = !gCursorModeActive;

    if (!gCursorModeActive) {
        gSavedMouseCursor = gameMouseGetCursor();
        gSavedMouseObjectsVisible = gameMouseObjectsIsVisible();
        gCursorModeActive = true;
    }

    if (gameMouseObjectsIsVisible()) {
        gameMouseObjectsHide();
    }

    if (enteringCursorMode || gameMouseGetCursor() != MOUSE_CURSOR_ARROW) {
        mouseHideCursor();
        gameMouseSetCursor(MOUSE_CURSOR_ARROW);
        mouseShowCursor();
    }
}

static void realTimeCombatExitCursorMode()
{
    if (!gCursorModeActive) {
        return;
    }

    mouseHideCursor();
    gameMouseSetCursor(gSavedMouseCursor);
    mouseShowCursor();

    if (gSavedMouseObjectsVisible) {
        gameMouseObjectsShow();
    } else {
        gameMouseObjectsHide();
    }

    gCursorModeActive = false;
}

void realTimeCombatRefreshCursor()
{
    if (realTimeCombatIsEnabled()) {
        realTimeCombatEnterCursorMode();
    } else {
        realTimeCombatExitCursorMode();
    }
}

static void realTimeCombatFaceMouse()
{
    if (animationIsBusy(gDude)) {
        return;
    }

    int mouseX;
    int mouseY;
    mouseGetPosition(&mouseX, &mouseY);

    int tile = tileFromScreenXY(mouseX, mouseY);
    if (!tileIsValid(tile) || tile == gDude->tile) {
        return;
    }

    int rotation = tileGetRotationTo(gDude->tile, tile);
    if (rotation == gDude->rotation) {
        return;
    }

    Rect dirtyRect;
    if (objectSetRotation(gDude, rotation, &dirtyRect) == 0) {
        tileWindowRefreshRect(&dirtyRect, gDude->elevation);
    }
}

static bool realTimeCombatIsCtrlPressed()
{
    return gPressedPhysicalKeys[SDL_SCANCODE_LCTRL] != KEY_STATE_UP
        || gPressedPhysicalKeys[SDL_SCANCODE_RCTRL] != KEY_STATE_UP;
}

static bool realTimeCombatIsReloadHitMode(int hitMode)
{
    return hitMode == HIT_MODE_LEFT_WEAPON_RELOAD
        || hitMode == HIT_MODE_RIGHT_WEAPON_RELOAD;
}

static bool realTimeCombatGetAttackMode(bool ranged, int* hitMode)
{
    if (!interface_get_current_attack_mode(hitMode)) {
        return false;
    }

    if (realTimeCombatIsReloadHitMode(*hitMode)) {
        return false;
    }

    Object* weapon = critterGetWeaponForHitMode(gDude, *hitMode);
    if (weapon == nullptr && !isUnarmedHitMode(*hitMode)) {
        *hitMode = HIT_MODE_PUNCH;
    }

    int attackType = weaponGetAttackTypeForHitMode(weapon, *hitMode);
    bool isRangedAttack = attackType == ATTACK_TYPE_RANGED || attackType == ATTACK_TYPE_THROW;

    return ranged ? isRangedAttack : !isRangedAttack;
}

static Object* realTimeCombatGetTargetUnderCursor()
{
    Object* target = gameMouseGetObjectUnderCursor(OBJ_TYPE_CRITTER, false, gDude->elevation);
    if (target == nullptr || target == gDude) {
        return nullptr;
    }

    if ((target->flags & OBJECT_HIDDEN) != 0 || critterIsDead(target)) {
        return nullptr;
    }

    return target;
}

static Object* realTimeCombatGetItemUnderCursor()
{
    Object* item = gameMouseGetObjectUnderCursor(OBJ_TYPE_ITEM, false, gDude->elevation);
    if (item == nullptr || (item->flags & OBJECT_HIDDEN) != 0) {
        return nullptr;
    }

    return item;
}

static Object* realTimeCombatGetTalkTargetUnderCursor()
{
    Object* target = gameMouseGetObjectUnderCursor(OBJ_TYPE_CRITTER, false, gDude->elevation);
    if (target == nullptr || target == gDude) {
        return nullptr;
    }

    if ((target->flags & OBJECT_HIDDEN) != 0 || critterIsDead(target)) {
        return nullptr;
    }

    if (!_obj_action_can_talk_to(target)) {
        return nullptr;
    }

    return target;
}

static bool realTimeCombatCanAttack(Object* target, int hitMode, bool aiming)
{
    int savedActionPoints = gDude->data.critter.combat.ap;
    int actionPointsRequired = weaponGetActionPointCost(gDude, hitMode, aiming);
    if (gDude->data.critter.combat.ap < actionPointsRequired) {
        gDude->data.critter.combat.ap = actionPointsRequired;
    }

    int badShot = _combat_check_bad_shot(gDude, target, hitMode, aiming);
    gDude->data.critter.combat.ap = savedActionPoints;

    return badShot == COMBAT_BAD_SHOT_OK;
}

static void realTimeCombatNotifyAttackTarget(Object* target, Object* weapon)
{
    if (target == nullptr || FID_TYPE(target->fid) != OBJ_TYPE_CRITTER) {
        return;
    }

    critterSetWhoHitMe(target, gDude);

    if (target->sid != -1) {
        scriptSetObjects(target->sid, gDude, weapon);
        scriptSetFixedParam(target->sid, 5);
        scriptExecProc(target->sid, SCRIPT_PROC_COMBAT);
    }

    _combatai_notify_onlookers(target);
}

static bool realTimeCombatAttack(Object* target, int hitMode, bool aiming)
{
    if (target == nullptr || animationIsBusy(gDude)) {
        return false;
    }

    unsigned int now = getTicks();
    if (gLastAttackTime != 0 && getTicksBetween(now, gLastAttackTime) < kAttackCooldownMs) {
        return false;
    }

    if (!realTimeCombatCanAttack(target, hitMode, aiming)) {
        return false;
    }

    int savedActionPoints = gDude->data.critter.combat.ap;
    int actionPointsRequired = weaponGetActionPointCost(gDude, hitMode, aiming);
    if (gDude->data.critter.combat.ap < actionPointsRequired) {
        gDude->data.critter.combat.ap = actionPointsRequired;
    }

    gWasMoving = false;
    int rc = _combat_attack(gDude, target, hitMode, HIT_LOCATION_UNCALLED);
    gDude->data.critter.combat.ap = savedActionPoints;
    interfaceRenderActionPoints(gDude->data.critter.combat.ap, _combat_free_move);

    if (rc == 0) {
        realTimeCombatNotifyAttackTarget(target, critterGetWeaponForHitMode(gDude, hitMode));
        gLastAttackTime = now;
    }

    return rc == 0;
}

static void realTimeCombatReload()
{
    Object* weapon;
    if (interfaceGetActiveItem(&weapon) != 0 || weapon == nullptr) {
        return;
    }

    if (itemGetType(weapon) != ITEM_TYPE_WEAPON || ammoGetCapacity(weapon) <= 0) {
        return;
    }

    if (weaponAttemptReload(gDude, weapon) == 0) {
        interfaceUpdateItems(false, INTERFACE_ITEM_ACTION_DEFAULT, INTERFACE_ITEM_ACTION_DEFAULT);
        _intface_update_ammo_lights();
    }
}

static void realTimeCombatHandleMouse()
{
    int mouseState = mouseGetEvent();
    gRangedAimActive = realTimeCombatIsCtrlPressed()
        && (mouseState & MOUSE_EVENT_RIGHT_BUTTON_DOWN_REPEAT) != 0;

    if (animationIsBusy(gDude)) {
        return;
    }

    if (!realTimeCombatIsCtrlPressed()
        && (mouseState & MOUSE_EVENT_RIGHT_BUTTON_DOWN) != 0
        && (mouseState & MOUSE_EVENT_RIGHT_BUTTON_REPEAT) == 0) {
        Object* target = realTimeCombatGetTalkTargetUnderCursor();
        if (target != nullptr) {
            gWasMoving = false;
            actionTalk(gDude, target);
        }
        return;
    }

    if ((mouseState & MOUSE_EVENT_LEFT_BUTTON_DOWN) == 0
        || (mouseState & MOUSE_EVENT_LEFT_BUTTON_REPEAT) != 0) {
        return;
    }

    Object* item = realTimeCombatGetItemUnderCursor();
    if (item != nullptr) {
        gWasMoving = false;
        actionPickUp(gDude, item);
        return;
    }

    int hitMode;
    if (!realTimeCombatGetAttackMode(gRangedAimActive, &hitMode)) {
        return;
    }

    Object* target = realTimeCombatGetTargetUnderCursor();
    realTimeCombatAttack(target, hitMode, gRangedAimActive);
}

static int realTimeCombatNormalizeAxis(int negativeKey, int positiveKey)
{
    bool negative = gPressedPhysicalKeys[negativeKey] != KEY_STATE_UP;
    bool positive = gPressedPhysicalKeys[positiveKey] != KEY_STATE_UP;
    return (positive ? 1 : 0) - (negative ? 1 : 0);
}

static bool realTimeCombatGetMovementDelta(int* dx, int* dy)
{
    int inputX = realTimeCombatNormalizeAxis(SDL_SCANCODE_A, SDL_SCANCODE_D);
    int inputY = realTimeCombatNormalizeAxis(SDL_SCANCODE_W, SDL_SCANCODE_S);
    if (inputX == 0 && inputY == 0) {
        return false;
    }

    *dx = inputX * kMovePixelsPerFrame;
    *dy = inputY * kMovePixelsPerFrame;

    if (inputX != 0 && inputY != 0) {
        // Approximate 1/sqrt(2) without adding floating point to the frame loop.
        *dx = *dx * 3 / 4;
        *dy = *dy * 3 / 4;
    }

    return true;
}

static void realTimeCombatSetMovingAnimation(bool moving)
{
    int anim = moving ? ANIM_RUNNING : ANIM_STAND;
    if (FID_ANIM_TYPE(gDude->fid) == anim) {
        return;
    }

    Rect dirtyRect;
    int fid = buildFid(FID_TYPE(gDude->fid), gDude->fid & 0xFFF, anim, (gDude->fid & 0xF000) >> 12, gDude->rotation + 1);
    if (moving && !artExists(fid)) {
        fid = buildFid(FID_TYPE(gDude->fid), gDude->fid & 0xFFF, ANIM_WALK, (gDude->fid & 0xF000) >> 12, gDude->rotation + 1);
    }

    if (objectSetFid(gDude, fid, &dirtyRect) == 0) {
        Rect frameRect;
        objectSetFrame(gDude, 0, &frameRect);
        rectUnion(&dirtyRect, &frameRect, &dirtyRect);
        tileWindowRefreshRect(&dirtyRect, gDude->elevation);
    }
}

static void realTimeCombatAdvanceMovingAnimation()
{
    unsigned int now = getTicks();
    if (getTicksBetween(now, gLastMoveFrameTime) < kMoveFrameDelayMs) {
        return;
    }

    Rect dirtyRect;
    if (objectSetNextFrame(gDude, &dirtyRect) == 0) {
        tileWindowRefreshRect(&dirtyRect, gDude->elevation);
    }

    gLastMoveFrameTime = now;
}

static bool realTimeCombatSyncTileForFootPosition(int footX, int footY, Rect* dirtyRect, bool* changedTile)
{
    *changedTile = false;

    int tile = tileFromScreenXY(footX, footY);
    if (!tileIsValid(tile)) {
        return false;
    }

    if (tile == gDude->tile) {
        return true;
    }

    if (_obj_blocking_at(gDude, tile, gDude->elevation) != nullptr) {
        return false;
    }

    if (objectSetLocation(gDude, tile, gDude->elevation, dirtyRect) != 0) {
        return false;
    }

    *changedTile = true;

    int baseX;
    int baseY;
    if (tileToScreenXY(gDude->tile, &baseX, &baseY) != 0) {
        return false;
    }

    baseX += 16;
    baseY += 8;

    Rect offsetRect;
    if (_obj_offset(gDude, footX - baseX, footY - baseY, &offsetRect) == 0) {
        rectUnion(dirtyRect, &offsetRect, dirtyRect);
    }

    scriptsExecSpatialProc(gDude, gDude->tile, gDude->elevation);
    return true;
}

static void realTimeCombatHandleMovement()
{
    if (animationIsBusy(gDude)) {
        return;
    }

    int dx;
    int dy;
    if (!realTimeCombatGetMovementDelta(&dx, &dy)) {
        if (gWasMoving) {
            _dude_stand(gDude, gDude->rotation, -1);
            gWasMoving = false;
        }
        return;
    }

    realTimeCombatSetMovingAnimation(true);
    realTimeCombatAdvanceMovingAnimation();

    Rect dirtyRect;
    objectGetRect(gDude, &dirtyRect);

    int baseX;
    int baseY;
    if (tileToScreenXY(gDude->tile, &baseX, &baseY) != 0) {
        return;
    }

    int footX = baseX + 16 + gDude->x + dx;
    int footY = baseY + 8 + gDude->y + dy;
    bool changedTile;
    if (!realTimeCombatSyncTileForFootPosition(footX, footY, &dirtyRect, &changedTile)) {
        return;
    }

    if (!changedTile) {
        Rect offsetRect;
        if (_obj_offset(gDude, dx, dy, &offsetRect) == 0) {
            rectUnion(&dirtyRect, &offsetRect, &dirtyRect);
        }
    }

    tileWindowRefreshRect(&dirtyRect, gDude->elevation);
    _tile_scroll_to(gDude->tile, 2);

    gWasMoving = true;
}

static bool realTimeCombatConsumesKey(int keyCode)
{
    switch (keyCode) {
    case -2:
    case KEY_LOWERCASE_W:
    case KEY_UPPERCASE_W:
    case KEY_LOWERCASE_A:
    case KEY_UPPERCASE_A:
    case KEY_LOWERCASE_S:
    case KEY_UPPERCASE_S:
    case KEY_LOWERCASE_D:
    case KEY_UPPERCASE_D:
    case KEY_LOWERCASE_R:
    case KEY_UPPERCASE_R:
        return true;
    default:
        return false;
    }
}

bool realTimeCombatUpdate(int keyCode)
{
    realTimeCombatRefreshCursor();

    if (!realTimeCombatIsEnabled()) {
        return false;
    }

    if (keyCode == KEY_LOWERCASE_R || keyCode == KEY_UPPERCASE_R) {
        realTimeCombatReload();
    }

    realTimeCombatFaceMouse();
    realTimeCombatHandleMouse();
    realTimeCombatHandleMovement();

    return realTimeCombatConsumesKey(keyCode);
}

} // namespace fallout
