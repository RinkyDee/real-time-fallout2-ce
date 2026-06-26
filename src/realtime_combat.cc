#include "realtime_combat.h"

#include <limits.h>
#include <stdio.h>
#include <string.h>
#include <unordered_map>

#include "actions.h"
#include "animation.h"
#include "art.h"
#include "combat.h"
#include "combat_ai.h"
#include "critter.h"
#include "debug.h"
#include "game.h"
#include "game_mouse.h"
#include "interface.h"
#include "inventory.h"
#include "input.h"
#include "item.h"
#include "kb.h"
#include "map.h"
#include "mouse.h"
#include "object.h"
#include "platform_compat.h"
#include "scripts.h"
#include "settings.h"
#include "tile.h"
#include "worldmap.h"

namespace fallout {

static constexpr unsigned int kMoveFrameDelayMs = 75;
static constexpr int kMovePixelsPerFrame = 4;
static constexpr int kNpcMovePixelsPerFrame = 3;
static constexpr int kAttackTargetPadding = 24;
static constexpr unsigned int kAttackCooldownMs = 650;
static constexpr unsigned int kNpcAttackCooldownMs = 1200;

static unsigned int gLastMoveFrameTime = 0;
static unsigned int gLastNpcMoveFrameTime = 0;
static unsigned int gLastAttackTime = 0;
static bool gWasMoving = false;
static bool gRangedAimActive = false;
static bool gCursorModeActive = false;
static int gSavedMouseCursor = MOUSE_CURSOR_NONE;
static bool gSavedMouseObjectsVisible = false;
static int gPendingMap = -1;
static char gPendingMapName[16];
static bool gMapTransitionInProgress = false;
static std::unordered_map<Object*, unsigned int> gNpcLastAttackTimes;

static void realTimeCombatFinalizeAttack();

static bool realTimeCombatNameContains(const char* string, const char* pattern)
{
    size_t patternLength = strlen(pattern);
    for (const char* p = string; *p != '\0'; p++) {
        if (compat_strnicmp(p, pattern, patternLength) == 0) {
            return true;
        }
    }

    return false;
}

static void realTimeCombatWriteTraceLine(const char* path, const char* line)
{
    if (path == nullptr || path[0] == '\0') {
        return;
    }

    FILE* stream = fopen(path, "a");
    if (stream == nullptr) {
        return;
    }

    fputs(line, stream);
    fclose(stream);
}

static void realTimeCombatWriteTraceLineNearFile(const char* filePath, const char* line)
{
    if (filePath == nullptr || filePath[0] == '\0') {
        return;
    }

    const char* slash = strrchr(filePath, '\\');
    const char* forwardSlash = strrchr(filePath, '/');
    if (forwardSlash != nullptr && (slash == nullptr || forwardSlash > slash)) {
        slash = forwardSlash;
    }

    if (slash == nullptr) {
        return;
    }

    char path[COMPAT_MAX_PATH];
    size_t directoryLength = slash - filePath;
    if (directoryLength + strlen("\\rtcombat_debug.log") + 1 > sizeof(path)) {
        return;
    }

    memcpy(path, filePath, directoryLength);
    path[directoryLength] = '\0';
    strcat(path, "\\rtcombat_debug.log");
    realTimeCombatWriteTraceLine(path, line);
}

static bool realTimeCombatIsMapNameEnabled(const char* name)
{
    return compat_strnicmp(name, "ARTEMPLE", 8) == 0
        || compat_strnicmp(name, "ARCAVES", 7) == 0
        || realTimeCombatNameContains(name, "TEMPLE")
        || realTimeCombatNameContains(name, "TEMP");
}

static bool realTimeCombatIsMapIndexEnabled(int map)
{
    if (map < 0) {
        return false;
    }

    if (map == MAP_ARROYO_TEMPLE) {
        return true;
    }

    char name[16];
    if (wmMapIdxToName(map, name, sizeof(name)) != 0) {
        return false;
    }

    return realTimeCombatIsMapNameEnabled(name);
}

void realTimeCombatSetPendingMap(int map)
{
    gPendingMap = map;
    gPendingMapName[0] = '\0';
    gMapTransitionInProgress = true;
}

void realTimeCombatSetPendingMapName(const char* name)
{
    if (name == nullptr) {
        gPendingMapName[0] = '\0';
        return;
    }

    strncpy(gPendingMapName, name, sizeof(gPendingMapName) - 1);
    gPendingMapName[sizeof(gPendingMapName) - 1] = '\0';
}

void realTimeCombatClearPendingMap()
{
    gPendingMap = -1;
    gPendingMapName[0] = '\0';
    gMapTransitionInProgress = false;
}

bool realTimeCombatIsMapEnabled()
{
    return true;
}

bool realTimeCombatShouldBlockClassicCombat()
{
    return true;
}

bool realTimeCombatIsEnabled()
{
    return gGameLoaded
        && !gameUiIsDisabled()
        && gameGetState() == GAME_STATE_0
        && interfaceBarEnabled()
        && !isoIsDisabled()
        && realTimeCombatIsMapEnabled();
}

void realTimeCombatTrace(const char* context, CombatStartData* combatStartData)
{
    Object* attacker = combatStartData != nullptr ? combatStartData->attacker : nullptr;
    Object* defender = combatStartData != nullptr ? combatStartData->defender : nullptr;

    char line[512];
    snprintf(line,
        sizeof(line),
        "RTC %s: blockClassic=%d currentMap=%d currentName=%s pendingMap=%d pendingName=%s transition=%d elev=%d combatState=0x%X attacker=%p defender=%p\n",
        context,
        realTimeCombatShouldBlockClassicCombat() ? 1 : 0,
        gMapHeader.index,
        gMapHeader.name,
        gPendingMap,
        gPendingMapName,
        gMapTransitionInProgress ? 1 : 0,
        gElevation,
        gCombatState,
        (void*)attacker,
        (void*)defender);

    debugPrint("\n%s", line);
    realTimeCombatWriteTraceLine("rtcombat_debug.log", line);
    realTimeCombatWriteTraceLine("data\\rtcombat_debug.log", line);
    realTimeCombatWriteTraceLineNearFile(settings.system.master_dat_path.c_str(), line);
}

bool realTimeCombatHandleTurnBasedCombatRequest(CombatStartData* combatStartData)
{
    realTimeCombatTrace("handle-turn-based-request", combatStartData);

    if (!realTimeCombatShouldBlockClassicCombat()) {
        return false;
    }

    if (isInCombat()) {
        _combat_over_from_load();
    }

    if (combatStartData != nullptr
        && combatStartData->attacker != nullptr
        && combatStartData->defender != nullptr
        && FID_TYPE(combatStartData->attacker->fid) == OBJ_TYPE_CRITTER
        && FID_TYPE(combatStartData->defender->fid) == OBJ_TYPE_CRITTER) {
        critterSetWhoHitMe(combatStartData->defender, combatStartData->attacker);

        if (combatStartData->attacker != gDude
            && combatStartData->attacker->data.critter.combat.team != combatStartData->defender->data.critter.combat.team) {
            critterSetWhoHitMe(combatStartData->attacker, combatStartData->defender);
            combatStartData->attacker->data.critter.combat.maneuver |= CRITTER_MANEUVER_ENGAGING;
        }

        _combatai_notify_onlookers(combatStartData->defender);
    }

    return true;
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

static bool realTimeCombatFaceObject(Object* object, Object* target)
{
    if (object == nullptr || target == nullptr || object->tile == target->tile) {
        return false;
    }

    int rotation = tileGetRotationTo(object->tile, target->tile);
    if (rotation == object->rotation) {
        return false;
    }

    Rect dirtyRect;
    if (objectSetRotation(object, rotation, &dirtyRect) != 0) {
        return false;
    }

    tileWindowRefreshRect(&dirtyRect, object->elevation);
    return true;
}

static bool realTimeCombatIsCtrlPressed()
{
    return gPressedPhysicalKeys[SDL_SCANCODE_LCTRL] != KEY_STATE_UP
        || gPressedPhysicalKeys[SDL_SCANCODE_RCTRL] != KEY_STATE_UP;
}

static int realTimeCombatAbs(int value)
{
    return value < 0 ? -value : value;
}

static int realTimeCombatSquared(int value)
{
    return value * value;
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

static bool realTimeCombatGetNpcAttackMode(Object* critter, int* hitMode)
{
    Object* weapon = critterGetItem2(critter);
    if (weapon != nullptr && itemGetType(weapon) == ITEM_TYPE_WEAPON) {
        *hitMode = HIT_MODE_RIGHT_WEAPON_PRIMARY;
        return weaponGetAttackTypeForHitMode(weapon, *hitMode) != ATTACK_TYPE_NONE;
    }

    weapon = critterGetItem1(critter);
    if (weapon != nullptr && itemGetType(weapon) == ITEM_TYPE_WEAPON) {
        *hitMode = HIT_MODE_LEFT_WEAPON_PRIMARY;
        return weaponGetAttackTypeForHitMode(weapon, *hitMode) != ATTACK_TYPE_NONE;
    }

    *hitMode = HIT_MODE_PUNCH;
    return true;
}

static Object* realTimeCombatGetTargetUnderCursor()
{
    Object* target = gameMouseGetObjectUnderCursor(OBJ_TYPE_CRITTER, false, gDude->elevation);
    if (target != nullptr && target != gDude) {
        if ((target->flags & OBJECT_HIDDEN) == 0
            && (target->data.critter.combat.results & (DAM_DEAD | DAM_KNOCKED_OUT)) == 0) {
            return target;
        }
    }

    int mouseX;
    int mouseY;
    mouseGetPosition(&mouseX, &mouseY);

    Object** critters;
    int critterCount = objectListCreate(-1, gDude->elevation, OBJ_TYPE_CRITTER, &critters);
    if (critterCount <= 0) {
        return nullptr;
    }

    Object* bestTarget = nullptr;
    int bestDistance = INT_MAX;

    for (int index = 0; index < critterCount; index++) {
        Object* candidate = critters[index];
        if (candidate == gDude
            || (candidate->flags & OBJECT_HIDDEN) != 0
            || (candidate->data.critter.combat.results & (DAM_DEAD | DAM_KNOCKED_OUT)) != 0) {
            continue;
        }

        Rect candidateRect;
        objectGetRect(candidate, &candidateRect);
        candidateRect.left -= kAttackTargetPadding;
        candidateRect.top -= kAttackTargetPadding;
        candidateRect.right += kAttackTargetPadding;
        candidateRect.bottom += kAttackTargetPadding;

        if (mouseX < candidateRect.left
            || mouseX > candidateRect.right
            || mouseY < candidateRect.top
            || mouseY > candidateRect.bottom) {
            continue;
        }

        int centerX = (candidateRect.left + candidateRect.right) / 2;
        int centerY = (candidateRect.top + candidateRect.bottom) / 2;
        int distance = realTimeCombatSquared(mouseX - centerX) + realTimeCombatSquared(mouseY - centerY);
        if (distance < bestDistance) {
            bestDistance = distance;
            bestTarget = candidate;
        }
    }

    objectListFree(critters);
    return bestTarget;
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

    if ((target->flags & OBJECT_HIDDEN) != 0
        || (target->data.critter.combat.results & (DAM_DEAD | DAM_KNOCKED_OUT)) != 0) {
        return nullptr;
    }

    if (!_obj_action_can_talk_to(target)) {
        return nullptr;
    }

    return target;
}

static Object* realTimeCombatGetInteractTargetUnderCursor()
{
    return gameMouseGetObjectUnderCursor(-1, true, gDude->elevation);
}

static bool realTimeCombatIsNaturallyHostileCritter(Object* critter)
{
    switch (critterGetKillType(critter)) {
    case KILL_TYPE_RADSCORPION:
    case KILL_TYPE_RAT:
    case KILL_TYPE_MANTIS:
    case KILL_TYPE_PLANT:
    case KILL_TYPE_ALIEN:
    case KILL_TYPE_GIANT_ANT:
        return true;
    default:
        return false;
    }
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

static bool realTimeCombatCanNpcAttack(Object* attacker, Object* target, int hitMode)
{
    int savedActionPoints = attacker->data.critter.combat.ap;
    int actionPointsRequired = weaponGetActionPointCost(attacker, hitMode, false);
    if (attacker->data.critter.combat.ap < actionPointsRequired) {
        attacker->data.critter.combat.ap = actionPointsRequired;
    }

    int badShot = _combat_check_bad_shot(attacker, target, hitMode, false);
    attacker->data.critter.combat.ap = savedActionPoints;

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
        realTimeCombatFinalizeAttack();
        realTimeCombatNotifyAttackTarget(target, critterGetWeaponForHitMode(gDude, hitMode));
        gLastAttackTime = now;
    }

    return rc == 0;
}

static bool realTimeCombatNpcAttack(Object* attacker, Object* target, int hitMode)
{
    if (attacker == nullptr || target == nullptr || animationIsBusy(attacker)) {
        return false;
    }

    if (!realTimeCombatCanNpcAttack(attacker, target, hitMode)) {
        return false;
    }

    int savedActionPoints = attacker->data.critter.combat.ap;
    int actionPointsRequired = weaponGetActionPointCost(attacker, hitMode, false);
    if (attacker->data.critter.combat.ap < actionPointsRequired) {
        attacker->data.critter.combat.ap = actionPointsRequired;
    }

    realTimeCombatFaceObject(attacker, target);

    int rc = _combat_attack(attacker, target, hitMode, HIT_LOCATION_UNCALLED);
    attacker->data.critter.combat.ap = savedActionPoints;

    return rc == 0;
}

static void realTimeCombatFinalizeAttack()
{
    Attack* attack = combat_get_data();
    if (attack == nullptr || attack->attacker == nullptr) {
        return;
    }

    Object* weapon = critterGetWeaponForHitMode(attack->attacker, attack->hitMode);
    if (weapon != nullptr && ammoGetCapacity(weapon) > 0) {
        ammoSetQuantity(weapon, ammoGetQuantity(weapon) - attack->ammoQuantity);

        if (attack->attacker == gDude) {
            _intface_update_ammo_lights();
        }
    }

    _combat_display(attack);
    _apply_damage(attack, true);
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
            return;
        }

        target = realTimeCombatGetInteractTargetUnderCursor();
        if (target != nullptr
            && target != gDude
            && FID_TYPE(target->fid) == OBJ_TYPE_SCENERY
            && _obj_action_can_use(target)) {
            gWasMoving = false;
            _action_use_an_object(gDude, target);
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

static void realTimeCombatSetObjectMovingAnimation(Object* object, bool moving)
{
    int anim = moving ? ANIM_RUNNING : ANIM_STAND;
    if (FID_ANIM_TYPE(object->fid) == anim) {
        return;
    }

    Rect dirtyRect;
    int fid = buildFid(FID_TYPE(object->fid), object->fid & 0xFFF, anim, (object->fid & 0xF000) >> 12, object->rotation + 1);
    if (moving && !artExists(fid)) {
        fid = buildFid(FID_TYPE(object->fid), object->fid & 0xFFF, ANIM_WALK, (object->fid & 0xF000) >> 12, object->rotation + 1);
    }

    if (objectSetFid(object, fid, &dirtyRect) == 0) {
        Rect frameRect;
        objectSetFrame(object, 0, &frameRect);
        rectUnion(&dirtyRect, &frameRect, &dirtyRect);
        tileWindowRefreshRect(&dirtyRect, object->elevation);
    }
}

static void realTimeCombatAdvanceObjectMovingAnimation(Object* object, unsigned int now)
{
    if (getTicksBetween(now, gLastNpcMoveFrameTime) < kMoveFrameDelayMs) {
        return;
    }

    Rect dirtyRect;
    if (objectSetNextFrame(object, &dirtyRect) == 0) {
        tileWindowRefreshRect(&dirtyRect, object->elevation);
    }
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
    realTimeCombatSetObjectMovingAnimation(gDude, moving);
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

static bool realTimeCombatSyncTileForFootPosition(Object* object, int footX, int footY, Rect* dirtyRect, bool* changedTile)
{
    *changedTile = false;

    int tile = tileFromScreenXY(footX, footY);
    if (!tileIsValid(tile)) {
        return false;
    }

    if (tile == object->tile) {
        return true;
    }

    if (_obj_blocking_at(object, tile, object->elevation) != nullptr) {
        return false;
    }

    if (objectSetLocation(object, tile, object->elevation, dirtyRect) != 0) {
        return false;
    }

    *changedTile = true;

    int baseX;
    int baseY;
    if (tileToScreenXY(object->tile, &baseX, &baseY) != 0) {
        return false;
    }

    baseX += 16;
    baseY += 8;

    Rect offsetRect;
    if (_obj_offset(object, footX - baseX, footY - baseY, &offsetRect) == 0) {
        rectUnion(dirtyRect, &offsetRect, dirtyRect);
    }

    if (object == gDude) {
        scriptsExecSpatialProc(gDude, gDude->tile, gDude->elevation);
    }

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
    if (!realTimeCombatSyncTileForFootPosition(gDude, footX, footY, &dirtyRect, &changedTile)) {
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

static bool realTimeCombatIsHostileToDude(Object* critter)
{
    if (critter == nullptr || critter == gDude) {
        return false;
    }

    if ((critter->flags & OBJECT_HIDDEN) != 0
        || (critter->data.critter.combat.results & (DAM_DEAD | DAM_KNOCKED_OUT)) != 0) {
        return false;
    }

    if (critter->elevation != gDude->elevation) {
        return false;
    }

    if (critter->data.critter.combat.whoHitMe == gDude) {
        return true;
    }

    int disposition = aiGetDisposition(critter) + 1;
    if (critter->data.critter.combat.team != gDude->data.critter.combat.team
        && (disposition == DISPOSITION_AGGRESSIVE
            || disposition == DISPOSITION_BERKSERK
            || realTimeCombatIsNaturallyHostileCritter(critter))
        && isWithinPerception(critter, gDude)) {
        critterSetWhoHitMe(critter, gDude);
        critter->data.critter.combat.maneuver |= CRITTER_MANEUVER_ENGAGING;
        return true;
    }

    return (critter->data.critter.combat.maneuver & CRITTER_MANEUVER_ENGAGING) != 0
        && critter->data.critter.combat.team != gDude->data.critter.combat.team;
}

static bool realTimeCombatMoveNpcTowardDude(Object* critter, unsigned int now)
{
    int baseX;
    int baseY;
    if (tileToScreenXY(critter->tile, &baseX, &baseY) != 0) {
        return false;
    }

    int dudeBaseX;
    int dudeBaseY;
    if (tileToScreenXY(gDude->tile, &dudeBaseX, &dudeBaseY) != 0) {
        return false;
    }

    int critterFootX = baseX + 16 + critter->x;
    int critterFootY = baseY + 8 + critter->y;
    int dudeFootX = dudeBaseX + 16 + gDude->x;
    int dudeFootY = dudeBaseY + 8 + gDude->y;

    int deltaX = dudeFootX - critterFootX;
    int deltaY = dudeFootY - critterFootY;
    int absDeltaX = realTimeCombatAbs(deltaX);
    int absDeltaY = realTimeCombatAbs(deltaY);
    if (absDeltaX == 0 && absDeltaY == 0) {
        return false;
    }

    int dx = 0;
    int dy = 0;
    if (absDeltaX >= absDeltaY) {
        dx = deltaX > 0 ? kNpcMovePixelsPerFrame : -kNpcMovePixelsPerFrame;
        dy = absDeltaY == 0 ? 0 : deltaY * kNpcMovePixelsPerFrame / absDeltaX;
    } else {
        dx = absDeltaX == 0 ? 0 : deltaX * kNpcMovePixelsPerFrame / absDeltaY;
        dy = deltaY > 0 ? kNpcMovePixelsPerFrame : -kNpcMovePixelsPerFrame;
    }

    realTimeCombatFaceObject(critter, gDude);
    realTimeCombatSetObjectMovingAnimation(critter, true);
    realTimeCombatAdvanceObjectMovingAnimation(critter, now);

    Rect dirtyRect;
    objectGetRect(critter, &dirtyRect);

    int footX = critterFootX + dx;
    int footY = critterFootY + dy;
    bool changedTile;
    if (!realTimeCombatSyncTileForFootPosition(critter, footX, footY, &dirtyRect, &changedTile)) {
        return false;
    }

    if (!changedTile) {
        Rect offsetRect;
        if (_obj_offset(critter, dx, dy, &offsetRect) == 0) {
            rectUnion(&dirtyRect, &offsetRect, &dirtyRect);
        }
    }

    tileWindowRefreshRect(&dirtyRect, critter->elevation);
    return true;
}

static void realTimeCombatHandleNpcs()
{
    if ((gDude->data.critter.combat.results & (DAM_DEAD | DAM_KNOCKED_OUT)) != 0) {
        return;
    }

    Object** critters;
    int critterCount = objectListCreate(-1, gDude->elevation, OBJ_TYPE_CRITTER, &critters);
    if (critterCount <= 0) {
        return;
    }

    unsigned int now = getTicks();

    for (int index = 0; index < critterCount; index++) {
        Object* critter = critters[index];
        if (!realTimeCombatIsHostileToDude(critter) || animationIsBusy(critter)) {
            continue;
        }

        int hitMode;
        if (!realTimeCombatGetNpcAttackMode(critter, &hitMode)) {
            continue;
        }

        int range = weaponGetRange(critter, hitMode);
        if (objectGetDistanceBetween(critter, gDude) > range) {
            realTimeCombatMoveNpcTowardDude(critter, now);
            continue;
        }

        unsigned int lastAttackTime = gNpcLastAttackTimes[critter];
        if (lastAttackTime != 0 && getTicksBetween(now, lastAttackTime) < kNpcAttackCooldownMs) {
            continue;
        }

        if (realTimeCombatNpcAttack(critter, gDude, hitMode)) {
            realTimeCombatFinalizeAttack();
            gNpcLastAttackTimes[critter] = now;
        }
    }

    objectListFree(critters);
    gLastNpcMoveFrameTime = now;
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
        gNpcLastAttackTimes.clear();
        return false;
    }

    if (keyCode == KEY_LOWERCASE_R || keyCode == KEY_UPPERCASE_R) {
        realTimeCombatReload();
    }

    realTimeCombatFaceMouse();
    realTimeCombatHandleMouse();
    realTimeCombatHandleMovement();
    realTimeCombatHandleNpcs();

    return realTimeCombatConsumesKey(keyCode);
}

} // namespace fallout
