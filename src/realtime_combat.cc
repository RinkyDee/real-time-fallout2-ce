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
#include "game_sound.h"
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
// NPC continuous-movement speed (pixels/frame). Slightly slower than the player
// so the player can still kite, but fast enough to close in.
static constexpr int kNpcMovePixelsPerFrame = 3;
static constexpr int kAttackTargetPadding = 24;
static constexpr unsigned int kAttackCooldownMs = 650;
static constexpr unsigned int kNpcAttackCooldownMs = 2200;
static constexpr unsigned int kDudeAttackAnimationHoldMs = 750;
// How long after an NPC starts an attack to leave its attack animation alone
// before real-time movement may resume / interrupt it.
static constexpr unsigned int kNpcAttackAnimationHoldMs = 700;
// How often a pursuing critter recomputes its detour path around walls while it
// cannot see the player in a straight line.
static constexpr unsigned int kNpcRepathIntervalMs = 250;
// Maximum number of path waypoints cached per critter.
static constexpr int kNpcPathMax = 48;
// Spacing (pixels) between samples when testing a straight walk line.
static constexpr int kNpcLineSampleSpacing = 12;
// How far a fleeing critter tries to run from the player in one move.
static constexpr int kNpcFleeDistance = 8;

// Per-critter real-time AI bookkeeping. NPC movement is continuous and pixel
// based (like the player): the critter homes straight toward the player when it
// has a clear walk line, and otherwise follows a cached pathfinder detour around
// walls. The tile stays authoritative for collision/scripts; only the visible
// motion is freed from the hex grid.
struct NpcAiState {
    unsigned int lastAttackTime = 0;
    unsigned int lastPathTime = 0;
    unsigned int lastFrameAdvanceTime = 0;
    int pathTiles[kNpcPathMax];
    int pathLength = 0;
    int pathIndex = 0;
    int pathTargetTile = -1;
    int fleeTile = -1;
};

static unsigned int gLastMoveFrameTime = 0;
static unsigned int gLastAttackTime = 0;
static unsigned int gLastDudeAttackAnimationTime = 0;
static bool gWasMoving = false;
static bool gCursorModeActive = false;
static int gSavedMouseCursor = MOUSE_CURSOR_NONE;
static bool gSavedMouseObjectsVisible = false;
static int gPendingMap = -1;
static char gPendingMapName[16];
static bool gMapTransitionInProgress = false;
static Object* gLootHoverTarget = nullptr;
static std::unordered_map<Object*, NpcAiState> gNpcAiStates;

static void realTimeCombatFinalizeAttack(Attack* attack);
static int realTimeCombatBuildExistingCritterFid(Object* object, int anim, int preferredWeaponAnimationCode = -1);
static void realTimeCombatSetCritterFidIfNeeded(Object* object, int fid);
static void realTimeCombatSetCursor(int cursor);

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

bool realTimeCombatIsDeathAnimationPending()
{
    return realTimeCombatIsEnabled()
        && (gDude->data.critter.combat.results & DAM_DEAD) != 0
        && animationIsBusy(gDude);
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

    if (enteringCursorMode) {
        realTimeCombatSetCursor(MOUSE_CURSOR_ARROW);
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

static void realTimeCombatClearLootHover()
{
    if (gLootHoverTarget == nullptr) {
        return;
    }

    Rect dirtyRect;
    if (objectClearOutline(gLootHoverTarget, &dirtyRect) == 0) {
        tileWindowRefreshRect(&dirtyRect, gLootHoverTarget->elevation);
    }

    gLootHoverTarget = nullptr;
}

bool realTimeCombatIsSkillTargetingActive()
{
    switch (gameMouseGetMode()) {
    case GAME_MOUSE_MODE_USE_CROSSHAIR:
    case GAME_MOUSE_MODE_USE_FIRST_AID:
    case GAME_MOUSE_MODE_USE_DOCTOR:
    case GAME_MOUSE_MODE_USE_LOCKPICK:
    case GAME_MOUSE_MODE_USE_STEAL:
    case GAME_MOUSE_MODE_USE_TRAPS:
    case GAME_MOUSE_MODE_USE_SCIENCE:
    case GAME_MOUSE_MODE_USE_REPAIR:
        return true;
    default:
        return false;
    }
}

void realTimeCombatRefreshCursor()
{
    // While a Skilldex skill is being aimed at a target, hand the cursor back to
    // the classic game-mouse handler so it can show the use-crosshair and run the
    // skill-on-target click logic.
    if (realTimeCombatIsEnabled() && !realTimeCombatIsSkillTargetingActive()) {
        realTimeCombatEnterCursorMode();
    } else {
        realTimeCombatClearLootHover();
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

static int realTimeCombatSquared(int value)
{
    return value * value;
}

static int realTimeCombatAbs(int value)
{
    return value < 0 ? -value : value;
}

static bool realTimeCombatCanInterruptDudeAnimation()
{
    return (gDude->data.critter.combat.results & (DAM_DEAD | DAM_KNOCKED_OUT)) == 0;
}

static bool realTimeCombatDudeAttackAnimationIsProtected()
{
    if (gLastDudeAttackAnimationTime == 0) {
        return false;
    }

    if (getTicksBetween(getTicks(), gLastDudeAttackAnimationTime) < kDudeAttackAnimationHoldMs) {
        return true;
    }

    return animationIsBusy(gDude) != 0;
}

static bool realTimeCombatInterruptDudeAnimation()
{
    if (!animationIsBusy(gDude)) {
        return true;
    }

    if (!realTimeCombatCanInterruptDudeAnimation()) {
        return false;
    }

    return reg_anim_clear(gDude) != -2;
}

static void realTimeCombatSetCursor(int cursor)
{
    if (gameMouseGetCursor() == cursor) {
        return;
    }

    mouseHideCursor();
    gameMouseSetCursor(cursor);
    mouseShowCursor();
}

static bool realTimeCombatIsReloadHitMode(int hitMode)
{
    return hitMode == HIT_MODE_LEFT_WEAPON_RELOAD
        || hitMode == HIT_MODE_RIGHT_WEAPON_RELOAD;
}

static bool realTimeCombatHitModeMatchesRange(Object* weapon, int hitMode, bool ranged)
{
    if (realTimeCombatIsReloadHitMode(hitMode)) {
        return false;
    }

    if (weapon == nullptr && !isUnarmedHitMode(hitMode)) {
        return false;
    }

    int attackType = weaponGetAttackTypeForHitMode(weapon, hitMode);
    bool isRangedAttack = attackType == ATTACK_TYPE_RANGED || attackType == ATTACK_TYPE_THROW;
    return ranged ? isRangedAttack : !isRangedAttack;
}

static bool realTimeCombatGetFallbackAttackMode(bool ranged, int* hitMode)
{
    int hand = interfaceGetCurrentHand();
    Object* weapon = hand == HAND_RIGHT ? critterGetItem2(gDude) : critterGetItem1(gDude);

    if (weapon == nullptr || itemGetType(weapon) != ITEM_TYPE_WEAPON) {
        if (ranged) {
            return false;
        }

        *hitMode = HIT_MODE_PUNCH;
        return true;
    }

    int primaryHitMode = hand == HAND_RIGHT ? HIT_MODE_RIGHT_WEAPON_PRIMARY : HIT_MODE_LEFT_WEAPON_PRIMARY;
    if (realTimeCombatHitModeMatchesRange(weapon, primaryHitMode, ranged)) {
        *hitMode = primaryHitMode;
        return true;
    }

    int secondaryHitMode = hand == HAND_RIGHT ? HIT_MODE_RIGHT_WEAPON_SECONDARY : HIT_MODE_LEFT_WEAPON_SECONDARY;
    if (realTimeCombatHitModeMatchesRange(weapon, secondaryHitMode, ranged)) {
        *hitMode = secondaryHitMode;
        return true;
    }

    return false;
}

static bool realTimeCombatGetAttackMode(bool ranged, int* hitMode)
{
    if (interface_get_current_attack_mode(hitMode)) {
        Object* weapon = critterGetWeaponForHitMode(gDude, *hitMode);
        if (weapon == nullptr && !isUnarmedHitMode(*hitMode)) {
            *hitMode = HIT_MODE_PUNCH;
        }

        if (realTimeCombatHitModeMatchesRange(weapon, *hitMode, ranged)) {
            return true;
        }
    }

    return realTimeCombatGetFallbackAttackMode(ranged, hitMode);
}

static bool realTimeCombatGetDefaultAttackMode(int* hitMode)
{
    if (realTimeCombatGetAttackMode(true, hitMode)) {
        return true;
    }

    if (realTimeCombatGetAttackMode(false, hitMode)) {
        return true;
    }

    return false;
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

static bool realTimeCombatIsLootableCritter(Object* target)
{
    return target != nullptr
        && target != gDude
        && FID_TYPE(target->fid) == OBJ_TYPE_CRITTER
        && (target->flags & OBJECT_HIDDEN) == 0
        && (target->data.critter.combat.results & DAM_DEAD) != 0
        && !critterFlagCheck(target->pid, CRITTER_NO_STEAL);
}

static Object* realTimeCombatGetLootTargetUnderCursor()
{
    Object* target = gameMouseGetObjectUnderCursor(-1, true, gDude->elevation);
    if (target == nullptr || target == gDude || (target->flags & OBJECT_HIDDEN) != 0) {
        return nullptr;
    }

    if (FID_TYPE(target->fid) == OBJ_TYPE_ITEM) {
        return target;
    }

    if (realTimeCombatIsLootableCritter(target)) {
        return target;
    }

    return nullptr;
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

static int realTimeCombatNpcBadShotReason(Object* attacker, Object* target, int hitMode)
{
    int savedActionPoints = attacker->data.critter.combat.ap;
    int actionPointsRequired = weaponGetActionPointCost(attacker, hitMode, false);
    if (attacker->data.critter.combat.ap < actionPointsRequired) {
        attacker->data.critter.combat.ap = actionPointsRequired;
    }

    int badShot = _combat_check_bad_shot(attacker, target, hitMode, false);
    attacker->data.critter.combat.ap = savedActionPoints;

    return badShot;
}

static bool realTimeCombatCanNpcAttack(Object* attacker, Object* target, int hitMode)
{
    return realTimeCombatNpcBadShotReason(attacker, target, hitMode) == COMBAT_BAD_SHOT_OK;
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

static void realTimeCombatPlayAttackAnimation(Object* attacker, Object* target, int hitMode)
{
    if (attacker == nullptr || target == nullptr) {
        return;
    }

    if ((attacker->data.critter.combat.results & (DAM_DEAD | DAM_KNOCKED_OUT)) != 0) {
        return;
    }

    int anim = critterGetAnimationForHitMode(attacker, hitMode);
    Object* weapon = critterGetWeaponForHitMode(attacker, hitMode);
    int weaponAnimationCode = weapon != nullptr ? weaponGetAnimationCode(weapon) : 0;
    int fid = realTimeCombatBuildExistingCritterFid(attacker, anim, weaponAnimationCode);
    bool hasAttackArt = artExists(fid);

    char sfxName[16];
    if (weapon != nullptr && weaponAnimationCode != 0) {
        strcpy(sfxName, sfxBuildWeaponName(WEAPON_SOUND_EFFECT_ATTACK, weapon, hitMode, target));
    } else {
        strcpy(sfxName, sfxBuildCharName(attacker, anim, CHARACTER_SOUND_EFFECT_UNUSED));
    }

    reg_anim_clear(attacker);
    if (hasAttackArt) {
        realTimeCombatSetCritterFidIfNeeded(attacker, fid);
    }

    if (attacker == gDude) {
        gWasMoving = false;
        gLastDudeAttackAnimationTime = getTicks();
    }

    reg_anim_begin(ANIMATION_REQUEST_UNRESERVED);
    animationRegisterRotateToTile(attacker, target->tile);
    animationRegisterPlaySoundEffect(attacker, sfxName, -1);
    if (hasAttackArt) {
        animationRegisterAnimate(attacker, anim, 0);
    }
    reg_anim_end();
}

static bool realTimeCombatPerformAttack(Object* attacker, Object* target, int hitMode, bool aiming)
{
    if (attacker == nullptr || target == nullptr) {
        return false;
    }

    if ((attacker->data.critter.combat.results & (DAM_DEAD | DAM_KNOCKED_OUT)) != 0
        || (target->data.critter.combat.results & (DAM_DEAD | DAM_KNOCKED_OUT)) != 0) {
        return false;
    }

    int savedActionPoints = attacker->data.critter.combat.ap;
    int actionPointsRequired = weaponGetActionPointCost(attacker, hitMode, aiming);
    if (attacker->data.critter.combat.ap < actionPointsRequired) {
        attacker->data.critter.combat.ap = actionPointsRequired;
    }

    Attack attack;
    attackInit(&attack, attacker, target, hitMode, HIT_LOCATION_UNCALLED);
    int rc = attackCompute(&attack);
    attacker->data.critter.combat.ap = savedActionPoints;

    if (attacker == gDude) {
        interfaceRenderActionPoints(attacker->data.critter.combat.ap, _combat_free_move);
    }

    if (rc == -1) {
        return false;
    }

    realTimeCombatFaceObject(attacker, target);
    realTimeCombatPlayAttackAnimation(attacker, target, hitMode);
    realTimeCombatFinalizeAttack(&attack);
    aiInfoSetLastTarget(attacker, target);

    return true;
}

static bool realTimeCombatAttack(Object* target, int hitMode, bool aiming)
{
    if (target == nullptr) {
        return false;
    }

    unsigned int now = getTicks();
    if (gLastAttackTime != 0 && getTicksBetween(now, gLastAttackTime) < kAttackCooldownMs) {
        return false;
    }

    if (!realTimeCombatCanAttack(target, hitMode, aiming)) {
        return false;
    }

    gWasMoving = false;
    if (realTimeCombatPerformAttack(gDude, target, hitMode, aiming)) {
        realTimeCombatNotifyAttackTarget(target, critterGetWeaponForHitMode(gDude, hitMode));
        gLastAttackTime = now;
        return true;
    }

    return false;
}

static bool realTimeCombatNpcAttack(Object* attacker, Object* target, int hitMode)
{
    if (attacker == nullptr || target == nullptr) {
        return false;
    }

    if (!realTimeCombatCanNpcAttack(attacker, target, hitMode)) {
        return false;
    }

    return realTimeCombatPerformAttack(attacker, target, hitMode, false);
}

static void realTimeCombatEnsureCritterDeathAnimation(Object* critter)
{
    if (critter == nullptr || FID_TYPE(critter->fid) != OBJ_TYPE_CRITTER) {
        return;
    }

    if ((critter->data.critter.combat.results & DAM_DEAD) == 0) {
        return;
    }

    int currentAnim = FID_ANIM_TYPE(critter->fid);
    if (currentAnim == ANIM_FALL_BACK || currentAnim == ANIM_FALL_FRONT) {
        return;
    }

    int anim = ANIM_FALL_BACK;
    int fid = buildFid(FID_TYPE(critter->fid), critter->fid & 0xFFF, anim, (critter->fid & 0xF000) >> 12, critter->rotation + 1);
    if (!artExists(fid)) {
        anim = ANIM_FALL_FRONT;
        fid = buildFid(FID_TYPE(critter->fid), critter->fid & 0xFFF, anim, (critter->fid & 0xF000) >> 12, critter->rotation + 1);
    }

    if (!artExists(fid)) {
        return;
    }

    reg_anim_clear(critter);
    reg_anim_begin(ANIMATION_REQUEST_RESERVED);
    animationRegisterAnimate(critter, anim, 0);
    reg_anim_end();
}

static void realTimeCombatEnsureAttackDeathAnimations(Attack* attack)
{
    if (attack == nullptr) {
        return;
    }

    if ((attack->attackerFlags & DAM_DEAD) != 0) {
        realTimeCombatEnsureCritterDeathAnimation(attack->attacker);
    }

    if ((attack->defenderFlags & DAM_DEAD) != 0) {
        realTimeCombatEnsureCritterDeathAnimation(attack->defender);
    }

    for (int index = 0; index < attack->extrasLength; index++) {
        if ((attack->extrasFlags[index] & DAM_DEAD) != 0) {
            realTimeCombatEnsureCritterDeathAnimation(attack->extras[index]);
        }
    }
}

static void realTimeCombatFinalizeDeadCritterState(Object* critter)
{
    if (critter == nullptr || FID_TYPE(critter->fid) != OBJ_TYPE_CRITTER) {
        return;
    }

    if ((critter->data.critter.combat.results & DAM_DEAD) == 0) {
        return;
    }

    Rect dirtyRect;
    objectGetRect(critter, &dirtyRect);

    Rect tempRect;
    if ((critter->flags & OBJECT_NO_BLOCK) == 0) {
        critter->flags |= OBJECT_NO_BLOCK;
        if (!critterFlagCheck(critter->pid, CRITTER_FLAT) && _obj_toggle_flat(critter, &tempRect) == 0) {
            rectUnion(&dirtyRect, &tempRect, &dirtyRect);
        }
    }

    if (objectDisableOutline(critter, &tempRect) == 0) {
        rectUnion(&dirtyRect, &tempRect, &dirtyRect);
    }

    tileWindowRefreshRect(&dirtyRect, critter->elevation);
}

static void realTimeCombatFinalizeAttackDeadCritterStates(Attack* attack)
{
    if (attack == nullptr) {
        return;
    }

    if ((attack->attackerFlags & DAM_DEAD) != 0) {
        realTimeCombatFinalizeDeadCritterState(attack->attacker);
    }

    if ((attack->defenderFlags & DAM_DEAD) != 0) {
        realTimeCombatFinalizeDeadCritterState(attack->defender);
    }

    for (int index = 0; index < attack->extrasLength; index++) {
        if ((attack->extrasFlags[index] & DAM_DEAD) != 0) {
            realTimeCombatFinalizeDeadCritterState(attack->extras[index]);
        }
    }
}

static void realTimeCombatFinalizeAttack(Attack* attack)
{
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
    realTimeCombatFinalizeAttackDeadCritterStates(attack);
    realTimeCombatEnsureAttackDeathAnimations(attack);
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

    if (animationIsBusy(gDude) && !realTimeCombatCanInterruptDudeAnimation()) {
        return;
    }

    if ((mouseState & MOUSE_EVENT_RIGHT_BUTTON_DOWN) != 0
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

    Object* target = realTimeCombatGetTargetUnderCursor();
    if (target != nullptr) {
        int hitMode;
        if (realTimeCombatGetDefaultAttackMode(&hitMode)) {
            realTimeCombatAttack(target, hitMode, false);
        }
        return;
    }

    Object* lootTarget = realTimeCombatGetLootTargetUnderCursor();
    if (lootTarget != nullptr && objectWithinWalkDistance(gDude, lootTarget)) {
        gWasMoving = false;
        if (FID_TYPE(lootTarget->fid) == OBJ_TYPE_CRITTER) {
            actionLootCritter(gDude, lootTarget);
        } else {
            actionPickUp(gDude, lootTarget);
        }
        return;
    }
}

static void realTimeCombatUpdateLootHover()
{
    if (realTimeCombatGetTargetUnderCursor() != nullptr) {
        realTimeCombatClearLootHover();
        return;
    }

    Object* target = realTimeCombatGetLootTargetUnderCursor();
    if (target != nullptr && !objectWithinWalkDistance(gDude, target)) {
        target = nullptr;
    }

    if (target == gLootHoverTarget) {
        return;
    }

    realTimeCombatClearLootHover();

    if (target == nullptr) {
        return;
    }

    Rect dirtyRect;
    if (objectSetOutline(target, OUTLINE_TYPE_ITEM, &dirtyRect) == 0) {
        tileWindowRefreshRect(&dirtyRect, target->elevation);
        gLootHoverTarget = target;
    }
}

static void realTimeCombatUpdateCombatCursor()
{
    int hitMode;
    Object* target = realTimeCombatGetTargetUnderCursor();
    if (target != nullptr
        && realTimeCombatGetAttackMode(true, &hitMode)
        && realTimeCombatCanAttack(target, hitMode, false)) {
        realTimeCombatSetCursor(MOUSE_CURSOR_CROSSHAIR);
        return;
    }

    if (realTimeCombatGetLootTargetUnderCursor() != nullptr) {
        realTimeCombatSetCursor(MOUSE_CURSOR_ARROW);
        return;
    }

    realTimeCombatSetCursor(MOUSE_CURSOR_ARROW);
}

static int realTimeCombatGetPreferredWeaponAnimationCode(Object* critter)
{
    Object* weapon = nullptr;

    if (critter == gDude) {
        if (interfaceGetActiveItem(&weapon) != 0 || weapon == nullptr || itemGetType(weapon) != ITEM_TYPE_WEAPON) {
            int hand = interfaceGetCurrentHand();
            weapon = hand == HAND_RIGHT ? critterGetItem2(gDude) : critterGetItem1(gDude);
        }
    } else {
        weapon = critterGetItem2(critter);
        if (weapon == nullptr || itemGetType(weapon) != ITEM_TYPE_WEAPON) {
            weapon = critterGetItem1(critter);
        }
    }

    if (weapon == nullptr || itemGetType(weapon) != ITEM_TYPE_WEAPON) {
        return 0;
    }

    return weaponGetAnimationCode(weapon);
}

static int realTimeCombatBuildExistingCritterFid(Object* object, int anim, int preferredWeaponAnimationCode)
{
    int frmId = object->fid & 0xFFF;
    int currentWeaponAnimationCode = (object->fid & 0xF000) >> 12;
    int equippedWeaponAnimationCode = realTimeCombatGetPreferredWeaponAnimationCode(object);
    int weaponAnimationCode = preferredWeaponAnimationCode != -1 ? preferredWeaponAnimationCode : equippedWeaponAnimationCode;
    int rotations[2] = {
        object->rotation + 1,
        FID_ROTATION(object->fid),
    };

    struct Candidate {
        int anim;
        int weaponAnimationCode;
    };

    Candidate candidates[] = {
        { anim, weaponAnimationCode },
        { anim == ANIM_RUNNING ? ANIM_WALK : anim, weaponAnimationCode },
        { anim, equippedWeaponAnimationCode },
        { anim == ANIM_RUNNING ? ANIM_WALK : anim, equippedWeaponAnimationCode },
        { anim, currentWeaponAnimationCode },
        { anim == ANIM_RUNNING ? ANIM_WALK : anim, currentWeaponAnimationCode },
        { anim, 0 },
        { anim == ANIM_RUNNING ? ANIM_WALK : anim, 0 },
        { ANIM_STAND, weaponAnimationCode },
        { ANIM_STAND, equippedWeaponAnimationCode },
        { ANIM_STAND, currentWeaponAnimationCode },
        { ANIM_STAND, 0 },
        { FID_ANIM_TYPE(object->fid), weaponAnimationCode },
        { FID_ANIM_TYPE(object->fid), equippedWeaponAnimationCode },
        { FID_ANIM_TYPE(object->fid), currentWeaponAnimationCode },
        { FID_ANIM_TYPE(object->fid), 0 },
    };

    for (int candidateIndex = 0; candidateIndex < sizeof(candidates) / sizeof(candidates[0]); candidateIndex++) {
        Candidate candidate = candidates[candidateIndex];

        bool duplicateCandidate = false;
        for (int previousCandidateIndex = 0; previousCandidateIndex < candidateIndex; previousCandidateIndex++) {
            if (candidates[previousCandidateIndex].anim == candidate.anim
                && candidates[previousCandidateIndex].weaponAnimationCode == candidate.weaponAnimationCode) {
                duplicateCandidate = true;
                break;
            }
        }

        if (duplicateCandidate) {
            continue;
        }

        for (int rotationIndex = 0; rotationIndex < 2; rotationIndex++) {
            int fid = buildFid(FID_TYPE(object->fid), frmId, candidate.anim, candidate.weaponAnimationCode, rotations[rotationIndex]);
            if (artExists(fid)) {
                return fid;
            }
        }
    }

    return object->fid;
}

static void realTimeCombatSetCritterFidIfNeeded(Object* object, int fid)
{
    if (object == nullptr || object->fid == fid) {
        return;
    }

    Rect dirtyRect;
    if (objectSetFid(object, fid, &dirtyRect) == 0) {
        Rect frameRect;
        objectSetFrame(object, 0, &frameRect);
        rectUnion(&dirtyRect, &frameRect, &dirtyRect);
        tileWindowRefreshRect(&dirtyRect, object->elevation);
    }
}

static void realTimeCombatValidateCritterFid(Object* object)
{
    if (object == nullptr || FID_TYPE(object->fid) != OBJ_TYPE_CRITTER || artExists(object->fid)) {
        return;
    }

    realTimeCombatSetCritterFidIfNeeded(object, realTimeCombatBuildExistingCritterFid(object, FID_ANIM_TYPE(object->fid)));
}

static void realTimeCombatSetObjectMovingAnimation(Object* object, bool moving)
{
    if (object == gDude && realTimeCombatDudeAttackAnimationIsProtected()) {
        return;
    }

    int anim = moving ? ANIM_RUNNING : ANIM_STAND;
    int fid = realTimeCombatBuildExistingCritterFid(object, anim);
    if (object->fid == fid && artExists(fid)) {
        return;
    }

    realTimeCombatSetCritterFidIfNeeded(object, fid);
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
    realTimeCombatValidateCritterFid(gDude);

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

static void realTimeCombatUpdateCamera()
{
    tileSetCenterWithScreenOffset(gDude->tile, -gDude->x, -gDude->y, TILE_SET_CENTER_REFRESH_WINDOW);
}

static void realTimeCombatHandleMovement()
{
    int dx;
    int dy;
    if (!realTimeCombatGetMovementDelta(&dx, &dy)) {
        bool attackAnimationProtected = realTimeCombatDudeAttackAnimationIsProtected();
        if (gWasMoving) {
            if (!attackAnimationProtected) {
                realTimeCombatSetObjectMovingAnimation(gDude, false);
            }
            gWasMoving = false;
        } else if (!animationIsBusy(gDude)
            && !attackAnimationProtected
            && (gDude->data.critter.combat.results & (DAM_DEAD | DAM_KNOCKED_OUT)) == 0
            && FID_ANIM_TYPE(gDude->fid) != ANIM_STAND) {
            realTimeCombatSetObjectMovingAnimation(gDude, false);
        }
        return;
    }

    bool attackAnimationProtected = realTimeCombatDudeAttackAnimationIsProtected();
    if (!attackAnimationProtected && !realTimeCombatInterruptDudeAnimation()) {
        return;
    }

    if (!attackAnimationProtected) {
        realTimeCombatSetMovingAnimation(true);
        realTimeCombatAdvanceMovingAnimation();
    }

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
    realTimeCombatUpdateCamera();

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

// Cap a screen-space delta to a per-frame step of `speed` pixels while keeping
// its direction, so a critter can move toward any point at an arbitrary angle
// (not just along the six hex directions).
static void realTimeCombatNpcNormalizeVector(int deltaX, int deltaY, int speed, int* dx, int* dy)
{
    int absDeltaX = realTimeCombatAbs(deltaX);
    int absDeltaY = realTimeCombatAbs(deltaY);

    *dx = 0;
    *dy = 0;

    if (absDeltaX == 0 && absDeltaY == 0) {
        return;
    }

    if (absDeltaX >= absDeltaY) {
        *dx = deltaX > 0 ? speed : -speed;
        *dy = absDeltaY == 0 ? 0 : deltaY * speed / absDeltaX;
    } else {
        *dx = absDeltaX == 0 ? 0 : deltaX * speed / absDeltaY;
        *dy = deltaY > 0 ? speed : -speed;
    }
}

// Move a critter by a screen-space pixel delta exactly like the player moves:
// shift the sprite by the offset and resynchronize the authoritative tile when
// the foot crosses a tile boundary (validated by _obj_blocking_at). Returns
// false when the step would enter a blocked tile.
static bool realTimeCombatNpcMoveFootBy(Object* critter, int dx, int dy)
{
    if (dx == 0 && dy == 0) {
        return false;
    }

    Rect dirtyRect;
    objectGetRect(critter, &dirtyRect);

    int baseX;
    int baseY;
    if (tileToScreenXY(critter->tile, &baseX, &baseY) != 0) {
        return false;
    }

    int footX = baseX + 16 + critter->x + dx;
    int footY = baseY + 8 + critter->y + dy;
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

// Step the critter one frame toward a screen point (a tile center or the
// player's exact foot position). Reports the applied pixel delta so the caller
// can face the movement direction.
static bool realTimeCombatNpcStepTowardPoint(Object* critter, int targetX, int targetY)
{
    int baseX;
    int baseY;
    if (tileToScreenXY(critter->tile, &baseX, &baseY) != 0) {
        return false;
    }

    int footX = baseX + 16 + critter->x;
    int footY = baseY + 8 + critter->y;

    int dx;
    int dy;
    realTimeCombatNpcNormalizeVector(targetX - footX, targetY - footY, kNpcMovePixelsPerFrame, &dx, &dy);

    return realTimeCombatNpcMoveFootBy(critter, dx, dy);
}

// True when a straight walk line from `fromX,fromY` to `toX,toY` crosses no
// blocked tiles (walls or other critters), so the critter can home directly
// instead of hugging the hex grid. The endpoint tile is ignored so the player's
// own (blocking) tile does not fail the test.
static bool realTimeCombatNpcLineIsClear(Object* critter, int fromX, int fromY, int toX, int toY, int targetTile)
{
    int deltaX = toX - fromX;
    int deltaY = toY - fromY;
    int span = realTimeCombatAbs(deltaX) > realTimeCombatAbs(deltaY)
        ? realTimeCombatAbs(deltaX)
        : realTimeCombatAbs(deltaY);
    int steps = span / kNpcLineSampleSpacing;
    if (steps < 1) {
        return true;
    }

    for (int index = 1; index <= steps; index++) {
        int sampleX = fromX + deltaX * index / steps;
        int sampleY = fromY + deltaY * index / steps;
        int tile = tileFromScreenXY(sampleX, sampleY);
        if (!tileIsValid(tile)) {
            return false;
        }

        if (tile == critter->tile || tile == targetTile) {
            continue;
        }

        if (_obj_blocking_at(critter, tile, critter->elevation) != nullptr) {
            return false;
        }
    }

    return true;
}

static void realTimeCombatFaceTile(Object* critter, int tile)
{
    if (!tileIsValid(tile) || tile == critter->tile) {
        return;
    }

    int rotation = tileGetRotationTo(critter->tile, tile);
    if (rotation == critter->rotation) {
        return;
    }

    Rect dirtyRect;
    if (objectSetRotation(critter, rotation, &dirtyRect) == 0) {
        tileWindowRefreshRect(&dirtyRect, critter->elevation);
    }
}

// Stand in place facing the player. Used while waiting on the attack cooldown,
// holding distance, or when blocked. Keeps idle critters on a clean STAND frame.
static void realTimeCombatNpcHold(Object* critter)
{
    if (animationIsBusy(critter)) {
        return;
    }

    realTimeCombatFaceObject(critter, gDude);
    realTimeCombatSetObjectMovingAnimation(critter, false);
}

// Drive the critter's walk/run animation manually, the same way the player's
// movement is animated, since these critters are no longer played through the
// engine's tile-move animation.
static void realTimeCombatNpcAnimateMovement(Object* critter, NpcAiState& state, unsigned int now)
{
    realTimeCombatSetObjectMovingAnimation(critter, true);
    realTimeCombatValidateCritterFid(critter);

    if (getTicksBetween(now, state.lastFrameAdvanceTime) < kMoveFrameDelayMs) {
        return;
    }

    Rect dirtyRect;
    if (objectSetNextFrame(critter, &dirtyRect) == 0) {
        tileWindowRefreshRect(&dirtyRect, critter->elevation);
    }

    state.lastFrameAdvanceTime = now;
}

// Cache a pathfinder route to the player, used only when a wall blocks the
// straight line. Prefers a collision-free route; if none exists (crowded
// corner) it plans one that ignores other critters so the critter still commits
// to heading around the wall.
static void realTimeCombatNpcComputePath(Object* critter, NpcAiState& state, unsigned int now)
{
    state.pathLength = 0;
    state.pathIndex = 0;
    state.pathTargetTile = gDude->tile;
    state.lastPathTime = now;

    unsigned char rotations[800];
    int length = pathfinderFindPath(critter, critter->tile, gDude->tile, rotations, 0, _obj_blocking_at);
    if (length <= 0) {
        length = pathfinderFindPath(critter, critter->tile, gDude->tile, rotations, 0, _obj_ai_blocking_at);
        if (length <= 0) {
            return;
        }
    }

    int tile = critter->tile;
    int count = length < kNpcPathMax ? length : kNpcPathMax;
    for (int index = 0; index < count; index++) {
        tile = tileGetTileInDirection(tile, rotations[index], 1);
        state.pathTiles[index] = tile;
    }

    state.pathLength = count;
}

// Continuous, pixel-based pursuit. Homes straight toward the player when the
// walk line is clear; otherwise follows the cached pathfinder detour waypoint
// by waypoint. Either way the motion is off-grid and tracks the player's
// current position, instead of hopping between hex centers toward a stale goal.
static void realTimeCombatNpcPursue(Object* critter, NpcAiState& state, unsigned int now)
{
    int critterBaseX;
    int critterBaseY;
    if (tileToScreenXY(critter->tile, &critterBaseX, &critterBaseY) != 0) {
        realTimeCombatNpcHold(critter);
        return;
    }
    int critterFootX = critterBaseX + 16 + critter->x;
    int critterFootY = critterBaseY + 8 + critter->y;

    int dudeBaseX;
    int dudeBaseY;
    if (tileToScreenXY(gDude->tile, &dudeBaseX, &dudeBaseY) != 0) {
        realTimeCombatNpcHold(critter);
        return;
    }
    int dudeFootX = dudeBaseX + 16 + gDude->x;
    int dudeFootY = dudeBaseY + 8 + gDude->y;

    int targetTile;
    int targetX;
    int targetY;

    if (realTimeCombatNpcLineIsClear(critter, critterFootX, critterFootY, dudeFootX, dudeFootY, gDude->tile)) {
        // Clear line of sight: charge straight at the player at any angle.
        state.pathLength = 0;
        targetTile = gDude->tile;
        targetX = dudeFootX;
        targetY = dudeFootY;
    } else {
        // A wall is in the way: route around it using a cached detour path.
        if (state.pathLength == 0
            || state.pathIndex >= state.pathLength
            || getTicksBetween(now, state.lastPathTime) >= kNpcRepathIntervalMs) {
            realTimeCombatNpcComputePath(critter, state, now);
        }

        while (state.pathIndex < state.pathLength && critter->tile == state.pathTiles[state.pathIndex]) {
            state.pathIndex++;
        }

        if (state.pathLength == 0 || state.pathIndex >= state.pathLength) {
            realTimeCombatNpcHold(critter);
            return;
        }

        targetTile = state.pathTiles[state.pathIndex];
        int waypointBaseX;
        int waypointBaseY;
        if (tileToScreenXY(targetTile, &waypointBaseX, &waypointBaseY) != 0) {
            realTimeCombatNpcHold(critter);
            return;
        }
        targetX = waypointBaseX + 16;
        targetY = waypointBaseY + 8;
    }

    if (!realTimeCombatNpcStepTowardPoint(critter, targetX, targetY)) {
        // Blocked by a critter directly ahead (or already on the spot): wait.
        realTimeCombatNpcHold(critter);
        return;
    }

    realTimeCombatFaceTile(critter, targetTile);
    realTimeCombatNpcAnimateMovement(critter, state, now);
}

// Continuous flee: run in a straight line toward a reachable tile away from the
// player (mirrors _ai_run_away's destination search), repicking when reached or
// blocked.
static void realTimeCombatNpcFlee(Object* critter, NpcAiState& state, unsigned int now)
{
    if (state.fleeTile < 0
        || critter->tile == state.fleeTile
        || getTicksBetween(now, state.lastPathTime) >= kNpcRepathIntervalMs) {
        state.fleeTile = -1;
        state.lastPathTime = now;

        int awayRotation = tileGetRotationTo(gDude->tile, critter->tile);
        int rotationOffsets[3] = { 0, 1, ROTATION_COUNT - 1 };
        for (int distance = kNpcFleeDistance; distance > 0 && state.fleeTile < 0; distance--) {
            for (int index = 0; index < 3; index++) {
                int rotation = (awayRotation + rotationOffsets[index]) % ROTATION_COUNT;
                int tile = tileGetTileInDirection(critter->tile, rotation, distance);
                if (tileIsValid(tile)
                    && pathfinderFindPath(critter, critter->tile, tile, nullptr, 1, _obj_blocking_at) > 0) {
                    state.fleeTile = tile;
                    break;
                }
            }
        }
    }

    if (state.fleeTile < 0) {
        realTimeCombatNpcHold(critter);
        return;
    }

    int destBaseX;
    int destBaseY;
    if (tileToScreenXY(state.fleeTile, &destBaseX, &destBaseY) != 0) {
        realTimeCombatNpcHold(critter);
        return;
    }

    if (!realTimeCombatNpcStepTowardPoint(critter, destBaseX + 16, destBaseY + 8)) {
        state.fleeTile = -1;
        realTimeCombatNpcHold(critter);
        return;
    }

    realTimeCombatFaceTile(critter, state.fleeTile);
    realTimeCombatNpcAnimateMovement(critter, state, now);
}

// Per-critter real-time AI decision, mirroring the branches of _ai_try_attack /
// _combat_ai. Movement is continuous and pixel based (see realTimeCombatNpcPursue);
// only attacks/deaths use the engine's registered animations.
static void realTimeCombatUpdateNpc(Object* critter, unsigned int now)
{
    NpcAiState& state = gNpcAiStates[critter];

    // Let our own attack animation play out before acting again.
    if (state.lastAttackTime != 0
        && getTicksBetween(now, state.lastAttackTime) < kNpcAttackAnimationHoldMs) {
        return;
    }

    // Keep the real-time AI authoritative over hostile critters: interrupt any
    // lingering registered animation (e.g. a script-issued idle/wander move) so
    // it doesn't override our continuous pixel movement and make the critter
    // appear to meander. Leave knockdown/get-up reactions and prioritized
    // sequences (deaths, scripted) alone.
    if (animationIsBusy(critter)) {
        if ((critter->data.critter.combat.results & DAM_KNOCKED_DOWN) != 0) {
            return;
        }

        if (reg_anim_clear(critter) == -2) {
            return;
        }
    }

    int hitMode;
    if (!realTimeCombatGetNpcAttackMode(critter, &hitMode)) {
        realTimeCombatNpcHold(critter);
        return;
    }

    // Flee when the original rules say to (hurt too much / below min hp).
    if (aiCombatShouldFlee(critter)) {
        critter->data.critter.combat.maneuver |= CRITTER_MANUEVER_FLEEING;
        realTimeCombatNpcFlee(critter, state, now);
        return;
    }
    state.fleeTile = -1;

    int reason = realTimeCombatNpcBadShotReason(critter, gDude, hitMode);

    if (reason == COMBAT_BAD_SHOT_NO_AMMO) {
        aiAttemptWeaponReload(critter, 1);
        return;
    }

    if (reason == COMBAT_BAD_SHOT_OK) {
        bool cooldownReady = state.lastAttackTime == 0
            || getTicksBetween(now, state.lastAttackTime) >= kNpcAttackCooldownMs;
        if (cooldownReady) {
            if (realTimeCombatNpcAttack(critter, gDude, hitMode)) {
                state.lastAttackTime = now;
            }
        } else {
            realTimeCombatNpcHold(critter);
        }
        return;
    }

    if (reason == COMBAT_BAD_SHOT_OUT_OF_RANGE || reason == COMBAT_BAD_SHOT_AIM_BLOCKED) {
        if (aiGetDistance(critter) == DISTANCE_STAY) {
            realTimeCombatNpcHold(critter);
            return;
        }

        realTimeCombatNpcPursue(critter, state, now);
        return;
    }

    // Crippled arms / not enough AP / anything else: hold and face the player.
    realTimeCombatNpcHold(critter);
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
        if (!realTimeCombatIsHostileToDude(critter)) {
            continue;
        }

        realTimeCombatUpdateNpc(critter, now);
    }

    objectListFree(critters);
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
        // WASD/R drive real-time movement and reload. 'S' is always movement now;
        // the SKILLDEX button uses its own KEY_INTERFACE_SKILLDEX code so it no
        // longer collides here.
        return true;
    default:
        return false;
    }
}

bool realTimeCombatUpdate(int keyCode)
{
    realTimeCombatRefreshCursor();

    if (!realTimeCombatIsEnabled()) {
        gNpcAiStates.clear();
        return false;
    }

    // While a Skilldex skill is being targeted (e.g. lockpick on a door), stand
    // aside so the classic game-mouse handler resolves the click via
    // actionUseSkill. Movement and NPC AI keep running (real-time combat does
    // not pause); only RTC's own mouse/cursor/attack handling is suspended.
    if (realTimeCombatIsSkillTargetingActive()) {
        realTimeCombatHandleMovement();
        realTimeCombatHandleNpcs();
        // Let the mouse event (-2) reach gameHandleKey, which dispatches it to
        // _gmouse_handle_event so the classic handler resolves the skill-on-
        // target click via actionUseSkill. Movement keys stay swallowed so 'A'
        // and friends don't fall through to legacy combat shortcuts.
        if (keyCode == -2) {
            return false;
        }
        return realTimeCombatConsumesKey(keyCode);
    }

    if (keyCode == KEY_LOWERCASE_R || keyCode == KEY_UPPERCASE_R) {
        realTimeCombatReload();
    }

    realTimeCombatValidateCritterFid(gDude);
    realTimeCombatFaceMouse();
    realTimeCombatHandleMouse();
    realTimeCombatUpdateLootHover();
    realTimeCombatUpdateCombatCursor();
    realTimeCombatHandleMovement();
    realTimeCombatHandleNpcs();

    return realTimeCombatConsumesKey(keyCode);
}

} // namespace fallout
