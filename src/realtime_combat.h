#ifndef REALTIME_COMBAT_H
#define REALTIME_COMBAT_H

namespace fallout {

struct CombatStartData;

void realTimeCombatSetPendingMap(int map);
void realTimeCombatSetPendingMapName(const char* name);
void realTimeCombatClearPendingMap();
bool realTimeCombatIsMapEnabled();
bool realTimeCombatShouldBlockClassicCombat();
bool realTimeCombatIsEnabled();
bool realTimeCombatIsDeathAnimationPending();
bool realTimeCombatHandleTurnBasedCombatRequest(CombatStartData* combatStartData);
void realTimeCombatTrace(const char* context, CombatStartData* combatStartData);
void realTimeCombatRefreshCursor();
bool realTimeCombatUpdate(int keyCode);

} // namespace fallout

#endif /* REALTIME_COMBAT_H */
