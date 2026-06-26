#ifndef REALTIME_COMBAT_H
#define REALTIME_COMBAT_H

namespace fallout {

bool realTimeCombatIsEnabled();
void realTimeCombatRefreshCursor();
bool realTimeCombatUpdate(int keyCode);

} // namespace fallout

#endif /* REALTIME_COMBAT_H */
