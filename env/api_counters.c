/* env/api_counters.c: the draws of harness/api_counters.c (env/lenv.h). */
#define ENV_S_INIT {S_STREAM}
#define ENV_S_CYCLE {S_CHUNK}
#define ENV_U_INIT {U_WBI}
#define ENV_U_CYCLE {U_S(S_CHUNK), U_IFLUSH}
#define ENV_B_CYCLE {B_RARE, B_STOP}
#define ENV_B_INJECT {U_S(S_CHUNK)}
#define ENV_D_INIT {D_STREAM}
#define ENV_D_CYCLE {D_ANY}
#include "env/lenv.h"
