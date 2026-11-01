/* env/api_reset.c: the draws of harness/api_reset.c (env/lenv.h). */
#define ENV_S_INIT {S_STREAM}
#define ENV_S_CYCLE {S_CHUNK}
#define ENV_U_INIT {U_WBI}
#define ENV_U_CYCLE {U_S(S_OUT), U_IFLUSH}
#define ENV_B_CYCLE {B_STOP}
#define ENV_D_INIT {D_STREAM}
#define ENV_STOP_RESTARTS 1
#include "env/lenv.h"
