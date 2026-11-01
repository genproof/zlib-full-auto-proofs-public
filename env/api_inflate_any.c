/* env/api_inflate_any.c: the draws of harness/api_inflate_any.c (env/lenv.h). */
#define ENV_S_INIT {S_STREAM}
#define ENV_S_CYCLE {S_CHUNK0}
#define ENV_U_INIT {U_WBI_OK}
#define ENV_U_CYCLE {U_S(S_CHUNK0), U_IFLUSH}
#define ENV_B_CYCLE {B_RARE, B_STOP}
#define ENV_B_INJECT {U_S(S_CHUNK)}
#define ENV_D_INIT {D_STREAM}
#define ENV_D_CYCLE {D_ANY}
#include "env/lenv.h"
