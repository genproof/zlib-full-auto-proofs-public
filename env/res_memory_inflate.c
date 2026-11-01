/* env/res_memory_inflate.c: the draws of harness/res_memory_inflate.c (env/lenv.h). */
#define ENV_S_INIT {S_STREAM}
#define ENV_S_CYCLE {S_CHUNK}
#define ENV_U_INIT {U_WBI_OK}
#define ENV_U_CYCLE {U_S(S_OUT), U_IFLUSH}
#define ENV_B_CYCLE {B_STOP}
#define ENV_D_INIT {D_STREAM}
#include "env/lenv.h"
