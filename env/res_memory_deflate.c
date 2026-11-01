/* env/res_memory_deflate.c: the draws of harness/res_memory_deflate.c (env/lenv.h). */
#define ENV_S_INIT {S_LEN}
#define ENV_S_CYCLE {S_CHUNK}
#define ENV_U_INIT {U_LEVEL_OK, U_WBD_OK, U_ML_OK, U_ST_OK}
#define ENV_U_CYCLE {U_S(S_CHUNK), U_DFLUSH}
#define ENV_B_CYCLE {B_STOP}
#define ENV_D_INIT {D_DATA}
#include "env/lenv.h"
