/* env/api_deflate_any.c: the draws of harness/api_deflate_any.c (env/lenv.h). */
#define ENV_S_INIT {S_LEN}
#define ENV_S_CYCLE {S_CHUNK0}
#define ENV_U_INIT {U_LEVEL_OK, U_WBD_OK, U_ML_OK, U_ST_OK}
#define ENV_U_CYCLE {U_S(S_CHUNK0), U_DFLUSH}
#define ENV_FINISH_U_CYCLE {U_S(S_CHUNK0)}
#define ENV_B_CYCLE {B_RARE, B_STOP}
#define ENV_FINISH_B_CYCLE {B_STOP}
#define ENV_B_INJECT {U_PARAM, U_PARAM}
#define ENV_D_INIT {D_DATA}
#define ENV_D_CYCLE {D_ANY}
#include "env/lenv.h"
