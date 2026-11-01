/* env/api_deterministic.c: the draws of harness/api_deterministic.c (env/lenv.h). */
#define ENV_S_INIT {S_LEN}
#define ENV_S_CYCLE {S_CHUNK, S_DFLUSH}
#define ENV_U_INIT {U_LEVEL_OK, U_WBD_OK, U_ML_OK, U_ST_OK}
#define ENV_U_CYCLE {U_S(S_CHUNK)}
#define ENV_B_CYCLE {B_RARE}
#define ENV_B_INJECT {U_PARAM, U_PARAM}
#define ENV_D_INIT {D_DATA}
#include "env/lenv.h"
