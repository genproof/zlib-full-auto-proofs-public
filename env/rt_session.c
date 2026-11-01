/* env/rt_session.c: the draws of harness/rt_session.c (env/lenv.h). */
#define ENV_S_INIT {S_HLEN, S_HLEN, S_HLEN, S_HLEN, S_LEN, S_CAP}
#define ENV_S_CYCLE {S_CHUNK, S_DFLUSH, S_CHUNK0}
#define ENV_U_INIT {U_LEVEL_OK, U_WBD_OK, U_ML_OK, U_ST_OK, U_ANY, U_ANY, U_ANY, U_ANY}
#define ENV_U_CYCLE {U_IFLUSH}
#define ENV_B_INIT {B_ANY}
#define ENV_D_INIT {D_DICT, D_ANY, D_NONZERO, D_NONZERO, D_DATA, D_ANY}
#define ENV_FINISH_CYCLE {S_CHUNK0}
#include "env/lenv.h"
