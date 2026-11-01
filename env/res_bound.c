/* env/res_bound.c: the draws of harness/res_bound.c (env/lenv.h). */
#define ENV_S_INIT {S_HLEN, S_HLEN, S_HLEN}
#define ENV_U_INIT {U_LEVEL_OK, U_WBD_OK, U_ML_OK, U_ST_OK, U_S(S_LEN), U_S(S_LEN), U_ANY, U_ANY, U_ANY, U_ANY}
#define ENV_B_INIT {B_ANY}
#define ENV_D_INIT {D_DATA, D_DICT, D_ANY, D_NONZERO, D_NONZERO}
#include "env/lenv.h"
