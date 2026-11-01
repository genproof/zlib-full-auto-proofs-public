/* env/rfc_trailing_bytes.c: the draws of harness/rfc_trailing_bytes.c (env/lenv.h). */
#define ENV_S_INIT {S_LEN, S_SMALLLEN}
#define ENV_U_INIT {U_LEVEL_OK, U_WBD_OK, U_ML_OK, U_ST_OK}
#define ENV_U_CYCLE {U_IFLUSH}
#define ENV_D_INIT {D_DATA, D_ANY}
#include "env/lenv.h"
