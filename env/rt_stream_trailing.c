/* env/rt_stream_trailing.c: the draws of harness/rt_stream_trailing.c (env/lenv.h). */
#define ENV_S_INIT {S_LEN, S_CAP}
#define ENV_S_CYCLE {S_CHUNK, S_DFLUSH, S_CHUNK0}
#define ENV_U_INIT {U_LEVEL_OK, U_WBD_OK, U_ML_OK, U_ST_OK}
#define ENV_U_CYCLE {U_IFLUSH}
#define ENV_D_INIT {D_DATA, D_ANY}
#define ENV_FINISH_CYCLE {S_CHUNK0}
#include "env/lenv.h"
