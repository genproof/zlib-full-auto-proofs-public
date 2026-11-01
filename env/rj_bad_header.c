/* env/rj_bad_header.c: the draws of harness/rj_bad_header.c (env/lenv.h). */
#define ENV_S_INIT {S_ZWB, S_SMALLLEN}
#define ENV_U_INIT {U_S(S_CHUNK), U_IFLUSH}
#define ENV_D_INIT {D_ZHDR, D_ANY}
#include "env/lenv.h"
