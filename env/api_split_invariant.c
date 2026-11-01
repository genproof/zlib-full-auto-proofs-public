/* env/api_split_invariant.c: the draws of harness/api_split_invariant.c (env/lenv.h). */
#define ENV_S_INIT {S_WSEL}
#define ENV_S_CYCLE {S_CHUNK}
#define ENV_U_INIT {U_S(S_STREAM), U_S(S_OUT), U_IFLUSH_NB}
#define ENV_U_CYCLE {U_IFLUSH}
#define ENV_D_INIT {D_STREAM}
#include "env/lenv.h"
