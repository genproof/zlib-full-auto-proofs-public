/* env/rfc_stored.c: the draws of harness/rfc_stored.c (env/lenv.h). */
#define ENV_S_INIT {S_LEN, S_NBLK, S_SMALL, S_UNI(2), S_UNI(7)}
#define ENV_S_CYCLE {S_CHUNK}
#define ENV_U_CYCLE {U_IFLUSH}
#define ENV_D_INIT {D_ANY, D_DATA}
#include "env/lenv.h"
