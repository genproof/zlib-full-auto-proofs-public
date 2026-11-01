/* env/inflate_codes.c: the draws of harness/inflate_codes.c (env/zenv.h). */
#define ENV_U32_INIT {R_WBITS, R_N, R_ANY}
#define ENV_U32_CYCLE {R_LIM, R_AOUT, R_FLUSH}
#define ENV_U8_INIT {R_NULL, R_NULL, R_NULL, R_ANY}
#define ENV_U8_CYCLE {R_OP, R_NULL, R_NULL, R_STOP}
#include "env/zenv.h"
