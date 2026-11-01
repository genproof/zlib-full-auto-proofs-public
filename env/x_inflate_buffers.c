/* env/inflate_buffers.c: the draws of harness/inflate_buffers.c (env/zenv.h). */
#define ENV_U32_INIT {R_WBITS, R_N}
#define ENV_U32_CYCLE {R_LIM, R_AOUT, R_FLUSH, R_ARG}
#define ENV_U8_CYCLE {R_OP, R_NULL, R_NULL, R_STOP}
#include "env/zenv.h"
