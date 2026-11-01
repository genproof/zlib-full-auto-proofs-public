/* env/inflate_header.c: the draws of harness/inflate_header.c (env/zenv.h). */
#define ENV_U32_INIT {R_GZWBITS, R_ANY, R_XLEN, R_STRLEN, R_STRLEN, R_DELTA, R_BUFMAX, R_BUFMAX, R_BUFMAX}
#define ENV_U32_CYCLE {R_LIM, R_AOUT, R_FLUSH}
#define ENV_U8_INIT {R_FLG, R_ANY, R_ANY, R_NULL, R_NULL, R_NULL}
#define ENV_U8_CYCLE {R_STOP}
#define ENV_STREAM_BYTES (-1)
#define ENV_NONZERO_FIRST 1
#define ENV_NONZERO_LAST 2
#include "env/zenv.h"
