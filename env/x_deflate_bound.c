/* env/deflate_bound.c: the draws of harness/deflate_bound.c (env/zenv.h). */
#define ENV_U32_INIT {R_LEVEL, R_DEFLATE_WBITS, R_MEMLEVEL, R_STRATEGY, R_DN, R_DLEN, R_SMALL, R_SMALL, R_SMALL, R_ANY}
#define ENV_U32_CYCLE {R_ANY}
#define ENV_U8_INIT {R_SEL4, R_SEL4, R_ANY, R_ANY, R_ANY, R_NULL, R_NULL, R_NULL}
#define ENV_U8_CYCLE {R_ANY}
#define ENV_STREAM_BYTES (-1)
#define ENV_DATA_BYTES 0
#define ENV_NONZERO_FIRST 3
#define ENV_NONZERO_LAST 4
#include "env/zenv.h"
