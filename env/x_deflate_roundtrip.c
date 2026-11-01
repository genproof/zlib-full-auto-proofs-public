/* the draws of harness/deflate_common.h's run (env/zenv.h); deflate_api draws one more int at the end */
#define ENV_U32_INIT {R_LEVEL, R_ANY, R_DEFLATE_WBITS, R_MEMLEVEL, R_STRATEGY, R_DN, R_DLEN, R_TUNE, R_TUNE, R_TUNE, \
		      R_TUNE, R_SMALL, R_SMALL, R_SMALL, R_ANY}
#define ENV_U32_CYCLE {R_LIM, R_AOUT, R_DEFLATE_FLUSH, R_LEVEL, R_STRATEGY}
#define ENV_U8_INIT {R_NULL, R_SEL4, R_SEL4, R_SEL4, R_ANY, R_ANY, R_ANY}
#define ENV_U8_CYCLE {R_SEL16}
#define ENV_STREAM_BYTES (-1)
#define ENV_DATA_BYTES 0
#define ENV_NONZERO_FIRST 3
#define ENV_NONZERO_LAST 4
#include "env/zenv.h"
