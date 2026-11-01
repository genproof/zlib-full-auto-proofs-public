/* env/adler32_ref.c: the draws of harness/adler32_ref.c (env/zenv.h): adler (valid), any, sizes, the bytes */
#define ENV_U32_INIT {R_CHUNK, R_SMALL, R_SMALL}
#define ENV_U32_CYCLE {R_CHUNK}
#define ENV_U8_CYCLE {R_ANY}
#define ENV_STREAM_BYTES (-1)
#define ENV_ADLER_MASK 0x1
#define ENV_DATA_BYTES 2
#include "env/zenv.h"
