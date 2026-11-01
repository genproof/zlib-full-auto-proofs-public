/* env/crc32_ref.c: the draws of harness/crc32_ref.c (env/zenv.h): crc, n, k, len, the bytes */
#define ENV_U32_INIT {R_CHUNK, R_SMALL, R_SMALL}
#define ENV_U32_CYCLE {R_CHUNK}
#define ENV_U8_CYCLE {R_ANY}
#define ENV_STREAM_BYTES (-1)
#define ENV_DATA_BYTES 1
#include "env/zenv.h"
