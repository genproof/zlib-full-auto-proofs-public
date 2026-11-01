// Law rj_bad_level: For any level outside -1..9, any data and any output space (any sizes the allocator provides),
// compress2 returns Z_STREAM_ERROR.
#include "laws_common.h"

int main(void) {
	// zlib.h, deflateInit: "The compression level must be Z_DEFAULT_COMPRESSION, or between 0 and 9"
	int level = (int) nondet_u32();
	gp_assume(level < -1 || level > 9);
	size_t data_len = upto(PTRDIFF_MAX);
	size_t out_size = upto(PTRDIFF_MAX);
	unsigned char *data = alloc_any_bytes(data_len);
	unsigned char *compressed = malloc(out_size);
	if (data == NULL || compressed == NULL)
		return 0;
	uLongf compressed_len = out_size;

	int code = compress2(compressed, &compressed_len, data, data_len, level);

	// zlib.h, compress2 returns "Z_STREAM_ERROR if the level parameter is invalid"
	gp_assert(code == Z_STREAM_ERROR);
	return 0;
}
