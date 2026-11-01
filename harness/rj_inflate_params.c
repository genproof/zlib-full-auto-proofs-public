// Law rj_inflate_params: For any windowBits (any int), inflateInit2 returns Z_OK when it is one of zlib.h's values
// (-15..-8, 0, 8..15, and those 0 or 8..15 plus 16 or 32), else Z_STREAM_ERROR (Z_MEM_ERROR ends the run).
#include "laws_common.h"

int main(void) {
	int window_bits = (int) nondet_u32();
	// zlib.h, inflateInit2: windowBits "should be in the range 8..15", "can also be zero to request that inflate
	// use the window size in the zlib header", "can also be -8..-15 for raw inflate", "Add 32 to windowBits to
	// enable zlib and gzip decoding with automatic header detection, or add 16 to decode only the gzip format"
	int low = window_bits & 15;
	int raw = window_bits >= -15 && window_bits <= -8;
	int wrapped = window_bits >= 0 && window_bits < 48 && (low == 0 || low >= 8);
	z_stream strm;
	new_stream(&strm);

	int code = inflateInit2(&strm, window_bits);

	if (code == Z_MEM_ERROR)
		return 0;
	// zlib.h: "Z_STREAM_ERROR if the parameters are invalid"
	if (raw || wrapped)
		gp_assert(code == Z_OK);
	else
		gp_assert(code == Z_STREAM_ERROR);
	return 0;
}
