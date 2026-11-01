// Law rj_deflate_params: For any level, method, windowBits, memLevel and strategy (any ints), deflateInit2 returns Z_OK
// when all of them are in zlib.h's ranges (below), else Z_STREAM_ERROR (Z_MEM_ERROR ends the run).
#include "laws_common.h"

int main(void) {
	int level = (int) nondet_u32();
	int method = (int) nondet_u32();
	int window_bits = (int) nondet_u32();
	int mem_level = (int) nondet_u32();
	int strategy = (int) nondet_u32();
	// zlib.h, deflateInit2: level "Z_DEFAULT_COMPRESSION, or between 0 and 9"; method "must be Z_DEFLATED";
	// memLevel 1..MAX_MEM_LEVEL (9, zconf.h); strategy Z_DEFAULT_STRATEGY (0) .. Z_FIXED (4); windowBits 8..15,
	// "-8..-15 for raw deflate", "Add 16 to windowBits to write a simple gzip header", but "For raw deflate or gzip
	// encoding, a request for a 256-byte window is rejected as invalid"
	int valid = level >= -1 && level <= 9 && method == Z_DEFLATED;
	valid = valid && mem_level >= 1 && mem_level <= 9 && strategy >= 0 && strategy <= Z_FIXED;
	int zlib_window = window_bits >= 8 && window_bits <= 15;
	int raw_window = window_bits >= -15 && window_bits <= -9;
	int gzip_window = window_bits >= 16 + 9 && window_bits <= 16 + 15;
	valid = valid && (zlib_window || raw_window || gzip_window);
	z_stream strm;
	new_stream(&strm);

	int code = deflateInit2(&strm, level, method, window_bits, mem_level, strategy);

	if (code == Z_MEM_ERROR)
		return 0;
	// zlib.h: "Z_STREAM_ERROR if any parameter is invalid"
	if (valid)
		gp_assert(code == Z_OK);
	else
		gp_assert(code == Z_STREAM_ERROR);
	return 0;
}
