// Law api_deterministic: Two streams made by deflateInit2 with the same level, windowBits, memLevel and strategy in
// zlib.h's ranges (both return Z_OK; Z_MEM_ERROR ends the run) and driven by the same calls on any data (any length the
// allocator provides) -- deflate() with the same next pieces of the data (at most 2^32 - 1 bytes each), the same output
// space (below 2^32) and the same flush Z_NO_FLUSH..Z_BLOCK, Z_FINISH coming with the rest of the data (once one call
// can take it), until Z_STREAM_END, each call after the same deflateParams with any level and strategy (any ints) or
// none -- behave the same: each call returns the same code on both, reads and writes as many bytes, writes the same
// bytes and leaves the same adler (Z_MEM_ERROR ends the run).
#include "laws_common.h"
#include "laws_session.h"

int main(void) {
	int level = (int) nondet_u32();
	int window_bits = (int) nondet_u32();
	int mem_level = (int) nondet_u32();
	int strategy = (int) nondet_u32();
	gp_assume(deflate_params_ok(level, window_bits, mem_level, strategy));
	size_t data_len = upto(PTRDIFF_MAX);
	unsigned char *data = alloc_any_bytes(data_len);
	if (data == NULL)
		return 0;
	z_stream first;
	z_stream second;
	new_stream(&first);
	new_stream(&second);
	int code_first = deflateInit2(&first, level, Z_DEFLATED, window_bits, mem_level, strategy);
	int code_second = deflateInit2(&second, level, Z_DEFLATED, window_bits, mem_level, strategy);
	if (code_first == Z_MEM_ERROR || code_second == Z_MEM_ERROR)
		return 0;
	gp_assert(code_first == Z_OK && code_second == Z_OK);
	size_t offered = 0;
	size_t read = 0;
	int flush = Z_NO_FLUSH;
	do {
		if (flush != Z_FINISH) {
			offered += upto(data_len - offered);
			flush = (int) upto(Z_BLOCK);
			if (flush == Z_FINISH && data_len - read > UINT_MAX)
				flush = Z_NO_FLUSH;
			if (flush == Z_FINISH)
				offered = data_len;
		}
		size_t take = clip(offered - read);
		size_t room = nondet_u32();
		unsigned char *in_first = copy_of(data + read, take);
		unsigned char *in_second = copy_of(data + read, take);
		unsigned char *out_first = malloc(room);
		unsigned char *out_second = malloc(room);
		if (in_first == NULL || in_second == NULL || out_first == NULL || out_second == NULL)
			return 0;
		set_buffer(&first, in_first, take, out_first, room);
		set_buffer(&second, in_second, take, out_second, room);
		if (nondet_u8() == 0) {
			int new_level = (int) nondet_u32();
			int new_strategy = (int) nondet_u32();
			code_first = deflateParams(&first, new_level, new_strategy);
			code_second = deflateParams(&second, new_level, new_strategy);
			gp_assert(code_first == code_second);
		}

		code_first = deflate(&first, flush);
		code_second = deflate(&second, flush);

		gp_assert(code_first == code_second && first.adler == second.adler);
		gp_assert(first.avail_in == second.avail_in && first.avail_out == second.avail_out);
		gp_assert(bytes_eq(out_first, out_second, room - first.avail_out));
		read += take - first.avail_in;
		free(in_first);
		free(in_second);
		free(out_first);
		free(out_second);
	} while (code_first != Z_STREAM_END);
	return 0;
}
