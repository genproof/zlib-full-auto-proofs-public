// Law api_inflate_deterministic: Two new streams made by inflateInit2 with the same windowBits in zlib.h's ranges (both
// return Z_OK; Z_MEM_ERROR ends the run) and fed the same input (any bytes, any length the allocator provides) in the
// same pieces below 2^32 bytes, with the same output space and the same flush (any int) on each inflate() call (input
// and output each an object of exactly avail_in and avail_out bytes, one per stream), behave the same: each call
// returns the same code on both, reads and writes as many bytes, writes the same bytes, and leaves the same total_in,
// total_out, msg, data_type and (except for raw streams, where zlib does not set it) adler (Z_MEM_ERROR ends the run).
#include "laws_common.h"
#include "laws_session.h"

int main(void) {
	int window_bits = (int) nondet_u32();
	gp_assume(inflate_window_ok(window_bits));
	size_t input_len = upto(PTRDIFF_MAX);
	unsigned char *input = alloc_any_bytes(input_len);
	if (input == NULL)
		return 0;
	z_stream first;
	z_stream second;
	new_stream(&first);
	new_stream(&second);
	int code_first = inflateInit2(&first, window_bits);
	int code_second = inflateInit2(&second, window_bits);
	if (code_first == Z_MEM_ERROR || code_second == Z_MEM_ERROR)
		return 0;
	gp_assert(code_first == Z_OK && code_second == Z_OK);
	size_t read = 0;
	do {
		size_t take = upto(clip(input_len - read));
		size_t out_size = nondet_u32();
		int flush = (int) nondet_u32();
		unsigned char *in_first = copy_of(input + read, take);
		unsigned char *in_second = copy_of(input + read, take);
		unsigned char *out_first = malloc(out_size);
		unsigned char *out_second = malloc(out_size);
		if (in_first == NULL || in_second == NULL || out_first == NULL || out_second == NULL)
			return 0;
		set_buffer(&first, in_first, take, out_first, out_size);
		set_buffer(&second, in_second, take, out_second, out_size);

		code_first = inflate(&first, flush);
		code_second = inflate(&second, flush);

		if (code_first == Z_MEM_ERROR || code_second == Z_MEM_ERROR)
			return 0;
		gp_assert(code_first == code_second);
		gp_assert(first.avail_in == second.avail_in && first.avail_out == second.avail_out);
		gp_assert(bytes_eq(out_first, out_second, out_size - first.avail_out));
		gp_assert(first.total_in == second.total_in && first.total_out == second.total_out);
		gp_assert(first.msg == second.msg && first.data_type == second.data_type);
		gp_assert(window_bits < 0 || first.adler == second.adler);
		read += take - first.avail_in;
		free(in_first);
		free(in_second);
		free(out_first);
		free(out_second);
	} while (nondet_u8() != 0);
	return 0;
}
