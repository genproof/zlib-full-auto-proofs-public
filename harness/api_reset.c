// Law api_reset: For any windowBits that inflateInit2 accepts, after any use of a stream (any input in any pieces, any
// output space, any flush, any number of calls), inflateReset (Z_OK) makes it behave exactly like a new one from
// inflateInit2 with the same windowBits: given any input (any length the allocator provides) in the same pieces (below
// 2^32 bytes), with the same output space and flush, each inflate() call returns the same code on both, reads and
// writes as many bytes, writes the same bytes, and leaves the same total_in, total_out, msg, data_type and (except for
// raw streams, where zlib does not set it) adler (Z_MEM_ERROR ends the run).
#include "laws_common.h"

int main(void) {
	int window_bits = (int) nondet_u32();
	z_stream used;
	z_stream fresh;
	new_stream(&used);
	new_stream(&fresh);
	if (inflateInit2(&used, window_bits) != Z_OK)
		return 0;
	for (int phase = 0; phase < 2; phase++) {
		size_t input_len = upto(PTRDIFF_MAX);
		unsigned char *input = alloc_any_bytes(input_len);
		if (input == NULL)
			return 0;
		size_t read = 0;
		do {
			size_t take = upto(clip(input_len - read));
			size_t room = nondet_u32();
			int flush = (int) nondet_u32();
			unsigned char *in_used = copy_of(input + read, take);
			unsigned char *in_fresh = copy_of(input + read, take);
			unsigned char *out_used = malloc(room);
			unsigned char *out_fresh = malloc(room);
			if (in_used == NULL || in_fresh == NULL || out_used == NULL || out_fresh == NULL)
				return 0;
			set_buffer(&used, in_used, take, out_used, room);
			set_buffer(&fresh, in_fresh, take, out_fresh, room);

			int code_used = inflate(&used, flush);
			int code_fresh = code_used;
			if (phase == 1)
				code_fresh = inflate(&fresh, flush);

			if (code_used == Z_MEM_ERROR || code_fresh == Z_MEM_ERROR)
				return 0;
			if (phase == 1) {
				gp_assert(code_used == code_fresh);
				gp_assert(used.avail_in == fresh.avail_in && used.avail_out == fresh.avail_out);
				gp_assert(bytes_eq(out_used, out_fresh, room - used.avail_out));
				gp_assert(used.total_in == fresh.total_in && used.total_out == fresh.total_out);
				gp_assert(used.msg == fresh.msg && used.data_type == fresh.data_type);
				gp_assert(window_bits < 0 || used.adler == fresh.adler);
			}
			read += take - used.avail_in;
			free(in_used);
			free(in_fresh);
			free(out_used);
			free(out_fresh);
		} while (nondet_u8() != 0);
		// zlib.h, inflateReset: "This function is equivalent to inflateEnd followed by inflateInit, but does
		// not free and reallocate the internal decompression state. The stream will keep attributes that may
		// have been set by inflateInit2."
		if (phase == 0) {
			gp_assert(inflateReset(&used) == Z_OK);
			if (inflateInit2(&fresh, window_bits) != Z_OK)
				return 0;
		}
	}
	return 0;
}
