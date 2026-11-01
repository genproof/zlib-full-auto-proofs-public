// Law api_counters: For any windowBits that inflateInit2 accepts and any input (any length the allocator provides), fed
// to any number of inflate() calls in any pieces below 2^32 bytes, each with any flush and any output space (input and
// output each an object of exactly avail_in and avail_out bytes), with inflateSetDictionary of any bytes between calls
// or not, inflate's counters are exact: after every call, next_in and next_out have moved on by exactly the bytes it
// read and wrote (avail_in and avail_out never grow), and total_in and total_out are the sums of those over all calls
// (Z_MEM_ERROR ends the run).
#include "laws_common.h"

int main(void) {
	int window_bits = (int) nondet_u32();
	size_t input_len = upto(PTRDIFF_MAX);
	unsigned char *input = alloc_any_bytes(input_len);
	z_stream strm;
	new_stream(&strm);
	if (input == NULL || inflateInit2(&strm, window_bits) != Z_OK)
		return 0;
	size_t read = 0;
	size_t written = 0;
	do {
		size_t take = upto(clip(input_len - read));
		size_t room = nondet_u32();
		unsigned char *piece = copy_of(input + read, take);
		unsigned char *out = alloc_any_bytes(room);
		if (piece == NULL || out == NULL)
			return 0;
		set_buffer(&strm, piece, take, out, room);

		if (inflate(&strm, (int) nondet_u32()) == Z_MEM_ERROR)
			return 0;

		// zlib.h, z_stream: "next_in: next input byte", "avail_in: number of bytes available at next_in",
		// "total_in: total number of input bytes read so far", and the same for next_out, avail_out, total_out
		gp_assert(strm.avail_in <= take && strm.avail_out <= room);
		gp_assert(strm.next_in == piece + (take - strm.avail_in));
		gp_assert(strm.next_out == out + (room - strm.avail_out));
		read += take - strm.avail_in;
		written += room - strm.avail_out;
		gp_assert(strm.total_in == read && strm.total_out == written);
		free(piece);
		free(out);
		if (nondet_u8() == 0) {
			size_t dict_len = nondet_u32();
			unsigned char *dict = alloc_any_bytes(dict_len);
			if (dict == NULL || inflateSetDictionary(&strm, dict, (uInt) dict_len) == Z_MEM_ERROR)
				return 0;
			free(dict);
		}
	} while (nondet_u8() != 0);
	return 0;
}
