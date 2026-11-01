// Law api_split_invariant: For any input (under 2^32 bytes), even garbage, and any wrapper with the 32 KiB window
// (inflateInit2 windowBits -15, 15, 31 or 47; inflateInit2 returns Z_OK), one inflate() call offered all of it, any
// output space and any flush but Z_BLOCK and Z_TREES gives the same result as a second stream fed the same input (a
// copy made before the first call) and output space in any pieces with any flush per call (until it returns
// Z_STREAM_END, Z_NEED_DICT or Z_DATA_ERROR, or a call offered all the rest with a flush other than Z_BLOCK and Z_TREES
// changes nothing): the same bytes written, and the same final code if the one call returned one of those three, else
// none of them (Z_MEM_ERROR ends the run).
#include "laws_common.h"

static int final(int code) {
	return code == Z_STREAM_END || code == Z_NEED_DICT || code == Z_DATA_ERROR;
}

int main(void) {
	int window_bits[4] = {-15, 15, 31, 47};
	int window = window_bits[upto(3)];
	size_t input_len = nondet_u32();
	size_t room = nondet_u32();
	unsigned char *input = alloc_any_bytes(input_len);
	if (input == NULL)
		return 0;
	unsigned char *input_split = copy_of(input, input_len);
	unsigned char *out_one = malloc(room);
	unsigned char *out_split = malloc(room);
	int flush = (int) nondet_u32();
	gp_assume(flush != Z_BLOCK && flush != Z_TREES);
	if (input_split == NULL || out_one == NULL || out_split == NULL)
		return 0;
	// zlib.h, inflate: "In this implementation, inflate() always flushes as much output as possible to the output
	// buffer"
	z_stream one;
	new_stream(&one);
	int code_one = inflateInit2(&one, window);
	if (code_one == Z_MEM_ERROR)
		return 0;
	gp_assert(code_one == Z_OK);
	set_buffer(&one, input, input_len, out_one, room);

	code_one = inflate(&one, flush);

	if (code_one == Z_MEM_ERROR)
		return 0;
	z_stream split;
	new_stream(&split);
	int code_split = inflateInit2(&split, window);
	if (code_split == Z_MEM_ERROR)
		return 0;
	gp_assert(code_split == Z_OK);
	split.next_in = input_split;
	split.next_out = out_split;
	for (;;) {
		size_t rest_in = input_len - (size_t) (split.next_in - input_split);
		size_t rest_out = room - (size_t) (split.next_out - out_split);
		uInt take = (uInt) upto(rest_in);
		uInt give = (uInt) upto(rest_out);
		int piece_flush = (int) nondet_u32();
		split.avail_in = take;
		split.avail_out = give;

		code_split = inflate(&split, piece_flush);

		if (code_split == Z_MEM_ERROR)
			return 0;
		int all_offered = take == rest_in && give == rest_out;
		int no_progress = split.avail_in == take && split.avail_out == give;
		int may_stop = piece_flush != Z_BLOCK && piece_flush != Z_TREES;
		if (final(code_split) || (all_offered && no_progress && may_stop))
			break;
	}
	if (final(code_one))
		gp_assert(code_split == code_one);
	else
		gp_assert(!final(code_split));
	gp_assert(split.total_out == one.total_out && bytes_eq(out_one, out_split, one.total_out));
	return 0;
}
