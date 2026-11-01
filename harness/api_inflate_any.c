// Law api_inflate_any: For any windowBits in zlib.h's ranges for inflateInit2 and any input (any length the allocator
// provides), fed to any number of inflate() calls in any pieces below 2^32 bytes, empty ones included, each with any
// flush and any output space below 2^32 bytes, none included (input and output each an object of exactly avail_in and
// avail_out bytes), with inflateSetDictionary of any bytes between calls or not: inflateInit2 returns Z_OK, and every
// inflate() returns one of the codes zlib.h documents for it: Z_OK, Z_STREAM_END, Z_NEED_DICT, Z_DATA_ERROR or
// Z_BUF_ERROR; leaves its input and the part of the output space it did not write (the last avail_out bytes) as they
// were; moves next_in and next_out exactly as far as it lowers avail_in and avail_out, and raises total_in and
// total_out by as much; and, offered neither input nor output space, does not return Z_OK (Z_MEM_ERROR ends the run).
#include "laws_common.h"
#include "laws_session.h"

int main(void) {
	int window_bits = (int) nondet_u32();
	gp_assume(inflate_window_ok(window_bits));
	size_t input_len = upto(PTRDIFF_MAX);
	unsigned char *input = alloc_any_bytes(input_len);
	if (input == NULL)
		return 0;
	z_stream strm;
	new_stream(&strm);
	int code = inflateInit2(&strm, window_bits);
	if (code == Z_MEM_ERROR)
		return 0;
	gp_assert(code == Z_OK);
	size_t read = 0;
	struct position at;
	do {
		size_t take = upto(clip(input_len - read));
		size_t room = nondet_u32();
		unsigned char *piece = copy_of(input + read, take);
		unsigned char *out = alloc_any_bytes(room);
		if (piece == NULL || out == NULL)
			return 0;
		unsigned char *before = copy_of(out, room);
		if (before == NULL)
			return 0;
		set_buffer(&strm, piece, take, out, room);
		position_of(&strm, &at);

		code = inflate(&strm, (int) nondet_u32());

		if (code == Z_MEM_ERROR)
			return 0;
		// zlib.h, inflate() "returns Z_OK", "Z_STREAM_END", "Z_NEED_DICT", "Z_DATA_ERROR", "Z_STREAM_ERROR if
		// the stream structure was inconsistent" (it never is here), "Z_MEM_ERROR", "Z_BUF_ERROR"
		gp_assert(code == Z_OK || code == Z_STREAM_END || code == Z_NEED_DICT || code == Z_DATA_ERROR ||
		          code == Z_BUF_ERROR);
		// zlib.h, inflate: "Decompress more input starting at next_in and update next_in and avail_in accordingly";
		// "Generate more output starting at next_out and update next_out and avail_out accordingly."; total_in,
		// total_out: "total number of input bytes read so far", "total number of bytes output so far"
		size_t wrote = room - strm.avail_out;
		gp_assert(accounted(&strm, &at) && counted(&strm, &at) && bytes_eq(piece, input + read, take));
		gp_assert(bytes_eq(out + wrote, before + wrote, strm.avail_out));
		// zlib.h, inflate() "returns Z_OK if some progress has been made (more input processed or more output
		// produced)"
		if (take == 0 && room == 0)
			gp_assert(code != Z_OK);
		read += take - strm.avail_in;
		free(piece);
		free(out);
		free(before);
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
