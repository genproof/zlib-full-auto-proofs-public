// Law api_deflate_any: For any level, windowBits, memLevel and strategy in zlib.h's ranges for deflateInit2 and any
// data (any length the allocator provides), fed to any number of deflate() calls in any pieces below 2^32 bytes, each
// with any output space below 2^32 bytes, none included (input and output each an object of exactly avail_in and
// avail_out bytes), and any flush (any int; once a call had Z_FINISH, every later call has Z_FINISH and the input that
// call left, as zlib.h asks), each call after deflateParams with any level and strategy (any ints) or none (before the
// first Z_FINISH), until Z_STREAM_END: deflateInit2 returns Z_OK (Z_MEM_ERROR ends the run); deflateParams returns
// Z_STREAM_ERROR exactly when its level is not -1..9 or its strategy not Z_DEFAULT_STRATEGY..Z_FIXED, else Z_OK or
// Z_BUF_ERROR; deflate() returns Z_STREAM_ERROR exactly when its flush is not Z_NO_FLUSH..Z_BLOCK, else Z_OK,
// Z_STREAM_END (only with Z_FINISH) or Z_BUF_ERROR, and Z_BUF_ERROR, moving no pointer and no counter, when it is
// offered no output space; and the calls leave the part of the output space they did not write (the last avail_out
// bytes) as it was.
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
	z_stream strm;
	new_stream(&strm);
	int code = deflateInit2(&strm, level, Z_DEFLATED, window_bits, mem_level, strategy);
	if (code == Z_MEM_ERROR)
		return 0;
	gp_assert(code == Z_OK);
	size_t read = 0;
	size_t left = 0;
	int finishing = 0;
	struct position at;
	do {
		size_t take = finishing ? left : upto(clip(data_len - read));
		size_t out_size = nondet_u32();
		int flush = finishing ? Z_FINISH : (int) nondet_u32();
		unsigned char *piece = copy_of(data + read, take);
		unsigned char *out = alloc_any_bytes(out_size);
		if (piece == NULL || out == NULL)
			return 0;
		unsigned char *before = copy_of(out, out_size);
		if (before == NULL)
			return 0;
		set_buffer(&strm, piece, take, out, out_size);
		// zlib.h, deflateParams: "Z_STREAM_ERROR if the source stream state was inconsistent or if a parameter was
		// invalid"; "The interpretation of level and strategy is as in deflateInit2()"
		if (!finishing && nondet_u8() == 0) {
			int new_level = (int) nondet_u32();
			int new_strategy = (int) nondet_u32();

			code = deflateParams(&strm, new_level, new_strategy);

			int valid = new_level >= -1 && new_level <= 9 && new_strategy >= 0 && new_strategy <= Z_FIXED;
			gp_assert(valid ? code == Z_OK || code == Z_BUF_ERROR : code == Z_STREAM_ERROR);
		}
		position_of(&strm, &at);

		code = deflate(&strm, flush);

		// zlib.h, deflate() "returns Z_OK", "Z_STREAM_END ... (only when flush is set to Z_FINISH), Z_STREAM_ERROR
		// if the stream state was inconsistent", "or Z_BUF_ERROR if no progress is possible (for example avail_in or
		// avail_out was zero)"; "Generate more output starting at next_out and update next_out and avail_out
		// accordingly."
		int bad_flush = flush < Z_NO_FLUSH || flush > Z_BLOCK;
		gp_assert((code == Z_STREAM_ERROR) == bad_flush);
		gp_assert(code == Z_OK || code == Z_BUF_ERROR || code == Z_STREAM_ERROR || code == Z_STREAM_END);
		gp_assert(code != Z_STREAM_END || flush == Z_FINISH);
		if (out_size == 0 && !bad_flush)
			gp_assert(code == Z_BUF_ERROR && unmoved(&strm, &at));
		size_t wrote = out_size - strm.avail_out;
		gp_assert(strm.avail_out <= out_size && bytes_eq(out + wrote, before + wrote, strm.avail_out));
		read += take - strm.avail_in;
		left = strm.avail_in;
		finishing = finishing || flush == Z_FINISH;
		free(piece);
		free(out);
		free(before);
	} while (code != Z_STREAM_END && nondet_u8() != 0);
	return 0;
}
