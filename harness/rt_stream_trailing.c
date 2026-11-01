// Law rt_stream_trailing: For any level, windowBits, memLevel and strategy in zlib.h's ranges for deflateInit2 and any
// data (any length the allocator provides) given to deflate() in any pieces (at most 2^32 - 1 bytes per call), with any
// output space (at most 2^32 - 1 bytes per call, none included, from a buffer of any size; running out of it ends the
// run) and any flush Z_NO_FLUSH..Z_BLOCK per call (Z_FINISH coming with the rest of the data once one call can take it,
// and repeated until Z_STREAM_END), then inflateInit2 with the matching windowBits and inflate() fed the compressed
// bytes followed by any bytes (any number up to PTRDIFF_MAX minus the stream's length) in any pieces, empty ones
// included, with any output space, none included, and any flush: deflateInit2 and inflateInit2 return Z_OK; every call
// moves next_in and next_out exactly as far as it lowers avail_in and avail_out; a deflate() call offered no output
// space returns Z_BUF_ERROR and moves no pointer and no counter; inflate() returns only Z_OK or Z_BUF_ERROR until
// Z_STREAM_END, a call offered neither input nor output space does not return Z_OK and moves no pointer and no
// counter, and at Z_STREAM_END it has read exactly the compressed bytes, none of the bytes after them, and written
// exactly the data, as a copy made before compression holds it (Z_MEM_ERROR ends the run).
#include "laws_common.h"
#include "laws_session.h"

int main(void) {
	int level = (int) nondet_u32();
	int window_bits = (int) nondet_u32();
	int mem_level = (int) nondet_u32();
	int strategy = (int) nondet_u32();
	gp_assume(deflate_params_ok(level, window_bits, mem_level, strategy));
	size_t data_len = upto(PTRDIFF_MAX);
	size_t out_size = upto(PTRDIFF_MAX);
	unsigned char *data = alloc_any_bytes(data_len);
	if (data == NULL)
		return 0;
	unsigned char *expected = copy_of(data, data_len);
	unsigned char *compressed = malloc(out_size);
	unsigned char *out = malloc(data_len);
	if (expected == NULL || compressed == NULL || out == NULL)
		return 0;
	z_stream compressor;
	new_stream(&compressor);
	int code = deflateInit2(&compressor, level, Z_DEFLATED, window_bits, mem_level, strategy);
	if (code == Z_MEM_ERROR)
		return 0;
	gp_assert(code == Z_OK);
	compressor.next_in = data;
	compressor.next_out = compressed;
	size_t offered = 0;
	int flush = Z_NO_FLUSH;
	struct position at;
	do {
		size_t read = (size_t) (compressor.next_in - data);
		if (flush != Z_FINISH) {
			offered += upto(data_len - offered);
			flush = (int) upto(Z_BLOCK);
			if (flush == Z_FINISH && data_len - read > UINT_MAX)
				flush = Z_NO_FLUSH;
			if (flush == Z_FINISH)
				offered = data_len;
		}
		compressor.avail_in = clip(offered - read);
		compressor.avail_out = clip(upto(out_size - (size_t) (compressor.next_out - compressed)));
		position_of(&compressor, &at);

		code = deflate(&compressor, flush);

		// zlib.h, deflate: "Compress more input starting at next_in and update next_in and avail_in accordingly";
		// "Z_BUF_ERROR if no progress is possible (for example avail_in or avail_out was zero)"
		gp_assert(accounted(&compressor, &at));
		if (at.avail_out == 0)
			gp_assert(code == Z_BUF_ERROR && unmoved(&compressor, &at));
		if (code != Z_STREAM_END && compressor.next_out == compressed + out_size)
			return 0;
	} while (code != Z_STREAM_END);
	size_t compressed_len = (size_t) (compressor.next_out - compressed);
	// RFC 1950 2.2: "Any data which may appear after ADLER32 are not part of the zlib stream." zlib.h,
	// inflateInit2: "inflate() will return Z_STREAM_END at the end of the gzip member."
	size_t after = upto(PTRDIFF_MAX - compressed_len);
	unsigned char *input = alloc_any_bytes(compressed_len + after);
	if (input == NULL)
		return 0;
	for (size_t i = 0; i < compressed_len; i++)
		input[i] = compressed[i];
	z_stream decompressor;
	new_stream(&decompressor);
	// zlib.h, deflateInit2: "a request for 8 will result in 9"; "use 9 with inflateInit2()"
	if (window_bits == 8)
		window_bits = 9;
	code = inflateInit2(&decompressor, window_bits);
	if (code == Z_MEM_ERROR)
		return 0;
	gp_assert(code == Z_OK);
	decompressor.next_in = input;
	decompressor.next_out = out;
	do {
		decompressor.avail_in = clip(upto(compressed_len + after - (size_t) (decompressor.next_in - input)));
		decompressor.avail_out = clip(upto(data_len - (size_t) (decompressor.next_out - out)));
		position_of(&decompressor, &at);

		code = inflate(&decompressor, (int) nondet_u32());

		if (code == Z_MEM_ERROR)
			return 0;
		gp_assert(code == Z_OK || code == Z_BUF_ERROR || code == Z_STREAM_END);
		gp_assert(accounted(&decompressor, &at));
		// zlib.h, inflate() "returns Z_OK if some progress has been made (more input processed or more output
		// produced)"
		if (at.avail_in == 0 && at.avail_out == 0)
			gp_assert(code != Z_OK && unmoved(&decompressor, &at));
	} while (code != Z_STREAM_END);
	gp_assert(decompressor.next_in == input + compressed_len);
	gp_assert(decompressor.next_out == out + data_len && bytes_eq(out, expected, data_len));
	return 0;
}
