// Law rfc_trailing_bytes: For any data (any length the allocator provides) compressed with deflateInit2 (any level,
// windowBits, memLevel and strategy in zlib.h's ranges; it returns Z_OK) and deflate (all of it, in pieces of at most
// 2^32 - 1 bytes, Z_FINISH with the last, into deflateBound_z bytes; the run ends unless it reaches Z_STREAM_END),
// followed by any bytes (any number up to PTRDIFF_MAX minus the stream's length; none if the stream is longer),
// inflate() fed all of it and room for the data, in pieces of at most 2^32 - 1 bytes, with any flush, after
// inflateInit2 with the matching windowBits (it returns Z_OK), returns only Z_OK or Z_BUF_ERROR until Z_STREAM_END and
// stops where the stream ends: when it returns Z_STREAM_END it has read exactly the compressed bytes and none of the
// bytes after them (Z_MEM_ERROR ends the run).
#include "laws_common.h"
#include "laws_session.h"

int main(void) {
	size_t data_len = upto(PTRDIFF_MAX);
	unsigned char *data = alloc_any_bytes(data_len);
	unsigned char *out = malloc(data_len);
	if (data == NULL || out == NULL)
		return 0;
	int level = (int) nondet_u32();
	int window_bits = (int) nondet_u32();
	int mem_level = (int) nondet_u32();
	int strategy = (int) nondet_u32();
	gp_assume(deflate_params_ok(level, window_bits, mem_level, strategy));
	z_stream compressor;
	new_stream(&compressor);
	int code = deflateInit2(&compressor, level, Z_DEFLATED, window_bits, mem_level, strategy);
	if (code == Z_MEM_ERROR)
		return 0;
	gp_assert(code == Z_OK);
	size_t out_size = deflateBound_z(&compressor, data_len);
	unsigned char *compressed = malloc(out_size);
	if (compressed == NULL)
		return 0;
	compressor.next_in = data;
	compressor.next_out = compressed;
	do {
		size_t rest = data_len - (size_t) (compressor.next_in - data);
		int flush = Z_NO_FLUSH;
		if (rest <= UINT_MAX)
			flush = Z_FINISH;
		compressor.avail_in = clip(rest);
		compressor.avail_out = clip(out_size - (size_t) (compressor.next_out - compressed));

		code = deflate(&compressor, flush);
	} while (code == Z_OK);
	if (code != Z_STREAM_END)
		return 0;
	size_t compressed_len = (size_t) (compressor.next_out - compressed);
	// RFC 1950 2.2: "Any data which may appear after ADLER32 are not part of the zlib stream." zlib.h,
	// inflateInit2: "inflate() will return Z_STREAM_END at the end of the gzip member."
	size_t room = 0;
	if (compressed_len < PTRDIFF_MAX)
		room = PTRDIFF_MAX - compressed_len;
	size_t after = upto(room);
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
		decompressor.avail_in = clip(compressed_len + after - (size_t) (decompressor.next_in - input));
		decompressor.avail_out = clip(data_len - (size_t) (decompressor.next_out - out));

		code = inflate(&decompressor, (int) nondet_u32());

		if (code == Z_MEM_ERROR)
			return 0;
		gp_assert(code == Z_OK || code == Z_BUF_ERROR || code == Z_STREAM_END);
	} while (code != Z_STREAM_END);
	gp_assert(decompressor.next_in == input + compressed_len);
	return 0;
}
