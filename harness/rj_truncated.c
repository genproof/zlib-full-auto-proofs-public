// Law rj_truncated: For any data (any length the allocator provides) compressed with deflateInit2 (any level,
// windowBits, memLevel and strategy it accepts) and deflate (all of it, in pieces of at most 2^32 - 1 bytes, Z_FINISH
// with the last, into deflateBound_z bytes; the run ends unless it reaches Z_STREAM_END), inflate() fed any proper
// prefix of the compressed bytes and room for the data, in pieces of at most 2^32 - 1 bytes, with any flush, until it
// has read all of the prefix, never returns Z_STREAM_END (Z_MEM_ERROR ends the run).
#include "laws_common.h"

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
	z_stream compressor;
	new_stream(&compressor);
	if (deflateInit2(&compressor, level, Z_DEFLATED, window_bits, mem_level, strategy) != Z_OK)
		return 0;
	size_t out_size = deflateBound_z(&compressor, data_len);
	unsigned char *compressed = malloc(out_size);
	if (compressed == NULL)
		return 0;
	compressor.next_in = data;
	compressor.next_out = compressed;
	int code;
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
	size_t prefix_len = upto(compressed_len - 1);
	z_stream decompressor;
	new_stream(&decompressor);
	// zlib.h, deflateInit2: "a request for 8 will result in 9"; "use 9 with inflateInit2()"
	if (window_bits == 8)
		window_bits = 9;
	if (inflateInit2(&decompressor, window_bits) != Z_OK)
		return 0;
	decompressor.next_in = compressed;
	decompressor.next_out = out;
	while (decompressor.next_in != compressed + prefix_len) {
		decompressor.avail_in = clip(prefix_len - (size_t) (decompressor.next_in - compressed));
		decompressor.avail_out = clip(data_len - (size_t) (decompressor.next_out - out));

		code = inflate(&decompressor, (int) nondet_u32());

		if (code == Z_MEM_ERROR)
			return 0;
		// RFC 1951 3.2.3: "BFINAL is set if and only if this is the last block of the data set"; the zlib and
		// gzip streams end with ADLER32 (RFC 1950 2.2), CRC32 and ISIZE (RFC 1952 2.3). zlib.h, inflate:
		// "Z_STREAM_END if the end of the compressed data has been reached and all uncompressed output has been
		// produced"
		gp_assert(code != Z_STREAM_END);
	}
	return 0;
}
