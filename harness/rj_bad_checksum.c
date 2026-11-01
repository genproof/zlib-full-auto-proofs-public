// Law rj_bad_checksum: For any data (any length the allocator provides) compressed with deflateInit2 (any level,
// windowBits, memLevel and strategy it accepts with the zlib or gzip wrapper) and deflate (all of it, in pieces of at
// most 2^32 - 1 bytes, Z_FINISH with the last, into deflateBound_z bytes; the run ends unless it reaches Z_STREAM_END),
// with its trailer then changed in any way (zlib: the Adler-32, the last 4 bytes; gzip: the CRC-32 and ISIZE, the last
// 8), inflate() fed all of it and room for the data, in pieces of at most 2^32 - 1 bytes, with any flush, returns Z_OK
// or Z_BUF_ERROR until it returns Z_DATA_ERROR, never Z_STREAM_END (Z_MEM_ERROR ends the run).
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
	unsigned char *change = alloc_any_bytes(8);
	if (change == NULL || window_bits < 8)
		return 0;
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
	// RFC 1950 2.2: ADLER32 is the last 4 bytes; RFC 1952 2.3: CRC32 and ISIZE, the last 8
	size_t trailer_len = 4;
	if (window_bits > 15)
		trailer_len = 8;
	int changed = 0;
	for (size_t i = 0; i < trailer_len; i++) {
		compressed[compressed_len - trailer_len + i] ^= change[i];
		changed |= change[i];
	}
	gp_assume(changed != 0);
	z_stream decompressor;
	new_stream(&decompressor);
	// zlib.h, deflateInit2: "a request for 8 will result in 9"; "use 9 with inflateInit2()"
	if (window_bits == 8)
		window_bits = 9;
	if (inflateInit2(&decompressor, window_bits) != Z_OK)
		return 0;
	decompressor.next_in = compressed;
	decompressor.next_out = out;
	do {
		decompressor.avail_in = clip(compressed_len - (size_t) (decompressor.next_in - compressed));
		decompressor.avail_out = clip(data_len - (size_t) (decompressor.next_out - out));

		code = inflate(&decompressor, (int) nondet_u32());

		if (code == Z_MEM_ERROR)
			return 0;
		// RFC 1950 2.3: "A compliant decompressor must check CMF, FLG, and ADLER32, and provide an error
		// indication if any of these have incorrect values." zlib.h, inflate: "The CRC-32 is checked against
		// the gzip trailer, as is the uncompressed length, modulo 2^32."
		gp_assert(code == Z_OK || code == Z_BUF_ERROR || code == Z_DATA_ERROR);
	} while (code != Z_DATA_ERROR);
	return 0;
}
