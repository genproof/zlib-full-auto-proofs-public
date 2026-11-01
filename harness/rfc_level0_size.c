// Law rfc_level0_size: For any data (any length the allocator provides) in b = max(1, ceil(data length / 65535))
// stored blocks, after deflateInit2 with level 0 and any windowBits, memLevel and strategy it accepts (others end the
// run), deflate() offered the data in pieces of any 1 to 65531 whole blocks of 65535 bytes (the rest last, with
// Z_FINISH) and any output space of at least that size (at most 2^32 - 1 bytes per call) returns Z_STREAM_END having
// written exactly the data plus 5 bytes per block plus the wrapper (raw: none; zlib: 2 header and 4 trailer bytes;
// gzip: 10 and 8).
#include "laws_common.h"

int main(void) {
	size_t data_len = upto(PTRDIFF_MAX);
	int window_bits = (int) nondet_u32();
	int mem_level = (int) nondet_u32();
	int strategy = (int) nondet_u32();
	size_t blocks = 1;
	if (data_len > 0)
		blocks = (data_len + 65534) / 65535;
	// RFC 1950 2.2: CMF, FLG ... ADLER32 (2 + 4 bytes); RFC 1952 2.3: a 10-byte header ... CRC32, ISIZE (8 bytes)
	size_t head_len = 0;
	size_t trailer_len = 0;
	if (window_bits >= 0 && window_bits <= 15) {
		head_len = 2;
		trailer_len = 4;
	}
	if (window_bits > 15) {
		head_len = 10;
		trailer_len = 8;
	}
	size_t size = head_len + 5 * blocks + data_len + trailer_len;
	size_t room = size + upto(SIZE_MAX - size);
	unsigned char *data = alloc_any_bytes(data_len);
	unsigned char *compressed = malloc(room);
	if (data == NULL || compressed == NULL)
		return 0;
	// zlib.h, deflateInit: "0 gives no compression at all (the input data is simply copied a block at a time)"
	z_stream strm;
	new_stream(&strm);
	if (deflateInit2(&strm, 0, Z_DEFLATED, window_bits, mem_level, strategy) != Z_OK)
		return 0;
	strm.next_in = data;
	strm.next_out = compressed;
	int code;
	do {
		size_t rest = data_len - (size_t) (strm.next_in - data);
		size_t piece = 65535 * (1 + upto(65530));
		int flush = Z_NO_FLUSH;
		if (piece >= rest) {
			piece = rest;
			flush = Z_FINISH;
		}
		strm.avail_in = (uInt) piece;
		strm.avail_out = clip(room - (size_t) (strm.next_out - compressed));

		code = deflate(&strm, flush);
	} while (code == Z_OK);
	// RFC 1951 3.2.4: each stored block is its header bits padded to a byte, LEN and NLEN (2 bytes each), then "LEN
	// bytes of literal data", at most 65535
	gp_assert(code == Z_STREAM_END && strm.total_out == size);
	return 0;
}
