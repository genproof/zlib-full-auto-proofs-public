// Law rfc_level0_blocks: For any data (any length the allocator provides) and b = max(1, ceil(data length / 65535)),
// after deflateInit2 with level 0 and any windowBits, memLevel and strategy it accepts (others end the run), and
// deflate() offered the data in pieces of any 1 to 65531 whole blocks of 65535 bytes (the rest last, with Z_FINISH)
// and any output space of at least that size (at most 2^32 - 1 bytes per call), what follows the wrapper header (raw:
// none; zlib: 2 bytes; gzip: 10) is b stored blocks holding the data in order, 65535 bytes in all but the last: each a
// byte with BFINAL (set on the last block only) and BTYPE 00, then LEN, NLEN = ~LEN and the LEN bytes (the data as a
// copy made before compression holds it), all within what deflate wrote.
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
	if (data == NULL)
		return 0;
	unsigned char *expected = copy_of(data, data_len);
	unsigned char *compressed = malloc(room);
	if (expected == NULL || compressed == NULL)
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
	if (code != Z_STREAM_END)
		return 0;
	// RFC 1951 3.2.3: "first bit BFINAL", "next 2 bits BTYPE", "00 - no compression"; 3.2.4: "LEN is the number of
	// data bytes in the block. NLEN is the one's complement of LEN." (2 bytes each, LSB first, 3.1.1)
	size_t at = head_len;
	size_t done = 0;
	for (size_t i = 0; i < blocks; i++) {
		size_t len = data_len - done;
		if (len > 65535)
			len = 65535;
		gp_assert(at + 5 + len <= strm.total_out && (compressed[at] & 7) == (i + 1 == blocks));
		gp_assert(compressed[at + 1] + 256 * compressed[at + 2] == len);
		gp_assert(compressed[at + 3] + 256 * compressed[at + 4] == 65535 - len);
		gp_assert(bytes_eq(compressed + at + 5, expected + done, len));
		at += 5 + len;
		done += len;
	}
	return 0;
}
