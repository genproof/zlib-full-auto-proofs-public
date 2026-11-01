// Law rfc_stored: Build, by RFC 1950/1951/1952, a stream of any data cut into any number of stored blocks of any sizes
// up to 65535 (any padding bits after each block header), raw, zlib (any CINFO the window allows, any FLEVEL) or gzip
// (any FTEXT, MTIME, XFL, OS), followed by any bytes (data, blocks and bytes after each up to 2^60, more than any
// allocator provides). inflate() (any window 8..15) fed it and room for the data, in pieces of at most 2^32 - 1 bytes,
// with any flush, returns Z_OK or Z_BUF_ERROR until Z_STREAM_END and has then written exactly the data, as a copy made
// before any zlib call holds it (Z_MEM_ERROR ends the run).
#include "laws_common.h"

int main(void) {
	size_t data_len = upto(1ul << 60);
	size_t blocks = 1 + upto((1ul << 60) - 1);
	size_t after = upto(1ul << 60);
	int wrapper = (int) upto(2);
	int window = 8 + (int) upto(7);
	size_t head_len = 0;
	size_t trailer_len = 0;
	if (wrapper == 1) {
		head_len = 2;
		trailer_len = 4;
	}
	if (wrapper == 2) {
		head_len = 10;
		trailer_len = 8;
	}
	size_t stream_len = head_len + 5 * blocks + data_len + trailer_len + after;
	unsigned char *stream = alloc_any_bytes(stream_len);
	unsigned char *data = alloc_any_bytes(data_len);
	if (stream == NULL || data == NULL)
		return 0;
	unsigned char *expected = copy_of(data, data_len);
	unsigned char *out = malloc(data_len);
	if (expected == NULL || out == NULL)
		return 0;
	// RFC 1950 2.2: CMF = CINFO << 4 | CM 8; FLG = FLEVEL (any), FDICT 0, FCHECK. RFC 1952 2.3: ID1 ID2 CM FLG
	// (FTEXT only) MTIME XFL OS (any)
	if (wrapper == 1) {
		stream[0] = (unsigned char) (upto(window - 8) << 4 | 8);
		stream[1] = (unsigned char) (stream[1] & 0xc0);
		stream[1] = (unsigned char) (stream[1] + (31 - (stream[0] * 256 + stream[1]) % 31) % 31);
	}
	if (wrapper == 2) {
		stream[0] = 0x1f;
		stream[1] = 0x8b;
		stream[2] = 8;
		stream[3] = stream[3] & 1;
	}
	// RFC 1951 3.2.3: "BFINAL is set if and only if this is the last block of the data set"; BTYPE "00 - no
	// compression". 3.2.4: "Any bits of input up to the next byte boundary are ignored. The rest of the block
	// consists of the following information: LEN NLEN ... LEN bytes of literal data"; "NLEN is the one's complement
	// of LEN"
	size_t at = head_len;
	size_t done = 0;
	for (size_t i = 0; i < blocks; i++) {
		size_t len = data_len - done;
		if (i + 1 < blocks && len > 65535)
			len = upto(65535);
		else if (i + 1 < blocks)
			len = upto(len);
		gp_assume(len <= 65535);
		int last = i + 1 == blocks;
		stream[at] = (unsigned char) ((stream[at] & 0xf8) | last);
		stream[at + 1] = (unsigned char) (len & 255);
		stream[at + 2] = (unsigned char) (len >> 8);
		stream[at + 3] = (unsigned char) (~len & 255);
		stream[at + 4] = (unsigned char) ((~len >> 8) & 255);
		for (size_t j = 0; j < len; j++)
			stream[at + 5 + j] = data[done + j];
		at += 5 + len;
		done += len;
	}
	// RFC 1950 2.2: ADLER32, 4 bytes, most significant first (2.1); RFC 1952 2.3: CRC32, ISIZE, 4 bytes each, least
	// significant first (2.1)
	uLong adler = adler32_z(1, data, data_len);
	uLong crc = crc32_z(0, data, data_len);
	for (int i = 0; i < 4; i++) {
		if (wrapper == 1)
			stream[at + i] = (unsigned char) (adler >> (24 - 8 * i));
		if (wrapper == 2) {
			stream[at + i] = (unsigned char) (crc >> (8 * i));
			stream[at + 4 + i] = (unsigned char) (data_len >> (8 * i));
		}
	}
	z_stream strm;
	new_stream(&strm);
	int window_bits[3] = {-window, window, 16 + window};
	if (inflateInit2(&strm, window_bits[wrapper]) != Z_OK)
		return 0;
	strm.next_in = stream;
	strm.next_out = out;
	int code;
	do {
		strm.avail_in = clip(stream_len - (size_t) (strm.next_in - stream));
		strm.avail_out = clip(data_len - (size_t) (strm.next_out - out));

		code = inflate(&strm, (int) nondet_u32());

		if (code == Z_MEM_ERROR)
			return 0;
		gp_assert(code == Z_OK || code == Z_BUF_ERROR || code == Z_STREAM_END);
	} while (code != Z_STREAM_END);
	gp_assert(strm.next_out == out + data_len && bytes_eq(out, expected, data_len));
	return 0;
}
