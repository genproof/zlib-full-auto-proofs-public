// Law rj_bad_block: Take a raw deflate stream (inflateInit2 with any windowBits -8..-15) whose first block, with any
// BFINAL, breaks RFC 1951: a stored block whose NLEN is not the one's complement of LEN; a block of the reserved type
// 11; a fixed-Huffman block of up to (PTRDIFF_MAX - 5) / 9 literals followed by the literal/length code 286 or 287, or
// by the length code 257 and the distance code 30 or 31; or a dynamic-Huffman block with HLIT 30 or 31 (287 or 288
// literal/length codes); then any bytes (any length the allocator provides). inflate() fed all of it and room for at
// least the literals, in pieces of at most 2^32 - 1 bytes, with any flush, returns Z_OK or Z_BUF_ERROR until it
// returns Z_DATA_ERROR, at the latest when offered the rest (after one more call if that one, with Z_TREES, stopped at
// the end of the block header; Z_MEM_ERROR ends the run).
#include "laws_common.h"

// RFC 1951 3.1.1: "Data elements are packed into bytes in order of increasing bit number within the byte"; "Huffman
// codes are packed starting with the most-significant bit of the code", the other elements with the least significant.
static void put_bits(unsigned char *stream, size_t *bit, unsigned value, unsigned count, int huffman) {
	for (unsigned i = 0; i < count; i++) {
		unsigned shift = huffman ? count - 1 - i : i;
		unsigned one = (value >> shift) & 1;
		unsigned char mask = (unsigned char) (1u << (*bit % 8));
		stream[*bit / 8] = (unsigned char) ((stream[*bit / 8] & ~mask) | (one ? mask : 0));
		*bit += 1;
	}
}
// RFC 1951 3.2.6, fixed codes: literals 0-143 are 8 bits from 00110000, 144-255 are 9 bits from 110010000.
static void put_literal(unsigned char *stream, size_t *bit, unsigned literal) {
	if (literal < 144)
		put_bits(stream, bit, 0x30 + literal, 8, 1);
	else
		put_bits(stream, bit, 0x190 + literal - 144, 9, 1);
}

int main(void) {
	int window_bits = -8 - (int) upto(7);
	unsigned kind = (unsigned) upto(4);
	unsigned which = nondet_u8() & 1;
	size_t literals = 0;
	if (kind == 2 || kind == 3)
		literals = upto((PTRDIFF_MAX - 5) / 9);
	size_t stream_len = 5 + 2 * literals + upto(PTRDIFF_MAX - 5 - 2 * literals);
	size_t room = literals + upto(PTRDIFF_MAX - literals);
	unsigned char *stream = alloc_any_bytes(stream_len);
	unsigned char *literal = alloc_any_bytes(literals);
	unsigned char *out = malloc(room);
	if (stream == NULL || literal == NULL || out == NULL)
		return 0;
	// RFC 1951 3.2.3: BTYPE "00 - no compression", "01 - compressed with fixed Huffman codes", "10 - ... dynamic
	// Huffman codes", "11 - reserved (error)"
	size_t bit = 1;
	unsigned btype[5] = {0, 3, 1, 1, 2};
	put_bits(stream, &bit, btype[kind], 2, 0);
	// RFC 1951 3.2.4: LEN and NLEN are bytes 1-4 (any bits up to the byte boundary are ignored); "NLEN is the one's
	// complement of LEN"
	if (kind == 0)
		gp_assume((stream[1] | stream[2] << 8) != (~(stream[3] | stream[4] << 8) & 0xffff));
	for (size_t i = 0; i < literals; i++)
		put_literal(stream, &bit, literal[i]);
	// RFC 1951 3.2.6: "Literal/length values 286-287 will never actually occur in the compressed data" (codes
	// 11000110, 11000111); "distance codes 30-31 will never actually occur" (after the length code 257, 0000001)
	if (kind == 2)
		put_bits(stream, &bit, 0xc6 + which, 8, 1);
	if (kind == 3) {
		put_bits(stream, &bit, 1, 7, 1);
		put_bits(stream, &bit, 30 + which, 5, 1);
	}
	// RFC 1951 3.2.7: "HLIT, # of Literal/Length codes - 257 (257 - 286)"
	if (kind == 4)
		put_bits(stream, &bit, 30 + which, 5, 0);
	z_stream strm;
	new_stream(&strm);
	if (inflateInit2(&strm, window_bits) != Z_OK)
		return 0;
	strm.next_in = stream;
	strm.next_out = out;
	int flush = (int) nondet_u32();
	int code;
	size_t in_rest, out_rest;
	do {
		in_rest = stream_len - (size_t) (strm.next_in - stream);
		out_rest = room - (size_t) (strm.next_out - out);
		strm.avail_in = clip(in_rest);
		strm.avail_out = clip(out_rest);

		code = inflate(&strm, flush);

		if (code == Z_MEM_ERROR)
			return 0;
	} while ((code == Z_OK || code == Z_BUF_ERROR) && (in_rest > UINT_MAX || out_rest > UINT_MAX));
	if (code == Z_OK && flush == Z_TREES)
		code = inflate(&strm, flush);

	gp_assert(code == Z_DATA_ERROR);
	return 0;
}
