// Law rj_far_back: Take a raw deflate stream (inflateInit2 with any windowBits -8..-15, no dictionary) that starts with
// a fixed-Huffman block of any number (below 32768) of literals (any bytes), then a length/distance pair with any
// length code, any distance code 0..29 and any extra bits whose distance is more than the number of literals written,
// then any bytes. inflate() called twice, first with any first part of it, any output space and any flush, then with
// the rest (up to 2^32 - 1 bytes of it), room for the literals and one byte more and any flush but Z_TREES, returns
// Z_DATA_ERROR the second time and never writes more than the literals (Z_MEM_ERROR ends the run).
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
	size_t literals = upto(32767);
	unsigned length_code = 257 + (unsigned) upto(28);
	unsigned distance_code = (unsigned) upto(29);
	unsigned extra = nondet_u32();
	// RFC 1951 3.2.5: distance codes 0-3 are distances 1-4; code d >= 4 has d / 2 - 1 extra bits on a base of ((2 +
	// d % 2) << (d / 2 - 1)) + 1
	unsigned distance_bits = 0;
	size_t distance = distance_code + 1;
	if (distance_code >= 4) {
		distance_bits = distance_code / 2 - 1;
		distance = ((2u | (distance_code & 1)) << distance_bits) + 1 + (extra & ((1u << distance_bits) - 1));
	}
	// RFC 1951 3.2.3: "a distance cannot refer past the beginning of the output stream"
	gp_assume(distance > literals);
	size_t stream_len = 6 + 2 * literals + upto(PTRDIFF_MAX - 6 - 2 * literals);
	unsigned char *stream = alloc_any_bytes(stream_len);
	unsigned char *literal = alloc_any_bytes(literals);
	if (stream == NULL || literal == NULL)
		return 0;
	// RFC 1951 3.2.6: length codes 256-279 are 7 bits from 0000000, 280-287 8 bits from 11000000; distance codes are
	// 5 bits
	size_t bit = 0;
	put_bits(stream, &bit, nondet_u8() & 1, 1, 0);
	put_bits(stream, &bit, 1, 2, 0);
	for (size_t i = 0; i < literals; i++)
		put_literal(stream, &bit, literal[i]);
	if (length_code < 280)
		put_bits(stream, &bit, length_code - 256, 7, 1);
	else
		put_bits(stream, &bit, 0xc0 + length_code - 280, 8, 1);
	// RFC 1951 3.2.5: length codes 265-284 have (code - 261) / 4 extra bits
	unsigned length_bits = 0;
	if (length_code >= 265 && length_code <= 284)
		length_bits = (length_code - 261) / 4;
	put_bits(stream, &bit, nondet_u32(), length_bits, 0);
	put_bits(stream, &bit, distance_code, 5, 1);
	put_bits(stream, &bit, extra, distance_bits, 0);
	// zlib.h: Z_TREES makes inflate() return "when the end of each deflate block header is reached"
	z_stream strm;
	new_stream(&strm);
	if (inflateInit2(&strm, window_bits) != Z_OK)
		return 0;
	size_t read = 0;
	size_t written = 0;
	for (int call = 1; call <= 2; call++) {
		size_t take;
		size_t room;
		int flush = (int) nondet_u32();
		if (call == 1) {
			take = upto(clip(stream_len));
			room = nondet_u32();
		} else {
			take = clip(stream_len - read);
			room = literals + 1 + upto(UINT_MAX - literals - 1);
			gp_assume(flush != Z_TREES);
		}
		unsigned char *piece = copy_of(stream + read, take);
		unsigned char *out = malloc(room);
		if (piece == NULL || out == NULL)
			return 0;
		set_buffer(&strm, piece, take, out, room);

		int code = inflate(&strm, flush);

		if (code == Z_MEM_ERROR)
			return 0;
		read += take - strm.avail_in;
		written += room - strm.avail_out;
		if (call == 2)
			gp_assert(code == Z_DATA_ERROR);
		gp_assert(written <= literals);
	}
	return 0;
}
