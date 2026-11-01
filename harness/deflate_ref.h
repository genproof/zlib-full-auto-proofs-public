// A reference DEFLATE encoder (RFC 1951), written from the RFC alone, for the inflate laws that check decoded output
// (inflate_decode): a bit writer, stored blocks (3.2.4), fixed-Huffman blocks (3.2.6) and dynamic-Huffman blocks
// (3.2.7) with ANY valid code lengths, literals, and back-references (3.2.5).
//
//  - Bits are packed starting with the least significant bit of each byte; data elements (lengths, extra bits) are
//    written least significant bit first, Huffman codes most significant bit first (3.1.1);
//  - canonical codes (3.2.2): bl_count[len] = the number of codes of each length, next_code[1] = 0,
//    next_code[len] = (next_code[len - 1] + bl_count[len - 1]) << 1, then the symbols in increasing order get
//    consecutive codes of their length;
//  - a dynamic block: BFINAL, BTYPE = 10, HLIT = nlen - 257, HDIST = ndist - 1, HCLEN = 19 - 4 (all 19 code length
//    code lengths, 3 bits each, in the order 16 17 18 0 8 7 9 6 10 5 11 4 12 3 13 2 14 1 15), then the nlen + ndist
//    code lengths (one sequence) in the code length code: 0..15 literally, 16 = copy the previous length 3..6 times
//    (2 extra bits), 17 = 3..10 zeros (3 extra bits), 18 = 11..138 zeros (7 extra bits), then the symbols.
// inflate accepts a dynamic block's codes when (inflate.c, inftrees.c): nlen <= 286, ndist <= 30; the code length
// code is complete; the literal/length code has a code for 256 and is complete or a single code of length 1; the
// distance code is complete, a single code of length 1, or empty.  kraft() and code_ok() state these.
#ifndef ZLIB_HARNESS_DEFLATE_REF_H
#define ZLIB_HARNESS_DEFLATE_REF_H
#include "zlib_common.h"

struct bw {                     // a bit writer, least significant bit first (RFC 1951 3.1.1)
	unsigned char *buf;
	unsigned len;           // complete bytes
	unsigned nb;            // bits in buf[len]
};

static void bw_bit(struct bw *w, unsigned b)
{
	if (w->nb == 0)
		w->buf[w->len] = 0;
	w->buf[w->len] = (unsigned char) (w->buf[w->len] | ((b & 1) << w->nb));
	w->nb++;
	if (w->nb == 8) {
		w->nb = 0;
		w->len++;
	}
}

static void bw_bits(struct bw *w, unsigned v, unsigned n)       // a value, its least significant bit first
{
	for (unsigned i = 0; i < n; ++i)
		bw_bit(w, v >> i);
}

static void bw_code(struct bw *w, unsigned c, unsigned n)       // a Huffman code, its most significant bit first
{
	for (unsigned i = n; i > 0; --i)
		bw_bit(w, c >> (i - 1));
}

static void bw_byte(struct bw *w, unsigned char b)              // at a byte boundary
{
	w->buf[w->len] = b;
	w->len++;
}

static void bw_align(struct bw *w)
{
	if (w->nb != 0) {
		w->nb = 0;
		w->len++;
	}
}

// the fixed literal/length code (RFC 1951 3.2.6)
static void bw_fixed(struct bw *w, unsigned v)
{
	if (v < 144)
		bw_code(w, 0x30 + v, 8);
	else if (v < 256)
		bw_code(w, 0x190 + (v - 144), 9);
	else if (v < 280)
		bw_code(w, v - 256, 7);
	else
		bw_code(w, 0xc0 + (v - 280), 8);
}

// RFC 1951 3.2.5: length codes 257..285 and distance codes 0..29
static const unsigned short ref_lbase[29] = {3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59,
					     67, 83, 99, 115, 131, 163, 195, 227, 258};
static const unsigned char ref_lext[29] = {0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5,
					   5, 5, 5, 0};
static const unsigned short ref_dbase[30] = {1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513,
					     769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577};
static const unsigned char ref_dext[30] = {0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10,
					   11, 11, 12, 12, 13, 13};

static unsigned len_code(unsigned len)          // the length code (0..28 for symbols 257..285) of a length 3..258
{
	unsigned i = 28;
	if (len < 258) {
		i = 0;
		while (i + 1 < 28 && ref_lbase[i + 1] <= len)
			i++;
	}
	return i;
}

static unsigned dist_code(unsigned dist)        // the distance code of a distance 1..32768
{
	unsigned j = 0;
	while (j + 1 < 30 && ref_dbase[j + 1] <= dist)
		j++;
	return j;
}

static void bw_fixed_match(struct bw *w, unsigned len, unsigned dist)
{
	const unsigned i = len_code(len), j = dist_code(dist);
	bw_fixed(w, 257 + i);
	bw_bits(w, len - ref_lbase[i], ref_lext[i]);
	bw_code(w, j, 5);
	bw_bits(w, dist - ref_dbase[j], ref_dext[j]);
}

// canonical codes (RFC 1951 3.2.2) of lens[0..n-1] (lengths <= 15) into codes[0..n-1]
static void canonical(const unsigned char *lens, unsigned n, unsigned short *codes)
{
	unsigned count[16], next[16];
	for (unsigned l = 0; l < 16; ++l)
		count[l] = 0;
	for (unsigned i = 0; i < n; ++i)
		count[lens[i]]++;
	count[0] = 0;
	unsigned c = 0;
	next[0] = 0;
	for (unsigned l = 1; l < 16; ++l) {
		c = (c + count[l - 1]) << 1;
		next[l] = c;
	}
	for (unsigned i = 0; i < n; ++i) {
		if (lens[i] != 0) {
			codes[i] = (unsigned short) next[lens[i]];
			next[lens[i]]++;
		} else {
			codes[i] = 0;
		}
	}
}

// the Kraft sum of lens[0..n-1] in units of 2^-15 (a complete code: 2^15), and the number of codes
static unsigned long kraft(const unsigned char *lens, unsigned n, unsigned *used)
{
	unsigned long k = 0;
	unsigned u = 0;
	for (unsigned i = 0; i < n; ++i) {
		if (lens[i] != 0) {
			k += 1ul << (15 - lens[i]);
			u++;
		}
	}
	*used = u;
	return k;
}

// does inflate accept these lengths (see the header comment)?  type 0: code length code, 1: literal/length, 2: distance
static int code_ok(const unsigned char *lens, unsigned n, int type)
{
	unsigned used;
	const unsigned long k = kraft(lens, n, &used);
	if (k == 32768)
		return 1;
	if (type == 0)
		return 0;
	if (used == 1 && k == 16384)
		return 1;                       // a single code of length 1
	return type == 2 && used == 0;          // no distance code at all
}

#endif
