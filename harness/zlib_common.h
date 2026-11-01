// Shared by the zlib harnesses (zlib 1.3.2 core: adler32.c, crc32.c, deflate.c, trees.c, inflate.c, inffast.c,
// inftrees.c, compress.c, uncompr.c, zutil.c).
//
// A harness draws every input from quickproof.h (nondet_*, pick), restricts it with gp_assume, and states each property
// with gp_assert (undefined behaviour when the property fails).  Buffers have exactly the size the claim allows.  Every
// call of inflate() or deflate() gets its input and its output space as objects of their own, allocated with exactly
// avail_in and avail_out bytes (exact_copy, exact_space): an access before next_in, after next_in + avail_in, before
// next_out or after next_out + avail_out is then outside an object, i.e. undefined behaviour in the semantics of the
// theorem, so "inflate reads only the input it is offered and writes only the space it is offered" is part of every
// law's "no undefined behaviour".
//
// The reference facts, written from the definitions, not from zlib:
//  - Adler-32 (RFC 1950 8.2): s1 = 1 + the sum of the bytes, s2 = the sum of the successive values of s1, both mod
//    65521; the checksum is s2 * 65536 + s1.  ref_adler32 updates a checksum byte by byte;
//  - CRC-32 (RFC 1952 8, ISO 3309): the reflected polynomial 0xedb88320, register preset to all ones and inverted at
//    the end.  ref_crc32 updates a checksum bit by bit;
//  - the zlib wrapper (RFC 1950): 2 header bytes, an optional 4-byte dictionary id (big-endian Adler-32 of the
//    dictionary), the deflate data, then the big-endian Adler-32 of the uncompressed data;
//  - the gzip wrapper (RFC 1952): a header of at least 10 bytes (1f 8b 08 FLG MTIME(4) XFL OS, then the optional
//    fields), the deflate data, then the little-endian CRC-32 and the little-endian length mod 2^32 of the data;
//  - the inflate windowBits of zlib.h: 8..15 (zlib wrapper, 2^windowBits window), 0 (zlib wrapper, the window size of
//    the header), -8..-15 (raw deflate), + 16 (gzip wrapper only; 16 itself: the window size of the header), + 32
//    (zlib or gzip, detected); everything else is rejected with Z_STREAM_ERROR.
#ifndef ZLIB_HARNESS_COMMON_H
#define ZLIB_HARNESS_COMMON_H
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include "quickproof.h"
#include "zlib.h"

#define GP_BASE 65521ul             // the Adler-32 modulus (RFC 1950)
#define GP_POLY 0xedb88320ul        // the CRC-32 polynomial, reflected (RFC 1952)

// Adler-32 of buf[0..n-1] continued from the checksum a (both halves < 65521 for a checksum).
static unsigned long ref_adler32(unsigned long a, const unsigned char *buf, unsigned long n)
{
	unsigned long s1 = a & 0xffff;
	unsigned long s2 = (a >> 16) & 0xffff;
	for (unsigned long i = 0; i < n; ++i) {
		s1 = (s1 + buf[i]) % GP_BASE;
		s2 = (s2 + s1) % GP_BASE;
	}
	return (s2 << 16) | s1;
}

// The CRC-32 register update by one byte, without pre- or post-conditioning (the register is the 32 low bits).
static unsigned long ref_crc_byte(unsigned long c, unsigned char b)
{
	c ^= b;
	for (int k = 0; k < 8; ++k) {
		if (c & 1)
			c = (c >> 1) ^ GP_POLY;
		else
			c = c >> 1;
	}
	return c;
}

// CRC-32 of buf[0..n-1] continued from the checksum c (its 32 low bits).
static unsigned long ref_crc32(unsigned long c, const unsigned char *buf, unsigned long n)
{
	c = (~c) & 0xffffffff;
	for (unsigned long i = 0; i < n; ++i)
		c = ref_crc_byte(c, buf[i]);
	return (~c) & 0xffffffff;
}

static unsigned long be32(const unsigned char *p)
{
	return ((unsigned long) p[0] << 24) | ((unsigned long) p[1] << 16) | ((unsigned long) p[2] << 8) | p[3];
}

static unsigned long le32(const unsigned char *p)
{
	return ((unsigned long) p[3] << 24) | ((unsigned long) p[2] << 16) | ((unsigned long) p[1] << 8) | p[0];
}

static int bytes_same(const unsigned char *a, const unsigned char *b, unsigned long n)
{
	for (unsigned long i = 0; i < n; ++i)
		if (a[i] != b[i])
			return 0;
	return 1;
}

static void bytes_copy(unsigned char *d, const unsigned char *s, unsigned long n)
{
	for (unsigned long i = 0; i < n; ++i)
		d[i] = s[i];
}

// A new object of exactly n bytes holding src[0..n-1] (NULL when the allocation fails).
static unsigned char *exact_copy(const unsigned char *src, unsigned n)
{
	unsigned char *p = malloc(n);
	if (p != NULL)
		bytes_copy(p, src, n);
	return p;
}

// A new object of exactly n bytes with any contents, and a snapshot of them in *snap (NULL when an allocation fails).
static unsigned char *exact_space(unsigned n, unsigned char **snap)
{
	unsigned char *p = malloc(n);
	unsigned char *q = malloc(n);
	if (p == NULL || q == NULL) {
		free(p);
		free(q);
		*snap = NULL;
		return NULL;
	}
	nondet_bytes(p, n);
	bytes_copy(q, p, n);
	*snap = q;
	return p;
}

// inflateInit2's windowBits check (zlib.h): accepted values.
static int inflate_wbits_ok(int w)
{
	if (w < 0)
		return w >= -15 && w <= -8;
	if (w >= 48)
		return 0;
	w &= 15;
	return w == 0 || (w >= 8 && w <= 15);
}

// Is a value one of inflate()'s documented return codes (zlib.h)?
static int inflate_code_ok(int r)
{
	return r == Z_OK || r == Z_STREAM_END || r == Z_NEED_DICT || r == Z_DATA_ERROR || r == Z_STREAM_ERROR ||
	       r == Z_MEM_ERROR || r == Z_BUF_ERROR;
}

// A z_stream with the default allocator (zalloc, zfree, opaque all Z_NULL: zlib uses zcalloc/zcfree, i.e. malloc and
// free) and any values in the fields the caller does not have to set.
static void stream_defaults(z_stream *s)
{
	s->zalloc = Z_NULL;
	s->zfree = Z_NULL;
	s->opaque = Z_NULL;
	s->next_in = Z_NULL;
	s->avail_in = 0;
	s->next_out = Z_NULL;
	s->avail_out = 0;
	pick(s->total_in);
	pick(s->total_out);
	pick(s->adler);
	pick(s->data_type);
	pick(s->reserved);
}

#endif
