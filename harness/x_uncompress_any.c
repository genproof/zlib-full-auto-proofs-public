// Law uncompress_any: uncompress and uncompress2 on ANY input.  ANY source of n <= 2^24 bytes (an object of exactly n
// bytes) and ANY destination capacity cap <= 2^20 (an object of exactly cap bytes with any contents; cap 0 too):
//  - no undefined behaviour: the source is only read, the destination written only within cap bytes;
//  - the result is Z_OK, Z_MEM_ERROR, Z_BUF_ERROR or Z_DATA_ERROR;
//  - *destLen is at most cap and the destination bytes from *destLen on are unchanged; uncompress2's *sourceLen is at
//    most n;
//  - on Z_OK the source starts with a valid zlib header without FDICT (RFC 1950), the *sourceLen consumed bytes end
//    with the big-endian Adler-32 of the *destLen bytes produced (by the reference definition), and uncompress
//    gives the same result and length.
// Bounds: n <= 2^24, cap <= 2^20.
#include "zlib_common.h"

#define GP_IN_MAX (1u << 24)
#define GP_CAP_MAX (1u << 20)

int main(void)
{
	const unsigned n = nondet_u32();
	const unsigned cap = nondet_u32();
	gp_assume(n <= GP_IN_MAX && cap <= GP_CAP_MAX);
	unsigned char *src = malloc(n);
	if (src == NULL)
		return 0;
	nondet_bytes(src, n);
	unsigned char *snap;
	unsigned char *dst = exact_space(cap, &snap);
	if (dst == NULL)
		return 0;
	uLongf dlen = cap;
	uLong slen = n;
	int r = uncompress2(dst, &dlen, src, &slen);
	gp_assert(r == Z_OK || r == Z_MEM_ERROR || r == Z_BUF_ERROR || r == Z_DATA_ERROR);
	gp_assert(dlen <= cap && slen <= n);
	gp_assert(bytes_same(dst + dlen, snap + dlen, cap - dlen));
	if (r == Z_OK) {
		gp_assert(slen >= 6);
		gp_assert((src[0] & 0x0f) == 8 && (src[0] >> 4) <= 7 && (((unsigned) src[0] << 8) | src[1]) % 31 == 0);
		gp_assert((src[1] & 0x20) == 0);
		gp_assert(be32(src + slen - 4) == ref_adler32(1, dst, dlen));
		unsigned char *snap2;
		unsigned char *d2 = exact_space(cap, &snap2);
		if (d2 == NULL)
			return 0;
		uLongf dlen2 = cap;
		const int r2 = uncompress(d2, &dlen2, src, n);
		if (r2 != Z_MEM_ERROR) {
			gp_assert(r2 == Z_OK && dlen2 == dlen && bytes_same(d2, dst, dlen));
		}
	}
	return 0;
}
