// Law adler32_ref: adler32 and adler32_z compute the Adler-32 of RFC 1950 8.2.  For ANY initial checksum adler whose
// halves are below 65521 (a valid checksum), ANY buffer of ANY n <= 2^20 bytes (an object of exactly n bytes), split
// at ANY point k <= n into two calls:
//  - adler32_z(adler, buf, n) and adler32(adler, buf, n) equal the plain definition (harness/zlib_common.h
//    ref_adler32: s1 = s1 + byte, s2 = s2 + s1, both mod 65521, byte by byte);
//  - continuing is concatenating: adler32_z(adler32_z(adler, buf, k), buf + k, n - k) is the same value;
//  - for ANY initial value at all (any 64-bit unsigned long): no undefined behaviour, and each half of the result is
//    congruent mod 65521 to the reference computed from the halves of the initial value;
//  - adler32(adler, Z_NULL, len) is 1 for ANY adler and len (the documented initial value), and adler32_z the same;
//  - the buffer is not changed.
// Bounds: n <= 2^20.
#include "zlib_common.h"

#define GP_N_MAX (1u << 20)

int main(void)
{
	unsigned long adler, any;
	pick(adler);
	pick(any);
	const unsigned n = nondet_u32();
	const unsigned k = nondet_u32();
	const unsigned len = nondet_u32();
	gp_assume((adler & 0xffff) < GP_BASE && ((adler >> 16) & 0xffff) < GP_BASE && adler <= 0xffffffff);
	gp_assume(n <= GP_N_MAX);
	gp_assume(k <= n);
	unsigned char *buf = malloc(n);
	unsigned char *snap = malloc(n);
	if (buf == NULL || snap == NULL)
		return 0;
	nondet_bytes(buf, n);
	bytes_copy(snap, buf, n);
	const unsigned long want = ref_adler32(adler, buf, n);
	gp_assert(adler32_z(adler, buf, n) == want);
	gp_assert(adler32(adler, buf, n) == want);
	gp_assert(adler32_z(adler32_z(adler, buf, k), buf + k, n - k) == want);
	const unsigned long r = adler32_z(any, buf, n);
	const unsigned long ref = ref_adler32(((((any >> 16) & 0xffff) % GP_BASE) << 16) | ((any & 0xffff) % GP_BASE),
					      buf, n);
	gp_assert((r & 0xffff) % GP_BASE == (ref & 0xffff));
	gp_assert(((r >> 16) & 0xffff) % GP_BASE == ((ref >> 16) & 0xffff));
	gp_assert(r <= 0xffffffff);
	gp_assert(adler32(any, Z_NULL, len) == 1);
	gp_assert(adler32_z(any, Z_NULL, len) == 1);
	gp_assert(bytes_same(buf, snap, n));
	free(buf);
	free(snap);
	return 0;
}
