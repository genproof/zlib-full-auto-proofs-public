// Law adler32_combine_ref: adler32_combine gives the Adler-32 of a concatenation.  For ANY two buffers A and B of ANY
// lengths na, nb <= 2^20 (objects of exactly their lengths), ANY valid initial checksum a0 for A (halves below 65521),
// and ANY valid checksums x, y and ANY length z (any z_off_t):
//  - adler32_combine(adler32(a0, A), adler32(1, B), nb) = adler32(a0, A B) (the reference ref_adler32 of the
//    concatenation) (adler32_combine64, which it calls, is not declared by zlib.h in this configuration);
//  - for ANY valid x, y and ANY z >= 0 (up to 2^63 - 1): adler32_combine(x, y, z) is the algebraic combination of
//    RFC 1950's sums: s1 = x1 + y1 - 1 and s2 = x2 + y2 + z * (x1 - 1), both mod 65521 (x1, x2 the low and high half
//    of x, the same for y), i.e. the checksum of a concatenation whose second part has length z;
//  - for a negative length it returns 0xffffffff;
//  - no undefined behaviour for ANY 64-bit x, y and ANY z.
// Bounds: na, nb <= 2^20.
#include "zlib_common.h"

#define GP_N_MAX (1u << 20)

static int valid(unsigned long a)
{
	return a <= 0xffffffff && (a & 0xffff) < GP_BASE && (a >> 16) < GP_BASE;
}

int main(void)
{
	unsigned long a0, x, y;
	z_off_t z;
	pick(a0);
	pick(x);
	pick(y);
	pick(z);
	const unsigned na = nondet_u32();
	const unsigned nb = nondet_u32();
	gp_assume(valid(a0));
	gp_assume(na <= GP_N_MAX && nb <= GP_N_MAX);
	unsigned char *ab = malloc((size_t) na + nb);
	if (ab == NULL)
		return 0;
	nondet_bytes(ab, (size_t) na + nb);
	const unsigned long aa = adler32_z(a0, ab, na);
	const unsigned long bb = adler32_z(1, ab + na, nb);
	const unsigned long want = ref_adler32(a0, ab, (unsigned long) na + nb);
	gp_assert(adler32_combine(aa, bb, (z_off_t) nb) == want);
	const unsigned long r = adler32_combine(x, y, z);
	if (z < 0) {
		gp_assert(r == 0xffffffff);
	} else if (valid(x) && valid(y)) {
		const unsigned long x1 = x & 0xffff, x2 = x >> 16, y1 = y & 0xffff, y2 = y >> 16;
		const unsigned long zm = (unsigned long) z % GP_BASE;
		const unsigned long s1 = (x1 + y1 + GP_BASE - 1) % GP_BASE;
		const unsigned long s2 = (x2 + y2 + zm * ((x1 + GP_BASE - 1) % GP_BASE)) % GP_BASE;
		gp_assert(r == ((s2 << 16) | s1));
	}
	free(ab);
	return 0;
}
