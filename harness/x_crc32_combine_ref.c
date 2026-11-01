// Law crc32_combine_ref: crc32_combine and its variants give the CRC-32 of a concatenation.  For ANY two buffers A
// and B of ANY lengths na, nb <= 2^20 (objects of exactly their lengths), ANY initial value c0 for A (any 64-bit
// value), and ANY two 64-bit values x, y and ANY length z (any z_off_t, also negative):
//  - crc32_combine(crc32(c0, A), crc32(0, B), nb) = crc32(c0, A B) (the CRC-32 of the concatenation, by the
//    reference ref_crc32), and so does crc32_combine_op(.., .., crc32_combine_gen(nb)) (crc32_combine64 and
//    crc32_combine_gen64, which these call, are not declared by zlib.h in this configuration);
//  - for ANY x, y and any length 0 <= z <= 2^20: crc32_combine(x, y, z) is the CRC register of x (32 low bits)
//    advanced over z zero bytes, xor the 32 low bits of y (the reference: z * 8 steps of the bitwise register
//    update), below 2^32;
//  - for a negative length crc32_combine returns 0 and crc32_combine_gen returns 0, and crc32_combine_op with the
//    operator 0 returns 0 (no undefined behaviour for any length).
// Bounds: na, nb <= 2^20; the shift reference for z <= 2^20.
#include "zlib_common.h"

#define GP_N_MAX (1u << 20)

int main(void)
{
	unsigned long c0, x, y;
	z_off_t z;
	pick(c0);
	pick(x);
	pick(y);
	pick(z);
	const unsigned na = nondet_u32();
	const unsigned nb = nondet_u32();
	gp_assume(na <= GP_N_MAX && nb <= GP_N_MAX);
	unsigned char *ab = malloc((size_t) na + nb);
	if (ab == NULL)
		return 0;
	nondet_bytes(ab, (size_t) na + nb);
	const unsigned long ca = crc32_z(c0, ab, na);
	const unsigned long cb = crc32_z(0, ab + na, nb);
	const unsigned long want = ref_crc32(c0, ab, (unsigned long) na + nb);
	gp_assert(crc32_combine(ca, cb, (z_off_t) nb) == want);
	gp_assert(crc32_combine_op(ca, cb, crc32_combine_gen((z_off_t) nb)) == want);
	if (z < 0) {
		gp_assert(crc32_combine(x, y, z) == 0);
		gp_assert(crc32_combine_gen(z) == 0);
		gp_assert(crc32_combine_op(x, y, 0) == 0);
	} else if (z <= (z_off_t) GP_N_MAX) {
		unsigned long reg = x & 0xffffffff;
		for (z_off_t i = 0; i < z; ++i)
			reg = ref_crc_byte(reg, 0);
		const unsigned long r = crc32_combine(x, y, z);
		gp_assert(r == (reg ^ (y & 0xffffffff)));
		gp_assert(r <= 0xffffffff);
	}
	free(ab);
	return 0;
}
