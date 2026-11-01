// Law rj_crc32_negative: For any negative length len2 and any CRC values crc1 and crc2, crc32_combine(crc1, crc2, len2)
// and crc32_combine_gen(len2) return 0.
#include "laws_common.h"

int main(void) {
	z_off_t len2 = -1 - (z_off_t) upto(PTRDIFF_MAX);
	uLong crc1 = (uLong) nondet_size();
	uLong crc2 = (uLong) nondet_size();
	// zlib.h, crc32_combine and crc32_combine_gen: "len2 must be non-negative, otherwise zero is returned."

	gp_assert(crc32_combine(crc1, crc2, len2) == 0);
	gp_assert(crc32_combine_gen(len2) == 0);

	return 0;
}
