// Law ck_crc32_null: For any CRC value and any length up to PTRDIFF_MAX, crc32_z with a Z_NULL buffer returns 0, the
// initial value.
#include "laws_common.h"

int main(void) {
	uLong crc = (uLong) nondet_size();
	size_t len = upto(PTRDIFF_MAX);
	// zlib.h, crc32: "If buf is Z_NULL, this function returns the required initial value for the crc." (usage:
	// "uLong crc = crc32(0L, Z_NULL, 0);")

	gp_assert(crc32_z(crc, Z_NULL, len) == 0);

	return 0;
}
