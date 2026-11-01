// Law ck_adler32_null: For any checksum value and any length up to PTRDIFF_MAX, adler32_z with a Z_NULL buffer returns
// 1, the initial value.
#include "laws_common.h"

int main(void) {
	uLong adler = (uLong) nondet_size();
	size_t len = upto(PTRDIFF_MAX);
	// zlib.h, adler32: "If buf is Z_NULL, this function returns the required initial value for the checksum."; RFC
	// 1950 2.2: "s1 is initialized to 1, s2 to zero".

	gp_assert(adler32_z(adler, Z_NULL, len) == 1);

	return 0;
}
