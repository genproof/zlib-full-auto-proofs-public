// Law ck_adler32: For any bytes (any length up to PTRDIFF_MAX that the allocator provides) and any Adler-32 value to
// continue from (both halves below 65521), adler32_z returns the Adler-32 of RFC 1950 as computed below.
#include "laws_common.h"

int main(void) {
	size_t len = upto(PTRDIFF_MAX);
	unsigned char *buf = alloc_any_bytes(len);
	if (buf == NULL)
		return 0;
	unsigned long s1 = upto(65520);
	unsigned long s2 = upto(65520);
	uLong start = s2 << 16 | s1;
	// RFC 1950 2.2: "s1 is the sum of all bytes, s2 is the sum of all s1 values. Both sums are done modulo 65521.
	// s1 is initialized to 1, s2 to zero. The Adler-32 checksum is stored as s2*65536 + s1"
	for (size_t i = 0; i < len; i++) {
		s1 = (s1 + buf[i]) % 65521;
		s2 = (s2 + s1) % 65521;
	}

	gp_assert(adler32_z(start, buf, len) == s2 * 65536 + s1);

	return 0;
}
