// Law ck_crc32: For any bytes (any length up to PTRDIFF_MAX that the allocator provides) and any CRC-32 value to
// continue from, crc32_z returns the CRC-32 of RFC 1952 as computed bit by bit below.
#include "laws_common.h"

int main(void) {
	size_t len = upto(PTRDIFF_MAX);
	unsigned char *buf = alloc_any_bytes(len);
	if (buf == NULL)
		return 0;
	uLong start = nondet_u32();
	// RFC 1952 2.3.1: CRC32 is "computed according to CRC-32 algorithm used in the ISO 3309 standard"; its section
	// 8 sample code: "c = crc ^ 0xffffffffL", per byte "c = crc_table[(c ^ buf[n]) & 0xff] ^ (c >> 8)", where a
	// table entry is 8 steps of "if (c & 1) { c = 0xedb88320L ^ (c >> 1); } else { c = c >> 1; }", "return c ^
	// 0xffffffffL"
	unsigned long crc = start ^ 0xffffffff;
	for (size_t i = 0; i < len; i++) {
		crc ^= buf[i];
		for (int step = 0; step < 8; step++) {
			if (crc & 1)
				crc = 0xedb88320 ^ (crc >> 1);
			else
				crc = crc >> 1;
		}
	}

	gp_assert(crc32_z(start, buf, len) == (crc ^ 0xffffffff));

	return 0;
}
