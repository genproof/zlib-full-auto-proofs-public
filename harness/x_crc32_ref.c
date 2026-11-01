// Law crc32_ref: crc32 and crc32_z compute the CRC-32 of RFC 1952 / ISO 3309.  For ANY initial value crc (any 64-bit
// unsigned long, not only checksums), ANY buffer of ANY n <= 2^20 bytes (an object of exactly n bytes), split at ANY
// point k <= n into two calls, and the Z_NULL buffer:
//  - crc32_z(crc, buf, n) and crc32(crc, buf, n) equal the bit-by-bit reference (harness/zlib_common.h ref_crc32:
//    reflected polynomial 0xedb88320, register preset to ~crc, inverted at the end) on the 32 low bits of crc, and are
//    below 2^32;
//  - continuing is concatenating: crc32_z(crc32_z(crc, buf, k), buf + k, n - k) is the same value;
//  - crc32(crc, Z_NULL, len) is 0 for ANY len (the documented initial value), and crc32_z the same;
//  - get_crc_table() returns the table of the CRC of every byte value: entry i is the reference register update of
//    the byte i from 0 (ref_crc_byte(0, i)), for i < 256;
//  - the buffer is not changed.
// Bounds: n <= 2^20.
#include "zlib_common.h"

#define GP_N_MAX (1u << 20)

int main(void)
{
	unsigned long crc;
	pick(crc);
	const unsigned n = nondet_u32();
	const unsigned k = nondet_u32();
	const unsigned len = nondet_u32();
	gp_assume(n <= GP_N_MAX);
	gp_assume(k <= n);
	unsigned char *buf = malloc(n);
	unsigned char *snap = malloc(n);
	if (buf == NULL || snap == NULL)
		return 0;
	nondet_bytes(buf, n);
	bytes_copy(snap, buf, n);
	const unsigned long want = ref_crc32(crc, buf, n);
	const unsigned long a = crc32_z(crc, buf, n);
	gp_assert(a == want);
	gp_assert(a <= 0xffffffff);
	gp_assert(crc32(crc, buf, n) == want);
	gp_assert(crc32_z(crc32_z(crc, buf, k), buf + k, n - k) == want);
	gp_assert(crc32(crc, Z_NULL, len) == 0);
	gp_assert(crc32_z(crc, Z_NULL, len) == 0);
	gp_assert(bytes_same(buf, snap, n));
	const z_crc_t *t = get_crc_table();
	for (unsigned i = 0; i < 256; ++i)
		gp_assert(t[i] == ref_crc_byte(0, (unsigned char) i));
	free(buf);
	free(snap);
	return 0;
}
