// Law ck_crc32_combine: For any bytes (any length up to PTRDIFF_MAX that the allocator provides), any split of them
// into a first and a second part and any CRC-32 value to start from, combining the first part's CRC (from start) with
// the second part's (from 0) gives the CRC of all the bytes (from start), with crc32_combine as with crc32_combine_op
// and crc32_combine_gen.
#include "laws_common.h"

int main(void) {
	size_t len = upto(PTRDIFF_MAX);
	size_t split = upto(len);
	unsigned char *buf = alloc_any_bytes(len);
	if (buf == NULL)
		return 0;
	uLong start = nondet_u32();

	uLong first = crc32_z(start, buf, split);
	uLong second = crc32_z(0, buf + split, len - split);
	uLong whole = crc32_z(start, buf, len);

	// zlib.h, crc32_combine: "crc32_combine() returns the CRC-32 check value of seq1 and seq2 concatenated,
	// requiring only crc1, crc2, and len2"; crc32_combine_gen: "Return the operator corresponding to length len2,
	// to be used with crc32_combine_op()".
	gp_assert(crc32_combine(first, second, (z_off_t) (len - split)) == whole);
	uLong op = crc32_combine_gen((z_off_t) (len - split));
	gp_assert(crc32_combine_op(first, second, op) == whole);
	return 0;
}
