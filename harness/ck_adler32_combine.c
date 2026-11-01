// Law ck_adler32_combine: For any bytes (any length up to PTRDIFF_MAX that the allocator provides), any split of them
// into a first and a second part and any Adler-32 value to start from (both halves below 65521), adler32_combine of the
// first part's checksum (from start) and the second part's (from 1) is the checksum of all the bytes (from start).
#include "laws_common.h"

int main(void) {
	size_t len = upto(PTRDIFF_MAX);
	size_t split = upto(len);
	unsigned char *buf = alloc_any_bytes(len);
	if (buf == NULL)
		return 0;
	uLong high = upto(65520);
	uLong start = high << 16 | upto(65520);

	uLong first = adler32_z(start, buf, split);
	uLong second = adler32_z(1, buf + split, len - split);
	uLong whole = adler32_z(start, buf, len);

	// zlib.h, adler32_combine: "adler32_combine() returns the Adler-32 checksum of seq1 and seq2 concatenated,
	// requiring only adler1, adler2, and len2."
	gp_assert(adler32_combine(first, second, (z_off_t) (len - split)) == whole);
	return 0;
}
