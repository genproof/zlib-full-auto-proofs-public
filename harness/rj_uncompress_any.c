// Law rj_uncompress_any: For any source (any bytes, any length the allocator provides, 0 included, and then also a
// Z_NULL buffer) and an output space of any size (0 included, and then also a Z_NULL buffer), uncompress2 returns one of
// the codes zlib.h documents for it: Z_OK, Z_MEM_ERROR, Z_BUF_ERROR or Z_DATA_ERROR; it sets the output length to at
// most the output space's size and the consumed source length to at most the source's length, and leaves the rest of
// the output space (after the bytes it reports written) as it was.
#include "laws_common.h"

int main(void) {
	size_t source_len = upto(PTRDIFF_MAX);
	size_t decompressed_size = upto(PTRDIFF_MAX);
	size_t null_if_empty = upto(1);
	unsigned char *source = Z_NULL;
	if (source_len > 0 || null_if_empty == 0)
		source = alloc_any_bytes(source_len);
	unsigned char *decompressed = Z_NULL;
	if (decompressed_size > 0 || null_if_empty == 0)
		decompressed = alloc_any_bytes(decompressed_size);
	if ((source == NULL && source_len > 0) || (decompressed == NULL && decompressed_size > 0))
		return 0;
	unsigned char *decompressed_copy = copy_of(decompressed, decompressed_size);
	if (decompressed_copy == NULL && decompressed_size > 0)
		return 0;
	uLongf decompressed_len = decompressed_size;
	uLong source_consumed_len = source_len;

	int code = uncompress2(decompressed, &decompressed_len, source, &source_consumed_len);

	// zlib.h, uncompress: "uncompress returns Z_OK if success, Z_MEM_ERROR if there was not enough memory,
	// Z_BUF_ERROR if there was not enough room in the output buffer, or Z_DATA_ERROR if the input data was corrupted
	// or incomplete"; "On exit, *destLen is the actual size of the uncompressed data."; uncompress2: "On return,
	// *sourceLen is the number of source bytes consumed."
	gp_assert(code == Z_OK || code == Z_MEM_ERROR || code == Z_BUF_ERROR || code == Z_DATA_ERROR);
	gp_assert(decompressed_len <= decompressed_size && source_consumed_len <= source_len);
	if (decompressed_size > 0)
		gp_assert(bytes_eq(decompressed + decompressed_len, decompressed_copy + decompressed_len,
				   decompressed_size - decompressed_len));
	return 0;
}
