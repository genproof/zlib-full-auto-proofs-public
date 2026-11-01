// Law rt_roundtrip: For any original data (any length the allocator provides, 0 included, and then also a Z_NULL
// buffer) and any level -1..9, compress2 into original_len + (original_len >> 12) + (original_len >> 14) +
// (original_len >> 25) + 13 bytes (compressBound's formula in compress.c) returns Z_OK with a compressed length within
// that bound, and uncompress2 of its output followed by any bytes (any number up to PTRDIFF_MAX minus the output's
// length), into an output space of any size at least the original's length (any size up to PTRDIFF_MAX; Z_NULL when
// the size is 0, or not), returns Z_OK, sets the output length to the original's length and the consumed source
// length to the compressed length (none of the bytes after them read), the output holds exactly the original data, as
// a copy made before compress2 holds it, and the bytes of the output space after it are unchanged (Z_MEM_ERROR ends
// the run).
#include "laws_common.h"

int main(void) {
	size_t original_len = upto(PTRDIFF_MAX);
	size_t decompressed_size = original_len + upto(PTRDIFF_MAX - original_len);
	size_t null_if_empty = upto(1);
	int level = -1 + (int) upto(10);
	size_t compressed_bound = original_len + (original_len >> 12) + (original_len >> 14) + (original_len >> 25) + 13;
	unsigned char *original = Z_NULL;
	if (original_len > 0 || null_if_empty == 0)
		original = alloc_any_bytes(original_len);
	if (original == NULL && original_len > 0)
		return 0;
	unsigned char *original_copy = copy_of(original, original_len);
	unsigned char *compressed = malloc(compressed_bound);
	unsigned char *decompressed = Z_NULL;
	if (decompressed_size > 0 || null_if_empty == 0)
		decompressed = alloc_any_bytes(decompressed_size);
	if ((original_copy == NULL && original_len > 0) || compressed == NULL ||
	    (decompressed == NULL && decompressed_size > 0))
		return 0;
	unsigned char *decompressed_copy = copy_of(decompressed, decompressed_size);
	if (decompressed_copy == NULL && decompressed_size > 0)
		return 0;
	// zlib.h, compress2: destLen "must be at least the value returned by compressBound(sourceLen)"
	uLongf compressed_len = compressed_bound;

	int code = compress2(compressed, &compressed_len, original, original_len, level);

	if (code == Z_MEM_ERROR)
		return 0;
	gp_assert(code == Z_OK && compressed_len <= compressed_bound);
	size_t suffix_len = 0;
	if (compressed_len < PTRDIFF_MAX)
		suffix_len = upto(PTRDIFF_MAX - compressed_len);
	unsigned char *source = alloc_any_bytes(compressed_len + suffix_len);
	if (source == NULL)
		return 0;
	for (size_t i = 0; i < compressed_len; i++)
		source[i] = compressed[i];
	uLongf decompressed_len = decompressed_size;
	uLong source_consumed_len = compressed_len + suffix_len;

	code = uncompress2(decompressed, &decompressed_len, source, &source_consumed_len);

	if (code == Z_MEM_ERROR)
		return 0;
	// zlib.h, uncompress: "On exit, *destLen is the actual size of the uncompressed data."; uncompress2: "On
	// return, *sourceLen is the number of source bytes consumed."
	gp_assert(code == Z_OK && decompressed_len == original_len && source_consumed_len == compressed_len);
	gp_assert(bytes_eq(decompressed, original_copy, original_len));
	if (decompressed_size > original_len)
		gp_assert(bytes_eq(decompressed + original_len, decompressed_copy + original_len,
				   decompressed_size - original_len));
	return 0;
}
