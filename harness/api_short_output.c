// Law api_short_output: For any original data of one byte or more (any length the allocator provides) compressed by
// compress2 at any level -1..9 into original_len + (original_len >> 12) + (original_len >> 14) + (original_len >> 25)
// + 13 bytes (compressBound's formula in compress.c; Z_OK, a compressed length within that bound), uncompress2 of that
// output followed by any bytes (any number up to PTRDIFF_MAX minus the output's length) into an output space of any
// size below the original's length (0 included, and then also a Z_NULL buffer) returns Z_BUF_ERROR, sets the output
// length to the output space's size and the consumed source length to less than the compressed length, and the output
// holds the first decompressed_size bytes of the original data, as a copy made before compress2 holds them
// (Z_MEM_ERROR ends the run).
#include "laws_common.h"

int main(void) {
	size_t original_len = 1 + upto(PTRDIFF_MAX - 1);
	size_t decompressed_size = upto(original_len - 1);
	size_t null_if_empty = upto(1);
	int level = -1 + (int) upto(10);
	size_t compressed_bound = original_len + (original_len >> 12) + (original_len >> 14) + (original_len >> 25) + 13;
	unsigned char *original = alloc_any_bytes(original_len);
	if (original == NULL)
		return 0;
	unsigned char *original_copy = copy_of(original, original_len);
	unsigned char *compressed = malloc(compressed_bound);
	unsigned char *decompressed = Z_NULL;
	if (decompressed_size > 0 || null_if_empty == 0)
		decompressed = alloc_any_bytes(decompressed_size);
	if (original_copy == NULL || compressed == NULL || (decompressed == NULL && decompressed_size > 0))
		return 0;
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
	// zlib.h, uncompress: "Z_BUF_ERROR if there was not enough room in the output buffer"; "In the case where there
	// is not enough room, uncompress() will fill the output buffer with the uncompressed data up to that point."
	gp_assert(code == Z_BUF_ERROR && decompressed_len == decompressed_size &&
		  bytes_eq(decompressed, original_copy, decompressed_size));
	gp_assert(source_consumed_len < compressed_len);
	return 0;
}
