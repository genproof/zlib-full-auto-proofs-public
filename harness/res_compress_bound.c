// Law res_compress_bound: For any original data (any length the allocator provides, 0 included, and then also a
// Z_NULL buffer) and any level -1..9, compressBound_z of the original's length is original_len + (original_len >> 12)
// + (original_len >> 14) + (original_len >> 25) + 13 (its formula in compress.c), and compress2_z into that many
// bytes returns Z_OK, never Z_BUF_ERROR, with a compressed length of at most that bound (Z_MEM_ERROR ends the run).
#include "laws_common.h"

int main(void) {
	int level = -1 + (int) upto(10);
	size_t original_len = upto(PTRDIFF_MAX);
	size_t null_if_empty = upto(1);
	size_t compressed_bound = original_len + (original_len >> 12) + (original_len >> 14) + (original_len >> 25) + 13;
	gp_assert(compressBound_z(original_len) == compressed_bound);
	size_t compressed_len = compressed_bound;
	unsigned char *original = Z_NULL;
	if (original_len > 0 || null_if_empty == 0)
		original = alloc_any_bytes(original_len);
	unsigned char *compressed = malloc(compressed_bound);
	if ((original == NULL && original_len > 0) || compressed == NULL)
		return 0;

	// zlib.h, compress2: destLen "must be at least the value returned by compressBound(sourceLen)"; compressBound
	// "returns an upper bound on the compressed size after compress() or compress2()"
	int code = compress2_z(compressed, &compressed_len, original, original_len, level);

	if (code == Z_MEM_ERROR)
		return 0;
	gp_assert(code == Z_OK && compressed_len <= compressed_bound);
	return 0;
}
