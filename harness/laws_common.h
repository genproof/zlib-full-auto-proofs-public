// laws_common.h: trivial helpers shared by the zlib laws (each law includes it once). No models, no algorithms.
#include <limits.h>
#include <stdlib.h>
#include "quickproof.h"
#include "zlib.h"
static size_t upto(size_t max) {
	size_t value = nondet_size();
	return value < max ? value : max;
}
static uInt clip(size_t n) { return n < UINT_MAX ? (uInt) n : UINT_MAX; }
static unsigned char *alloc_any_bytes(size_t n) {
	unsigned char *bytes = malloc(n);
	if (bytes != NULL)
		nondet_bytes(bytes, n);
	return bytes;
}
static unsigned char *copy_of(const unsigned char *source, size_t n) {
	unsigned char *copy = malloc(n);
	for (size_t i = 0; copy != NULL && i < n; i++)
		copy[i] = source[i];
	return copy;
}
static int bytes_eq(const unsigned char *a, const unsigned char *b, size_t n) {
	for (size_t i = 0; i < n; i++)
		if (a[i] != b[i])
			return 0;
	return 1;
}
static void set_buffer(z_stream *strm, unsigned char *in, size_t in_len, unsigned char *out, size_t out_len) {
	strm->next_in = in;
	strm->avail_in = (uInt) in_len;
	strm->next_out = out;
	strm->avail_out = (uInt) out_len;
}
static void new_stream(z_stream *strm) {
	strm->zalloc = Z_NULL;
	strm->zfree = Z_NULL;
	strm->opaque = Z_NULL;
	set_buffer(strm, Z_NULL, 0, Z_NULL, 0);
}
