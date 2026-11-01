// Law res_free_inflate: Counted through the zalloc and zfree it is given, inflate gives back every byte it took: when
// inflateInit2 with any windowBits (any int) fails, and after it succeeded, one inflate() of any input (under 2^32
// bytes) with any output space and flush, and inflateEnd, nothing is left allocated; and inflateInit2 and inflate
// return Z_MEM_ERROR only when the zalloc has returned Z_NULL.
#include "laws_common.h"

struct count {
	size_t now;
	size_t peak;
	int failed;
};
static voidpf counted_alloc(voidpf opaque, uInt items, uInt size) {
	struct count *count = opaque;
	size_t bytes = (size_t) items * size;
	size_t *block = malloc(sizeof (size_t) + bytes);
	if (block == NULL) {
		count->failed = 1;
		return Z_NULL;
	}
	block[0] = bytes;
	count->now += bytes;
	if (count->now > count->peak)
		count->peak = count->now;
	return block + 1;
}
static void counted_free(voidpf opaque, voidpf address) {
	struct count *count = opaque;
	size_t *block = (size_t *) address - 1;
	count->now -= block[0];
	free(block);
}
static void counted_stream(z_stream *strm, struct count *count) {
	count->now = 0;
	count->peak = 0;
	count->failed = 0;
	strm->zalloc = counted_alloc;
	strm->zfree = counted_free;
	strm->opaque = count;
	set_buffer(strm, Z_NULL, 0, Z_NULL, 0);
}

int main(void) {
	int window_bits = (int) nondet_u32();
	size_t input_len = nondet_u32();
	size_t room = nondet_u32();
	unsigned char *input = alloc_any_bytes(input_len);
	unsigned char *out = malloc(room);
	if (input == NULL || out == NULL)
		return 0;
	struct count count;
	z_stream strm;
	counted_stream(&strm, &count);

	int code = inflateInit2(&strm, window_bits);
	if (code == Z_OK) {
		set_buffer(&strm, input, input_len, out, room);
		code = inflate(&strm, (int) nondet_u32());
		inflateEnd(&strm);
	}

	// zlib.h, inflateInit2 and inflate: "Z_MEM_ERROR if there was not enough memory"; inflateEnd: "All dynamically
	// allocated data structures for this stream are freed."
	gp_assert(code != Z_MEM_ERROR || count.failed);
	gp_assert(count.now == 0);
	return 0;
}
