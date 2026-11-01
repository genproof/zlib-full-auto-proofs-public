// Law res_free_deflate: Counted through the zalloc and zfree it is given, deflate gives back every byte it took: when
// deflateInit2 with any parameters (any ints) fails, and after it succeeded, one deflate() of any data (under 2^32
// bytes) with any output space and flush, and deflateEnd, nothing is left allocated; and deflateInit2 returns
// Z_MEM_ERROR only when the zalloc has returned Z_NULL.
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
	int level = (int) nondet_u32();
	int window_bits = (int) nondet_u32();
	int mem_level = (int) nondet_u32();
	int strategy = (int) nondet_u32();
	size_t data_len = nondet_u32();
	size_t room = nondet_u32();
	unsigned char *data = alloc_any_bytes(data_len);
	unsigned char *out = malloc(room);
	if (data == NULL || out == NULL)
		return 0;
	struct count count;
	z_stream strm;
	counted_stream(&strm, &count);

	int code = deflateInit2(&strm, level, Z_DEFLATED, window_bits, mem_level, strategy);
	if (code == Z_OK) {
		set_buffer(&strm, data, data_len, out, room);
		deflate(&strm, (int) nondet_u32());
		deflateEnd(&strm);
	}

	// zlib.h, deflateInit2: "Z_MEM_ERROR if there was not enough memory"; deflateEnd: "All dynamically allocated
	// data structures for this stream are freed."
	gp_assert(code != Z_MEM_ERROR || count.failed);
	gp_assert(count.now == 0);
	return 0;
}
