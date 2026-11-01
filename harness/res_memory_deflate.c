// Law res_memory_deflate: Counted through the zalloc and zfree it is given, deflate never holds more than zconf.h's (1
// << (w + 2)) + (1 << (memLevel + 9)) bytes plus 5968 bytes, the size of deflate_state on this platform (x86_64, LP64,
// CompCert), w the window bits (windowBits without the raw sign or the gzip 16; 9 for 8, which deflateInit2 turns into
// 9), for deflateInit2 with any level, windowBits, memLevel and strategy in zlib.h's ranges and any number of deflate()
// calls on any data (any length the allocator provides) in any pieces below 2^32 bytes, each with any output space and
// any flush: deflateInit2 returns Z_OK, or Z_MEM_ERROR only when the zalloc has returned Z_NULL; and after every call,
// the most it has held at any time is within that bound.
#include "laws_common.h"
#include "laws_session.h"

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
	gp_assume(deflate_params_ok(level, window_bits, mem_level, strategy));
	size_t data_len = upto(PTRDIFF_MAX);
	unsigned char *data = alloc_any_bytes(data_len);
	if (data == NULL)
		return 0;
	struct count count;
	z_stream strm;
	counted_stream(&strm, &count);

	int code = deflateInit2(&strm, level, Z_DEFLATED, window_bits, mem_level, strategy);

	// zlib.h, deflateInit2: "Z_MEM_ERROR if there was not enough memory"
	gp_assert(code == Z_OK || (code == Z_MEM_ERROR && count.failed));
	if (code != Z_OK)
		return 0;
	int w = window_bits;
	if (w < 0)
		w = -w;
	if (w > 15)
		w = w - 16;
	// zlib.h, deflateInit2: "a request for 8 will result in 9 (a 512-byte window)"
	if (w == 8)
		w = 9;
	size_t read = 0;
	do {
		size_t take = upto(clip(data_len - read));
		size_t room = nondet_u32();
		unsigned char *out = malloc(room);
		if (out == NULL)
			return 0;
		set_buffer(&strm, data + read, take, out, room);

		deflate(&strm, (int) nondet_u32());

		// zconf.h: "The memory requirements for deflate are (in bytes): (1 << (windowBits+2)) + (1 <<
		// (memLevel+9)) that is: 128K for windowBits=15 + 128K for memLevel = 8 (default values) plus a few
		// kilobytes for small objects."
		gp_assert(count.peak <= (1ul << (w + 2)) + (1ul << (mem_level + 9)) + 5968);
		read += take - strm.avail_in;
		free(out);
	} while (nondet_u8() != 0);
	return 0;
}
