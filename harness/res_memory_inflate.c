// Law res_memory_inflate: Counted through the zalloc and zfree it is given, inflate never holds more than zconf.h's
// (1 << w) bytes plus 7160 bytes, the size of struct inflate_state on this platform (x86_64, LP64, CompCert), w the
// window bits (windowBits without the raw sign or the 16 or 32 of gzip and detection, 15 for 0), for inflateInit2 with
// any windowBits in zlib.h's ranges and any number of inflate() calls on any input (any length the allocator provides)
// in any pieces below 2^32 bytes, each with any output space and any flush: inflateInit2 returns Z_OK, or Z_MEM_ERROR
// only when the zalloc has returned Z_NULL; inflate returns Z_MEM_ERROR only when the zalloc has returned Z_NULL; and
// after every call, the most it has held at any time is within that bound.
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
	int window_bits = (int) nondet_u32();
	gp_assume(inflate_window_ok(window_bits));
	size_t input_len = upto(PTRDIFF_MAX);
	unsigned char *input = alloc_any_bytes(input_len);
	if (input == NULL)
		return 0;
	struct count count;
	z_stream strm;
	counted_stream(&strm, &count);

	int code = inflateInit2(&strm, window_bits);

	// zlib.h, inflateInit2: "Z_MEM_ERROR if there was not enough memory"
	gp_assert(code == Z_OK || (code == Z_MEM_ERROR && count.failed));
	if (code != Z_OK)
		return 0;
	int w = window_bits & 15;
	if (window_bits < 0)
		w = -window_bits;
	if (w == 0)
		w = 15;
	size_t read = 0;
	do {
		size_t take = upto(clip(input_len - read));
		size_t room = nondet_u32();
		unsigned char *out = malloc(room);
		if (out == NULL)
			return 0;
		set_buffer(&strm, input + read, take, out, room);

		code = inflate(&strm, (int) nondet_u32());

		// zconf.h: "The memory requirements for inflate are (in bytes) 1 << windowBits that is, 32K for
		// windowBits=15 (default value) plus about 7 kilobytes for small objects."
		gp_assert(code != Z_MEM_ERROR || count.failed);
		gp_assert(count.peak <= (1ul << w) + 7160);
		read += take - strm.avail_in;
		free(out);
	} while (nondet_u8() != 0);
	return 0;
}
