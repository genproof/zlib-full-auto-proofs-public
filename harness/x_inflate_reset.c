// Law inflate_reset: inflateReset and inflateReset2 give a stream that behaves exactly like a new one.  inflateInit2
// with ANY windowBits; ANY input of n <= 2^24 bytes; ANY number of inflate() calls (ANY flush, ANY split, ANY output
// space <= 2^20 bytes; objects of exactly avail_in and avail_out bytes); then inflateReset, or inflateReset2 with ANY
// windowBits; then the same input from its start, fed by ANY number of inflate() calls (ANY flush, ANY split, ANY
// output space), in lockstep to the reset stream and to a stream freshly made by inflateInit2 with the same
// windowBits, each call offering both streams the same bytes and the same amount of output space.  Properties:
//  - inflateReset returns Z_OK; inflateReset2 returns Z_OK exactly when inflateInit2 accepts its windowBits;
//  - after the reset total_in and total_out are 0, msg is Z_NULL, and every call returns the same code on both
//    streams, consumes and produces the same number of bytes, produces the same bytes, and leaves the same total_in,
//    total_out, data_type, msg, and (with a wrapper) adler;
// unless one of them runs out of memory (Z_MEM_ERROR: the reset stream keeps its window, the new one allocates its
// own), which ends the run.
// Bounds: n <= 2^24 input bytes, at most 2^20 bytes of output space per call, any number of calls.
#include "zlib_common.h"

#define GP_IN_MAX (1u << 24)
#define GP_OUT_MAX (1u << 20)

int main(void)
{
	const int wbits = (int) nondet_u32();
	const unsigned n = nondet_u32();
	gp_assume(n <= GP_IN_MAX);
	unsigned char *src = malloc(n);
	if (src == NULL)
		return 0;
	nondet_bytes(src, n);
	z_stream a, b;
	stream_defaults(&a);
	stream_defaults(&b);
	int r = inflateInit2(&a, wbits);
	if (r != Z_OK)
		return 0;
	int phase = 1, w2 = wbits;
	unsigned pos = 0;
	for (;;) {
		const unsigned nlim = nondet_u32();
		const unsigned aout = nondet_u32();
		const int flush = (int) nondet_u32();
		const int wsel = (int) nondet_u32();
		const unsigned char stop = nondet_u8();
		const unsigned char how = nondet_u8();
		gp_assume(pos <= nlim && nlim <= n);
		gp_assume(aout <= GP_OUT_MAX);
		const unsigned ain = nlim - pos;
		unsigned char *ia = exact_copy(src + pos, ain);
		unsigned char *ib = exact_copy(src + pos, ain);
		unsigned char *sa, *sb;
		unsigned char *oa = exact_space(aout, &sa);
		unsigned char *ob = exact_space(aout, &sb);
		if (ia == NULL || ib == NULL || oa == NULL || ob == NULL)
			return 0;
		a.next_in = ia;
		a.avail_in = ain;
		a.next_out = oa;
		a.avail_out = aout;
		const int ra = inflate(&a, flush);
		if (ra == Z_MEM_ERROR)
			return 0;
		if (phase == 2) {
			b.next_in = ib;
			b.avail_in = ain;
			b.next_out = ob;
			b.avail_out = aout;
			const int rb = inflate(&b, flush);
			if (rb == Z_MEM_ERROR)
				return 0;
			gp_assert(ra == rb);
			gp_assert(a.avail_in == b.avail_in && a.avail_out == b.avail_out);
			gp_assert(bytes_same(oa, ob, aout - a.avail_out));
			gp_assert(a.total_in == b.total_in && a.total_out == b.total_out);
			gp_assert(a.data_type == b.data_type && a.msg == b.msg);
			if (w2 >= 0)
				gp_assert(a.adler == b.adler);
		}
		pos += ain - a.avail_in;
		free(ia);
		free(ib);
		free(oa);
		free(ob);
		free(sa);
		free(sb);
		if (stop == 0) {
			if (phase == 2)
				break;
			// the reset, and the new stream
			if (how & 1) {
				r = inflateReset(&a);
				gp_assert(r == Z_OK);
			} else {
				w2 = wsel;
				r = inflateReset2(&a, w2);
				gp_assert((r == Z_OK) == inflate_wbits_ok(w2));
				if (r != Z_OK)
					return 0;
			}
			gp_assert(a.total_in == 0 && a.total_out == 0 && a.msg == Z_NULL);
			r = inflateInit2(&b, w2);
			if (r != Z_OK)
				return 0;
			phase = 2;
			pos = 0;
			if (w2 < 0)
				b.adler = a.adler;      // a raw stream never sets adler: start both alike
		}
	}
	inflateEnd(&a);
	inflateEnd(&b);
	return 0;
}
