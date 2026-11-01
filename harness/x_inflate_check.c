// Law inflate_check: what inflate() produces is what the stream's check value vouches for.  inflateInit2 with ANY
// windowBits; ANY input of n <= 2^24 bytes; ANY number of inflate() calls with ANY flush value, ANY split of the input
// and ANY output space (each call: objects of exactly avail_in and avail_out bytes).  Let `out` be all the bytes
// inflate() has produced so far.  Properties:
//  - with a zlib or gzip wrapper (windowBits >= 0; zlib or gzip as detected from the first two bytes for 32..47),
//    once out is not empty: the stream starts with a valid header (zlib, RFC 1950: CM = 8, CINFO <= 7, the header
//    is a multiple of 31; gzip, RFC 1952: 1f 8b 08 and no reserved flag), and after every call strm->adler is the
//    Adler-32 (zlib) or CRC-32 (gzip) of out, computed by the plain definition (harness/zlib_common.h);
//  - on Z_STREAM_END with a zlib wrapper: the 4 bytes before the end of the consumed input are the big-endian
//    Adler-32 of out; with a gzip wrapper: the 8 bytes before it are the little-endian CRC-32 of out and the length of
//    out mod 2^32; strm->adler is that check value; total_out is the length of out;
//  - with a raw stream (windowBits < 0) strm->adler is never changed.
// So no stream is accepted (Z_STREAM_END) whose trailer does not match the data inflate delivered.
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
	z_stream s;
	stream_defaults(&s);
	const unsigned long adler0 = s.adler;
	int r = inflateInit2(&s, wbits);
	if (r != Z_OK) {
		free(src);
		return 0;
	}
	const int raw = wbits < 0;
	const int gz = !raw && ((wbits >= 16 && wbits < 32) ||
				(wbits >= 32 && n >= 2 && src[0] == 0x1f && src[1] == 0x8b));
	unsigned pos = 0;
	unsigned long tout = 0;                 // the length of out
	unsigned long ra = 1, rc = 0;           // Adler-32 and CRC-32 of out
	for (;;) {
		const unsigned nlim = nondet_u32();
		const unsigned aout = nondet_u32();
		const int flush = (int) nondet_u32();
		const unsigned char stop = nondet_u8();
		gp_assume(pos <= nlim && nlim <= n);
		gp_assume(aout <= GP_OUT_MAX);
		const unsigned ain = nlim - pos;
		unsigned char *ib = exact_copy(src + pos, ain);
		unsigned char *osnap;
		unsigned char *ob = exact_space(aout, &osnap);
		if (ib == NULL || ob == NULL)
			return 0;
		s.next_in = ib;
		s.avail_in = ain;
		s.next_out = ob;
		s.avail_out = aout;
		r = inflate(&s, flush);
		if (r == Z_MEM_ERROR)
			return 0;
		const unsigned used = ain - s.avail_in;
		const unsigned made = aout - s.avail_out;
		pos += used;
		tout += made;
		ra = ref_adler32(ra, ob, made);
		rc = ref_crc32(rc, ob, made);
		if (raw) {
			gp_assert(s.adler == adler0);
		} else if (tout != 0) {
			if (gz) {
				gp_assert(src[0] == 0x1f && src[1] == 0x8b && src[2] == 8 && (src[3] & 0xe0) == 0);
				gp_assert(s.adler == rc);
			} else {
				gp_assert((src[0] & 0x0f) == 8 && (src[0] >> 4) <= 7);
				gp_assert((((unsigned) src[0] << 8) | src[1]) % 31 == 0);
				gp_assert(s.adler == ra);
			}
		}
		if (r == Z_STREAM_END && !raw) {
			gp_assert(s.total_out == tout);
			if (gz) {
				gp_assert(pos >= 18);
				gp_assert(le32(src + pos - 8) == rc);
				gp_assert(le32(src + pos - 4) == (tout & 0xffffffff));
				gp_assert(s.adler == rc);
			} else {
				gp_assert(pos >= 6);
				gp_assert(be32(src + pos - 4) == ra);
				gp_assert(s.adler == ra);
			}
		}
		free(ib);
		free(ob);
		free(osnap);
		if (stop == 0)
			break;
	}
	inflateEnd(&s);
	free(src);
	return 0;
}
