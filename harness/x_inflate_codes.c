// Law inflate_codes: the return codes of the inflate API are exactly the documented ones (zlib.h), for ANY input and
// ANY sequence of calls.  inflateInit2_ with ANY windowBits, the right or ANY other version string and stream size,
// or a Z_NULL stream; then ANY number of calls of inflate() (ANY flush value, ANY split of the input, ANY output
// space; next_in or next_out may be Z_NULL) and of inflateSetDictionary (ANY bytes, ANY length, at any time); then
// inflateEnd, and every entry point again on the ended stream.  The input is ANY n <= 2^24 bytes; input and output
// space as in inflate_buffers (each call: objects of exactly avail_in and avail_out bytes).  Properties:
//  - inflateInit2_: Z_VERSION_ERROR exactly when the version string does not start with '1' or the stream size is not
//    sizeof(z_stream); else Z_STREAM_ERROR exactly for a Z_NULL stream or a windowBits zlib.h rejects; else Z_OK or
//    Z_MEM_ERROR;
//  - inflate() returns one of Z_OK, Z_STREAM_END, Z_NEED_DICT, Z_DATA_ERROR, Z_STREAM_ERROR, Z_MEM_ERROR,
//    Z_BUF_ERROR, and:
//    - Z_STREAM_ERROR exactly when next_out is Z_NULL or next_in is Z_NULL with avail_in > 0 (the stream is valid);
//    - Z_OK only when the call made progress (consumed or produced a byte) and flush is not Z_FINISH;
//    - Z_BUF_ERROR only when the call made no progress or flush is Z_FINISH;
//    - Z_DATA_ERROR with strm->msg set;
//    - Z_NEED_DICT only for a zlib-wrapped stream (windowBits 0..15 or 32..47) whose header has FDICT set, after
//      exactly its 6 first bytes were consumed (header and dictionary id), with strm->adler = the dictionary id (the
//      big-endian bytes 2..5); it is repeated, without progress, until a dictionary is set;
//    - Z_STREAM_END, Z_DATA_ERROR and Z_MEM_ERROR are final: every later call with valid pointers returns the same code
//      and consumes and produces nothing;
//  - inflateSetDictionary: on a raw stream Z_OK or Z_MEM_ERROR (at any time, also after Z_MEM_ERROR); on a wrapped
//    stream Z_STREAM_ERROR unless inflate just asked for a dictionary, and then Z_DATA_ERROR exactly when the Adler-32
//    of the dictionary is not the id;
//  - inflateEnd returns Z_OK and clears strm->state; afterwards inflate, inflateEnd, inflateReset, inflateReset2,
//    inflateSetDictionary, inflateGetDictionary, inflateSync, inflatePrime and inflateValidate return
//    Z_STREAM_ERROR, inflateMark -65536 and inflateCodesUsed (unsigned long)-1; inflate and inflateEnd on a
//    Z_NULL stream return Z_STREAM_ERROR.
// Bounds: n <= 2^24 input bytes, at most 2^20 bytes of output space per call, any number of calls.
#include "zlib_common.h"

#define GP_IN_MAX (1u << 24)
#define GP_OUT_MAX (1u << 20)

int main(void)
{
	const int wbits = (int) nondet_u32();
	const unsigned n = nondet_u32();
	const int ssize = (int) nondet_u32();
	const unsigned char vsel = nondet_u8();
	const unsigned char ssel = nondet_u8();
	const unsigned char nullstrm = nondet_u8();
	const unsigned char vbyte = nondet_u8();
	gp_assume(n <= GP_IN_MAX);
	unsigned char *src = malloc(n);
	if (src == NULL)
		return 0;
	nondet_bytes(src, n);
	char other[2];
	other[0] = (char) vbyte;
	other[1] = 0;
	const char *version = vsel != 0 ? ZLIB_VERSION : other;
	const int stream_size = ssel != 0 ? (int) sizeof(z_stream) : ssize;
	z_stream s;
	stream_defaults(&s);
	int r = inflateInit2_(nullstrm == 0 ? Z_NULL : &s, wbits, version, stream_size);
	const int verr = version[0] != '1' || stream_size != (int) sizeof(z_stream);
	gp_assert((r == Z_VERSION_ERROR) == verr);
	if (!verr) {
		gp_assert(r == Z_OK || r == Z_STREAM_ERROR || r == Z_MEM_ERROR);
		// inflateInit2_ allocates its state before it checks windowBits, so a failed allocation gives
		// Z_MEM_ERROR whatever windowBits is: the exact Z_STREAM_ERROR condition is stated for the other results.
		if (r != Z_MEM_ERROR)
			gp_assert((r == Z_STREAM_ERROR) == (nullstrm == 0 || !inflate_wbits_ok(wbits)));
	}
	if (r != Z_OK) {
		free(src);
		return 0;
	}
	const int zlib_ok = wbits >= 0 && (wbits < 16 || wbits >= 32);      // a zlib wrapper is accepted
	unsigned pos = 0;
	int final = Z_OK;           // the final code once returned, else Z_OK
	int in_dict = 0;            // inflate() just returned Z_NEED_DICT
	for (;;) {
		const unsigned nlim = nondet_u32();
		const unsigned aout = nondet_u32();
		const int flush = (int) nondet_u32();
		const unsigned char op = nondet_u8();
		const unsigned char in_null = nondet_u8();
		const unsigned char out_null = nondet_u8();
		const unsigned char stop = nondet_u8();
		gp_assume(pos <= nlim && nlim <= n);
		gp_assume(aout <= GP_OUT_MAX);
		const unsigned ain = nlim - pos;
		unsigned char *ib = exact_copy(src + pos, ain);
		unsigned char *osnap;
		unsigned char *ob = exact_space(aout, &osnap);
		if (ib == NULL || ob == NULL)
			return 0;
		if (op < 24) {
			// a dictionary: the aout bytes of ob
			r = inflateSetDictionary(&s, ob, aout);
			if (wbits < 0) {
				gp_assert(r == Z_OK || r == Z_MEM_ERROR);
			} else if (!in_dict) {
				gp_assert(r == Z_STREAM_ERROR);
			} else {
				gp_assert((r == Z_DATA_ERROR) == (ref_adler32(1, ob, aout) != s.adler));
				gp_assert(r == Z_OK || r == Z_DATA_ERROR || r == Z_MEM_ERROR);
			}
			if (r == Z_MEM_ERROR) {
				final = Z_MEM_ERROR;
				in_dict = 0;
			}
		} else {
			s.next_in = in_null == 0 ? Z_NULL : ib;
			s.avail_in = ain;
			s.next_out = out_null == 0 ? Z_NULL : ob;
			s.avail_out = aout;
			r = inflate(&s, flush);
			gp_assert(inflate_code_ok(r));
			gp_assert(s.avail_in <= ain && s.avail_out <= aout);
			const unsigned used = ain - s.avail_in;
			const unsigned made = aout - s.avail_out;
			const int badptr = out_null == 0 || (in_null == 0 && ain != 0);
			gp_assert((r == Z_STREAM_ERROR) == badptr);
			if (r == Z_OK)
				gp_assert((used != 0 || made != 0) && flush != Z_FINISH);
			if (r == Z_BUF_ERROR)
				gp_assert((used == 0 && made == 0) || flush == Z_FINISH);
			if (r == Z_DATA_ERROR)
				gp_assert(s.msg != Z_NULL);
			if (!badptr && final != Z_OK) {
				gp_assert(r == final);
				gp_assert(used == 0 && made == 0);
			}
			if (r == Z_NEED_DICT) {
				gp_assert(zlib_ok);
				gp_assert(pos + used == 6);
				gp_assert((src[1] & 0x20) != 0);
				gp_assert(s.adler == be32(src + 2));
				if (in_dict)
					gp_assert(used == 0 && made == 0);
			}
			if (!badptr) {
				if (r == Z_STREAM_END || r == Z_DATA_ERROR || r == Z_MEM_ERROR)
					final = r;
				in_dict = r == Z_NEED_DICT;
			}
			pos += used;
		}
		free(ib);
		free(ob);
		free(osnap);
		if (stop == 0)
			break;
	}
	r = inflateEnd(&s);
	gp_assert(r == Z_OK);
	gp_assert(s.state == Z_NULL);
	unsigned char b[1];
	uInt dl;
	b[0] = 0;
	s.next_in = b;
	s.avail_in = 1;
	s.next_out = b;
	s.avail_out = 1;
	gp_assert(inflate(&s, Z_NO_FLUSH) == Z_STREAM_ERROR);
	gp_assert(inflateEnd(&s) == Z_STREAM_ERROR);
	gp_assert(inflateReset(&s) == Z_STREAM_ERROR);
	gp_assert(inflateReset2(&s, 15) == Z_STREAM_ERROR);
	gp_assert(inflateSetDictionary(&s, b, 1) == Z_STREAM_ERROR);
	gp_assert(inflateGetDictionary(&s, b, &dl) == Z_STREAM_ERROR);
	gp_assert(inflateSync(&s) == Z_STREAM_ERROR);
	gp_assert(inflatePrime(&s, 1, 1) == Z_STREAM_ERROR);
	gp_assert(inflateValidate(&s, 1) == Z_STREAM_ERROR);
	gp_assert(inflateMark(&s) == -65536L);
	gp_assert(inflateCodesUsed(&s) == (unsigned long) -1);
	gp_assert(inflate(Z_NULL, Z_NO_FLUSH) == Z_STREAM_ERROR);
	gp_assert(inflateEnd(Z_NULL) == Z_STREAM_ERROR);
	free(src);
	return 0;
}
