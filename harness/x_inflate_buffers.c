// Law inflate_buffers: inflate's buffer discipline and counters, for ANY input and ANY sequence of calls of the inflate
// API.  inflateInit2 with ANY windowBits (any int: zlib, gzip, raw, auto-detect, and every invalid value), then ANY
// number of calls, each of them, at the caller's choice: inflate() with ANY flush value (any int), inflateSync,
// inflateGetDictionary, inflateSetDictionary (any bytes, any length), inflatePrime (any bits, any value),
// inflateReset, inflateReset2 (any windowBits), inflateValidate, inflateMark, inflateCodesUsed, inflateSyncPoint; then
// inflateEnd.  The input is ANY n <= 2^24 bytes; each call is offered the next ANY number of not yet consumed bytes
// (next_in = the start of a new object of exactly that many bytes; for inflate() also Z_NULL with any avail_in) and
// ANY output space of at most 2^20 bytes (next_out = a new object of exactly avail_out bytes with any contents; for
// inflate() also Z_NULL).  Misuse not covered: a Z_NULL next_in with avail_in > 0 for inflateSync (which does not
// check it, unlike inflate()).
// Properties:
//  - no undefined behaviour: in particular every call reads only [next_in, next_in + avail_in) and writes only
//    [next_out, next_out + avail_out) (each its own object), and inflateGetDictionary writes only the dictionary
//    length it reports;
//  - inflateInit2 returns Z_OK, Z_MEM_ERROR, or Z_STREAM_ERROR, the last exactly for the windowBits zlib.h rejects
//    (unless the state allocation failed first: Z_MEM_ERROR); after Z_OK
//    total_in and total_out are 0;
//  - after every call: 0 <= avail_in <= what was offered, next_in advanced by exactly the bytes consumed
//    (avail_in decrease), the same for next_out/avail_out and the bytes produced; next_in stays Z_NULL when it was;
//  - inflate() writes only the bytes it reports as produced: the rest of the output space is unchanged, and the
//    input is unchanged;
//  - total_in and total_out count exactly the bytes consumed and produced since the last init or reset (inflateSync:
//    total_in counts the bytes it skipped), except in the inflate() call that returns Z_MEM_ERROR (the stream is then
//    unusable; on the unmodified code also after Z_NEED_DICT, fixed by patch F1);
//  - inflateGetDictionary reports at most 2^15 bytes and writes exactly that many;
//  - inflateEnd returns Z_OK.
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
	int r = inflateInit2(&s, wbits);
	gp_assert(r == Z_OK || r == Z_STREAM_ERROR || r == Z_MEM_ERROR);
	// inflateInit2_ allocates its state before it checks windowBits, so a failed allocation gives
	// Z_MEM_ERROR whatever windowBits is: the exact Z_STREAM_ERROR condition is stated for the other results
	// (as in inflate_codes.c).
	if (r != Z_MEM_ERROR)
		gp_assert((r == Z_STREAM_ERROR) == !inflate_wbits_ok(wbits));
	if (r != Z_OK) {
		free(src);
		return 0;
	}
	gp_assert(s.total_in == 0 && s.total_out == 0);
	unsigned pos = 0;           // input consumed so far: the next call is offered src[pos..lim)
	unsigned lim = 0;
	for (;;) {
		const unsigned nlim = nondet_u32();
		const unsigned aout = nondet_u32();
		const int flush = (int) nondet_u32();
		const unsigned arg = nondet_u32();
		const unsigned char op = nondet_u8();
		const unsigned char in_null = nondet_u8();
		const unsigned char out_null = nondet_u8();
		const unsigned char stop = nondet_u8();
		gp_assume(pos <= nlim && nlim <= n);
		gp_assume(aout <= GP_OUT_MAX);
		lim = nlim;
		const unsigned ain = lim - pos;
		unsigned char *ib = exact_copy(src + pos, ain);
		unsigned char *osnap;
		unsigned char *ob = exact_space(aout, &osnap);
		if (ib == NULL || ob == NULL)
			return 0;
		// Z_NULL pointers are passed to inflate() only (the other functions do not check them)
		const int nin = op < 200 && in_null == 0, nout = op < 200 && out_null == 0;
		s.next_in = nin ? Z_NULL : ib;
		s.avail_in = ain;
		s.next_out = nout ? Z_NULL : ob;
		s.avail_out = aout;
		const unsigned long tin = s.total_in, tout = s.total_out;
		int reset = 0;
		if (op < 200) {
			r = inflate(&s, flush);
		} else if (op < 210) {
			r = inflateSync(&s);
			gp_assert(r == Z_OK || r == Z_BUF_ERROR || r == Z_DATA_ERROR || r == Z_STREAM_ERROR);
		} else if (op < 220) {
			uInt dl = 0;
			r = inflateGetDictionary(&s, Z_NULL, &dl);
			gp_assert(r == Z_OK);
			gp_assert(dl <= 32768);
			if (dl <= aout) {
				r = inflateGetDictionary(&s, ob, Z_NULL);
				gp_assert(r == Z_OK);
				gp_assert(bytes_same(ob + dl, osnap + dl, aout - dl));
				bytes_copy(osnap, ob, dl);      // the dictionary is not output: the checks below see no change
			}
		} else if (op < 230) {
			r = inflateSetDictionary(&s, ob, aout);
			gp_assert(r == Z_OK || r == Z_STREAM_ERROR || r == Z_DATA_ERROR || r == Z_MEM_ERROR);
		} else if (op < 235) {
			r = inflatePrime(&s, (int) arg, flush);
			gp_assert(r == Z_OK || r == Z_STREAM_ERROR);
		} else if (op < 240) {
			r = inflateReset(&s);
			gp_assert(r == Z_OK);
			reset = 1;
		} else if (op < 245) {
			r = inflateReset2(&s, (int) arg);
			gp_assert((r == Z_OK) == inflate_wbits_ok((int) arg));
			gp_assert(r == Z_OK || r == Z_STREAM_ERROR);
			reset = r == Z_OK;
		} else if (op < 250) {
			r = inflateValidate(&s, (int) arg);
			gp_assert(r == Z_OK);
		} else if (op < 252) {
			(void) inflateMark(&s);
			r = Z_OK;
		} else if (op < 254) {
			(void) inflateCodesUsed(&s);
			r = Z_OK;
		} else {
			r = inflateSyncPoint(&s);
			gp_assert(r == 0 || r == 1);
		}
		gp_assert(s.avail_in <= ain);
		gp_assert(s.avail_out <= aout);
		const unsigned used = ain - s.avail_in;
		const unsigned made = aout - s.avail_out;
		if (nin) {
			gp_assert(s.next_in == Z_NULL);
			gp_assert(used == 0);
		} else {
			gp_assert(s.next_in == ib + used);
		}
		if (nout) {
			gp_assert(s.next_out == Z_NULL);
			gp_assert(made == 0);
		} else {
			gp_assert(s.next_out == ob + made);
		}
		gp_assert(bytes_same(ib, src + pos, ain));
		gp_assert(bytes_same(ob + made, osnap + made, aout - made));
		if (reset) {
			gp_assert(s.total_in == 0 && s.total_out == 0);
		} else if (!(op < 200 && r == Z_MEM_ERROR)) {
			gp_assert(s.total_in == tin + used);
			gp_assert(s.total_out == tout + made);
		}
		pos += used;
		if (reset) {
			// a new stream: the rest of the input is offered from where it stands
			lim = pos;
		}
		free(ib);
		free(ob);
		free(osnap);
		if (stop == 0)
			break;
	}
	r = inflateEnd(&s);
	gp_assert(r == Z_OK);
	free(src);
	return 0;
}
