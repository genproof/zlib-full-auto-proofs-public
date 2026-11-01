// Law inflate_dict: preset dictionaries (RFC 1950 FDICT; zlib.h inflateSetDictionary, inflateGetDictionary).  ANY
// dictionary of dlen <= 2^16 bytes; a zlib stream with FDICT (ANY window size 2^wb, wb 8..15, ANY FLEVEL, the
// dictionary id = the Adler-32 of the dictionary) or a raw stream, built by the reference encoder of
// harness/deflate_ref.h (RFC 1951) from ANY sequence of stored blocks (ANY bytes) and fixed-Huffman blocks of ANY
// literals and back-references of ANY length 3..258 at ANY distance 1..min(dlen + bytes so far, 2^wb) -- reaching
// into the dictionary -- (a drawn reference out of range is not sent), the last block final.  inflateInit2 with a
// windowBits that accepts it (zlib: wb, 0, 32 + wb; raw: -wb); for a raw stream inflateSetDictionary right after it;
// then inflate() calls with ANY flush value, ANY further amount of the input (an amount beyond the end offers the
// rest), ANY output space <= 2^20 bytes (objects of exactly avail_in and avail_out bytes), until Z_STREAM_END; when
// inflate returns Z_NEED_DICT the caller sets, at its choice, first a wrong dictionary (the right one with its first
// byte changed, or one zero byte when dlen = 0), then the right one.  After every call inflateGetDictionary is asked
// for the length, then for the bytes into an object of exactly that length.  Properties:
//  - raw: inflateSetDictionary returns Z_OK;
//  - zlib: inflate returns Z_NEED_DICT, with strm->adler = the Adler-32 of the dictionary, until the dictionary is
//    set, and before producing anything; the wrong dictionary gives Z_DATA_ERROR, the right one Z_OK;
//  - otherwise every call returns Z_OK, Z_BUF_ERROR or Z_STREAM_END; the bytes produced are the next bytes of the
//    encoded data; at Z_STREAM_END all of it was produced and exactly the stream consumed;
//  - once the dictionary is set, inflateGetDictionary's length is min(dlen + bytes produced, 2^wb) and its bytes are
//    the last that many bytes of the dictionary followed by the bytes produced (the sliding window); except after
//    the call that returns Z_STREAM_END on a zlib stream, whose output inflate does not add to the window (by design:
//    inflate.c, updatewindow's comment and state CHECK; the window is not needed after the end).
// (Z_MEM_ERROR ends the run.)  Bounds: dlen <= 2^16, data <= 2^18 bytes, stream <= 2^19 bytes.
#include "deflate_ref.h"

#define GP_DICT_MAX (1u << 16)
#define GP_DATA_MAX (1u << 18)
#define GP_STREAM_MAX (1u << 19)
#define GP_OUT_MAX (1u << 20)

// history byte k of (dict ++ data): k < dlen in the dictionary
static unsigned char hist(const unsigned char *dict, unsigned dlen, const unsigned char *data, unsigned k)
{
	return k < dlen ? dict[k] : data[k - dlen];
}

int main(void)
{
	const unsigned char wrap = nondet_u8();         // 0 raw, else zlib
	const unsigned char flevel = nondet_u8();
	const unsigned char isel = nondet_u8();
	const unsigned char wsel = nondet_u8();
	const unsigned wb = nondet_u32();
	const unsigned dlen = nondet_u32();
	gp_assume(wb >= 8 && wb <= 15);
	gp_assume(dlen <= GP_DICT_MAX);
	const int zlib = wrap != 0;
	unsigned char *dict = malloc(dlen);
	unsigned char *bad = malloc(dlen == 0 ? 1 : dlen);
	unsigned char *data = malloc(GP_DATA_MAX);
	unsigned char *src = malloc(GP_STREAM_MAX);
	if (dict == NULL || bad == NULL || data == NULL || src == NULL)
		return 0;
	nondet_bytes(dict, dlen);
	const unsigned blen = dlen == 0 ? 1 : dlen;
	if (dlen == 0) {
		bad[0] = 0;
	} else {
		bytes_copy(bad, dict, dlen);
		bad[0] = (unsigned char) (dict[0] ^ 1);
	}
	const unsigned long dictid = ref_adler32(1, dict, dlen);
	struct bw w;
	w.buf = src;
	w.len = 0;
	w.nb = 0;
	const unsigned maxd = 1u << wb;
	if (zlib) {
		const unsigned cmf = ((wb - 8) << 4) | 8;
		const unsigned flg0 = ((unsigned) (flevel & 3) << 6) | 0x20;
		const unsigned flg = flg0 + (31 - ((cmf << 8) + flg0) % 31) % 31;
		bw_byte(&w, (unsigned char) cmf);
		bw_byte(&w, (unsigned char) flg);
		bw_byte(&w, (unsigned char) (dictid >> 24));
		bw_byte(&w, (unsigned char) (dictid >> 16));
		bw_byte(&w, (unsigned char) (dictid >> 8));
		bw_byte(&w, (unsigned char) dictid);
	}
	unsigned n = 0;
	for (;;) {
		const unsigned char more = nondet_u8();
		const unsigned char btype = nondet_u8();
		const unsigned last = more == 0;
		gp_assume(w.len + 8 <= GP_STREAM_MAX);
		bw_bits(&w, last, 1);
		if ((btype & 3) == 0) {                 // stored
			const unsigned len = nondet_u32();
			gp_assume(len <= 65535);
			gp_assume(n + len <= GP_DATA_MAX);
			bw_bits(&w, 0, 2);
			bw_align(&w);
			gp_assume(w.len + 4 + len <= GP_STREAM_MAX);
			bw_byte(&w, (unsigned char) len);
			bw_byte(&w, (unsigned char) (len >> 8));
			bw_byte(&w, (unsigned char) ~len);
			bw_byte(&w, (unsigned char) (~len >> 8));
			nondet_bytes(data + n, len);
			bytes_copy(src + w.len, data + n, len);
			w.len += len;
			n += len;
		} else {                                // fixed Huffman codes
			bw_bits(&w, 1, 2);
			for (;;) {
				const unsigned char kind = nondet_u8();
				gp_assume(w.len + 8 <= GP_STREAM_MAX);
				if (kind == 0)
					break;
				if (kind < 128) {
					const unsigned char lit = nondet_u8();
					gp_assume(n < GP_DATA_MAX);
					data[n] = lit;
					n++;
					bw_fixed(&w, lit);
				} else {
					const unsigned len = nondet_u32();
					const unsigned dist = nondet_u32();
					if (len < 3 || len > 258 || dist < 1 || dist > dlen + n || dist > maxd)
						continue;
					gp_assume(n + len <= GP_DATA_MAX);
					for (unsigned i = 0; i < len; ++i)
						data[n + i] = hist(dict, dlen, data, dlen + n + i - dist);
					n += len;
					bw_fixed_match(&w, len, dist);
				}
			}
			bw_fixed(&w, 256);
		}
		if (last)
			break;
	}
	bw_align(&w);
	gp_assume(w.len + 4 <= GP_STREAM_MAX);
	if (zlib) {
		const unsigned long a = ref_adler32(1, data, n);
		bw_byte(&w, (unsigned char) (a >> 24));
		bw_byte(&w, (unsigned char) (a >> 16));
		bw_byte(&w, (unsigned char) (a >> 8));
		bw_byte(&w, (unsigned char) a);
	}
	const unsigned slen = w.len;

	const int iw = !zlib ? -(int) wb : isel < 85 ? (int) wb : isel < 170 ? 0 : 32 + (int) wb;
	z_stream s;
	stream_defaults(&s);
	int r = inflateInit2(&s, iw);
	if (r != Z_OK)
		return 0;
	int dict_set = 0;
	if (!zlib) {
		r = inflateSetDictionary(&s, dict, dlen);
		if (r == Z_MEM_ERROR)
			return 0;
		gp_assert(r == Z_OK);
		dict_set = 1;
	}
	unsigned pos = 0, lim = 0, opos = 0;
	for (;;) {
		const unsigned step = nondet_u32();
		const unsigned aout = nondet_u32();
		const int flush = (int) nondet_u32();
		gp_assume(aout <= GP_OUT_MAX);
		lim = step < slen - lim ? lim + step : slen;
		const unsigned ain = lim - pos;
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
		const unsigned made = aout - s.avail_out;
		pos += ain - s.avail_in;
		if (r == Z_NEED_DICT) {
			gp_assert(zlib && !dict_set);
			gp_assert(made == 0 && opos == 0);
			gp_assert(s.adler == dictid);
			if (wsel == 0) {
				r = inflateSetDictionary(&s, bad, blen);
				gp_assert(r == Z_DATA_ERROR);
			}
			r = inflateSetDictionary(&s, dict, dlen);
			if (r == Z_MEM_ERROR)
				return 0;
			gp_assert(r == Z_OK);
			dict_set = 1;
		} else {
			gp_assert(r == Z_OK || r == Z_BUF_ERROR || r == Z_STREAM_END);
			gp_assert(made <= n - opos);
			gp_assert(bytes_same(ob, data + opos, made));
			opos += made;
		}
		if (dict_set && (r != Z_STREAM_END || !zlib)) {
			uInt dl = 0;
			gp_assert(inflateGetDictionary(&s, Z_NULL, &dl) == Z_OK);
			const unsigned long have = (unsigned long) dlen + opos;
			gp_assert(dl == (have < maxd ? have : maxd));
			unsigned char *gd = malloc(dl);
			if (gd == NULL)
				return 0;
			gp_assert(inflateGetDictionary(&s, gd, Z_NULL) == Z_OK);
			for (unsigned i = 0; i < dl; ++i)
				gp_assert(gd[i] == hist(dict, dlen, data, (unsigned) (have - dl) + i));
			free(gd);
		}
		free(ib);
		free(ob);
		free(osnap);
		if (r == Z_STREAM_END)
			break;
	}
	gp_assert(opos == n);
	gp_assert(pos == slen);
	inflateEnd(&s);
	return 0;
}
