// Law inflate_decode: inflate decodes correctly.  The input is a stream built here by the reference encoder of
// harness/deflate_ref.h (written from RFC 1951 alone) from ANY sequence of blocks:
//  - stored blocks (3.2.4) of ANY length <= 65535 holding ANY bytes;
//  - fixed-Huffman blocks (3.2.6) and dynamic-Huffman blocks (3.2.7) of ANY sequence of literals (ANY byte) and
//    back-references of ANY length 3..258 at ANY distance 1..min(bytes so far, 2^wb) (3.2.5), ended by the
//    end-of-block code; a dynamic block with ANY nlen 257..286 and ndist 1..30 code lengths <= 15 that inflate
//    accepts (deflate_ref.h code_ok: complete codes, the single-code and empty-distance-code exceptions, a code for
//    256) and ANY complete code length code, its code lengths sent with ANY choice, per position, between the
//    literal length and a valid run (16: 3..6 copies of the previous length, 17: 3..10 zeros, 18: 11..138 zeros, of
//    ANY run length; runs may cross from the literal/length to the distance lengths);
//    (a drawn symbol that cannot be sent -- a length or distance out of range, a symbol without a code in a dynamic
//    block, an invalid run -- is not sent;)
//  - the last block marked final;
// in a raw, zlib (RFC 1950: ANY window size 2^wb, wb 8..15, ANY FLEVEL, the Adler-32 trailer) or gzip (RFC 1952: a
// minimal header, the CRC-32 and length trailer) wrapper; followed by ANY 0..16 bytes of garbage.  inflateInit2 with a
// windowBits that accepts it (raw: -wb; zlib: wb, 0, or 32 + wb; gzip: 16 + wb or 32 + wb); then inflate() calls with
// ANY flush value, offered ANY further amount of the input (an amount beyond the end offers the rest) and ANY output
// space <= 2^20 bytes (each call: objects of exactly avail_in and avail_out bytes), until Z_STREAM_END.  Properties:
//  - every call returns Z_OK, Z_BUF_ERROR or Z_STREAM_END (never an error on a valid stream);
//  - the bytes produced by each call are the next bytes of the encoded data (the output is always a prefix of it);
//  - at Z_STREAM_END all the data has been produced (total_out = its length) and exactly the stream was consumed
//    (none of the garbage after it);
//  - data_type (zlib.h): whenever inflate reports a block boundary (bit 128: just after an end-of-block code or the
//    header), the output so far is exactly the data of the blocks completed; bit 64 (decoding the last block) is set
//    exactly when the output may have reached the last block: with it, the output covers all blocks before the last,
//    without it, at most those.
// (Z_MEM_ERROR ends the run.)  Bounds: data <= 2^18 bytes, stream <= 2^19 bytes, any number of blocks and symbols.
#include "deflate_ref.h"

#define GP_DATA_MAX (1u << 18)
#define GP_STREAM_MAX (1u << 19)
#define GP_OUT_MAX (1u << 20)

static const unsigned char cl_order[19] = {16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15};

// the header of a dynamic block after BTYPE: the drawn code lengths (returns 0 when they are not acceptable: the run
// is then dropped by gp_assume), the code lengths sent with the drawn runs; the codes in lcodes/dcodes
static void dyn_header(struct bw *w, unsigned nlen, unsigned ndist, unsigned char *ll, unsigned short *lcodes,
		       unsigned short *dcodes)
{
	const unsigned m = nlen + ndist;
	unsigned char cl[19], choice[316], runs[316];
	unsigned short clcodes[19];
	nondet_bytes(ll, m);
	nondet_bytes(cl, 19);
	nondet_bytes(choice, m);
	nondet_bytes(runs, m);
	for (unsigned i = 0; i < m; ++i)
		gp_assume(ll[i] <= 15);
	for (unsigned i = 0; i < 19; ++i)
		gp_assume(cl[i] <= 7);
	gp_assume(ll[256] != 0);
	gp_assume(code_ok(ll, nlen, 1) && code_ok(ll + nlen, ndist, 2) && code_ok(cl, 19, 0));
	canonical(ll, nlen, lcodes);
	canonical(ll + nlen, ndist, dcodes);
	canonical(cl, 19, clcodes);
	bw_bits(w, nlen - 257, 5);
	bw_bits(w, ndist - 1, 5);
	bw_bits(w, 19 - 4, 4);
	for (unsigned i = 0; i < 19; ++i)
		bw_bits(w, cl[cl_order[i]], 3);
	unsigned i = 0;
	while (i < m) {
		const unsigned r = runs[i];
		unsigned same = 0;              // how many of ll[i..] equal ll[i]
		while (i + same < m && ll[i + same] == ll[i] && same < 138)
			same++;
		if (choice[i] >= 192 && ll[i] == 0 && r >= 11 && r <= 138 && r <= same && cl[18] != 0) {
			bw_code(w, clcodes[18], cl[18]);
			bw_bits(w, r - 11, 7);
			i += r;
		} else if (choice[i] >= 192 && ll[i] == 0 && r >= 3 && r <= 10 && r <= same && cl[17] != 0) {
			bw_code(w, clcodes[17], cl[17]);
			bw_bits(w, r - 3, 3);
			i += r;
		} else if (choice[i] >= 192 && i > 0 && ll[i - 1] == ll[i] && r >= 3 && r <= 6 && r <= same &&
			   cl[16] != 0) {
			bw_code(w, clcodes[16], cl[16]);
			bw_bits(w, r - 3, 2);
			i += r;
		} else {
			gp_assume(cl[ll[i]] != 0);      // the literal length must have a code
			bw_code(w, clcodes[ll[i]], cl[ll[i]]);
			i++;
		}
	}
}

int main(void)
{
	const unsigned char wrap = nondet_u8();         // 0 raw, 1 zlib, 2 gzip (others: raw)
	const unsigned wb = nondet_u32();
	const unsigned char flevel = nondet_u8();
	const unsigned char isel = nondet_u8();
	gp_assume(wb >= 8 && wb <= 15);
	unsigned char *data = malloc(GP_DATA_MAX);
	unsigned char *src = malloc(GP_STREAM_MAX);
	unsigned char *isb = malloc(GP_DATA_MAX + 1);   // isb[k]: k bytes of data end a block (or k = 0)
	if (data == NULL || src == NULL || isb == NULL)
		return 0;
	for (unsigned i = 0; i <= GP_DATA_MAX; ++i)
		isb[i] = 0;
	isb[0] = 1;
	struct bw w;
	w.buf = src;
	w.len = 0;
	w.nb = 0;
	const unsigned maxd = 1u << wb;
	if (wrap == 1) {
		const unsigned cmf = ((wb - 8) << 4) | 8;
		const unsigned flg0 = (unsigned) (flevel & 3) << 6;
		const unsigned flg = flg0 + (31 - ((cmf << 8) + flg0) % 31) % 31;
		bw_byte(&w, (unsigned char) cmf);
		bw_byte(&w, (unsigned char) flg);
	} else if (wrap == 2) {
		static const unsigned char gz[10] = {0x1f, 0x8b, 8, 0, 0, 0, 0, 0, 0, 3};
		for (unsigned i = 0; i < 10; ++i)
			bw_byte(&w, gz[i]);
	}
	unsigned char ll[316];                          // a dynamic block's code lengths, and its codes
	unsigned short lcodes[286], dcodes[30];
	unsigned n = 0;                                 // the data so far
	unsigned last_start = 0;                        // the data before the last block
	for (;;) {
		const unsigned char more = nondet_u8();
		const unsigned char btype = nondet_u8();
		const unsigned last = more == 0;
		if (last)
			last_start = n;
		const unsigned bt = btype & 3;          // 0 stored, 1 fixed, 2 dynamic, 3 fixed
		gp_assume(w.len + 8 <= GP_STREAM_MAX);
		bw_bits(&w, last, 1);
		if (bt == 0) {                          // stored
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
		} else {                                // Huffman codes
			const int dyn = bt == 2;
			unsigned nlen = 0, ndist = 0;
			if (dyn) {
				nlen = nondet_u32();
				ndist = nondet_u32();
				gp_assume(nlen >= 257 && nlen <= 286 && ndist >= 1 && ndist <= 30);
				gp_assume(w.len + 16 + 2 * (nlen + ndist) <= GP_STREAM_MAX);
				bw_bits(&w, 2, 2);
				dyn_header(&w, nlen, ndist, ll, lcodes, dcodes);
			} else {
				bw_bits(&w, 1, 2);
			}
			for (;;) {
				const unsigned char kind = nondet_u8();
				gp_assume(w.len + 8 <= GP_STREAM_MAX);
				if (kind == 0)
					break;
				if (kind < 128) {
					const unsigned char lit = nondet_u8();
					if (dyn && ll[lit] == 0)
						continue;       // no code for it
					gp_assume(n < GP_DATA_MAX);
					data[n] = lit;
					n++;
					if (dyn)
						bw_code(&w, lcodes[lit], ll[lit]);
					else
						bw_fixed(&w, lit);
				} else {
					const unsigned len = nondet_u32();
					const unsigned dist = nondet_u32();
					if (len < 3 || len > 258 || dist < 1 || dist > n || dist > maxd)
						continue;
					const unsigned lc = len_code(len), dc = dist_code(dist);
					if (dyn && (257 + lc >= nlen || ll[257 + lc] == 0 || dc >= ndist ||
						    ll[nlen + dc] == 0))
						continue;       // no code for it
					gp_assume(n + len <= GP_DATA_MAX);
					for (unsigned i = 0; i < len; ++i)
						data[n + i] = data[n + i - dist];
					n += len;
					if (dyn) {
						bw_code(&w, lcodes[257 + lc], ll[257 + lc]);
						bw_bits(&w, len - ref_lbase[lc], ref_lext[lc]);
						bw_code(&w, dcodes[dc], ll[nlen + dc]);
						bw_bits(&w, dist - ref_dbase[dc], ref_dext[dc]);
					} else {
						bw_fixed_match(&w, len, dist);
					}
				}
			}
			if (dyn)
				bw_code(&w, lcodes[256], ll[256]);
			else
				bw_fixed(&w, 256);
		}
		isb[n] = 1;
		if (last)
			break;
	}
	bw_align(&w);
	gp_assume(w.len + 8 + 16 <= GP_STREAM_MAX);
	if (wrap == 1) {
		const unsigned long a = ref_adler32(1, data, n);
		bw_byte(&w, (unsigned char) (a >> 24));
		bw_byte(&w, (unsigned char) (a >> 16));
		bw_byte(&w, (unsigned char) (a >> 8));
		bw_byte(&w, (unsigned char) a);
	} else if (wrap == 2) {
		const unsigned long c = ref_crc32(0, data, n);
		bw_byte(&w, (unsigned char) c);
		bw_byte(&w, (unsigned char) (c >> 8));
		bw_byte(&w, (unsigned char) (c >> 16));
		bw_byte(&w, (unsigned char) (c >> 24));
		bw_byte(&w, (unsigned char) n);
		bw_byte(&w, (unsigned char) (n >> 8));
		bw_byte(&w, (unsigned char) (n >> 16));
		bw_byte(&w, (unsigned char) (n >> 24));
	}
	const unsigned slen = w.len;                    // the stream
	const unsigned glen = nondet_u32();
	gp_assume(glen <= 16);
	nondet_bytes(src + slen, glen);                 // garbage after it
	const unsigned total = slen + glen;

	int iw;
	if (wrap == 1)
		iw = isel < 85 ? (int) wb : isel < 170 ? 0 : 32 + (int) wb;
	else if (wrap == 2)
		iw = isel < 128 ? 16 + (int) wb : 32 + (int) wb;
	else
		iw = -(int) wb;
	z_stream s;
	stream_defaults(&s);
	int r = inflateInit2(&s, iw);
	if (r != Z_OK)
		return 0;
	unsigned pos = 0, lim = 0, opos = 0;
	for (;;) {
		const unsigned step = nondet_u32();
		const unsigned aout = nondet_u32();
		const int flush = (int) nondet_u32();
		gp_assume(aout <= GP_OUT_MAX);
		lim = step < total - lim ? lim + step : total;
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
		gp_assert(r == Z_OK || r == Z_BUF_ERROR || r == Z_STREAM_END);
		const unsigned made = aout - s.avail_out;
		gp_assert(made <= n - opos);
		gp_assert(bytes_same(ob, data + opos, made));
		opos += made;
		if (s.data_type & 128)
			gp_assert(isb[opos] != 0);
		if (s.data_type & 64)
			gp_assert(opos >= last_start);
		else
			gp_assert(opos <= last_start);
		pos += ain - s.avail_in;
		free(ib);
		free(ob);
		free(osnap);
		if (r == Z_STREAM_END)
			break;
	}
	gp_assert(opos == n);
	gp_assert(s.total_out == n);
	gp_assert(pos == slen);
	inflateEnd(&s);
	return 0;
}
