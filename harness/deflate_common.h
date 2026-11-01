// Shared by the deflate laws (deflate_roundtrip, deflate_api): a compression run with ANY parameters and ANY sequence
// of calls, recorded so that the laws can check it.  See harness/zlib_common.h for the conventions (draws, exact
// buffers).
//
// The run (deflate_run):
//  - deflateInit2 with ANY level, method, windowBits, memLevel and strategy (any int each);
//  - at the caller's choice: deflateTune with ANY four ints; deflateSetDictionary with ANY dictionary of dlen <= 2^15
//    bytes; deflateSetHeader with a gzip header of ANY text flag, time, OS, header-CRC flag, an extra field of ANY
//    xlen <= 2^12 bytes, a name and a comment of ANY length <= 2^12 of ANY non-zero bytes (each with its zero byte);
//  - then ANY number of calls until deflate returns Z_STREAM_END: deflate() with ANY flush value of zlib.h
//    (Z_NO_FLUSH .. Z_BLOCK), or deflateParams with ANY level and strategy, each offered the next ANY number of not yet
//    consumed bytes of the data (n <= 2^20 bytes, an object of exactly that many per call) and ANY output space (at
//    most 2^20 bytes, an object of exactly that many per call); the first Z_FINISH ends the data: the data is what has
//    been offered up to that call, and every later call is deflate(Z_FINISH) offered the rest of it (zlib.h: "If
//    deflate returns with avail_out == 0, this function must be called again with Z_FINISH and more output space ...
//    but no more input data").
// Bound: the total output (at most 2^22 bytes) is kept for the laws.
#ifndef ZLIB_HARNESS_DEFLATE_COMMON_H
#define ZLIB_HARNESS_DEFLATE_COMMON_H
#include "zlib_common.h"

#define GP_DATA_MAX (1u << 20)
#define GP_DICT_MAX (1u << 15)
#define GP_HSTR_MAX (1u << 12)
#define GP_DOUT_MAX (1u << 20)
#define GP_COMP_MAX (1u << 22)

// deflateInit2's parameter check (zlib.h, deflateInit2): accepted values
static int deflate_params_ok(int level, int method, int wbits, int mem, int strategy)
{
	int wrap = 1;
	if (level == Z_DEFAULT_COMPRESSION)
		level = 6;
	if (wbits < 0) {
		if (wbits < -15)
			return 0;
		wrap = 0;
		wbits = -wbits;
	} else if (wbits > 15) {
		wrap = 2;
		wbits -= 16;
	}
	return mem >= 1 && mem <= 9 && method == Z_DEFLATED && wbits >= 8 && wbits <= 15 && level >= 0 && level <= 9 &&
	       strategy >= 0 && strategy <= Z_FIXED && (wbits != 8 || wrap == 1);
}

struct drun {
	int level, method, wbits, mem, strategy;
	int init;                       // deflateInit2's result
	int wrap;                       // 0 raw, 1 zlib, 2 gzip
	int wb;                         // the window bits (8..15; 8 means 9 for deflate)
	unsigned char *data;            // the data: data[0..n), of which the first nf were compressed
	unsigned n, nf;
	unsigned char *dict;            // the dictionary (dlen bytes) when set (dict_set)
	unsigned dlen;
	int dict_set;                   // a non-empty dictionary was set
	int head_set;                   // a gzip header was set
	gz_header h;
	unsigned char *xf, *nf_, *cf;   // the header's extra, name, comment fields
	unsigned xlen, nl, cl;
	unsigned char *comp;            // the compressed output, clen bytes
	unsigned long clen;
	int ended;                      // deflate returned Z_STREAM_END
	int api_ok;                     // every call's API check held (deflate_api)
};

// 1 when every byte of buf[0..n) is non-zero
static void draw_nonzero_bytes(unsigned char *buf, unsigned n)
{
	nondet_bytes(buf, n);
	for (unsigned i = 0; i < n; ++i)
		gp_assume(buf[i] != 0);
}

// the run; returns 0 when the harness's own allocations fail (the run ends there), else 1
static int deflate_run(struct drun *R, z_stream *s, int api)
{
	R->level = (int) nondet_u32();
	const int mval = (int) nondet_u32();
	R->wbits = (int) nondet_u32();
	R->mem = (int) nondet_u32();
	R->strategy = (int) nondet_u32();
	R->n = nondet_u32();
	R->dlen = nondet_u32();
	const int t1 = (int) nondet_u32(), t2 = (int) nondet_u32(), t3 = (int) nondet_u32(), t4 = (int) nondet_u32();
	R->xlen = nondet_u32();
	R->nl = nondet_u32();
	R->cl = nondet_u32();
	const unsigned long mtime = nondet_u32();
	const unsigned char msel = nondet_u8();
	const unsigned char tsel = nondet_u8();
	const unsigned char dsel = nondet_u8();
	const unsigned char hsel = nondet_u8();
	const unsigned char text = nondet_u8();
	const unsigned char os = nondet_u8();
	const unsigned char hcrc = nondet_u8();
	gp_assume(R->n <= GP_DATA_MAX && R->dlen <= GP_DICT_MAX);
	gp_assume(R->xlen <= GP_HSTR_MAX && R->nl <= GP_HSTR_MAX && R->cl <= GP_HSTR_MAX);
	R->method = msel == 0 ? mval : Z_DEFLATED;
	R->data = malloc(R->n);
	R->dict = malloc(R->dlen);
	R->xf = malloc(R->xlen);
	R->nf_ = malloc(R->nl + 1);
	R->cf = malloc(R->cl + 1);
	R->comp = malloc(GP_COMP_MAX);
	if (R->data == NULL || R->dict == NULL || R->xf == NULL || R->nf_ == NULL || R->cf == NULL || R->comp == NULL)
		return 0;
	nondet_bytes(R->data, R->n);
	nondet_bytes(R->dict, R->dlen);
	nondet_bytes(R->xf, R->xlen);
	draw_nonzero_bytes(R->nf_, R->nl);
	R->nf_[R->nl] = 0;
	draw_nonzero_bytes(R->cf, R->cl);
	R->cf[R->cl] = 0;
	R->clen = 0;
	R->ended = 0;
	R->api_ok = 1;
	R->dict_set = 0;
	R->head_set = 0;
	R->nf = R->n;
	stream_defaults(s);
	R->init = deflateInit2(s, R->level, R->method, R->wbits, R->mem, R->strategy);
	if (api) {
		gp_assert(R->init == Z_OK || R->init == Z_STREAM_ERROR || R->init == Z_MEM_ERROR);
		gp_assert((R->init == Z_STREAM_ERROR) == !deflate_params_ok(R->level, R->method, R->wbits, R->mem, R->strategy));
	}
	if (R->init != Z_OK)
		return 1;
	R->wrap = R->wbits < 0 ? 0 : R->wbits > 15 ? 2 : 1;
	R->wb = R->wbits < 0 ? -R->wbits : R->wbits > 15 ? R->wbits - 16 : R->wbits;
	int r;
	if (tsel == 0) {
		r = deflateTune(s, t1, t2, t3, t4);
		if (api)
			gp_assert(r == Z_OK);
	}
	if (dsel == 0) {
		r = deflateSetDictionary(s, R->dict, R->dlen);
		if (api)
			gp_assert((r == Z_STREAM_ERROR) == (R->wrap == 2) && (r == Z_OK || r == Z_STREAM_ERROR));
		R->dict_set = r == Z_OK && R->dlen > 0;      // an empty dictionary is no dictionary (no FDICT)
	}
	if (hsel == 0) {
		R->h.text = text & 1;
		R->h.time = mtime;
		R->h.xflags = 0;
		R->h.os = os;
		R->h.extra = R->xf;
		R->h.extra_len = R->xlen;
		R->h.extra_max = 0;
		R->h.name = R->nf_;
		R->h.name_max = 0;
		R->h.comment = R->cf;
		R->h.comm_max = 0;
		R->h.hcrc = hcrc & 1;
		R->h.done = 0;
		r = deflateSetHeader(s, &R->h);
		if (api)
			gp_assert((r == Z_OK) == (R->wrap == 2) && (r == Z_OK || r == Z_STREAM_ERROR));
		R->head_set = r == Z_OK;
	}
	unsigned pos = 0, lim = 0;
	int finishing = 0;
	for (;;) {
		const unsigned nlim = nondet_u32();
		const unsigned aout = nondet_u32();
		const int fsel = (int) nondet_u32();
		const int plev = (int) nondet_u32();
		const int pstrat = (int) nondet_u32();
		const unsigned char psel = nondet_u8();
		gp_assume(aout <= GP_DOUT_MAX && aout <= GP_COMP_MAX - R->clen);
		int flush = fsel;
		if (finishing) {
			flush = Z_FINISH;
			lim = R->nf;
		} else {
			gp_assume(pos <= nlim && nlim <= R->n);
			gp_assume(flush >= Z_NO_FLUSH && flush <= Z_BLOCK);
			lim = nlim;
			if (flush == Z_FINISH) {
				finishing = 1;
				R->nf = lim;
			}
		}
		const unsigned ain = lim - pos;
		unsigned char *ib = exact_copy(R->data + pos, ain);
		unsigned char *osnap;
		unsigned char *ob = exact_space(aout, &osnap);
		if (ib == NULL || ob == NULL)
			return 0;
		s->next_in = ib;
		s->avail_in = ain;
		s->next_out = ob;
		s->avail_out = aout;
		const unsigned long tin = s->total_in, tout = s->total_out;
		const int params = !finishing && psel == 0;
		if (params)
			r = deflateParams(s, plev, pstrat);
		else
			r = deflate(s, flush);
		const unsigned used = ain - s->avail_in;
		const unsigned made = aout - s->avail_out;
		if (api) {
			gp_assert(s->avail_in <= ain && s->avail_out <= aout);
			gp_assert(s->next_in == ib + used && s->next_out == ob + made);
			gp_assert(s->total_in == tin + used && s->total_out == tout + made);
			gp_assert(bytes_same(ib, R->data + pos, ain));
			gp_assert(bytes_same(ob + made, osnap + made, aout - made));
			if (params) {
				const int pok = plev >= -1 && plev <= 9 && pstrat >= 0 && pstrat <= Z_FIXED;
				gp_assert(r == Z_OK || r == Z_BUF_ERROR || r == Z_STREAM_ERROR);
				gp_assert((r == Z_STREAM_ERROR) == !pok);
			} else {
				gp_assert(r == Z_OK || r == Z_STREAM_END || r == Z_BUF_ERROR);
				if (r == Z_STREAM_END)
					gp_assert(flush == Z_FINISH && pos + used == R->nf && s->avail_in == 0);
				if (r == Z_BUF_ERROR)
					gp_assert(used == 0 && made == 0);
			}
		}
		bytes_copy(R->comp + R->clen, ob, made);
		R->clen += made;
		pos += used;
		free(ib);
		free(ob);
		free(osnap);
		if (!params && r == Z_STREAM_END)
			break;
	}
	R->ended = 1;
	return 1;
}

#endif
