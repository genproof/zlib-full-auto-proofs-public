// Law deflate_bound_split: deflateBound bounds the compressed size also when the data is given in pieces (zlib.h:
// "it is possible for the compressed size to be larger than the value returned by deflateBound() if flush options
// other than Z_FINISH or Z_NO_FLUSH are used").  deflateInit2 with ANY parameters it accepts; optionally a preset
// dictionary of ANY dlen <= 2^15 bytes or a gzip header with ANY fields (as deflate_bound); b = deflateBound(strm, n)
// for ANY data of n <= 2^20 bytes; then deflate() calls with Z_NO_FLUSH offered ANY split of the data, then, from a
// call of the caller's choice on, Z_FINISH offered the rest, until Z_STREAM_END, each call with ANY output space
// <= 2^20 bytes (objects of exactly avail_in and avail_out bytes).  Properties:
//  - every call returns Z_OK, Z_BUF_ERROR or Z_STREAM_END; the total output (total_out) never exceeds b.
// (Allocation failures, Z_MEM_ERROR, end the run.)  Bounds: n <= 2^20, dlen <= 2^15, header fields <= 2^12.
#include "deflate_common.h"

int main(void)
{
	const int level = (int) nondet_u32();
	const int wbits = (int) nondet_u32();
	const int mem = (int) nondet_u32();
	const int strategy = (int) nondet_u32();
	const unsigned n = nondet_u32();
	const unsigned dlen = nondet_u32();
	const unsigned xlen = nondet_u32();
	const unsigned nl = nondet_u32();
	const unsigned cl = nondet_u32();
	const unsigned long mtime = nondet_u32();
	const unsigned char dsel = nondet_u8();
	const unsigned char hsel = nondet_u8();
	const unsigned char text = nondet_u8();
	const unsigned char os = nondet_u8();
	const unsigned char hcrc = nondet_u8();
	const unsigned char xsel = nondet_u8();
	const unsigned char nsel = nondet_u8();
	const unsigned char csel = nondet_u8();
	gp_assume(deflate_params_ok(level, Z_DEFLATED, wbits, mem, strategy));
	gp_assume(n <= GP_DATA_MAX && dlen <= GP_DICT_MAX);
	gp_assume(xlen <= GP_HSTR_MAX && nl <= GP_HSTR_MAX && cl <= GP_HSTR_MAX);
	unsigned char *data = malloc(n);
	unsigned char *dict = malloc(dlen);
	unsigned char *xf = malloc(xlen);
	unsigned char *nf = malloc(nl + 1);
	unsigned char *cf = malloc(cl + 1);
	if (data == NULL || dict == NULL || xf == NULL || nf == NULL || cf == NULL)
		return 0;
	nondet_bytes(data, n);
	nondet_bytes(dict, dlen);
	nondet_bytes(xf, xlen);
	draw_nonzero_bytes(nf, nl);
	nf[nl] = 0;
	draw_nonzero_bytes(cf, cl);
	cf[cl] = 0;
	z_stream s;
	stream_defaults(&s);
	int r = deflateInit2(&s, level, Z_DEFLATED, wbits, mem, strategy);
	if (r != Z_OK)
		return 0;
	if (dsel == 0 && wbits <= 15)
		gp_assert(deflateSetDictionary(&s, dict, dlen) == Z_OK);
	gz_header h;
	if (hsel == 0 && wbits > 15) {
		h.text = text & 1;
		h.time = mtime;
		h.xflags = 0;
		h.os = os;
		h.extra = xsel == 0 ? Z_NULL : xf;
		h.extra_len = xlen;
		h.extra_max = 0;
		h.name = nsel == 0 ? Z_NULL : nf;
		h.name_max = 0;
		h.comment = csel == 0 ? Z_NULL : cf;
		h.comm_max = 0;
		h.hcrc = hcrc & 1;
		h.done = 0;
		gp_assert(deflateSetHeader(&s, &h) == Z_OK);
	}
	const uLong bound = deflateBound(&s, n);
	unsigned pos = 0;
	int finishing = 0;
	for (;;) {
		const unsigned nlim = nondet_u32();
		const unsigned aout = nondet_u32();
		const unsigned char fsel = nondet_u8();
		gp_assume(aout <= GP_DOUT_MAX);
		unsigned lim = n;
		if (!finishing) {
			gp_assume(pos <= nlim && nlim <= n);
			lim = nlim;
			if (fsel == 0) {
				finishing = 1;
				lim = n;
			}
		}
		const unsigned ain = lim - pos;
		unsigned char *ib = exact_copy(data + pos, ain);
		unsigned char *osnap;
		unsigned char *ob = exact_space(aout, &osnap);
		if (ib == NULL || ob == NULL)
			return 0;
		s.next_in = ib;
		s.avail_in = ain;
		s.next_out = ob;
		s.avail_out = aout;
		r = deflate(&s, finishing ? Z_FINISH : Z_NO_FLUSH);
		gp_assert(r == Z_OK || r == Z_BUF_ERROR || r == Z_STREAM_END);
		gp_assert(s.total_out <= bound);
		pos += ain - s.avail_in;
		free(ib);
		free(ob);
		free(osnap);
		if (r == Z_STREAM_END)
			break;
	}
	deflateEnd(&s);
	return 0;
}
