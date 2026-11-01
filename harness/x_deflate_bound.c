// Law deflate_bound: deflateBound is an upper bound on the compressed size (zlib.h: "If that first deflate() call is
// provided the sourceLen input bytes, an output buffer allocated to the size returned by deflateBound(), and the
// flush value Z_FINISH, then deflate() is guaranteed to return Z_STREAM_END").  deflateInit2 with ANY parameters it
// accepts (level -1..9, windowBits 9..15, 8 for zlib, -9..-15, 25..31, memLevel 1..9, strategy 0..4), optionally a
// preset dictionary of ANY dlen <= 2^15 bytes and a gzip header with ANY text flag, time, OS, header-CRC flag, extra
// field of ANY xlen <= 2^12 bytes, name and comment of ANY length <= 2^12 (non-zero bytes); then deflateBound(strm, n)
// for ANY data of n <= 2^20 bytes; then ONE deflate(Z_FINISH) call offered all n bytes and an output buffer of
// exactly that bound.  Properties:
//  - deflate returns Z_STREAM_END, having consumed all n bytes and produced at most the bound;
//  - compressBound(n) >= n, and deflateBound of a stream with the default parameters (level 6 or -1, windowBits 15,
//    memLevel 8, no dictionary) is at most compressBound(n).
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
	int dict_set = 0;
	if (dsel == 0 && wbits <= 15) {
		gp_assert(deflateSetDictionary(&s, dict, dlen) == Z_OK);
		dict_set = 1;
	}
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
	gp_assert(compressBound(n) >= n);
	if (!dict_set && (level == 6 || level == -1) && wbits == 15 && mem == 8)
		gp_assert(bound <= compressBound(n));
	unsigned char *ob = malloc(bound);
	if (ob == NULL)
		return 0;
	s.next_in = data;
	s.avail_in = n;
	s.next_out = ob;
	s.avail_out = (uInt) bound;
	gp_assert(bound <= 0xffffffff);
	r = deflate(&s, Z_FINISH);
	gp_assert(r == Z_STREAM_END);
	gp_assert(s.avail_in == 0);
	gp_assert(s.total_out <= bound);
	deflateEnd(&s);
	return 0;
}
