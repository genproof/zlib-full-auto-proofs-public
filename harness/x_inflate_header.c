// Law inflate_header: inflateGetHeader and the gzip header (RFC 1952 2.3).  inflateInit2 with ANY windowBits, then
// inflateGetHeader with a gz_header whose extra, name and comment buffers are each Z_NULL or an object of exactly
// extra_max, name_max, comm_max bytes, ANY maxima (<= 2^16), holding anything.  The input is a gzip member built
// here from ANY header fields: ANY FLG byte (FTEXT, FHCRC, FEXTRA, FNAME, FCOMMENT and the reserved bits), ANY MTIME,
// XFL, OS, an extra field of ANY XLEN <= 65535 bytes of ANY contents, a file name and a comment of ANY length
// <= 2^16 of ANY non-zero bytes (each ended by a zero byte), the header CRC (the low 16 bits of the CRC-32 of the
// header before it) or ANY wrong value; then an empty final stored block and the gzip trailer of the empty data.
// It is inflated by ANY number of calls with ANY flush value, ANY split of the input and ANY output space (each call:
// objects of exactly avail_in and avail_out bytes).  Properties:
//  - inflateGetHeader returns Z_STREAM_ERROR exactly when windowBits allows no gzip wrapper (< 16), else Z_OK;
//  - no undefined behaviour: in particular inflate writes the header buffers only within their maxima (each buffer is
//    an object of exactly its maximum; no slack);
//  - a header with a reserved flag bit set, or a wrong header CRC (FHCRC), is never accepted: no Z_STREAM_END, and
//    on Z_DATA_ERROR for a reserved bit done is still 0; a valid member never gives Z_DATA_ERROR;
//  - once done is 1 (the header is complete): text, time, xflags, os and hcrc are the header's FTEXT, MTIME, XFL, OS
//    and FHCRC; with FEXTRA extra_len is XLEN and the extra buffer holds the first min(XLEN, extra_max) bytes of the
//    field, without it head->extra is Z_NULL; with FNAME the name buffer holds the first min(length + 1,
//    name_max) bytes of the name and its zero byte, without it head->name is Z_NULL; the same for the comment;
//    the rest of each buffer is unchanged;
//  - on Z_STREAM_END: done is 1, the whole member was consumed and nothing was produced.
// Bounds: XLEN <= 65535, name and comment <= 2^16 bytes, buffer maxima <= 2^16, at most 2^20 bytes of output space
// per call, any number of calls.
#include "zlib_common.h"

#define GP_STR_MAX (1u << 16)
#define GP_BUF_MAX (1u << 16)
#define GP_OUT_MAX (1u << 20)

// buf[0..n-1] := any non-zero bytes
static void draw_nonzero(unsigned char *buf, unsigned n)
{
	nondet_bytes(buf, n);
	for (unsigned i = 0; i < n; ++i)
		gp_assume(buf[i] != 0);
}

// a header buffer: Z_NULL (when nul == 0) or exactly max bytes with any contents, and a snapshot
static unsigned char *head_buf(unsigned max, unsigned char nul, unsigned char **snap)
{
	if (nul == 0) {
		*snap = Z_NULL;
		return Z_NULL;
	}
	return exact_space(max, snap);
}

// field f (the header's bytes, len of them) as a header buffer of maximum max should hold it; the rest unchanged
static int field_ok(const unsigned char *buf, const unsigned char *snap, unsigned max, const unsigned char *f,
		    unsigned len)
{
	unsigned k = len < max ? len : max;
	return bytes_same(buf, f, k) && bytes_same(buf + k, snap + k, max - k);
}

int main(void)
{
	const int wbits = (int) nondet_u32();
	const unsigned char flg = nondet_u8();
	const unsigned long mtime = nondet_u32();
	const unsigned char xfl = nondet_u8();
	const unsigned char os = nondet_u8();
	const unsigned xlen = nondet_u32();
	const unsigned nl = nondet_u32();
	const unsigned cl = nondet_u32();
	const unsigned delta = nondet_u32();
	const unsigned xmax = nondet_u32();
	const unsigned nmax = nondet_u32();
	const unsigned cmax = nondet_u32();
	const unsigned char xnul = nondet_u8();
	const unsigned char nnul = nondet_u8();
	const unsigned char cnul = nondet_u8();
	gp_assume(xlen <= 65535 && nl <= GP_STR_MAX && cl <= GP_STR_MAX);
	gp_assume(xmax <= GP_BUF_MAX && nmax <= GP_BUF_MAX && cmax <= GP_BUF_MAX);
	// the member: header, empty final stored block (01 00 00 ff ff), CRC-32 and ISIZE of the empty data (0, 0)
	const unsigned hlen = 10 + ((flg & 4) ? 2 + xlen : 0) + ((flg & 8) ? nl + 1 : 0) + ((flg & 16) ? cl + 1 : 0);
	const unsigned total = hlen + ((flg & 2) ? 2 : 0) + 5 + 8;
	unsigned char *src = malloc(total);
	unsigned char *xf = malloc(xlen);           // the fields, as the header buffers should hold them
	unsigned char *nf = malloc(nl + 1);
	unsigned char *cf = malloc(cl + 1);
	if (src == NULL || xf == NULL || nf == NULL || cf == NULL)
		return 0;
	nondet_bytes(xf, xlen);
	draw_nonzero(nf, nl);
	nf[nl] = 0;
	draw_nonzero(cf, cl);
	cf[cl] = 0;
	src[0] = 0x1f;
	src[1] = 0x8b;
	src[2] = 8;
	src[3] = flg;
	src[4] = (unsigned char) mtime;
	src[5] = (unsigned char) (mtime >> 8);
	src[6] = (unsigned char) (mtime >> 16);
	src[7] = (unsigned char) (mtime >> 24);
	src[8] = xfl;
	src[9] = os;
	unsigned k = 10;
	if (flg & 4) {
		src[k] = (unsigned char) xlen;
		src[k + 1] = (unsigned char) (xlen >> 8);
		bytes_copy(src + k + 2, xf, xlen);
		k += 2 + xlen;
	}
	if (flg & 8) {
		bytes_copy(src + k, nf, nl + 1);
		k += nl + 1;
	}
	if (flg & 16) {
		bytes_copy(src + k, cf, cl + 1);
		k += cl + 1;
	}
	const unsigned long hcrc = ref_crc32(0, src, hlen) & 0xffff;
	if (flg & 2) {
		const unsigned long stored = (hcrc ^ delta) & 0xffff;
		src[k] = (unsigned char) stored;
		src[k + 1] = (unsigned char) (stored >> 8);
		k += 2;
	}
	src[k] = 1;
	src[k + 1] = 0;
	src[k + 2] = 0;
	src[k + 3] = 0xff;
	src[k + 4] = 0xff;
	for (unsigned i = 0; i < 8; ++i)
		src[k + 5 + i] = 0;
	const int reserved = (flg & 0xe0) != 0;
	const int badcrc = (flg & 2) && (delta & 0xffff) != 0;

	z_stream s;
	stream_defaults(&s);
	int r = inflateInit2(&s, wbits);
	if (r != Z_OK)
		return 0;
	gz_header h;
	unsigned char *xs, *ns, *cs;
	h.extra = head_buf(xmax, xnul, &xs);
	h.name = head_buf(nmax, nnul, &ns);
	h.comment = head_buf(cmax, cnul, &cs);
	if ((xnul != 0 && h.extra == Z_NULL) || (nnul != 0 && h.name == Z_NULL) || (cnul != 0 && h.comment == Z_NULL))
		return 0;
	h.extra_max = xmax;
	h.name_max = nmax;
	h.comm_max = cmax;
	pick(h.text);
	pick(h.time);
	pick(h.xflags);
	pick(h.os);
	pick(h.extra_len);
	pick(h.hcrc);
	pick(h.done);
	r = inflateGetHeader(&s, &h);
	gp_assert((r == Z_STREAM_ERROR) == (wbits < 16));
	if (r != Z_OK) {
		gp_assert(r == Z_STREAM_ERROR);
		inflateEnd(&s);
		return 0;
	}
	gp_assert(h.done == 0);
	unsigned pos = 0;
	for (;;) {
		const unsigned nlim = nondet_u32();
		const unsigned aout = nondet_u32();
		const int flush = (int) nondet_u32();
		const unsigned char stop = nondet_u8();
		gp_assume(pos <= nlim && nlim <= total);
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
		gp_assert(r == Z_OK || r == Z_BUF_ERROR || r == Z_STREAM_END || r == Z_DATA_ERROR);
		pos += ain - s.avail_in;
		if (reserved || badcrc)
			gp_assert(r != Z_STREAM_END);
		else
			gp_assert(r != Z_DATA_ERROR);
		if (reserved && r == Z_DATA_ERROR)
			gp_assert(h.done == 0);
		if (h.done != 0) {
			gp_assert(h.done == 1);
			gp_assert(h.text == (flg & 1));
			gp_assert(h.time == mtime);
			gp_assert(h.xflags == xfl);
			gp_assert(h.os == os);
			gp_assert(h.hcrc == ((flg >> 1) & 1));
			if (flg & 4) {
				gp_assert(h.extra_len == xlen);
				if (xnul != 0)
					gp_assert(field_ok(h.extra, xs, xmax, xf, xlen));
			} else {
				gp_assert(h.extra == Z_NULL);
			}
			if (flg & 8) {
				if (nnul != 0)
					gp_assert(field_ok(h.name, ns, nmax, nf, nl + 1));
			} else {
				gp_assert(h.name == Z_NULL);
			}
			if (flg & 16) {
				if (cnul != 0)
					gp_assert(field_ok(h.comment, cs, cmax, cf, cl + 1));
			} else {
				gp_assert(h.comment == Z_NULL);
			}
		}
		if (r == Z_STREAM_END) {
			gp_assert(h.done == 1);
			gp_assert(pos == total);
			gp_assert(s.total_out == 0);
		}
		free(ib);
		free(ob);
		free(osnap);
		if (stop == 0)
			break;
	}
	inflateEnd(&s);
	return 0;
}
