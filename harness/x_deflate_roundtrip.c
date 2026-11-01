// Law deflate_roundtrip: inflate gives back exactly what deflate compressed, for every parameter and call sequence of
// deflate.  The compression run of harness/deflate_common.h: deflateInit2 with ANY level, method, windowBits,
// memLevel, strategy (any ints); optionally deflateTune with ANY four ints, a preset dictionary of ANY dlen <= 2^15
// bytes, a gzip header with ANY fields; ANY data of n <= 2^20 bytes, compressed by ANY sequence of deflate() calls
// with ANY flush values (Z_NO_FLUSH .. Z_BLOCK) and deflateParams calls with ANY level and strategy, ANY split of the
// data and of the output space (at most 2^20 bytes per call, objects of exactly avail_in and avail_out bytes); the
// first Z_FINISH ends the data (data[0..nf)).  When deflateInit2 accepted the parameters and the run reached
// Z_STREAM_END, the output is inflated in one call (inflateInit2 with the matching windowBits: -w for raw, 0 for
// zlib, 32 for gzip; the dictionary set when inflate asks for it (zlib, Z_NEED_DICT with strm->adler = the
// dictionary's Adler-32) or before (raw); inflateGetHeader with buffers of exactly the header fields' sizes), its
// input exactly the compressed bytes, its output space exactly nf bytes, flush Z_FINISH.  Properties:
//  - inflate returns Z_STREAM_END, having consumed all the compressed bytes and produced exactly nf bytes, which are
//    data[0..nf);
//  - with a gzip header: inflate reports it complete (done = 1) with the text flag, time, OS, header-CRC flag, extra
//    field, name and comment that were given to deflateSetHeader;
//  - deflateEnd returns Z_OK.
// (Allocation failures, Z_MEM_ERROR, end the run.)  Bounds: n <= 2^20, dlen <= 2^15, header fields <= 2^12 bytes,
// at most 2^22 bytes of compressed output in total.
#include "deflate_common.h"

int main(void)
{
	struct drun R;
	z_stream s;
	if (!deflate_run(&R, &s, 0) || R.init != Z_OK)
		return 0;
	gp_assert(deflateEnd(&s) == Z_OK);
	z_stream t;
	stream_defaults(&t);
	const int iw = R.wrap == 0 ? -R.wb : R.wrap == 1 ? 0 : 32;
	int r = inflateInit2(&t, iw);
	if (r != Z_OK)
		return 0;
	gz_header ih;
	if (R.head_set) {
		ih.extra = malloc(R.xlen);
		ih.extra_max = R.xlen;
		ih.name = malloc(R.nl + 1);
		ih.name_max = R.nl + 1;
		ih.comment = malloc(R.cl + 1);
		ih.comm_max = R.cl + 1;
		if (ih.extra == NULL || ih.name == NULL || ih.comment == NULL)
			return 0;
		gp_assert(inflateGetHeader(&t, &ih) == Z_OK);
	}
	if (R.wrap == 0 && R.dict_set) {
		r = inflateSetDictionary(&t, R.dict, R.dlen);
		if (r == Z_MEM_ERROR)
			return 0;
		gp_assert(r == Z_OK);
	}
	unsigned char *ib = exact_copy(R.comp, (unsigned) R.clen);
	unsigned char *ob = malloc(R.nf);
	if (ib == NULL || ob == NULL)
		return 0;
	t.next_in = ib;
	t.avail_in = (unsigned) R.clen;
	t.next_out = ob;
	t.avail_out = R.nf;
	r = inflate(&t, Z_FINISH);
	if (R.wrap == 1 && R.dict_set) {
		gp_assert(r == Z_NEED_DICT);
		gp_assert(t.adler == ref_adler32(1, R.dict, R.dlen));
		r = inflateSetDictionary(&t, R.dict, R.dlen);
		if (r == Z_MEM_ERROR)
			return 0;
		gp_assert(r == Z_OK);
		r = inflate(&t, Z_FINISH);
	}
	if (r == Z_MEM_ERROR)
		return 0;
	gp_assert(r == Z_STREAM_END);
	gp_assert(t.avail_in == 0 && t.avail_out == 0);
	gp_assert(bytes_same(ob, R.data, R.nf));
	if (R.head_set) {
		gp_assert(ih.done == 1);
		gp_assert(ih.text == R.h.text && ih.time == R.h.time && ih.os == R.h.os && ih.hcrc == R.h.hcrc);
		gp_assert(ih.extra_len == R.xlen && bytes_same(ih.extra, R.xf, R.xlen));
		gp_assert(bytes_same(ih.name, R.nf_, R.nl + 1));
		gp_assert(bytes_same(ih.comment, R.cf, R.cl + 1));
	}
	inflateEnd(&t);
	return 0;
}
