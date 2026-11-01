// Law deflate_api: deflate's documented interface, for every parameter and call sequence.  The compression run of
// harness/deflate_common.h (ANY parameters, tuning, dictionary, gzip header, data of n <= 2^20 bytes, ANY sequence of
// deflate() and deflateParams calls with ANY split of the data and of the output space, each call's input and output
// space objects of exactly avail_in and avail_out bytes).  Properties:
//  - deflateInit2 returns Z_OK, Z_MEM_ERROR, or Z_STREAM_ERROR exactly for the parameters zlib.h rejects (level not
//    in -1..9, method not Z_DEFLATED, windowBits not in 8..15, -8..-15 or 24..31 with 8 only for zlib, memLevel not
//    in 1..9, strategy not in 0..4); deflateTune returns Z_OK; deflateSetDictionary returns Z_STREAM_ERROR exactly
//    for a gzip stream, else Z_OK; deflateSetHeader returns Z_OK exactly for a gzip stream;
//  - no undefined behaviour: every call reads only its input and writes only its output space;
//  - after every call: avail_in, avail_out, next_in, next_out, total_in and total_out consistent with the bytes
//    consumed and produced; the input unchanged; the output space beyond the bytes produced unchanged;
//  - deflate() returns Z_OK, Z_STREAM_END or Z_BUF_ERROR; Z_BUF_ERROR only without progress; Z_STREAM_END only for
//    flush Z_FINISH with all the data consumed; deflateParams returns Z_OK or Z_BUF_ERROR, or Z_STREAM_ERROR exactly
//    for a level not in -1..9 or a strategy not in 0..4;
//  - at Z_STREAM_END: strm->adler is the Adler-32 (zlib) or CRC-32 (gzip) of the data, by the reference definitions,
//    and the output ends with the trailer: the big-endian Adler-32 (zlib), or the little-endian CRC-32 and length
//    mod 2^32 (gzip); a zlib output starts with a valid zlib header (RFC 1950) whose FDICT flag is set exactly when
//    a dictionary was set, followed by the dictionary's Adler-32; a gzip output starts with 1f 8b 08;
//  - afterwards deflate(Z_FINISH) returns Z_STREAM_END without progress, deflate with another flush value or an
//    invalid one Z_STREAM_ERROR; deflateEnd returns Z_OK; then deflate, deflateEnd, deflateReset, deflateParams,
//    deflateSetDictionary and deflatePrime return Z_STREAM_ERROR.
// Bounds: n <= 2^20, dlen <= 2^15, header fields <= 2^12 bytes, at most 2^22 bytes of compressed output in total.
#include "deflate_common.h"

int main(void)
{
	struct drun R;
	z_stream s;
	if (!deflate_run(&R, &s, 1) || R.init != Z_OK)
		return 0;
	const unsigned long c = R.clen;
	const unsigned char *o = R.comp;
	if (R.wrap == 1) {
		const unsigned long a = ref_adler32(1, R.data, R.nf);
		gp_assert(s.adler == a);
		gp_assert(c >= 6 + (R.dict_set ? 4 : 0));
		gp_assert((o[0] & 0x0f) == 8 && (o[0] >> 4) <= 7 && (((unsigned) o[0] << 8) | o[1]) % 31 == 0);
		gp_assert(((o[1] & 0x20) != 0) == R.dict_set);
		if (R.dict_set)
			gp_assert(be32(o + 2) == ref_adler32(1, R.dict, R.dlen));
		gp_assert(be32(o + c - 4) == a);
	} else if (R.wrap == 2) {
		const unsigned long k = ref_crc32(0, R.data, R.nf);
		gp_assert(s.adler == k);
		gp_assert(c >= 18);
		gp_assert(o[0] == 0x1f && o[1] == 0x8b && o[2] == 8);
		gp_assert(le32(o + c - 8) == k && le32(o + c - 4) == (R.nf & 0xffffffff));
	}
	unsigned char b[1];
	const int bad = (int) nondet_u32();
	b[0] = 0;
	s.next_in = b;
	s.avail_in = 0;
	s.next_out = b;
	s.avail_out = 1;
	gp_assert(deflate(&s, Z_FINISH) == Z_STREAM_END);
	gp_assert(s.avail_out == 1);
	gp_assert(deflate(&s, Z_SYNC_FLUSH) == Z_STREAM_ERROR);
	if (bad < 0 || bad > Z_BLOCK)
		gp_assert(deflate(&s, bad) == Z_STREAM_ERROR);
	gp_assert(deflateEnd(&s) == Z_OK);
	gp_assert(deflate(&s, Z_FINISH) == Z_STREAM_ERROR);
	gp_assert(deflateEnd(&s) == Z_STREAM_ERROR);
	gp_assert(deflateReset(&s) == Z_STREAM_ERROR);
	gp_assert(deflateParams(&s, 1, 0) == Z_STREAM_ERROR);
	gp_assert(deflateSetDictionary(&s, b, 1) == Z_STREAM_ERROR);
	gp_assert(deflatePrime(&s, 1, 1) == Z_STREAM_ERROR);
	return 0;
}
