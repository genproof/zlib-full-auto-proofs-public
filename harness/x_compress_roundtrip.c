// Law compress_roundtrip: the one-call utility functions.  For ANY data of n <= 2^20 bytes and ANY level (any int):
//  - compress2(dest, &destLen, data, n, level) with destLen = compressBound(n) and dest an object of exactly that many
//    bytes returns Z_STREAM_ERROR exactly for a level not in -1..9, else Z_OK (or Z_MEM_ERROR), with destLen
//    at most compressBound(n); compress() (level -1) the same;
//  - uncompress(out, &outLen, dest, destLen) with outLen = n and out an object of exactly n bytes (any contents)
//    returns Z_OK with outLen = n and out = data; uncompress2 does too and sets its source length to destLen;
//  - when n > 0: uncompress with exactly n - 1 bytes of output space returns Z_BUF_ERROR, having written at most
//    n - 1 bytes; with only the first k < destLen compressed bytes (ANY k) uncompress returns Z_DATA_ERROR or
//    Z_BUF_ERROR (an incomplete stream is never accepted).
// (Allocation failures, Z_MEM_ERROR, end the run.)  Bounds: n <= 2^20.
#include "zlib_common.h"

#define GP_N_MAX (1u << 20)

int main(void)
{
	const unsigned n = nondet_u32();
	const int level = (int) nondet_u32();
	const unsigned k = nondet_u32();
	const unsigned char plain = nondet_u8();
	gp_assume(n <= GP_N_MAX);
	unsigned char *data = malloc(n);
	if (data == NULL)
		return 0;
	nondet_bytes(data, n);
	const uLong cb = compressBound(n);
	unsigned char *dest = malloc(cb);
	if (dest == NULL)
		return 0;
	uLongf dlen = cb;
	int r;
	if (plain == 0)
		r = compress(dest, &dlen, data, n);
	else
		r = compress2(dest, &dlen, data, n, level);
	const int lev_ok = plain == 0 || (level >= -1 && level <= 9);
	if (r == Z_MEM_ERROR)
		return 0;
	gp_assert((r == Z_STREAM_ERROR) == !lev_ok);
	if (!lev_ok)
		return 0;
	gp_assert(r == Z_OK);
	gp_assert(dlen <= cb);
	unsigned char *out = malloc(n);
	if (out == NULL)
		return 0;
	nondet_bytes(out, n);
	uLongf olen = n;
	r = uncompress(out, &olen, dest, dlen);
	if (r == Z_MEM_ERROR)
		return 0;
	gp_assert(r == Z_OK && olen == n && bytes_same(out, data, n));
	nondet_bytes(out, n);
	olen = n;
	uLong slen = dlen;
	r = uncompress2(out, &olen, dest, &slen);
	if (r == Z_MEM_ERROR)
		return 0;
	gp_assert(r == Z_OK && olen == n && slen == dlen && bytes_same(out, data, n));
	if (n > 0) {
		unsigned char *small = malloc(n - 1);
		if (small == NULL)
			return 0;
		olen = n - 1;
		r = uncompress(small, &olen, dest, dlen);
		if (r == Z_MEM_ERROR)
			return 0;
		gp_assert(r == Z_BUF_ERROR && olen <= n - 1);
	}
	gp_assume(k < dlen);
	olen = n;
	r = uncompress(out, &olen, dest, k);
	if (r == Z_MEM_ERROR)
		return 0;
	gp_assert(r == Z_DATA_ERROR || r == Z_BUF_ERROR);
	return 0;
}
