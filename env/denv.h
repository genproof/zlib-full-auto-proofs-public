/* env/denv.h: the draws of harness/inflate_decode.c and harness/inflate_dict.c (untrusted: only steers testing).  Knobs:
 *   DV_U8_HEAD   the number of header u8 draws before the blocks (wrap and selectors; the first is the wrapper);
 *   DV_U32_HEAD  the number of u32 draws before the blocks (the first is the window bits; inflate_dict: the
 *                dictionary length second, whose value extends the back-reference range);
 *   DV_NO_GARBAGE  no garbage-length draw after the stream;
 *   DV_SMALL     shorter stored blocks and larger input steps (fewer calls: inflate_dict checks the whole window
 *                after every call).
 * It follows the
 * harness's encoder: the wrapper, then per block `more` and the block type (stored, fixed, dynamic), for a dynamic
 * block nlen, ndist and the byte arrays (code lengths: complete codes from random trees, the single-code and empty
 * distance codes sometimes; a complete code length code over all 19 symbols; run choices and run lengths), per
 * Huffman-coded symbol its kind (end of block, literal, back-reference) and its values, keeping back-references valid
 * (it tracks the data length) and literals coded; then the garbage length, then per inflate() call the input step,
 * the output space and the flush value. */
#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include "zlib.h"
extern uint64_t quickproof_rnd(void);

static unsigned dv_r(unsigned n) { return n ? (unsigned) (quickproof_rnd() % n) : 0; }

static int dv_phase;            /* 0 header u8s, 1 block start (more), 2 block type, 3 symbols, 4 after encoding */
static unsigned dv_u8k, dv_n, dv_wb, dv_last, dv_pending_len, dv_blocks;
static int dv_want_match;       /* the next two u32 are a back-reference's length and distance */
static int dv_after_kind_lit;   /* the next u8 is a literal */
static int dv_stored_len;       /* the next u32 is a stored block's length */
static int dv_dyn_hdr;          /* the next u32 are nlen (2), ndist (1) */
static int dv_dyn_bytes;        /* the next bytes draws are ll (4), cl (3), choice (2), runs (1) */
static unsigned dv_nlen, dv_ndist, dv_dyn;
static unsigned char dv_ll[316];
static unsigned dv_u32k, dv_callk, dv_dlen;
#ifndef DV_U8_HEAD
#define DV_U8_HEAD 3
#endif
#ifndef DV_U32_HEAD
#define DV_U32_HEAD 1
#endif

/* a complete code over `want` (>= 2) leaves of depth <= maxd: depths into d[], returns the number of leaves */
static unsigned dv_tree(unsigned *d, unsigned want, unsigned maxd)
{
	unsigned k = 2;
	d[0] = 1;
	d[1] = 1;
	while (k < want) {
		unsigned tries = 0, i;
		do {
			i = dv_r(k);
		} while (d[i] >= maxd && ++tries < 64);
		if (d[i] >= maxd)
			break;
		d[i]++;
		d[k++] = d[i];
	}
	return k;
}

/* lengths of n symbols: a complete code on random symbols (`must` always used if < n) */
static void dv_code(unsigned char *ll, unsigned n, unsigned maxd, unsigned must)
{
	unsigned d[320];
	memset(ll, 0, n);
	unsigned want = 2 + dv_r(dv_r(2) ? n - 1 : (n < 40 ? n - 1 : 40));
	if (want > n)
		want = n;
	unsigned k = dv_tree(d, want, maxd);
	unsigned placed = 0;
	if (must < n) {
		ll[must] = (unsigned char) d[0];
		placed = 1;
	}
	while (placed < k) {
		unsigned s = dv_r(n);
		if (ll[s] == 0) {
			ll[s] = (unsigned char) d[placed];
			placed++;
		}
	}
}

uint8_t nondet_u8(void)
{
	unsigned k = dv_u8k++;
	if (k == 0)
		return (uint8_t) dv_r(3);                        /* wrap */
	if (k < DV_U8_HEAD)
		return (uint8_t) (dv_r(4) ? 1 + dv_r(255) : quickproof_rnd());   /* selectors */
	if (dv_after_kind_lit) {
		dv_after_kind_lit = 0;
		dv_n++;
		if (dv_dyn) {
			for (unsigned t = 0; t < 64; ++t) {
				unsigned c = dv_r(256);
				if (dv_ll[c])
					return (uint8_t) c;
			}
			dv_n--;                                  /* probably not coded: not sent */
		}
		return (uint8_t) (dv_r(2) ? 'a' + dv_r(4) : quickproof_rnd());
	}
	if (dv_phase <= 1) {                                     /* more */
		dv_phase = 2;
		dv_blocks++;
		dv_last = dv_blocks > 8 || dv_r(4) == 0;
		return (uint8_t) (dv_last ? 0 : 1 + dv_r(255));
	}
	if (dv_phase == 2) {                                     /* block type */
		unsigned t = dv_r(5);
		t = t == 0 ? 0 : t < 3 ? 1 : 2;
		dv_dyn = t == 2;
		if (t == 0) {
			dv_stored_len = 1;
			dv_phase = dv_last ? 4 : 1;
		} else {
			dv_phase = 3;
			if (t == 2)
				dv_dyn_hdr = 2;
		}
		if (t == 1 && dv_r(2))
			t = 3;
		return (uint8_t) (t | (dv_r(64) << 2));
	}
	if (dv_phase == 3) {                                     /* kind */
		unsigned k2 = dv_r(40);
		if (k2 == 0) {
			dv_phase = dv_last ? 4 : 1;
			return 0;
		}
		if (k2 < 22 || dv_n + dv_dlen == 0) {
			dv_after_kind_lit = 1;
			return (uint8_t) (1 + dv_r(127));
		}
		dv_want_match = 2;
		return (uint8_t) (128 + dv_r(128));
	}
	return (uint8_t) quickproof_rnd();
}

uint32_t nondet_u32(void)
{
	unsigned k = dv_u32k++;
	if (k == 0) {
		dv_wb = 8 + dv_r(8);
		return dv_wb;                                    /* window bits */
	}
	if (k < DV_U32_HEAD) {
		dv_dlen = dv_r(4) ? dv_r(300) : dv_r(4) ? dv_r(40000) : 0;
		return dv_dlen;                                  /* dictionary length */
	}
	if (dv_dyn_hdr == 2) {
		dv_dyn_hdr = 1;
		dv_nlen = dv_r(4) ? 257 + dv_r(30) : 286;
		return dv_nlen;
	}
	if (dv_dyn_hdr == 1) {
		dv_dyn_hdr = 0;
		dv_ndist = dv_r(4) ? 1 + dv_r(30) : 30;
		dv_dyn_bytes = 4;
		return dv_ndist;
	}
	if (dv_want_match == 2) {
		dv_want_match = 1;
		dv_pending_len = dv_r(8) ? 3 + dv_r(30) : 3 + dv_r(256);
		return dv_pending_len;
	}
	if (dv_want_match == 1) {
		dv_want_match = 0;
		unsigned maxd = dv_n + dv_dlen < (1u << dv_wb) ? dv_n + dv_dlen : (1u << dv_wb);
		unsigned d = dv_r(2) ? 1 + dv_r(maxd < 8 ? maxd : 8) : 1 + dv_r(maxd);
		if (dv_r(32) == 0)
			d = maxd + 1;                            /* invalid: not sent */
		else
			dv_n += dv_pending_len;                  /* (dynamic: maybe not coded; then a guess) */
		return d;
	}
	if (dv_stored_len) {
		dv_stored_len = 0;
#if defined(__COMPCERT__) || defined(DV_SMALL)
		unsigned len = dv_r(4) ? dv_r(100) : dv_r(600);
#else
		unsigned len = dv_r(4) ? dv_r(300) : dv_r(4) ? dv_r(5000) : 65535 - dv_r(3);
#endif
		dv_n += len;
		return len;
	}
#ifndef DV_NO_GARBAGE
	if (dv_phase == 4) {
		dv_phase = 5;
		return dv_r(17);                                 /* garbage */
	}
#endif
	/* per inflate() call: step, aout, flush */
	switch (dv_callk++ % 3) {
	case 0: {
		unsigned m = dv_r(8);
#ifdef DV_SMALL
		return m < 1 ? dv_r(4) : m < 4 ? dv_r(256) : m < 7 ? dv_r(4000) : 1u << 30;
#else
		return m < 2 ? dv_r(4) : m < 5 ? dv_r(64) : m < 7 ? dv_r(2000) : 1u << 30;
#endif
	}
	case 1: {
		unsigned m = dv_r(8);
#ifdef __COMPCERT__
		return m < 1 ? 0 : m < 4 ? 1 + dv_r(16) : 1 + dv_r(1000);
#else
		return m < 1 ? 0 : m < 4 ? 1 + dv_r(16) : m < 6 ? 1 + dv_r(1000) : 1 + dv_r(70000);
#endif
	}
	default: {
		static const int fl[] = {Z_NO_FLUSH, Z_NO_FLUSH, Z_SYNC_FLUSH, Z_FINISH, Z_BLOCK, Z_TREES};
		return (uint32_t) fl[dv_r(6)];
	}
	}
}

size_t nondet_size(void) { return (size_t) quickproof_rnd(); }

void nondet_bytes(uint8_t *buf, size_t n)
{
	if (dv_dyn_bytes == 4 && n == dv_nlen + dv_ndist) {      /* the code lengths */
		dv_dyn_bytes = 3;
		dv_code(dv_ll, dv_nlen, 15, 256);
		unsigned m = dv_r(8);
		if (m == 0) {
			memset(dv_ll + dv_nlen, 0, dv_ndist);            /* no distance code */
		} else if (m == 1 || dv_ndist == 1) {
			memset(dv_ll + dv_nlen, 0, dv_ndist);            /* a single distance code */
			dv_ll[dv_nlen + dv_r(dv_ndist)] = 1;
		} else {
			dv_code(dv_ll + dv_nlen, dv_ndist, 15, 1000);
		}
		memcpy(buf, dv_ll, n);
		return;
	}
	if (dv_dyn_bytes == 3 && n == 19) {                      /* the code length code: all 19 coded */
		static const unsigned char base[19] = {4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5};
		dv_dyn_bytes = 2;
		for (unsigned i = 0; i < 19; ++i)
			buf[i] = base[i];
		for (unsigned i = 18; i > 0; --i) {              /* shuffle */
			unsigned j = dv_r(i + 1);
			unsigned char t = buf[i];
			buf[i] = buf[j];
			buf[j] = t;
		}
		return;
	}
	if (dv_dyn_bytes == 2) {                                 /* run choices: mostly runs where possible */
		dv_dyn_bytes = 1;
		for (size_t i = 0; i < n; ++i)
			buf[i] = (uint8_t) (dv_r(3) ? 192 + dv_r(64) : dv_r(192));
		return;
	}
	if (dv_dyn_bytes == 1) {                                 /* run lengths */
		dv_dyn_bytes = 0;
		for (size_t i = 0; i < n; ++i) {
			unsigned m = dv_r(3);
			buf[i] = (uint8_t) (m == 0 ? 3 + dv_r(4) : m == 1 ? 3 + dv_r(8) : 11 + dv_r(128));
		}
		return;
	}
	for (size_t i = 0; i < n; ++i)
		buf[i] = (uint8_t) (dv_r(2) ? 'a' + dv_r(4) : quickproof_rnd());
}
