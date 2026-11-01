/* env/zenv.h: value distributions for native and interpreter runs of the zlib laws (untrusted: they only steer
 * testing; the theorems quantify over every value).  Each env/<law>.c sets the roles of its draws and includes this
 * file, which defines the four nondet_* of quickproof.h on top of quickproof_rnd().  Plain C, so CompCert's interpreter
 * runs it too (tools/interp.sh GP_ENV).
 *
 * A law's draws are described by role, by position:
 *   ENV_U32_INIT  roles of the first nondet_u32 draws (e.g. windowBits, the input length), then
 *   ENV_U32_CYCLE roles of the per-call nondet_u32 draws, repeated;
 *   ENV_U8_CYCLE  roles of the per-call nondet_u8 draws, repeated (after ENV_U8_INIT);
 * the first nondet_bytes draw of the input length (role R_N) is the input; later ones of the dictionary's length
 * are often the dictionary.  For an input the environment makes, with zlib's own deflate (the library under test,
 * linked with the law), a zlib, gzip or raw stream of random data matching the windowBits it drew, sometimes with a
 * preset dictionary or a gzip header, or random bytes, or a valid header followed by random bytes; then mutates it
 * or not (bit flips, truncation, garbage appended).
 */
#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include "zlib.h"
extern uint64_t quickproof_rnd(void);
#define ENV_RND quickproof_rnd

enum { R_ANY, R_WBITS, R_N, R_LIM, R_AOUT, R_FLUSH, R_ARG, R_OP, R_NULL, R_STOP, R_SMALL, R_LEVEL, R_MEMLEVEL,
       R_STRATEGY, R_DEFLATE_FLUSH, R_DEFLATE_WBITS, R_DLEN, R_BIT, R_CHUNK,
       /* inflate_header: the gzip header fields; the input length is computed from them (env_header_len) */
       R_GZWBITS, R_FLG, R_XLEN, R_STRLEN, R_DELTA, R_BUFMAX,
       /* deflate laws: the data length (the input of R_LIM), deflateTune's arguments, selectors (0: 1/4, 1/16) */
       R_DN, R_TUNE, R_SEL4, R_SEL16 };

#ifdef __COMPCERT__
#define ENV_DATA_MAX 400
#define ENV_DATA_BIG 1200
#else
#define ENV_DATA_MAX 3000
#define ENV_DATA_BIG 70000
#endif
#define ENV_STREAM_CAP (ENV_DATA_BIG + ENV_DATA_BIG / 8 + 4096)

static unsigned env_u32_k, env_u8_k, env_bytes_k;
static int env_wbits;
static unsigned env_n, env_lim, env_have_stream;
static unsigned char env_stream[ENV_STREAM_CAP];
static unsigned char env_data[ENV_DATA_BIG];
static unsigned env_data_n;
static unsigned char env_dict[300];
static unsigned env_dlen;

static unsigned env_r(unsigned n) { return n ? (unsigned) (ENV_RND() % n) : 0; }

static unsigned env_flg, env_xlen, env_strlen[2], env_nstr, env_header;

/* the length of the gzip member harness/inflate_header.c builds from the drawn fields */
static unsigned env_header_len(void)
{
	return 10 + ((env_flg & 4) ? 2 + env_xlen : 0) + ((env_flg & 8) ? env_strlen[0] + 1 : 0) +
	       ((env_flg & 16) ? env_strlen[1] + 1 : 0) + ((env_flg & 2) ? 2 : 0) + 5 + 8;
}

static void env_gen_data(unsigned char *d, unsigned n)
{
	unsigned mode = env_r(5), i = 0;
	while (i < n) {
		if (mode == 0) {
			d[i++] = (unsigned char) ENV_RND();
		} else if (mode == 1) {
			d[i++] = (unsigned char) ('a' + env_r(4));
		} else if (mode == 2 && i > 0 && env_r(3)) {
			unsigned dist = 1 + env_r(i < 300 ? i : 300), len = 3 + env_r(40);
			while (len-- && i < n) {
				d[i] = d[i - dist];
				i++;
			}
		} else if (mode == 3) {
			unsigned char c = (unsigned char) ENV_RND();
			unsigned len = 1 + env_r(300);
			while (len-- && i < n)
				d[i++] = c;
		} else {
			d[i++] = (unsigned char) (env_r(2) ? ENV_RND() : 'x');
		}
	}
}

static unsigned env_data_len(void)
{
	unsigned k = env_r(10);
	if (k < 2)
		return env_r(20);
	if (k < 8)
		return env_r(ENV_DATA_MAX);
	return env_r(ENV_DATA_BIG);
}

/* deflate env_data[0..n) into env_stream with deflate windowBits w: the length, 0 on failure */
static unsigned env_deflate(int w, unsigned n, int with_dict, int with_head)
{
	z_stream d;
	gz_header h;
	static unsigned char hx[40], hn[20], hc[20];
	static const int fl[] = {Z_NO_FLUSH, Z_NO_FLUSH, Z_NO_FLUSH, Z_PARTIAL_FLUSH, Z_SYNC_FLUSH, Z_FULL_FLUSH, Z_BLOCK};
	d.zalloc = Z_NULL;
	d.zfree = Z_NULL;
	d.opaque = Z_NULL;
	int level = (int) env_r(11) - 1;
#ifdef __COMPCERT__
	int mem = 1 + (int) env_r(3);
#else
	int mem = 1 + (int) env_r(9);
#endif
	if (deflateInit2(&d, level, Z_DEFLATED, w, mem, (int) env_r(5)) != Z_OK)
		return 0;
	if (with_head) {
		h.text = (int) env_r(2);
		h.time = (uLong) ENV_RND() & 0xffffffff;
		h.xflags = 0;
		h.os = (int) env_r(256);
		h.extra = Z_NULL;
		h.name = Z_NULL;
		h.comment = Z_NULL;
		h.extra_len = 0;
		if (env_r(2)) {
			h.extra_len = env_r(40);
			for (unsigned i = 0; i < h.extra_len; i++)
				hx[i] = (unsigned char) ENV_RND();
			h.extra = hx;
		}
		if (env_r(2)) {
			unsigned l = env_r(19);
			for (unsigned i = 0; i < l; i++)
				hn[i] = (unsigned char) (1 + env_r(255));
			hn[l] = 0;
			h.name = hn;
		}
		if (env_r(2)) {
			unsigned l = env_r(19);
			for (unsigned i = 0; i < l; i++)
				hc[i] = (unsigned char) (1 + env_r(255));
			hc[l] = 0;
			h.comment = hc;
		}
		h.hcrc = (int) env_r(2);
		deflateSetHeader(&d, &h);
	}
	if (with_dict) {
		env_dlen = 1 + env_r(sizeof env_dict);
		env_gen_data(env_dict, env_dlen);
		if (deflateSetDictionary(&d, env_dict, env_dlen) != Z_OK)
			env_dlen = 0;
	}
	d.next_out = env_stream;
	d.avail_out = sizeof env_stream;
	unsigned pos = 0;
	int ret = Z_OK;
	while (ret != Z_STREAM_END) {
		unsigned chunk = env_r(4) ? env_r(n - pos + 1) : n - pos;
		d.next_in = env_data + pos;
		d.avail_in = chunk;
		int f = pos + chunk == n && env_r(3) ? Z_FINISH : fl[env_r(7)];
		ret = deflate(&d, f);
		pos += chunk - d.avail_in;
		if (ret == Z_STREAM_ERROR || d.avail_out == 0) {
			deflateEnd(&d);
			return 0;
		}
		if (pos == n && f != Z_FINISH) {
			d.next_in = env_data + pos;
			d.avail_in = 0;
			ret = deflate(&d, Z_FINISH);
		}
	}
	unsigned len = (unsigned) (sizeof env_stream - d.avail_out);
	deflateEnd(&d);
	return len;
}

/* an inflate windowBits value: valid ones of each kind mostly, sometimes anything */
static int env_pick_wbits(void)
{
	unsigned k = env_r(20);
	int w = 8 + (int) env_r(8);
	if (k < 6)
		return w;                       /* zlib */
	if (k < 7)
		return 0;
	if (k < 11)
		return 16 + w;                  /* gzip */
	if (k < 12)
		return 16;
	if (k < 15)
		return 32 + w;                  /* zlib or gzip */
	if (k < 19)
		return -w;                      /* raw */
	return (int) (ENV_RND() % 100) - 50;
}

/* the input for windowBits w: a stream (mostly matching w), random bytes, or a header and random bytes; mutated */
static unsigned env_make_input(int w)
{
	unsigned k = env_r(16), len = 0;
	env_dlen = 0;
	if (k < 12) {
		int wb = w;
		if (wb < 0)
			wb = wb < -15 || wb > -9 ? -15 : wb;
		else if (wb == 0 || wb == 16 || wb == 32)
			wb = wb + 15;
		else if (wb >= 48 || (wb & 15) < 9)
			wb = (wb & ~15) + 9 + (int) env_r(7);
		if (wb >= 32)
			wb = env_r(2) ? wb - 16 : wb - 32;       /* auto-detect: gzip or zlib */
		if (wb >= 48 || wb < -15)
			wb = 15;
		env_data_n = env_data_len();
		env_gen_data(env_data, env_data_n);
		len = env_deflate(wb, env_data_n, wb >= 9 && wb <= 15 ? env_r(6) == 0 : wb < 0 ? env_r(8) == 0 : 0,
				  wb > 15 ? env_r(3) == 0 : 0);
	} else if (k < 14) {
		if (k == 12) {
			env_stream[0] = 0x78;
			env_stream[1] = 0x9c;
			len = 2;
		} else {
			static const unsigned char gz[10] = {0x1f, 0x8b, 8, 0, 0, 0, 0, 0, 0, 3};
			memcpy(env_stream, gz, 10);
			len = 10;
		}
		unsigned extra = env_r(400);
		for (unsigned i = 0; i < extra; i++)
			env_stream[len++] = (unsigned char) ENV_RND();
	} else {
		len = env_r(300);
		for (unsigned i = 0; i < len; i++)
			env_stream[i] = (unsigned char) ENV_RND();
	}
	unsigned m = env_r(8);
	if (m == 1 && len) {
		unsigned c = 1 + env_r(4);
		while (c--)
			env_stream[env_r(len)] ^= (unsigned char) (1u << env_r(8));
	} else if (m == 2 && len) {
		len = env_r(len);
	} else if (m == 3) {
		unsigned c = env_r(20);
		while (c-- && len < sizeof env_stream)
			env_stream[len++] = (unsigned char) ENV_RND();
	}
	env_have_stream = 1;
	return len;
}

static uint32_t env_value(int role)
{
	switch (role) {
	case R_WBITS:
		env_wbits = env_pick_wbits();
		return (uint32_t) env_wbits;
	case R_N:
		env_n = env_make_input(env_wbits);
		env_lim = 0;
		return env_n;
	case R_LIM: {
		unsigned k = env_r(16), lim = env_lim;
		if (env_header && !env_have_stream) {
			env_n = env_header_len();
			env_have_stream = 1;
		}
		if (k < 2)
			lim = env_lim;
		else if (k < 6)
			lim = env_lim + 1 + env_r(8);
		else if (k < 10)
			lim = env_lim + 1 + env_r(64);
		else if (k < 14)
			lim = env_n;
		else if (k < 15 || env_r(8))
			lim = env_lim + env_r(1000);
		else
			return (uint32_t) ENV_RND();
		if (lim > env_n)
			lim = env_n;
		env_lim = lim;
		return lim;
	}
	case R_AOUT: {
		unsigned k = env_r(16);
#ifdef __COMPCERT__
		if (k >= 14)
			k = env_r(9);           /* the interpreter: no output space of 2^20 */
#endif
		if (k < 1)
			return 0;
		if (k < 5)
			return 1 + env_r(16);
		if (k < 9)
			return 1 + env_r(300);
		if (k < 14)
			return 1 + env_r(ENV_DATA_BIG);
		if (k < 15 && env_dlen)
			return env_dlen;
		if (env_r(4))
			return 1 + env_r(ENV_DATA_BIG);
		return 1u << 20;
	}
	case R_FLUSH: {
		unsigned k = env_r(20);
		if (k < 8)
			return Z_NO_FLUSH;
		if (k < 10)
			return Z_SYNC_FLUSH;
		if (k < 14)
			return Z_FINISH;
		if (k < 16)
			return Z_BLOCK;
		if (k < 18)
			return Z_TREES;
		return (uint32_t) ((int) env_r(12) - 3);
	}
	case R_ARG: {
		unsigned k = env_r(4);
		if (k == 0)
			return (uint32_t) env_pick_wbits();
		if (k == 1)
			return (uint32_t) ((int) env_r(20) - 2);
		return (uint32_t) ENV_RND();
	}
	case R_SMALL:
		return env_r(40);
	case R_LEVEL:
		return env_r(16) == 0 ? (uint32_t) ENV_RND() : (uint32_t) ((int) env_r(11) - 1);
	case R_MEMLEVEL:
#ifdef __COMPCERT__
		return env_r(16) == 0 ? (uint32_t) ENV_RND() : 1 + env_r(3);
#else
		return env_r(16) == 0 ? (uint32_t) ENV_RND() : 1 + env_r(9);
#endif
	case R_STRATEGY:
		return env_r(16) == 0 ? (uint32_t) ENV_RND() : env_r(5);
	case R_DEFLATE_WBITS: {
		unsigned k = env_r(16);
		int w = 9 + (int) env_r(7);
		if (k < 6)
			return (uint32_t) w;
		if (k < 10)
			return (uint32_t) (16 + w);
		if (k < 14)
			return (uint32_t) -w;
		if (k < 15)
			return 8;
		return (uint32_t) ((int) env_r(80) - 40);
	}
	case R_DEFLATE_FLUSH: {
		static const int fl[] = {Z_NO_FLUSH, Z_NO_FLUSH, Z_NO_FLUSH, Z_PARTIAL_FLUSH, Z_SYNC_FLUSH, Z_FULL_FLUSH,
					 Z_BLOCK, Z_FINISH, Z_FINISH};
		return (uint32_t) fl[env_r(9)];
	}
	case R_DLEN:
		return env_r(4) == 0 ? 0 : 1 + env_r(300);
	case R_DN:
		env_n = env_data_len();
		env_lim = 0;
		env_have_stream = 0;
		return env_n;
	case R_TUNE: {
		unsigned k = env_r(8);
		if (k < 5)
			return env_r(300);
		if (k < 6)
			return env_r(5);
		return (uint32_t) ENV_RND();
	}
	case R_GZWBITS: {
		unsigned k = env_r(8);
		env_header = 1;
		if (k < 4)
			return (uint32_t) (16 + 8 + env_r(8));
		if (k < 7)
			return (uint32_t) (32 + 8 + env_r(8));
		return (uint32_t) env_pick_wbits();
	}
	case R_XLEN:
		env_xlen = env_r(4) == 0 ? 0 : env_r(8) ? env_r(40) : env_r(70000);
		return env_xlen;
	case R_STRLEN: {
		unsigned v = env_r(4) == 0 ? 0 : env_r(8) ? env_r(40) : env_r(70000);
		if (env_nstr < 2)
			env_strlen[env_nstr++] = v;
		return v;
	}
	case R_DELTA:
		return env_r(4) == 0 ? (uint32_t) ENV_RND() : 0;
	case R_BUFMAX:
		return env_r(4) == 0 ? 0 : env_r(8) ? env_r(48) : env_r(70000);
	case R_CHUNK: {
		unsigned k = env_r(8);
		if (k < 2)
			return env_r(8);
		if (k < 5)
			return env_r(300);
		return env_r(ENV_DATA_BIG);
	}
	default:
		break;
	}
	return (uint32_t) ENV_RND();
}

#ifndef ENV_U32_NINIT
#define ENV_U32_NINIT (sizeof init / sizeof init[0])
#endif
#ifndef ENV_U8_INIT
#define ENV_U8_INIT {R_ANY}
#define ENV_U8_NINIT 0
#endif
#ifndef ENV_U8_NINIT
#define ENV_U8_NINIT (sizeof init / sizeof init[0])
#endif
#ifndef ENV_STREAM_BYTES
#define ENV_STREAM_BYTES 0
#endif
#ifndef ENV_DATA_BYTES
#define ENV_DATA_BYTES (-1)
#endif

uint32_t nondet_u32(void)
{
	static const int init[] = ENV_U32_INIT;
	static const int cyc[] = ENV_U32_CYCLE;
	unsigned k = env_u32_k++;
	unsigned ni = ENV_U32_NINIT;
	if (k < ni)
		return env_value(init[k]);
	return env_value(cyc[(k - ni) % (sizeof cyc / sizeof cyc[0])]);
}

static uint8_t env_u8_role(int role)
{
	switch (role) {
	case R_OP:
		return env_r(8) ? (uint8_t) env_r(200) : (uint8_t) (200 + env_r(56));
	case R_NULL:
		return env_r(32) == 0 ? 0 : 1;
	case R_STOP:
#ifdef __COMPCERT__
		return env_r(6) == 0 ? 0 : 1;
#else
		return env_r(40) == 0 ? 0 : 1;
#endif
	case R_BIT:
		return (uint8_t) env_r(2);
	case R_SEL4:
		return (uint8_t) env_r(4);
	case R_SEL16:
		return (uint8_t) env_r(16);
	case R_FLG:
		env_flg = env_r(8) == 0 ? (unsigned) env_r(256) : (unsigned) env_r(32);
		return (uint8_t) env_flg;
	default:
		break;
	}
	return (uint8_t) ENV_RND();
}

uint8_t nondet_u8(void)
{
	static const int init[] = ENV_U8_INIT;
	static const int cyc[] = ENV_U8_CYCLE;
	unsigned k = env_u8_k++;
	unsigned ni = ENV_U8_NINIT;
	if (k < ni)
		return env_u8_role(init[k]);
	return env_u8_role(cyc[(k - ni) % (sizeof cyc / sizeof cyc[0])]);
}

size_t nondet_size(void)
{
	return (size_t) env_value(R_ANY);
}

void nondet_bytes(uint8_t *buf, size_t n)
{
	unsigned k = env_bytes_k++;
	if (env_have_stream && k == ENV_STREAM_BYTES && n == env_n) {
		memcpy(buf, env_stream, n);
		return;
	}
	if (env_dlen && n == env_dlen && env_r(2)) {
		memcpy(buf, env_dict, n);
		return;
	}
#ifdef ENV_ADLER_MASK
	if (k < 32 && ((ENV_ADLER_MASK >> k) & 1) && n == 8) {
		/* an unsigned long holding a valid Adler-32 checksum (halves below 65521), sometimes anything */
		uint64_t v = env_r(16) == 0 ? ENV_RND() : (uint64_t) env_r(65521) << 16 | env_r(65521);
		if (env_r(16) == 0)
			v = env_r(2) ? 1 : 0;
		memcpy(buf, &v, 8);
		return;
	}
#endif
#ifdef ENV_LEN_MASK
	if (k < 32 && ((ENV_LEN_MASK >> k) & 1) && n == 8) {
		/* a length (z_off_t): mostly small and non-negative, sometimes negative or huge */
		unsigned m = env_r(16);
		int64_t v = m < 12 ? (int64_t) env_r(m < 8 ? 64 : 5000) : m < 14 ? -(int64_t) env_r(1000) - 1 :
			    (int64_t) (ENV_RND() >> 1);
		memcpy(buf, &v, 8);
		return;
	}
#endif
#ifdef ENV_NONZERO_FIRST
	if (k >= ENV_NONZERO_FIRST && k <= ENV_NONZERO_LAST) {
		for (size_t i = 0; i < n; ++i)
			buf[i] = (uint8_t) (1 + env_r(255));
		return;
	}
#endif
	if ((int) k == ENV_DATA_BYTES) {
		env_gen_data(buf, (unsigned) n);
		return;
	}
	for (size_t i = 0; i < n; ++i)
		buf[i] = (uint8_t) ENV_RND();
}
