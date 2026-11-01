/* env/lenv.h: value distributions for native and interpreter runs of the short zlib laws (harness/laws_common.h).
 * Untrusted: it only steers testing; the theorems quantify over every value.  Each env/<law>.c lists the roles of its
 * law's draws by position, per nondet_* function: ENV_<K>_INIT (the first draws), then ENV_<K>_CYCLE repeated
 * (K = S for nondet_size, U for nondet_u32, B for nondet_u8, D for nondet_bytes).  U_S(r) is the size role r of an S
 * draw for a U draw (a length or an output space drawn by nondet_u32).  Optional switches:
 *   ENV_FINISH_CYCLE: after an S_DFLUSH (or U_DFLUSH) draw returned Z_FINISH, the S draws follow this cycle instead;
 *   ENV_FINISH_U_CYCLE, ENV_FINISH_B_CYCLE: the same for the U and the B draws;
 *   ENV_STOP_RESTARTS: after a B_STOP draw returned 0, the S and D draws start again at their INIT lists;
 *   ENV_B_INJECT: after a B_RARE draw returned 0, the next U draws take these roles (a conditional call's parameters)
 *     without moving on in the U cycle.
 * The roles *_OK draw only values in zlib.h's ranges (the laws that assume them); S_CHUNK0 is S_CHUNK with an empty
 * piece or no output space more often.
 * For an input the environment makes, with zlib's own deflate (the library under test, linked with the law), a raw,
 * zlib or gzip stream of generated data that fits the windowBits drawn before (U_WBI, S_WSEL), sometimes with a
 * preset dictionary or a gzip header, and mutates it or not (bit flips, truncation, appended bytes). */
#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include "zlib.h"
extern uint64_t quickproof_rnd(void);
#define ENV_RND quickproof_rnd

enum { X_NONE,
       S_LEN, S_SMALLLEN, S_LEN0, S_CHUNK, S_OUT, S_SPLIT, S_STREAM, S_HUGE, S_SMALL, S_WSEL, S_ZWB, S_HLEN, S_CAP,
       S_DFLUSH, S_NBLK, S_KTRUNC, S_FARK,
       U_ANY, U_LEVEL, U_WBD, U_WBD_WRAP, U_WBI, U_ML, U_ST, U_METHOD, U_IFLUSH, U_IFLUSH_NB, U_IFLUSH_NT, U_DFLUSH,
       U_PARAM, U_BADLEVEL,
       B_ANY, B_STOP, B_RARE, B_BIT,
       D_ANY, D_DATA, D_DICT, D_STREAM, D_NONZERO, D_ZHDR,
       S_CHUNK0, U_LEVEL_OK, U_WBD_OK, U_ML_OK, U_ST_OK, U_WBI_OK };
#define S_UNI(k) (1000 + (k))                       /* uniform 0..k */
#define U_S(r) (100000 + (r))                       /* a U draw with the size role r */

#ifdef __COMPCERT__
#define ENV_DATA_MAX 300
#define ENV_ALL 4096u
#define ENV_ML_MAX 2
#define ENV_L0_MULT 1
#else
#define ENV_L0_MULT 5
#define ENV_DATA_MAX 70000
#define ENV_ALL (1u << 20)
#define ENV_ML_MAX 9
#endif
#define ENV_STREAM_CAP (ENV_DATA_MAX + ENV_DATA_MAX / 4 + 70000)

static unsigned env_k[4];                           /* draws so far, per kind: S, U, B, D */
static int env_wbits, env_finished, env_have_stream;
static size_t env_len, env_stream_len, env_data_len, env_dict_len;
static unsigned char env_stream[ENV_STREAM_CAP], env_data[ENV_DATA_MAX + 1], env_dict[512];

static unsigned env_r(unsigned n) { return n ? (unsigned) (ENV_RND() % n) : 0; }

static size_t env_data_size(void)
{
	unsigned k = env_r(10);
	if (k < 2)
		return env_r(20);
	if (k < 7)
		return env_r(ENV_DATA_MAX < 3000 ? ENV_DATA_MAX : 3000);
	return env_r(ENV_DATA_MAX + 1);
}

static void env_gen(unsigned char *d, size_t n)
{
	unsigned mode = env_r(6);
	size_t i = 0;
	while (i < n) {
		if (mode == 0) {
			d[i++] = (unsigned char) ENV_RND();
		} else if (mode == 1) {
			d[i++] = (unsigned char) ('a' + env_r(4));
		} else if (mode == 2 && i > 0 && env_r(3)) {
			size_t dist = 1 + env_r(i < 300 ? (unsigned) i : 300), len = 3 + env_r(60);
			while (len-- && i < n) {
				d[i] = d[i - dist];
				i++;
			}
		} else if (mode == 3) {
			unsigned char c = (unsigned char) ENV_RND();
			unsigned len = 1 + env_r(300);
			while (len-- && i < n)
				d[i++] = c;
		} else if (mode == 4 && env_dict_len && env_r(2)) {
			size_t at = env_r((unsigned) env_dict_len), len = 3 + env_r(40);
			while (len-- && i < n && at < env_dict_len)
				d[i++] = env_dict[at++];
		} else {
			d[i++] = (unsigned char) (env_r(2) ? ENV_RND() : 'x');
		}
	}
}

/* deflate env_data[0..env_data_len) into env_stream with deflate windowBits w; its length, 0 on failure */
static size_t env_deflate(int w, int with_dict, int with_head)
{
	z_stream d;
	gz_header h;
	static unsigned char hx[40], hn[20], hc[20];
	static const int fl[] = {Z_NO_FLUSH, Z_NO_FLUSH, Z_NO_FLUSH, Z_PARTIAL_FLUSH, Z_SYNC_FLUSH, Z_FULL_FLUSH, Z_BLOCK};
	d.zalloc = Z_NULL;
	d.zfree = Z_NULL;
	d.opaque = Z_NULL;
	d.next_in = Z_NULL;                              /* deflateSetDictionary saves and restores them */
	d.avail_in = 0;
	if (deflateInit2(&d, (int) env_r(11) - 1, Z_DEFLATED, w, 1 + (int) env_r(ENV_ML_MAX), (int) env_r(5)) != Z_OK)
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
		unsigned dl = 1 + env_r(sizeof env_dict);
		env_gen(env_dict, dl);
		if (deflateSetDictionary(&d, env_dict, dl) == Z_OK)
			env_dict_len = dl;
	}
	d.next_out = env_stream;
	d.avail_out = sizeof env_stream;
	size_t pos = 0, n = env_data_len;
	int ret = Z_OK;
	while (ret != Z_STREAM_END) {
		size_t chunk = env_r(4) ? env_r((unsigned) (n - pos + 1)) : n - pos;
		d.next_in = env_data + pos;
		d.avail_in = (uInt) chunk;
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
	size_t len = sizeof env_stream - d.avail_out;
	deflateEnd(&d);
	return len;
}

/* a stream for inflate windowBits w (env_wbits): mostly one that fits, sometimes not; mutated or not */
static size_t env_make_stream(void)
{
	int w = env_wbits, dw;
	unsigned k = env_r(16);
	size_t len = 0;
	env_dict_len = 0;
	env_data_len = env_data_size();
	env_gen(env_data, env_data_len);
	if (k < 13) {
		int raw = w < 0, gz = (w >= 16 && w < 32) || (w >= 32 && w < 48 && env_r(2)) || (w >= 48 && env_r(2));
		int lo = raw ? -w : (w & 15);
		if (lo < 9 || lo > 15)
			lo = raw || gz ? 15 : (lo == 0 ? 15 : 8);
		dw = 9 + (int) env_r((unsigned) (lo - 8));  /* 9..lo; zlib with lo 8: 8 (deflate makes it 9) */
		if (!raw && !gz && lo == 8)
			dw = 8;
		if (env_r(10) == 0)
			dw = 9 + (int) env_r(7);                 /* any window: too large sometimes */
		len = env_deflate(raw ? -dw : gz ? 16 + dw : dw, !gz && env_r(6) == 0, gz && env_r(3) == 0);
	} else if (k < 15) {
		static const unsigned char zh[2] = {0x78, 0x9c}, gh[10] = {0x1f, 0x8b, 8, 0, 0, 0, 0, 0, 0, 3};
		if (k == 13) {
			memcpy(env_stream, zh, 2);
			len = 2;
		} else {
			memcpy(env_stream, gh, 10);
			len = 10;
		}
		unsigned extra = env_r(400);
		for (unsigned i = 0; i < extra; i++)
			env_stream[len++] = (unsigned char) ENV_RND();
	} else {
		len = env_r(300);
		for (size_t i = 0; i < len; i++)
			env_stream[i] = (unsigned char) ENV_RND();
	}
	unsigned m = env_r(8);
	if (m == 1 && len) {
		unsigned c = 1 + env_r(4);
		while (c--)
			env_stream[env_r((unsigned) len)] ^= (unsigned char) (1u << env_r(8));
	} else if (m == 2 && len) {
		len = env_r((unsigned) len);
	} else if (m == 3) {
		unsigned c = env_r(20);
		while (c-- && len < sizeof env_stream)
			env_stream[len++] = (unsigned char) ENV_RND();
	}
	env_have_stream = 1;
	env_stream_len = len;
	return len;
}

static size_t env_chunk(void)
{
	unsigned k = env_r(20);
	if (k < 6)
		return ENV_ALL;
	if (k < 10)
		return env_r(17);
	if (k < 15)
		return env_r(301);
	return env_r(ENV_DATA_MAX < 5000 ? ENV_DATA_MAX + 1 : 5001);
}

static size_t env_size_role(int role)
{
	if (role >= 1000)
		return env_r((unsigned) (role - 1000 + 1));
	switch (role) {
	case S_LEN:
		return env_len = env_data_size();
	case S_SMALLLEN:
		return env_len = env_r(env_r(4) ? 40 : 400);
	case S_LEN0: {
		unsigned k = env_r(4);
		size_t base = (size_t) 65535 * env_r(ENV_L0_MULT);
		if (k == 0)
			return env_len = base;
		if (k == 1)
			return env_len = base + env_r(3) - (base ? 1 : 0);
		return env_len = env_data_size();
	}
	case S_CHUNK:
		return env_chunk();
	case S_CHUNK0:
		return env_r(5) == 0 ? 0 : env_chunk();
	case S_OUT: {
		unsigned k = env_r(4);
		if (k < 2 && env_data_len)
			return env_data_len + env_r(64);
		if (k == 2)
			return env_r((unsigned) env_data_len + 1);
		return env_chunk();
	}
	case S_SPLIT: {
		unsigned k = env_r(4);
		return k == 0 ? 0 : k == 1 ? env_len : env_r((unsigned) env_len + 1);
	}
	case S_STREAM:
		return env_len = env_make_stream();
	case S_HUGE:
		return env_r(2) ? (size_t) ENV_RND() : env_r(100);
	case S_SMALL:
		return env_r(8);
	case S_NBLK:
		return env_r(3) ? env_r(3) : env_r(8);
	case S_WSEL: {
		unsigned sel = env_r(4);
		env_wbits = sel == 0 ? -15 : 16 * (int) sel - 1;
		return sel;
	}
	case S_ZWB: {
		static const int z[] = {0, 8, 9, 10, 11, 12, 13, 14, 15, 32, 40, 41, 42, 43, 44, 45, 46, 47};
		env_wbits = z[env_r(18)];
		return (size_t) env_wbits;
	}
	case S_HLEN:
		return env_r(4) == 0 ? 0 : env_r(8) ? env_r(40) : env_r(ENV_DATA_MAX < 3000 ? ENV_DATA_MAX : 3000);
	case S_CAP:                                     /* a buffer for the compressed bytes: mostly 4 MiB, sometimes small */
		return env_r(8) ? (size_t) 1 << 22 : env_r(2000);
	case S_FARK: {
		unsigned k = env_r(10);
		return k < 5 ? env_r(4) : k < 8 ? env_r(64) : env_r(2000);
	}
	case S_KTRUNC:
		return env_r(3) == 0 ? (size_t) -1 : env_r(3000);
	case S_DFLUSH: {
		static const int fl[] = {Z_NO_FLUSH, Z_NO_FLUSH, Z_NO_FLUSH, Z_PARTIAL_FLUSH, Z_SYNC_FLUSH, Z_FULL_FLUSH,
					 Z_BLOCK, Z_FINISH, Z_FINISH};
		int f = fl[env_r(9)];
		if (f == Z_FINISH)
			env_finished = 1;
		return (size_t) f;
	}
	default:
		break;
	}
	return (size_t) ENV_RND();
}

static int env_inflate_wbits(void)
{
	unsigned k = env_r(20);
	int w = 8 + (int) env_r(8);
	if (k < 5)
		return w;
	if (k < 6)
		return 0;
	if (k < 9)
		return 16 + w;
	if (k < 10)
		return 16;
	if (k < 12)
		return 32 + w;
	if (k < 13)
		return 32;
	if (k < 18)
		return -w;
	return (int) env_r(120) - 60;
}

static uint32_t env_u32_role(int role)
{
	if (role >= 100000)
		return (uint32_t) env_size_role(role - 100000);
	switch (role) {
	case U_LEVEL:
		return env_r(16) == 0 ? (uint32_t) ENV_RND() : (uint32_t) ((int) env_r(11) - 1);
	case U_WBD:
	case U_WBD_WRAP: {
		unsigned k = env_r(16);
		int w = 9 + (int) env_r(7);
		if (k < 6)
			return (uint32_t) w;
		if (k < 10)
			return (uint32_t) (16 + w);
		if (k < 14)
			return role == U_WBD ? (uint32_t) -w : (uint32_t) w;
		if (k < 15)
			return 8;
		return (uint32_t) ((int) env_r(80) - 40);
	}
	case U_WBI:
		env_wbits = env_inflate_wbits();
		return (uint32_t) env_wbits;
	case U_WBI_OK:
		do
			env_wbits = env_inflate_wbits();
		while (!(env_wbits >= -15 && env_wbits <= -8) &&
		       !(env_wbits >= 0 && env_wbits < 48 && ((env_wbits & 15) == 0 || (env_wbits & 15) >= 8)));
		return (uint32_t) env_wbits;
	case U_LEVEL_OK:
		return (uint32_t) ((int) env_r(11) - 1);
	case U_WBD_OK: {
		unsigned k = env_r(15);
		int w = 9 + (int) env_r(7);
		if (k < 6)
			return (uint32_t) w;
		if (k < 10)
			return (uint32_t) (16 + w);
		if (k < 14)
			return (uint32_t) -w;
		return 8;
	}
	case U_ML_OK:
		return 1 + env_r(ENV_ML_MAX);
	case U_ST_OK:
		return env_r(5);
	case U_ML:
		return env_r(16) == 0 ? (uint32_t) ENV_RND() : 1 + env_r(ENV_ML_MAX);
	case U_ST:
		return env_r(16) == 0 ? (uint32_t) ENV_RND() : env_r(5);
	case U_METHOD:
		return env_r(8) == 0 ? (uint32_t) ENV_RND() : Z_DEFLATED;
	case U_IFLUSH:
	case U_IFLUSH_NB:
	case U_IFLUSH_NT: {
		static const int fl[] = {Z_NO_FLUSH, Z_NO_FLUSH, Z_NO_FLUSH, Z_SYNC_FLUSH, Z_FINISH, Z_FINISH, Z_BLOCK,
					 Z_TREES, 99, -1};
		int f;
		do
			f = fl[env_r(10)];
		while ((role == U_IFLUSH_NB && (f == Z_BLOCK || f == Z_TREES)) || (role == U_IFLUSH_NT && f == Z_TREES));
		return (uint32_t) f;
	}
	case U_DFLUSH: {
		uint32_t f = env_r(8) == 0 ? (uint32_t) ENV_RND() : env_r(6);
		if (f == Z_FINISH)
			env_finished = 1;
		return f;
	}
	case U_BADLEVEL:
		return env_r(2) ? (uint32_t) ENV_RND() : (uint32_t) ((int) env_r(34) - 12);
	case U_PARAM:
		return env_r(8) == 0 ? (uint32_t) ENV_RND() : (uint32_t) ((int) env_r(11) - 1);
	default:
		break;
	}
	return (uint32_t) ENV_RND();
}

static uint8_t env_u8_role(int role)
{
	switch (role) {
	case B_STOP:
#ifdef __COMPCERT__
		return env_r(4) == 0 ? 0 : 1;
#else
		return env_r(12) == 0 ? 0 : 1;
#endif
	case B_RARE:
		return env_r(8) == 0 ? 0 : 1;
	case B_BIT:
		return (uint8_t) env_r(2);
	default:
		break;
	}
	return (uint8_t) ENV_RND();
}

static void env_bytes_role(int role, uint8_t *buf, size_t n)
{
	switch (role) {
	case D_DATA:
		env_gen(buf, n);
		return;
	case D_DICT:
		env_gen(buf, n);
		env_dict_len = n < sizeof env_dict ? n : sizeof env_dict;
		memcpy(env_dict, buf + (n - env_dict_len), env_dict_len);
		return;
	case D_STREAM:
		if (env_have_stream && n == env_stream_len) {
			memcpy(buf, env_stream, n);
			return;
		}
		break;
	case D_NONZERO:
		for (size_t i = 0; i < n; i++)
			buf[i] = (uint8_t) (1 + env_r(255));
		return;
	case D_ZHDR: {                                   /* a zlib header with one defect or several, then anything */
		for (size_t i = 0; i < n; i++)
			buf[i] = (uint8_t) ENV_RND();
		if (n < 2 || env_r(4) == 0)
			return;
		unsigned k = env_r(3), cinfo = env_r(8), cm = 8;
		if (k == 0)
			cinfo = 8 + env_r(8);                    /* CINFO above 7 */
		else if (k == 1)
			cm = env_r(16) == 8 ? 15 : env_r(16);    /* CM not 8 */
		else if ((env_wbits & 15) != 0)
			cinfo = (unsigned) (env_wbits & 15) - 8 + 1 + env_r(16 - (unsigned) (env_wbits & 15)); /* > window */
		buf[0] = (uint8_t) (cinfo << 4 | cm);
		buf[1] = (uint8_t) (env_r(256) & 0xe0);
		buf[1] = (uint8_t) (buf[1] + (31 - (buf[0] * 256 + buf[1]) % 31) % 31);
		return;
	}
	default:
		break;
	}
	for (size_t i = 0; i < n; i++)
		buf[i] = (uint8_t) ENV_RND();
}

#define ENV_N(a) (sizeof (a) / sizeof (a)[0])
#ifndef ENV_S_INIT
#define ENV_S_INIT {X_NONE}
#endif
#ifndef ENV_S_CYCLE
#define ENV_S_CYCLE {X_NONE}
#endif
#ifndef ENV_U_INIT
#define ENV_U_INIT {X_NONE}
#endif
#ifndef ENV_U_CYCLE
#define ENV_U_CYCLE {X_NONE}
#endif
#ifndef ENV_B_INIT
#define ENV_B_INIT {X_NONE}
#endif
#ifndef ENV_B_CYCLE
#define ENV_B_CYCLE {X_NONE}
#endif
#ifndef ENV_D_INIT
#define ENV_D_INIT {X_NONE}
#endif
#ifndef ENV_D_CYCLE
#define ENV_D_CYCLE {X_NONE}
#endif

/* the role of draw number k of a kind: INIT[k] while k is in it (X_NONE entries are skipped), then the cycle */
static int env_role(const int *init, unsigned ni, const int *cyc, unsigned nc, unsigned k)
{
	unsigned real = (ni == 1 && init[0] == X_NONE) ? 0 : ni;
	if (k < real)
		return init[k];
	return cyc[(k - real) % nc];
}

size_t nondet_size(void)
{
	static const int init[] = ENV_S_INIT, cyc[] = ENV_S_CYCLE;
#ifdef ENV_FINISH_CYCLE
	static const int fin[] = ENV_FINISH_CYCLE;
	static unsigned kf;
	if (env_finished)
		return env_size_role(fin[kf++ % ENV_N(fin)]);
#endif
	return env_size_role(env_role(init, ENV_N(init), cyc, ENV_N(cyc), env_k[0]++));
}

static unsigned env_inject_at, env_inject_n;   /* ENV_B_INJECT: the next injected role, and how many are left */

uint32_t nondet_u32(void)
{
	static const int init[] = ENV_U_INIT, cyc[] = ENV_U_CYCLE;
#ifdef ENV_B_INJECT
	static const int inject[] = ENV_B_INJECT;
	if (env_inject_n > 0) {
		env_inject_n--;
		return env_u32_role(inject[env_inject_at++ % ENV_N(inject)]);
	}
#endif
#ifdef ENV_FINISH_U_CYCLE
	static const int fin[] = ENV_FINISH_U_CYCLE;
	static unsigned kf;
	if (env_finished)
		return env_u32_role(fin[kf++ % ENV_N(fin)]);
#endif
	return env_u32_role(env_role(init, ENV_N(init), cyc, ENV_N(cyc), env_k[1]++));
}

uint8_t nondet_u8(void)
{
	static const int init[] = ENV_B_INIT, cyc[] = ENV_B_CYCLE;
#ifdef ENV_FINISH_B_CYCLE
	static const int fin[] = ENV_FINISH_B_CYCLE;
	static unsigned kf;
	if (env_finished)
		return env_u8_role(fin[kf++ % ENV_N(fin)]);
#endif
	int role = env_role(init, ENV_N(init), cyc, ENV_N(cyc), env_k[2]++);
	uint8_t v = env_u8_role(role);
#ifdef ENV_B_INJECT
	if (role == B_RARE && v == 0) {
		static const int inject[] = ENV_B_INJECT;
		env_inject_at = 0;
		env_inject_n = ENV_N(inject);
	}
#endif
#ifdef ENV_STOP_RESTARTS
	if (role == B_STOP && v == 0) {
		env_k[0] = 0;
		env_k[3] = 0;
	}
#endif
	return v;
}

void nondet_bytes(uint8_t *buf, size_t n)
{
	static const int init[] = ENV_D_INIT, cyc[] = ENV_D_CYCLE;
	env_bytes_role(env_role(init, ENV_N(init), cyc, ENV_N(cyc), env_k[3]++), buf, n);
}
