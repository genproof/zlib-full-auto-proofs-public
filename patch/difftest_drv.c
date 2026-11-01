/* patch/difftest_drv.c: the differential test of the quickproof patch (patch/difftest.sh).
 *
 * Built once against the unmodified zlib and once against the patched one; both binaries must print the same
 * bytes.  Per case: a stream made by zlib's deflate from random data with random parameters (zlib, gzip or raw
 * wrapper, any level, strategy, memLevel, window, a preset dictionary, a gzip header, flushes of every kind in
 * the middle), or random bytes, or a gzip/zlib header followed by random bytes; then mutated (bit flips, byte
 * changes, truncation, appended garbage) or not.  It is inflated with a random windowBits (the matching one, the
 * auto-detecting one, or any value), a random split of the input and of the output space over the calls, a random
 * flush per call, and between calls any of inflateGetHeader (with random buffer sizes), inflateSetDictionary
 * (the right, a wrong, or no dictionary on Z_NEED_DICT; any dictionary on a raw stream), inflateGetDictionary,
 * inflatePrime, inflateSync, inflateMark, inflateCodesUsed, inflateSyncPoint, inflateReset2, inflateValidate.
 * After every call it prints everything a caller can observe: the return code, the stream fields, the output
 * bytes, the header fields and buffers, the dictionary.
 *
 * Per case also (deflate_probe): deflateBound for random parameters, and one deflate(Z_FINISH) call into exactly
 * the complete stream's length.
 *
 * With GP_NO_TOTAL_IN_AFTER_NEED_DICT=1 in the environment, total_in is not printed for a stream after it returned
 * Z_NEED_DICT (patch F1 changes exactly that value); with GP_HIDE_DEFLATE_FIXES=1, deflateBound is not printed for
 * Z_FIXED at levels 1-3 with windowBits 15 and memLevel 8 (F3 changes exactly that value), nor the result of the
 * exact-length call for a raw stream at levels 1-9 (F5 changes exactly that result).  With GP_HIDE_F4=1 the
 * inflateprime_probe (F4) prints no observables and the random inflatePrime calls are skipped.  With GP_HIDE_F6=1
 * the sync_window_probe (F6) prints no observables; with GP_NO_F6_SYNC=1 inflateSync is not called while the
 * stream's windowBits request takes the window size from the header (0, 16 or 32): F6 changes what inflateSync does
 * exactly there, and on the unmodified code a later inflateReset2 can make that path overflow the window (F6), undefined behaviour that no comparison can use.  The
 * summary line counts the streams and cases concerned.
 *
 * usage: difftest_drv SEED CASES
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "zlib.h"

static unsigned long long rs;
static unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static unsigned rn(unsigned n) { return n ? (unsigned)(rnd() % n) : 0; }

static int hide_total_in, hide_deflate_fixes, hide_f4, hide_f6, no_f6_sync;
static long need_dict_streams, f3_cases, f5_cases, f4_cases, f6_syncs;

static void put_hex(const unsigned char *b, unsigned n)
{
    static const char hx[] = "0123456789abcdef";
    for (unsigned i = 0; i < n; i++) { putchar(hx[b[i] >> 4]); putchar(hx[b[i] & 15]); }
}

/* random data with some structure (repeats, runs, small alphabets) */
static void gen_data(unsigned char *d, unsigned n)
{
    unsigned mode = rn(5), i = 0;
    while (i < n) {
        if (mode == 0) d[i++] = (unsigned char)rnd();
        else if (mode == 1) d[i++] = (unsigned char)('a' + rn(4));
        else if (mode == 2 && i > 0 && rn(3)) {
            unsigned dist = 1 + rn(i < 300 ? i : 300), len = 3 + rn(40);
            while (len-- && i < n) { d[i] = d[i - dist]; i++; }
        }
        else if (mode == 3) { unsigned char c = (unsigned char)rnd(); unsigned len = 1 + rn(300); while (len-- && i < n) d[i++] = c; }
        else d[i++] = (unsigned char)(rn(2) ? rnd() : 'x');
    }
}

static const int flushes[] = {Z_NO_FLUSH, Z_PARTIAL_FLUSH, Z_SYNC_FLUSH, Z_FULL_FLUSH, Z_BLOCK, Z_FINISH};

/* deflate data into out (cap bytes): returns the length, or 0 on failure */
static unsigned make_stream(unsigned char *out, unsigned cap, const unsigned char *data, unsigned n, int wbits,
                            const unsigned char *dict, unsigned dlen)
{
    z_stream d;
    memset(&d, 0, sizeof d);
    int level = (int)rn(11) - 1, mem = 1 + (int)rn(9), strat = (int)rn(5);
    if (deflateInit2(&d, level, Z_DEFLATED, wbits, mem, strat) != Z_OK) return 0;
    gz_header h;
    unsigned char extra[40], name[20], comment[20];
    if (wbits > 15 && rn(2)) {
        memset(&h, 0, sizeof h);
        h.text = (int)rn(2); h.time = (uLong)rnd() & 0xffffffff; h.os = (int)rn(256); h.xflags = 0;
        if (rn(2)) { h.extra_len = rn(40); for (unsigned i = 0; i < h.extra_len; i++) extra[i] = (unsigned char)rnd(); h.extra = extra; }
        if (rn(2)) { unsigned l = rn(19); for (unsigned i = 0; i < l; i++) name[i] = (unsigned char)(1 + rn(255)); name[l] = 0; h.name = name; }
        if (rn(2)) { unsigned l = rn(19); for (unsigned i = 0; i < l; i++) comment[i] = (unsigned char)(1 + rn(255)); comment[l] = 0; h.comment = comment; }
        h.hcrc = (int)rn(2);
        deflateSetHeader(&d, &h);
    }
    if (dlen && wbits <= 15) deflateSetDictionary(&d, dict, dlen);
    d.next_out = out; d.avail_out = cap;
    unsigned pos = 0;
    int ret = Z_OK;
    while (ret != Z_STREAM_END) {
        unsigned chunk = rn(4) ? rn(n - pos + 1) : n - pos;
        d.next_in = (unsigned char *)data + pos; d.avail_in = chunk;
        int fl = pos + chunk == n && rn(2) ? Z_FINISH : flushes[rn(6)];
        if (rn(20) == 0) deflateParams(&d, (int)rn(10), (int)rn(5));
        ret = deflate(&d, fl);
        pos += chunk - d.avail_in;
        if (ret == Z_STREAM_ERROR || d.avail_out == 0) { deflateEnd(&d); return 0; }
        if (pos == n && fl != Z_FINISH && rn(2)) { d.next_in = (unsigned char *)data + pos; d.avail_in = 0; ret = deflate(&d, Z_FINISH); }
    }
    unsigned len = cap - d.avail_out;
    deflateEnd(&d);
    return len;
}

/* deflateBound for random parameters (F3), and one deflate(Z_FINISH) call into exactly the length of the complete
   stream (F5: for a raw stream at levels 1-9 the last block then exactly fills the output space) */
static void deflate_probe(const unsigned char *data, unsigned n)
{
    static unsigned char out[90000];
    z_stream d;
    memset(&d, 0, sizeof d);
    int level = (int)rn(11) - 1, strat = (int)rn(5), mem = rn(2) ? 8 : 1 + (int)rn(9);
    int kind = (int)rn(3), wb = rn(2) ? 15 : 9 + (int)rn(7);
    int wbits = kind == 0 ? wb : kind == 1 ? wb + 16 : -wb;
    if (deflateInit2(&d, level, Z_DEFLATED, wbits, mem, strat) != Z_OK) return;
    uLong b = deflateBound(&d, n);
    int f3 = wb == 15 && mem == 8 && strat == Z_FIXED && level >= 1 && level <= 3;
    f3_cases += f3;
    if (f3 && hide_deflate_fixes) printf("bound -\n");
    else printf("bound %lu\n", b);
    d.next_in = (unsigned char *)data; d.avail_in = n;
    d.next_out = out; d.avail_out = sizeof out;
    int r = deflate(&d, Z_FINISH);
    unsigned len = (unsigned)(sizeof out - d.avail_out);
    printf("deflate %d %u\n", r, len);
    deflateEnd(&d);
    if (r != Z_STREAM_END) return;
    memset(&d, 0, sizeof d);
    if (deflateInit2(&d, level, Z_DEFLATED, wbits, mem, strat) != Z_OK) return;
    d.next_in = (unsigned char *)data; d.avail_in = n;
    d.next_out = out; d.avail_out = len;
    r = deflate(&d, Z_FINISH);
    int f5 = kind == 2 && level != 0;
    f5_cases += f5;
    if (f5 && hide_deflate_fixes) printf("exact -");
    else printf("exact %d", r);
    printf(" %lu %u", d.total_out, d.avail_out);
    unsigned char one[1];
    d.next_out = one; d.avail_out = 1;
    r = deflate(&d, Z_FINISH);
    printf(" then %d %lu\n", r, d.total_out);
    deflateEnd(&d);
}

/* F4: raw inflate, two 16-bit inflatePrime() calls before the first inflate() (documented
   use; up to 32 bits buffered), then one inflate() on 6 input bytes and 258 output bytes -- the fast path.
   On the unmodified code inflate_fast rewinds next_in before the input (overread; avail_in and total_in
   corrupted); F4 enters inflate_fast only when bits < 8, so the slow path handles the primed bits.  value is
   the first prime's bits: 3 = final block (Z_STREAM_END), 2 = non-final (reads a further block header). */
static void inflateprime_probe(unsigned value)
{
    unsigned char in[6] = {0}, out[258];
    z_stream s;
    memset(&s, 0, sizeof s);
    if (inflateInit2(&s, -15) != Z_OK) return;
    inflatePrime(&s, 16, (int)value);
    inflatePrime(&s, 16, 0);
    s.next_in = in; s.avail_in = 6;
    s.next_out = out; s.avail_out = 258;
    int r = inflate(&s, Z_NO_FLUSH);
    f4_cases++;
    if (hide_f4)
        printf("prime_probe v%u -\n", value);
    else
        printf("prime_probe v%u r%d in%+ld ai%u ti%lu\n", value, r, (long)(s.next_in - in), s.avail_in,
               s.total_in);
    inflateEnd(&s);
}

/* F6: inflateInit2(0) (the window size from the zlib header), inflateSync() before any header
   (the sync pattern 00 00 ff ff first), then raw deflate data with back-references, decoded into 64 bytes of output
   per call.  On the unmodified code the stream becomes raw with wbits 0, its window is allocated with 1 byte, and
   a back-reference across calls fails ("invalid distance too far back"); with F6 the raw stream has a 32 KiB window
   and the data decodes.  (No inflateReset2 here: on the unmodified code the next header would then overflow the
   1-byte window.) */
static void sync_window_probe(void)
{
    static unsigned char data[4000], comp[4200], out[4000];
    static unsigned clen;
    if (clen == 0) {
        for (unsigned i = 0; i < sizeof data; i++)
            data[i] = (unsigned char)"abcdefghijklmnopqrstuvwxyz0123456789"[(i * 7 + i / 50) % 36];
        z_stream d;
        memset(&d, 0, sizeof d);
        if (deflateInit2(&d, 6, Z_DEFLATED, -15, 8, Z_DEFAULT_STRATEGY) != Z_OK) return;
        comp[0] = 0; comp[1] = 0; comp[2] = 0xff; comp[3] = 0xff;
        d.next_in = data; d.avail_in = sizeof data;
        d.next_out = comp + 4; d.avail_out = sizeof comp - 4;
        deflate(&d, Z_FINISH);
        clen = (unsigned)(sizeof comp - d.avail_out);
        deflateEnd(&d);
    }
    z_stream s;
    memset(&s, 0, sizeof s);
    if (inflateInit2(&s, 0) != Z_OK) return;
    s.next_in = comp; s.avail_in = clen;
    int rs = inflateSync(&s), r;
    unsigned got = 0;
    do {
        s.next_out = out + got; s.avail_out = sizeof out - got < 64 ? (unsigned)(sizeof out - got) : 64;
        r = inflate(&s, Z_NO_FLUSH);
        got = (unsigned)(s.next_out - out);
    } while (r == Z_OK && got < sizeof out);
    if (hide_f6)
        printf("sync_probe -\n");
    else
        printf("sync_probe s%d r%d to%lu same%d msg[%s]\n", rs, r, s.total_out,
               got == sizeof data && memcmp(out, data, sizeof data) == 0, s.msg ? s.msg : "-");
    inflateEnd(&s);
}

static int window_from_header(int w) { return w >= 0 && (w & 15) == 0; }

static void show_stream(const z_stream *s, const unsigned char *in0, const unsigned char *out0, int after_need_dict)
{
    printf(" in+%ld ai%u out+%ld ao%u", (long)(s->next_in ? s->next_in - in0 : -1), s->avail_in,
           (long)(s->next_out - out0), s->avail_out);
    if (!(hide_total_in && after_need_dict)) printf(" ti%lu", s->total_in);
    printf(" to%lu ad%lu dt%d msg[%s]", s->total_out, s->adler, s->data_type, s->msg ? s->msg : "-");
}

static void one_case(void)
{
    static unsigned char data[70000], comp[80000], dict[300], inbuf[80000], out[140000];
    unsigned n = rn(4) ? rn(2000) : rn(66000);
    gen_data(data, n);
    deflate_probe(data, n);
    inflateprime_probe(3);      /* F4: a final fixed block from the bit buffer; Z_STREAM_END, no overread */
    sync_window_probe();        /* F6: a raw stream after inflateSync with windowBits 0 */
    unsigned dlen = rn(3) == 0 ? 1 + rn(300) : 0;
    gen_data(dict, dlen);
    int kind = (int)rn(3);                              /* 0 zlib, 1 gzip, 2 raw */
    int wb = 8 + (int)rn(8);
    int wbits = kind == 0 ? wb : kind == 1 ? wb + 16 : -wb;
    unsigned clen;
    unsigned src = rn(10);
    if (src < 7) {
        clen = make_stream(comp, sizeof comp, data, n, wbits, dict, dlen);
    } else if (src < 9) {                               /* a valid header, then random bytes */
        clen = 0;
        if (src == 7) { comp[0] = 0x78; comp[1] = 0x9c; clen = 2; }
        else { static const unsigned char gz[10] = {0x1f, 0x8b, 8, 0, 0, 0, 0, 0, 0, 3}; memcpy(comp, gz, 10); clen = 10; }
        unsigned extra = rn(3000);
        for (unsigned i = 0; i < extra; i++) comp[clen++] = (unsigned char)rnd();
    } else {
        clen = rn(3000);
        for (unsigned i = 0; i < clen; i++) comp[i] = (unsigned char)rnd();
    }
    /* mutations */
    unsigned mut = rn(4);
    if (mut == 1 && clen) { unsigned k = 1 + rn(4); while (k--) comp[rn(clen)] ^= (unsigned char)(1u << rn(8)); }
    else if (mut == 2 && clen) clen = rn(clen);
    else if (mut == 3) { unsigned k = rn(20); while (k--) comp[clen++] = (unsigned char)rnd(); }
    memcpy(inbuf, comp, clen);

    int iw;
    switch (rn(6)) {
    case 0: case 1: case 2: iw = wbits; break;
    case 3: iw = 32 + wb; break;
    case 4: iw = (int)rn(64) - 20; break;
    default: iw = 0; break;
    }
    printf("case n%u clen%u wbits%d iw%d\n", n, clen, wbits, iw);
    put_hex(comp, clen);                                /* the compressed stream: deflate's behaviour too */
    putchar('\n');
    z_stream s;
    memset(&s, 0, sizeof s);
    int r = inflateInit2(&s, iw);
    printf("init %d\n", r);
    if (r != Z_OK) return;
    int wreq = iw;              /* the stream's windowBits request (inflateInit2, inflateReset2) */
    gz_header h;
    unsigned char hx[64], hn[64], hc[64];
    memset(&h, 0, sizeof h);
    memset(hx, 0xa5, sizeof hx); memset(hn, 0xa5, sizeof hn); memset(hc, 0xa5, sizeof hc);
    int have_head = 0;
    if (rn(3) == 0) {
        h.extra = rn(4) ? hx : NULL; h.extra_max = rn(65);
        h.name = rn(4) ? hn : NULL; h.name_max = rn(65);
        h.comment = rn(4) ? hc : NULL; h.comm_max = rn(65);
        r = inflateGetHeader(&s, &h);
        printf("gethead %d\n", r);
        have_head = r == Z_OK;
    }
    unsigned pos = 0, opos = 0, calls = 0;
    int need_dict_seen = 0;
    for (;;) {
        unsigned ain = rn(5) == 0 ? clen - pos : rn(clen - pos + 1);
        if (rn(8) == 0) ain = rn(3);
        if (ain > clen - pos) ain = clen - pos;
        unsigned aout = rn(5) == 0 ? (unsigned)(sizeof out - opos) : rn(rn(2) ? 300 : 70000);
        if (aout > sizeof out - opos) aout = (unsigned)(sizeof out - opos);
        int fl = rn(8) == 0 ? (int)rn(10) - 2 : (int[]){Z_NO_FLUSH, Z_SYNC_FLUSH, Z_FINISH, Z_BLOCK, Z_TREES}[rn(5)];
        s.next_in = ain == 0 && rn(2) ? NULL : inbuf + pos;
        s.avail_in = ain;
        s.next_out = out + opos;
        s.avail_out = aout;
        const unsigned char *in0 = inbuf + pos;
        unsigned char *out0 = out + opos;
        r = inflate(&s, fl);
        if (r == Z_NEED_DICT && !need_dict_seen) { need_dict_seen = 1; need_dict_streams++; }
        printf("inflate fl%d ain%u aout%u -> %d", fl, ain, aout, r);
        show_stream(&s, s.next_in == NULL ? s.next_in : in0, out0, need_dict_seen);
        unsigned used = s.next_in ? (unsigned)(s.next_in - in0) : 0, made = (unsigned)(s.next_out - out0);
        printf(" mark%ld codes%lu sp%d\n", inflateMark(&s), inflateCodesUsed(&s), inflateSyncPoint(&s));
        put_hex(out0, made); putchar('\n');
        pos += used; opos += made;
        if (have_head)
            printf("head done%d text%d time%lu xf%d os%d xl%u hcrc%d\n", h.done, h.text, h.time, h.xflags, h.os,
                   h.extra_len, h.hcrc);
        if (r == Z_NEED_DICT) {
            unsigned c = rn(3);
            if (c == 0) r = inflateSetDictionary(&s, dict, dlen);
            else if (c == 1) r = inflateSetDictionary(&s, data, n < 300 ? n : 300);
            else r = 99;
            printf("setdict %d %d\n", (int)c, r);
            if (r == 99) break;
        }
        if (r == Z_STREAM_END || r == Z_DATA_ERROR || r == Z_MEM_ERROR || r == Z_STREAM_ERROR) {
            int f6 = 0;
            if (r == Z_DATA_ERROR && rn(3) == 0 && pos < clen && !(f6 = no_f6_sync && window_from_header(wreq))) {
                s.next_in = inbuf + pos; s.avail_in = clen - pos;
                in0 = inbuf + pos;
                r = inflateSync(&s);
                printf("sync %d", r);
                show_stream(&s, in0, out0, need_dict_seen);
                putchar('\n');
                pos += (unsigned)(s.next_in - in0);
                if (r == Z_OK) continue;
            }
            f6_syncs += f6;
            break;
        }
        if (++calls > 4000) break;
        unsigned extra = rn(30);
        if (extra == 0 && !hide_f4) { int b = (int)rn(20) - 2, v = (int)rnd(); printf("prime %d\n", inflatePrime(&s, b, v)); }
        else if (extra == 1 && iw < 0) { printf("rawdict %d\n", inflateSetDictionary(&s, dict, dlen)); }
        else if (extra == 2) {
            unsigned char dd[32768]; uInt dl = 0;
            r = inflateGetDictionary(&s, NULL, &dl);
            int r2 = inflateGetDictionary(&s, dd, NULL);
            printf("getdict %d %d %u ", r, r2, dl); put_hex(dd, dl); putchar('\n');
        }
        else if (extra == 3) { printf("validate %d\n", inflateValidate(&s, (int)rn(2))); }
        else if (extra == 4 && rn(4) == 0) {
            int w = rn(2) ? iw : (int)rn(64) - 20, rr = inflateReset2(&s, w);
            printf("reset2 %d %d\n", w, rr);
            if (rr == Z_OK) wreq = w;
            pos = 0;
        }
        else if (extra == 5 && rn(4) == 0) { printf("reset %d\n", inflateReset(&s)); pos = 0; }
        if (pos == clen && opos == sizeof out) break;
        if (opos > sizeof out - 1000) opos = 0;
    }
    if (have_head) {
        printf("headbufs "); put_hex(hx, sizeof hx); putchar(' '); put_hex(hn, sizeof hn); putchar(' '); put_hex(hc, sizeof hc); putchar('\n');
    }
    printf("end %d\n", inflateEnd(&s));
}

int main(int argc, char **argv)
{
    unsigned long seed = argc > 1 ? strtoul(argv[1], 0, 10) : 1;
    long cases = argc > 2 ? atol(argv[2]) : 1000;
    hide_total_in = getenv("GP_NO_TOTAL_IN_AFTER_NEED_DICT") != NULL;
    hide_deflate_fixes = getenv("GP_HIDE_DEFLATE_FIXES") != NULL;
    hide_f4 = getenv("GP_HIDE_F4") != NULL;
    hide_f6 = getenv("GP_HIDE_F6") != NULL;
    no_f6_sync = getenv("GP_NO_F6_SYNC") != NULL;
    rs = 0x9E3779B97F4A7C15ULL ^ seed * 0x2545F4914F6CDD1DULL;
    for (long c = 0; c < cases; c++) one_case();
    fprintf(stderr, "%ld cases, %ld streams with Z_NEED_DICT, %ld F3 bounds, %ld F5 exact finishes, %ld F4 primes, "
            "%ld F6 syncs skipped\n", cases, need_dict_streams, f3_cases, f5_cases, f4_cases, f6_syncs);
    return 0;
}
