# The quickproof patch of zlib 1.3.2 (patch/PATCH.md), run at the tree root of zlib 1.3.2.
# Every changed line carries a `quickproof:` comment with the original.
#
# Idiom edits (no change of behaviour; checked by patch/difftest.sh):
#   I1  inftrees.h, inflate.h: include guards (none upstream; inftrees.h's exactly as in our earlier proof of inflate_table).  quickproof/tools/interp.sh compiles all units and a
#       harness as one translation unit for CompCert's interpreter, where `code`, `codetype`, `inflate_mode` and
#       `struct inflate_state` would be defined two or three times.  No change for clightgen or a compiler, which
#       see each unit separately.
#   I2  `break;` after the last case of seven switches whose last case falls off the end of the switch body (VST's switch
#       rule cannot prove that; as in our earlier proof of inflate_table): inftrees.c inflate_table `switch (type)`, inflate.c
#       inflate() `switch (BITS(2))` (block type), deflate.c deflateBound() (wrapper length), zutil.c
#       zlibCompileFlags() (four).  Same behaviour by the C standard (6.8.4.2, 6.8.6.3).
#   I3  inflate.c, inflate(): the `goto inf_leave`s, 14 direct and 23 through PULLBYTE/NEEDBITS (VST has no rule for goto).  Every goto becomes
#       `leave = 1; break;`, and `if (leave) break;` after every loop or inner switch that such a break leaves, so
#       that the break reaches the main `for (;;)`, whose body is now `switch (state->mode) {...}
#       if (leave) break;`.  The label inf_leave is the code right after that loop, as before.  PULLBYTE and
#       NEEDBITS become blocks (no do/while(0), whose loop would catch the break).
#   I4  inffast.c, inflate_fast(): the two backward gotos (`goto dolen`, `goto dodist`: the second-level table
#       lookups) become a `for (;;)` around the table walk, left when the entry is not a link; the if/else chains
#       after it lose their link branch (which can no longer be taken).
#   I5  deflate.c, deflateInit2_(): `s->prev` (the hash chains) is zeroed after it is allocated.  slide_hash() reads
#       every entry of s->prev, also those never written ("If n is not on any hash chain, prev[n] is garbage but its
#       value will never be used"): reading uninitialised memory is undefined in CompCert's semantics (Vundef; the
#       comparison `m >= wsize` is stuck: found by `qp interp`, law deflate_api).  The values of such entries are
#       never used, so the compressed output is the same (patch/difftest.sh compares it byte for byte).
#   I6  deflate.h: the extern declarations of trees.c's tables `_length_code[]` and `_dist_code[]` get their sizes
#       (256 and DIST_CODE_LEN = 512, as trees.h defines them).  deflate.c's Clight declares an incomplete array
#       (tarray tuchar 0) where trees.c's defines tarray tuchar 256 / 512, and VST's linker (QPlink) refuses
#       different types of one global ("Gvar type/readonly/volatile clash", found by building the contracts of the
#       deflate laws).  A declaration's array size does not change the object code (patch/PATCH.md).
#
# Fixes (behaviour changes, F1-F9; `--no-fix` leaves them out):
#   F1  inflate.c, inflate(), state DICT: `return Z_NEED_DICT` leaves inflate() without adding the bytes consumed
#       by the call (the zlib header and the 4-byte dictionary id) to strm->total_in, which zlib.h documents as
#       the "total number of input bytes read so far"; total_in stays 6 bytes short for the rest of the stream.
#       Fix: add them before returning.
#   F2  adler32.c, adler32_z(): with buf == Z_NULL and len == 1 it reads buf[0] (the Z_NULL test is "deferred" after
#       the one-byte fast path), although zlib.h says "If buf is Z_NULL, this function returns the required initial
#       value for the checksum" (F2).  Fix: the Z_NULL test first.  Every call with buf != Z_NULL gives
#       the same result as before.
#   F3  deflate.c, deflateBound_z(): for windowBits 15 and memLevel 8 it returns its tight bound (about 0.03%) for
#       every strategy and level, which assumes that a block can always be stored when that is shorter.  With
#       Z_FIXED at levels 1-3 (deflate_fast, which keeps length-3 matches at any distance) a block that reaches back
#       further than the window cannot be stored (block_start < 0) and its fixed codes cost 25 bits per far
#       length-3 match of 24 data bits: one deflate(Z_FINISH) into deflateBound() bytes returns Z_OK (F3).  Fix: the conservative bound for that case (fixedlen, since w_bits <= hash_bits).
#   F4  inflate.c, inflate(), state LEN: inflate_fast() is entered only when fewer than 8 bits are buffered
#       (`have >= 6 && left >= 258 && bits < 8`).  inflate_fast ends with `in -= bits >> 3` ("on entry, bits < 8,
#       so in won't go too far back", inffast.c); inflatePrime() may leave up to 32 bits buffered that were never
#       read from next_in, so a primed fast-path entry rewinds next_in before the caller's input, reads outside it
#       and corrupts avail_in / total_in (F4).  The slow path decodes the same symbols with the same
#       output when 8+ bits are buffered; zlib never enters inflate_fast with 8+ bits without inflatePrime.
#   F5  deflate.c, FLUSH_BLOCK: when the last block of a raw stream (no trailer) exactly fills the output space,
#       deflate_fast/slow/rle/huff return finish_started and deflate() returns Z_OK although the stream is complete
#       (zlib.h: deflate(Z_FINISH) into deflateBound() bytes "is guaranteed to return Z_STREAM_END"; F5, known upstream: madler/zlib #1300, PR #1326).  Fix, as PR #1326: return early only when the block
#       is not the last one, or output is still pending, or a trailer is still to be written; otherwise the caller
#       goes on to return finish_done (deflate() returns Z_STREAM_END).
#   F6  inflate.c, inflateSync(): when no header was processed (state->flags == -1) inflateSync makes the stream raw
#       (wrap = 0) but leaves wbits at 0 if inflateInit2/inflateReset2 asked for the window size of the header
#       (windowBits 0, 16 or 32).  inflate() then allocates the window with 1U << 0 = 1 byte, and decodes the raw
#       data with a 1-byte window (a back-reference across calls fails: "invalid distance too far back").  After
#       inflateReset2() with the same windowBits (the window is freed only when wbits changes: it is kept), the
#       next zlib or gzip header sets wbits to its size without reallocating the window, and updatewindow() copies
#       up to 32 KiB into the 1-byte window (heap overflow; F6).  Fix: the raw stream gets the largest
#       window, `if (state->wbits == 0) state->wbits = 15;`, as inflate() does for a gzip header (which carries no
#       window size).  Then wbits == 0 holds only while no window is allocated, which every use of wbits assumes.
#   F7  inflate.c, HEAD (zlib header): state->wbits = len was stored before the `len > 15` check, so a header whose
#       CINFO asks for a window > 32 KiB (len 16..23) left wbits out of range although the header is rejected
#       ("invalid window size"); inflateReset() keeps wbits (restored only when windowBits changes), so a later
#       stream uses a window of 1U << wbits and dmax = 1U << len above zlib's 32 KiB maximum (F7).
#       Fix: validate len before storing it (test, then `if (state->wbits == 0) state->wbits = len;`), so wbits <= 15
#       is an invariant.  Every accepted header is unchanged.
#   F8  inflate.c, inflateReset2()/inflateReset()/inflateSync(), inflate.h (a comment): with windowBits 0, 16 or 32 the
#       window size comes from the header, which overwrites state->wbits (the request, 0); inflateReset() kept the
#       size of the previous stream, so a reset stream whose header asks for a larger window was rejected ("invalid
#       window size") and one asking for a smaller window decoded with the larger one (F8).  Fix
#       without a new field: bit 3 of state->wrap records the request (inflateReset2); inflateReset() then restores
#       wbits = 0 and frees the window (with wbits 0 no window may be allocated: F6).  inflateSync() calls
#       inflateReset() for a stream that goes on: it hides bit 3 from that call, so the stream keeps its window
#       size and its window as before.  Only streams reset after a header set their window size behave differently.
#   F9  deflate.c, deflate_stored(): the comparisons of len with `left + s->strm->avail_in` computed the sum in 32 bits
#       (two of them; the first casts to ulg): on a Z_FINISH call with more than 2^32 - 1 bytes of window and input
#       together it wraps, and a block of the wrapped length is written as the last one with input unread
#       (compress2_z() into compressBound_z() bytes returns Z_BUF_ERROR for inputs over 51 TiB at level 0; a direct
#       raw deflate(Z_FINISH) with about 4 GiB of input returns Z_STREAM_END with it unread; F9).
#       Fix, as offered upstream: `(z_size_t)left + ...` in all three (ulg is 32 bits on LLP64 systems).
#
#   D1  DEVIATION (2026-10-11): the 11 struct assignments of `code` values, 4 in inftrees.c
#       (inflate_table: exactly our earlier proof's deviation, text included, so that its proof of inflate_table
#       can be reused) and 7 in inflate.c (inflate(): `here = state->lencode[...]`, `last = here`,
#       `here = state->distcode[...]`), are written member by member (op, bits, val).  VST's floyd logic has no rule
#       for a struct assignment.  `code` is {uchar op; uchar bits; ushort val}, 4 bytes, no padding; every member of
#       the source is defined; source and target never overlap (`here`/`last` are locals); the index expressions
#       read nothing the member stores change.  Same bytes, different object code: checked by patch/difftest.sh.
#       To be dropped if the framework gets a struct-assignment rule.
#   D2  DEVIATION (2026-10-15; same kind as D1): deflateParams() decides whether to
#       flush by comparing the compressor function pointers `configuration_table[s->level].func` and
#       `configuration_table[level].func`.  VST's Floyd logic cannot prove the three function globals
#       (deflate_stored/fast/slow) have distinct addresses (function globals own no memory; the run refuted
#       `semax_gv_distinct` for Floyd's semax), so deflate_api and deflate_roundtrip were not derivable.  D2 compares
#       the compressor's kind instead, DEFLATE_KIND(l) = 0 for level 0 (stored), 1 for 1-3 (fast), 2 for 4-9 (slow),
#       which is configuration_table's mapping (and also right with FASTEST, levels 0 and 1).  Distinct functions have
#       distinct addresses (C11 6.5.9p6), so the test has the same value on every implementation: same behaviour.
#       Only deflateParams' Clight changes; the macro adds no global.

import re
import sys


def code_only(text):
    """The text without comments."""
    return re.sub(r'/\*.*?\*/', ' ', text, flags=re.S)


def rep(text, old, new, cnt=1):
    n = text.count(old)
    assert n == cnt, (old[:80], n, cnt)
    return text.replace(old, new)


def edit(path, fn):
    s = open(path).read()
    s = fn(s)
    open(path, 'w').write(s)


# ---------------------------------------------------------------------------------------------- I1 include guards

def inftrees_h(s):
    # exactly the include guard of our earlier proof of inflate_table
    s = rep(s, '''/* Structure for decoding tables.''', '''#ifndef QUICKPROOF_INFTREES_H   /* quickproof: (no include guard) */
#define QUICKPROOF_INFTREES_H   /* quickproof: (no include guard) */

/* Structure for decoding tables.''')
    return s + '''
#endif /* QUICKPROOF_INFTREES_H: quickproof: (no include guard) */
'''


def guard(name):
    def f(s):
        return ('#ifndef %s   /* quickproof: (no include guard) */\n#define %s   /* quickproof: (no include guard) */\n'
                % (name, name)) + s + '\n#endif /* %s: quickproof: (no include guard) */\n' % name
    return f


# ---------------------------------------------------------------------------------------------- I2 inftrees.c

def inftrees(s):
    return rep(s, '''    case DISTS:
        base = dbase;
        extra = dext;
    }
''', '''    case DISTS:
        base = dbase;
        extra = dext;
        break;          /* quickproof: (no break: the last case fell off the end of the switch) */
    }
''')


def deflate_c(s):
    s = rep(s, '''    default:                                /* for compiler happiness */
        wraplen = 18;
    }''', '''    default:                                /* for compiler happiness */
        wraplen = 18;
        break;          /* quickproof: (no break: the last case fell off the end of the switch) */
    }''')
    # I5
    return rep(s, '''        deflateEnd (strm);
        return Z_MEM_ERROR;
    }
#ifdef LIT_MEM
    s->d_buf = (ushf *)(s->pending_buf + (s->lit_bufsize << 1));''', '''        deflateEnd (strm);
        return Z_MEM_ERROR;
    }
    zmemzero((Bytef *)s->prev, (unsigned)(s->w_size * sizeof(Pos)));  /* quickproof: (new: slide_hash reads all of prev) */
#ifdef LIT_MEM
    s->d_buf = (ushf *)(s->pending_buf + (s->lit_bufsize << 1));''')


def deflate_h(s):
    # I6 (the const declarations: deflate.h's GEN_TREES_H variant is not compiled)
    return rep(s, '''  extern const uch ZLIB_INTERNAL _length_code[];
  extern const uch ZLIB_INTERNAL _dist_code[];''', '''  extern const uch ZLIB_INTERNAL _length_code[256];  /* quickproof: extern const uch ZLIB_INTERNAL _length_code[]; */
  extern const uch ZLIB_INTERNAL _dist_code[512];    /* quickproof: extern const uch ZLIB_INTERNAL _dist_code[]; */''')


def zutil_c(s):
    for k in ('3;', '3 << 2;', '3 << 4;', '3 << 6;'):
        s = rep(s, '''    default:    flags += %s
    }''' % k, '''    default:    flags += %s
                break;  /* quickproof: (no break: the last case fell off the end of the switch) */
    }''' % k)
    return s


# ---------------------------------------------------------------------------------------------- D1 struct copies

def fieldcopy_inftrees(s):
    # exactly the deviation of our earlier proof of inflate_table (its field copy)
    s = rep(s, '''        *(*table)++ = here;             /* make a table to force an error */
        *(*table)++ = here;
''', '''        (*table)->op = here.op;         /* quickproof: *(*table)++ = here;  (make a table to force an error) */
        (*table)->bits = here.bits;     /* quickproof: (struct copy, field by field) */
        (*table)->val = here.val;       /* quickproof: (struct copy, field by field) */
        (*table)++;                     /* quickproof: (struct copy, field by field) */
        (*table)->op = here.op;         /* quickproof: *(*table)++ = here; */
        (*table)->bits = here.bits;     /* quickproof: (struct copy, field by field) */
        (*table)->val = here.val;       /* quickproof: (struct copy, field by field) */
        (*table)++;                     /* quickproof: (struct copy, field by field) */
''')
    s = rep(s, '''            next[(huff >> drop) + fill] = here;
''', '''            next[(huff >> drop) + fill].op = here.op;      /* quickproof: next[(huff >> drop) + fill] = here; */
            next[(huff >> drop) + fill].bits = here.bits;  /* quickproof: (struct copy, field by field) */
            next[(huff >> drop) + fill].val = here.val;    /* quickproof: (struct copy, field by field) */
''')
    s = rep(s, '''        next[huff] = here;
''', '''        next[huff].op = here.op;        /* quickproof: next[huff] = here; */
        next[huff].bits = here.bits;    /* quickproof: (struct copy, field by field) */
        next[huff].val = here.val;      /* quickproof: (struct copy, field by field) */
''')
    return s


def copy3(indent, dst, src, orig):
    """dst = src (a `code` value) member by member, with the original in the first line's comment."""
    return ('%s%s.op = %s.op;  /* quickproof: %s */\n%s%s.bits = %s.bits;  /* quickproof: (struct copy, field by field) */\n'
            '%s%s.val = %s.val;  /* quickproof: (struct copy, field by field) */\n'
            % (indent, dst, src, orig, indent, dst, src, indent, dst, src))


def deflate_params_kind(s):
    # D2 (deviation): deflateParams() compares the compressors' kinds (by level) instead of their function pointers.
    s = rep(s, '''int ZEXPORT deflateParams(z_streamp strm, int level, int strategy) {
    deflate_state *s;
    compress_func func;
''', '''#define DEFLATE_KIND(l) ((l) == 0 ? 0 : (l) <= 3 ? 1 : 2)   /* quickproof: D2: the compressor of configuration_table[l] (stored/fast/slow) */
int ZEXPORT deflateParams(z_streamp strm, int level, int strategy) {
    deflate_state *s;
''')
    s = rep(s, '''    func = configuration_table[s->level].func;

    if ((strategy != s->strategy || func != configuration_table[level].func) &&
        s->last_flush != -2) {''', '''    if ((strategy != s->strategy || DEFLATE_KIND(s->level) != DEFLATE_KIND(level)) &&   /* quickproof: D2: was `func = configuration_table[s->level].func;` and `func != configuration_table[level].func` */
        s->last_flush != -2) {''')
    return s


def fieldcopy_inflate(s):
    i5, i4 = ' ' * 20, ' ' * 16
    # CODELENS
    s = rep(s, '''                    here = state->lencode[BITS(state->lenbits)];
                    if ((unsigned)(here.bits) <= bits) break;''',
            copy3(i5, 'here', 'state->lencode[BITS(state->lenbits)]', 'here = state->lencode[BITS(state->lenbits)];') +
            '''                    if ((unsigned)(here.bits) <= bits) break;''')
    # LEN and DIST
    for tab, nb in (('lencode', 'lenbits'), ('distcode', 'distbits')):
        s = rep(s, '''                here = state->%s[BITS(state->%s)];
                if ((unsigned)(here.bits) <= bits) break;''' % (tab, nb),
                copy3(i4, 'here', 'state->%s[BITS(state->%s)]' % (tab, nb),
                      'here = state->%s[BITS(state->%s)];' % (tab, nb)) +
                '''                if ((unsigned)(here.bits) <= bits) break;''')
        s = rep(s, '''                last = here;
                for (;;) {
                    here = state->%s[last.val +
                            (BITS(last.bits + last.op) >> last.bits)];''' % tab,
                copy3(i4, 'last', 'here', 'last = here;') + '''                for (;;) {
''' + copy3(i5, 'here', 'state->%s[last.val + (BITS(last.bits + last.op) >> last.bits)]' % tab,
            'here = state->%s[last.val + (BITS(last.bits + last.op) >> last.bits)];' % tab).rstrip('\n'))
    assert not re.search(r'\b(here|last)\s*=\s*(here|state->\w+\[)', code_only(s)), 'a struct copy is left in inflate.c'
    return s


# ---------------------------------------------------------------------------------------------- I3 inflate.c

LEAVE = '{ leave = 1; break; }'


def inflate_c(s):
    # the macros
    s = rep(s, '''#define PULLBYTE() \\
    do { \\
        if (have == 0) goto inf_leave; \\
        have--; \\
        hold += (unsigned long)(*next++) << bits; \\
        bits += 8; \\
    } while (0)''', '''#define PULLBYTE() \\
    { /* quickproof: do { */ \\
        if (have == 0) { leave = 1; break; } /* quickproof: if (have == 0) goto inf_leave; */ \\
        have--; \\
        hold += (unsigned long)(*next++) << bits; \\
        bits += 8; \\
    } /* quickproof: } while (0) */''')
    s = rep(s, '''#define NEEDBITS(n) \\
    do { \\
        while (bits < (unsigned)(n)) \\
            PULLBYTE(); \\
    } while (0)''', '''#define NEEDBITS(n) \\
    { /* quickproof: do { */ \\
        while (bits < (unsigned)(n)) \\
            PULLBYTE(); \\
        if (leave) break; /* quickproof: (the goto of PULLBYTE) */ \\
    } /* quickproof: } while (0) */''')
    # the flag
    s = rep(s, '''    int ret;                    /* return code */
#ifdef GUNZIP
    unsigned char hbuf[4];''', '''    int ret;                    /* return code */
    int leave = 0;              /* quickproof: (new: 1 = goto inf_leave) */
#ifdef GUNZIP
    unsigned char hbuf[4];''')
    # the main loop: a block with the exit test after the switch
    s = rep(s, '''    ret = Z_OK;
    for (;;)
        switch (state->mode) {
        case HEAD:''', '''    ret = Z_OK;
    for (;;) {                  /* quickproof: for (;;) */
        switch (state->mode) {
        case HEAD:''')
    s = rep(s, '''        default:
            return Z_STREAM_ERROR;
        }

    /*
       Return from inflate(), updating the total counts and the check value.
       If there was no progress during the inflate() call, return a buffer
       error.  Call updatewindow() to create and/or update the window state.
       Note: a memory error from inflate() is non-recoverable.
     */
  inf_leave:
    RESTORE();''', '''        default:
            return Z_STREAM_ERROR;
        }
        if (leave) break;       /* quickproof: (new: the goto inf_leave) */
    }                           /* quickproof: (new: end of the loop body) */

    /*
       Return from inflate(), updating the total counts and the check value.
       If there was no progress during the inflate() call, return a buffer
       error.  Call updatewindow() to create and/or update the window state.
       Note: a memory error from inflate() is non-recoverable.
     */
    /* quickproof: inf_leave: */
    RESTORE();''')
    # direct gotos at the top level of a case (a break leaves the switch)
    s = rep(s, '''                if (state->length) goto inf_leave;
''', '''                if (state->length) %s /* quickproof: goto inf_leave; */
''' % LEAVE)
    s = rep(s, '''                if (have == 0) goto inf_leave;
                copy = 0;
''', '''                if (have == 0) %s /* quickproof: goto inf_leave; */
                copy = 0;
''' % LEAVE, cnt=2)
    s = rep(s, '''                if (len) goto inf_leave;
''', '''                if (len) %s /* quickproof: goto inf_leave; */
''' % LEAVE, cnt=2)
    s = rep(s, '''            if (flush == Z_BLOCK || flush == Z_TREES) goto inf_leave;
''', '''            if (flush == Z_BLOCK || flush == Z_TREES) %s /* quickproof: goto inf_leave; */
''' % LEAVE)
    # TYPEDO: the goto inside the inner switch on the block type
    s = rep(s, '''                if (flush == Z_TREES) {
                    DROPBITS(2);
                    goto inf_leave;
                }
                break;
            case 2:                             /* dynamic block */''', '''                if (flush == Z_TREES) {
                    DROPBITS(2);
                    leave = 1;                  /* quickproof: goto inf_leave; */
                    break;                      /* quickproof: (new: leaves the inner switch) */
                }
                break;
            case 2:                             /* dynamic block */''')
    s = rep(s, '''                strm->msg = (z_const char *)"invalid block type";
                state->mode = BAD;
            }
            DROPBITS(2);
            break;''', '''                strm->msg = (z_const char *)"invalid block type";
                state->mode = BAD;
                break;          /* quickproof: (no break: the last case fell off the end of the switch) */
            }
            if (leave) break;                   /* quickproof: (new: the goto of case 1) */
            DROPBITS(2);
            break;''')
    s = rep(s, '''            if (flush == Z_TREES) goto inf_leave;
''', '''            if (flush == Z_TREES) %s /* quickproof: goto inf_leave; */
''' % LEAVE, cnt=2)
    s = rep(s, '''                if (copy == 0) goto inf_leave;
''', '''                if (copy == 0) %s /* quickproof: goto inf_leave; */
''' % LEAVE)
    # LENLENS: NEEDBITS inside a while
    s = rep(s, '''            while (state->have < state->ncode) {
                NEEDBITS(3);
                state->lens[order[state->have++]] = (unsigned short)BITS(3);
                DROPBITS(3);
            }
''', '''            while (state->have < state->ncode) {
                NEEDBITS(3);
                state->lens[order[state->have++]] = (unsigned short)BITS(3);
                DROPBITS(3);
            }
            if (leave) break;                   /* quickproof: (new: the goto of NEEDBITS in the loop) */
''')
    # CODELENS: PULLBYTE in a for inside a while, NEEDBITS inside the while
    s = rep(s, '''                for (;;) {
                    here = state->lencode[BITS(state->lenbits)];
                    if ((unsigned)(here.bits) <= bits) break;
                    PULLBYTE();
                }
                if (here.val < 16) {''', '''                for (;;) {
                    here = state->lencode[BITS(state->lenbits)];
                    if ((unsigned)(here.bits) <= bits) break;
                    PULLBYTE();
                }
                if (leave) break;               /* quickproof: (new: the goto of PULLBYTE in the loop) */
                if (here.val < 16) {''')
    s = rep(s, '''            /* handle error breaks in while */
            if (state->mode == BAD) break;
''', '''            /* handle error breaks in while */
            if (leave) break;                   /* quickproof: (new: the gotos of the loop) */
            if (state->mode == BAD) break;
''')
    # LEN and DIST: PULLBYTE in for loops
    for tab in ('lencode', 'distcode'):
        bitsname = 'lenbits' if tab == 'lencode' else 'distbits'
        s = rep(s, '''            for (;;) {
                here = state->%s[BITS(state->%s)];
                if ((unsigned)(here.bits) <= bits) break;
                PULLBYTE();
            }
''' % (tab, bitsname), '''            for (;;) {
                here = state->%s[BITS(state->%s)];
                if ((unsigned)(here.bits) <= bits) break;
                PULLBYTE();
            }
            if (leave) break;                   /* quickproof: (new: the goto of PULLBYTE in the loop) */
''' % (tab, bitsname))
        s = rep(s, '''                for (;;) {
                    here = state->%s[last.val +
                            (BITS(last.bits + last.op) >> last.bits)];
                    if ((unsigned)(last.bits + here.bits) <= bits) break;
                    PULLBYTE();
                }
''' % tab, '''                for (;;) {
                    here = state->%s[last.val +
                            (BITS(last.bits + last.op) >> last.bits)];
                    if ((unsigned)(last.bits + here.bits) <= bits) break;
                    PULLBYTE();
                }
                if (leave) break;               /* quickproof: (new: the goto of PULLBYTE in the loop) */
''' % tab)
    s = rep(s, '''            if (left == 0) goto inf_leave;
''', '''            if (left == 0) %s /* quickproof: goto inf_leave; */
''' % LEAVE, cnt=2)
    s = rep(s, '''        case DONE:
            ret = Z_STREAM_END;
            goto inf_leave;
        case BAD:
            ret = Z_DATA_ERROR;
            goto inf_leave;''', '''        case DONE:
            ret = Z_STREAM_END;
            leave = 1;                  /* quickproof: goto inf_leave; */
            break;                      /* quickproof: (new) */
        case BAD:
            ret = Z_DATA_ERROR;
            leave = 1;                  /* quickproof: goto inf_leave; */
            break;                      /* quickproof: (new) */''')
    assert not re.search(r'\bgoto\b|^\s*(?!default\b)\w+:\s*$', code_only(s), re.M), 'a goto or label is left in inflate.c'
    return s


def adler32_fix(s):
    s = rep(s, '''    /* in case user likes doing a byte at a time, keep it fast */
    if (len == 1) {''', '''    if (buf == Z_NULL)          /* quickproof: FIX F2 (new: before the one-byte path, which reads buf[0]) */
        return 1L;              /* quickproof: FIX F2 (new) */

    /* in case user likes doing a byte at a time, keep it fast */
    if (len == 1) {''')
    return s


def inflate_fix(s):
    return rep(s, '''            if (state->havedict == 0) {
                RESTORE();
                return Z_NEED_DICT;
            }''', '''            if (state->havedict == 0) {
                RESTORE();
                strm->total_in += in - strm->avail_in;  /* quickproof: FIX F1 (new: count the bytes read) */
                return Z_NEED_DICT;
            }''')


def inflate_fast_guard(s):
    # F4: enter inflate_fast only when fewer than 8 bits are buffered, so that its final
    # `in -= bits >> 3` ("on entry, bits < 8, so in won't go too far back", inffast.c) cannot move next_in
    # before the start of the caller's input.  inflatePrime() may leave up to 32 bits buffered that were never
    # pulled from next_in; without this guard a primed fast-path entry rewinds next_in before the buffer,
    # overreads, and corrupts avail_in / total_in.  zlib never enters inflate_fast with 8+ bits buffered, and
    # when it does (after priming) the slow path decodes the same symbols with the same output: an equivalence
    # test over ~180000 random valid streams finds no observable difference.
    return rep(s, '''        case LEN:
            if (have >= 6 && left >= 258) {''', '''        case LEN:
            if (have >= 6 && left >= 258 && bits < 8) {  /* quickproof: FIX F4: if (have >= 6 && left >= 258) { */''')


def inflate_sync_window(s):
    # F6: inflateSync() makes a stream raw when no header was processed; with windowBits 0, 16 or
    # 32 (the window size from the header) wbits was still 0, so the raw stream's window was allocated with 1 byte
    # and a later inflateReset2() with the same windowBits kept it for a stream whose header then set wbits to 15
    # (heap overflow in updatewindow).  A raw stream gets the largest window, as inflate() gives a gzip stream.
    return rep(s, '''    if (state->flags == -1)
        state->wrap = 0;    /* if no header yet, treat as raw */
    else''', '''    if (state->flags == -1) {   /* quickproof: FIX F6: if (state->flags == -1) */
        state->wrap = 0;    /* if no header yet, treat as raw */
        if (state->wbits == 0)  /* quickproof: FIX F6 (new) */
            state->wbits = 15;  /* quickproof: FIX F6 (new: no header, so the largest window, as for gzip) */
    }                           /* quickproof: FIX F6 (new) */
    else''')


def inflate_head_wbits(s):
    # F7: inflate()'s zlib-header HEAD state assigned state->wbits = len before checking len <= 15,
    # so a header whose CINFO asks for a window > 32 KiB (len 16..23) left wbits out of range even though the header
    # is rejected ("invalid window size"); inflateReset() keeps wbits, so a later stream uses a window of 1U << wbits
    # (and dmax = 1U << len) above zlib's 32 KiB maximum.  Fix: validate len before storing it, so wbits <= 15 is an
    # invariant.  Every accepted header is unchanged (it has len <= 15, and with windowBits 0 wbits still becomes len).
    return rep(s, '''            if (state->wbits == 0)
                state->wbits = len;
            if (len > 15 || len > state->wbits) {
                strm->msg = (z_const char *)"invalid window size";
                state->mode = BAD;
                break;
            }''', '''            if (len > 15 || (state->wbits != 0 && len > state->wbits)) {  /* quickproof: FIX F7: test the size before storing it (was `if (state->wbits == 0) state->wbits = len;` then `if (len > 15 || len > state->wbits)`) */
                strm->msg = (z_const char *)"invalid window size";
                state->mode = BAD;
                break;
            }
            if (state->wbits == 0)  /* quickproof: FIX F7 (new: store wbits only after the size is validated, so wbits <= 15) */
                state->wbits = len;  /* quickproof: FIX F7 (new) */''')


def inflate_reset_window(s):
    # F8: with windowBits 0, 16 or 32 the window size comes from each stream's header, but
    # inflate()'s HEAD state overwrites state->wbits (the request, 0) with the size it found, and inflateReset() kept
    # it: after a stream with a small window, a reset stream whose header asks for a larger one was rejected
    # ("invalid window size"), and one asking for a smaller one decoded with the larger window.  Fix without a new
    # field of struct inflate_state: bit 3 of wrap (bits 0-2 are taken) records the request; inflateReset() then
    # restores wbits = 0 and frees the window (it may be too small for the next header; with wbits 0 no window may
    # be allocated, see F6).  inflateSync() calls inflateReset() but goes on decoding the same stream: it hides
    # bit 3 from that call, so its stream keeps its window size and its window, as before.
    s = rep(s, '''    /* update state and reset the rest of it */
    state->wrap = wrap;''', '''    /* update state and reset the rest of it */
    if (windowBits == 0)                /* quickproof: FIX F8 (new: bit 3 of wrap, the window size of each header) */
        wrap |= 8;                      /* quickproof: FIX F8 (new) */
    state->wrap = wrap;''')
    s = rep(s, '''int ZEXPORT inflateReset(z_streamp strm) {
    struct inflate_state FAR *state;

    if (inflateStateCheck(strm)) return Z_STREAM_ERROR;
    state = (struct inflate_state FAR *)strm->state;
''', '''int ZEXPORT inflateReset(z_streamp strm) {
    struct inflate_state FAR *state;

    if (inflateStateCheck(strm)) return Z_STREAM_ERROR;
    state = (struct inflate_state FAR *)strm->state;
    if (state->wrap & 8) {              /* quickproof: FIX F8 (new: the next header sets the window size again) */
        if (state->window != Z_NULL) {  /* quickproof: FIX F8 (new: the window may be too small for it) */
            ZFREE(strm, state->window); /* quickproof: FIX F8 (new) */
            state->window = Z_NULL;     /* quickproof: FIX F8 (new) */
        }                               /* quickproof: FIX F8 (new) */
        state->wbits = 0;               /* quickproof: FIX F8 (new) */
    }                                   /* quickproof: FIX F8 (new) */
''')
    s = rep(s, '''    int flags;                  /* temporary to save header status */
    unsigned long in, out;      /* temporary to save total_in and total_out */''', '''    int flags;                  /* temporary to save header status */
    int wrap;                   /* quickproof: FIX F8 (new: temporary to save the wrapper bits) */
    unsigned long in, out;      /* temporary to save total_in and total_out */''')
    s = rep(s, '''    flags = state->flags;
    in = strm->total_in;  out = strm->total_out;
    inflateReset(strm);
    strm->total_in = in;  strm->total_out = out;
    state->flags = flags;
''', '''    flags = state->flags;
    wrap = state->wrap;         /* quickproof: FIX F8 (new: the stream goes on with its window size) */
    state->wrap = wrap & ~8;    /* quickproof: FIX F8 (new: hide bit 3 from inflateReset()) */
    in = strm->total_in;  out = strm->total_out;
    inflateReset(strm);
    strm->total_in = in;  strm->total_out = out;
    state->flags = flags;
    state->wrap = wrap;         /* quickproof: FIX F8 (new) */
''')
    return s


def inflate_h_wrap(s):
    # F8: the meaning of bit 3 of wrap, where the field is declared (a comment: no change of the Clight)
    return rep(s, '''    int wrap;                   /* bit 0 true for zlib, bit 1 true for gzip,
                                   bit 2 true to validate check value */
''', '''    int wrap;                   /* bit 0 true for zlib, bit 1 true for gzip,
                                   bit 2 true to validate check value */
                                /* quickproof: FIX F8 (new): bit 3 true if the window size comes from the header */
''')


def deflate_stored_sum(s):
    # F9: deflate_stored() compares len with the window bytes plus the input, `left +
    # s->strm->avail_in`, in three places; the first casts to ulg, the other two add in 32-bit unsigned arithmetic.
    # On a Z_FINISH call with more than 2^32 - 1 bytes of window and input together the sum wraps, and when the
    # block that fits in avail_out has exactly the wrapped length it is written as the last one with input unread:
    # compress2_z() into compressBound_z() bytes returns Z_BUF_ERROR (sizes over 51 TiB at level 0), and a direct
    # raw deflate(Z_FINISH) with about 4 GiB of input returns Z_STREAM_END with that input unread.  Fix (the patch
    # offered upstream): the three sums in z_size_t (ulg is 32 bits on LLP64 systems such as 64-bit Windows, where
    # the existing (ulg) cast does not prevent the wrap).  Every sum below 2^32 compares as before.
    s = rep(s, '''        if (len > (ulg)left + s->strm->avail_in)''', '''        if (len > (z_size_t)left + s->strm->avail_in)  /* quickproof: FIX F9: if (len > (ulg)left + s->strm->avail_in) */''')
    s = rep(s, '''                                len != left + s->strm->avail_in))''', '''                                len != (z_size_t)left + s->strm->avail_in))  /* quickproof: FIX F9: len != left + s->strm->avail_in)) */''')
    s = rep(s, '''        last = flush == Z_FINISH && len == left + s->strm->avail_in ? 1 : 0;''', '''        last = flush == Z_FINISH &&    /* quickproof: FIX F9: last = flush == Z_FINISH && len == left + s->strm->avail_in ? 1 : 0; */
               len == (z_size_t)left + s->strm->avail_in ? 1 : 0;  /* quickproof: FIX F9 (new line) */''')
    return s


def deflate_fix(s):
    s = rep(s, '''    if (s->w_bits != 15 || s->hash_bits != 8 + 7) {''', '''    if (s->w_bits != 15 || s->hash_bits != 8 + 7 ||  /* quickproof: FIX F3: if (s->w_bits != 15 || s->hash_bits != 8 + 7) { */
        (s->strategy == Z_FIXED && s->level >= 1 && s->level <= 3)) {  /* quickproof: FIX F3 (new) */''')
    s = rep(s, '''#define FLUSH_BLOCK(s, last) { \\
   FLUSH_BLOCK_ONLY(s, last); \\
   if (s->strm->avail_out == 0) return (last) ? finish_started : need_more; \\
}''', '''#define FLUSH_BLOCK(s, last) { \\
   FLUSH_BLOCK_ONLY(s, last); \\
   if (s->strm->avail_out == 0 && /* quickproof: FIX F5: if (s->strm->avail_out == 0) return (last) ? finish_started : need_more; */ \\
       (!(last) || s->pending != 0 || s->wrap != 0)) /* quickproof: FIX F5 (new, madler/zlib PR #1326) */ \\
       return (last) ? finish_started : need_more;   /* quickproof: FIX F5 (moved) */ \\
}''')
    return s


# ---------------------------------------------------------------------------------------------- I4 inffast.c

def inffast(s):
    s = rep(s, '''        here = lcode + (hold & lmask);
      dolen:
        op = (unsigned)(here->bits);
        hold >>= op;
        bits -= op;
        op = (unsigned)(here->op);
        if (op == 0) {                          /* literal */''', '''        here = lcode + (hold & lmask);
        for (;;) {                              /* quickproof: dolen: */
            op = (unsigned)(here->bits);
            hold >>= op;
            bits -= op;
            op = (unsigned)(here->op);
            if (op == 0 || (op & 16) || (op & 64))  /* quickproof: (new: not a link) */
                break;                          /* quickproof: (new) */
            here = lcode + here->val + (hold & ((1U << op) - 1));  /* quickproof: (moved: 2nd level length code) */
        }                                       /* quickproof: (new) */
        if (op == 0) {                          /* literal */''')
    s = rep(s, '''            here = dcode + (hold & dmask);
          dodist:
            op = (unsigned)(here->bits);
            hold >>= op;
            bits -= op;
            op = (unsigned)(here->op);
            if (op & 16) {                      /* distance base */''', '''            here = dcode + (hold & dmask);
            for (;;) {                          /* quickproof: dodist: */
                op = (unsigned)(here->bits);
                hold >>= op;
                bits -= op;
                op = (unsigned)(here->op);
                if ((op & 16) || (op & 64))     /* quickproof: (new: not a link) */
                    break;                      /* quickproof: (new) */
                here = dcode + here->val + (hold & ((1U << op) - 1));  /* quickproof: (moved: 2nd level distance code) */
            }                                   /* quickproof: (new) */
            if (op & 16) {                      /* distance base */''')
    s = rep(s, '''            else if ((op & 64) == 0) {          /* 2nd level distance code */
                here = dcode + here->val + (hold & ((1U << op) - 1));
                goto dodist;
            }
            else {''', '''            /* quickproof: else if ((op & 64) == 0) { here = dcode + ...; goto dodist; }  (moved into the loop) */
            else {''')
    s = rep(s, '''        else if ((op & 64) == 0) {              /* 2nd level length code */
            here = lcode + here->val + (hold & ((1U << op) - 1));
            goto dolen;
        }
        else if (op & 32) {''', '''        /* quickproof: else if ((op & 64) == 0) { here = lcode + ...; goto dolen; }  (moved into the loop) */
        else if (op & 32) {''')
    assert not re.search(r'\bgoto\b|^\s*(?!default\b)\w+:\s*$', code_only(s), re.M), 'a goto or label is left in inffast.c'
    return s


if __name__ == '__main__':
    fix = '--no-fix' not in sys.argv[1:]
    edit('inftrees.h', inftrees_h)
    edit('inflate.h', guard('QUICKPROOF_INFLATE_H'))
    edit('inftrees.c', inftrees)
    edit('inftrees.c', fieldcopy_inftrees)
    edit('deflate.c', deflate_c)
    edit('deflate.h', deflate_h)
    edit('zutil.c', zutil_c)
    edit('inflate.c', inflate_c)
    edit('inflate.c', fieldcopy_inflate)
    edit('deflate.c', deflate_params_kind)
    if fix:
        edit('inflate.c', inflate_fix)
        edit('inflate.c', inflate_fast_guard)
        edit('inflate.c', inflate_sync_window)
        edit('inflate.c', inflate_head_wbits)
        edit('inflate.c', inflate_reset_window)
        edit('inflate.h', inflate_h_wrap)
        edit('adler32.c', adler32_fix)
        edit('deflate.c', deflate_fix)
        edit('deflate.c', deflate_stored_sum)
    edit('inffast.c', inffast)
