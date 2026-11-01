# Edits to zlib 1.3.2

`patch/zlibpatch.py` makes these edits to zlib 1.3.2 (`da607da739fa`); the C files at the root of the repository
are its output, and every changed line keeps the original in a `quickproof:` comment. The idiom edits I1-I6 and
the deviations D1 and D2 are meant to change no behaviour; this is tested, not proved (see
[Differential test](#differential-test)). The fixes F1-F9 each change zlib's behaviour only in the case their
section below describes. `--no-fix` applies I1-I6, D1 and D2 only (`patch/difftest.sh` uses it).

Spec names below are those of this repository. The comments of `zlibpatch.py` use the older names without `x_`
(`deflate_api` for `x_deflate_api`).

## Idiom edits

### I1: include guards (`inftrees.h`, `inflate.h`)

Change: include guards `QUICKPROOF_INFTREES_H` and `QUICKPROOF_INFLATE_H`.

Why: `quickproof/tools/interp.sh` compiles the units and a spec as one translation unit for CompCert's
interpreter, where `code`, `codetype`, `inflate_mode` and `struct inflate_state` would be defined twice. clightgen
and compilers see each unit separately, so neither the generated Clight nor the object code changes.

### I2: `break;` at the end of seven switches (`inftrees.c`, `inflate.c`, `deflate.c`, `zutil.c`)

Change: `break;` after the last case of the seven switches whose last case falls off the end of the switch body:
`inflate_table`'s `switch (type)`, `inflate()`'s `switch (BITS(2))` (block type), `deflateBound`'s wrapper-length
switch, and the four switches of `zlibCompileFlags`.

Why: VST's switch rule cannot prove a switch whose last case can fall off the end (the normal postcondition of
`switch_ret_assert` is `FF`). C (6.8.4.2, 6.8.6.3) and CompCert define both forms identically. `qp lint` flags
them.

### I3: the `goto inf_leave`s of `inflate()` (`inflate.c`)

Change: the 14 direct `goto inf_leave`s and the one in `PULLBYTE`, expanded at 23 sites (5 `PULLBYTE`, 18
`NEEDBITS`). Each goto becomes `leave = 1; break;` (a new local `int leave = 0`), and `if (leave) break;` follows
every loop or inner switch such a break leaves: the LENLENS and CODELENS loops, the code-reading `for (;;)` loops of
CODELENS, LEN and DIST, and the block-type switch of TYPEDO. The main loop's body is now
`switch (state->mode) {...} if (leave) break;`, so a break reaches the code after the loop, where the label
`inf_leave` was. `PULLBYTE` and `NEEDBITS` become blocks instead of `do { } while (0)` (whose loop would catch the
break); every use is a statement of its own (no `if (..) NEEDBITS(..); else`).

Why: VST has no rule for `goto`.

### I4: the backward gotos of `inflate_fast()` (`inffast.c`)

Change: the backward `goto dolen` and `goto dodist` (second-level table entries). The table walk
(`op = here->bits; hold >>= op; bits -= op; op = here->op;`) is a `for (;;)` that ends when the entry is not a link
(length table: `op == 0 || (op & 16) || (op & 64)`; distance table: `(op & 16) || (op & 64)`), with the link step
`here = lcode + here->val + (hold & ((1U << op) - 1))` inside it. The `else if ((op & 64) == 0)` link branches of
the if/else chains after it are removed, since they can no longer be taken. The conditions are the negations of the
original chains' paths to the gotos, in the same order.

Why: VST has no rule for `goto`.

### I5: `prev` cleared in `deflateInit2_()` (`deflate.c`)

Change: `zmemzero(s->prev, w_size * sizeof(Pos))` after the allocations succeed.

Why: `slide_hash()` reads every entry of `s->prev`, also those never written ("If n is not on any hash chain,
prev[n] is garbage but its value will never be used"). Reading uninitialised memory gives `Vundef` in CompCert, and
`m >= wsize` on it is stuck: `qp interp` stopped there on spec `x_deflate_api` ("Stuck state: in function
slide_hash, expression <loc m> = <undef>"). The garbage values are never used, so the compressed output is
unchanged (the differential test compares it byte for byte).

### I6: array sizes in two extern declarations (`deflate.h`)

Change: the extern declarations `_length_code[]` and `_dist_code[]` get their sizes `[256]` and `[512]`, as
`trees.h` defines them.

Why: deflate.c's Clight declares an incomplete array (`tarray tuchar 0`) where trees.c defines `tarray tuchar 256`
and `512`. VST's linker QPlink refuses two types for one global ("Gvar type/readonly/volatile clash"), so the
contracts of the deflate specs did not build. The size in an extern declaration does not change the object code
(checked: deflate.o and trees.o byte-identical with and without, gcc -O2 and ccomp).

## Deviations

### D1: struct assignments of `code` values written member by member (`inftrees.c`, `inflate.c`)

Change: the 11 struct assignments of `code` values are written member by member (op, bits, val): four in
`inflate_table` (`*(*table)++ = here` twice, `next[...] = here` twice), and in `inflate()` `here =
state->lencode[i]` (CODELENS, LEN), `last = here` and `here = state->lencode[last.val + ...]` (LEN), and the same
for `distcode` (DIST). The patched `inftrees.c` and `inftrees.h` are those of our earlier proof of `inflate_table`,
so its proof can be reused.

Why: VST's Floyd logic has no rule for a struct assignment (Clight `Sassign` of a `By_copy` type). `code` is 4
bytes with no padding; every member of the source is defined; source and target never overlap (`here` and `last`
are locals; `inflate()` does not write the table); the index expressions read nothing the member stores write
(`hold`, `state->lenbits`, `last`), so the three loads read one entry. The same bytes are written but the object
code differs: the differential test checks it (the idiom-patched build includes D1). To be dropped if QuickProof
gets a struct-assignment rule.

### D2: `deflateParams` compares the compressors' kinds (`deflate.c`)

Change: the flush test compares the compressors' kinds, `DEFLATE_KIND(s->level) != DEFLATE_KIND(level)` with
`DEFLATE_KIND(l) = l == 0 ? 0 : l <= 3 ? 1 : 2`, instead of the function pointers
`configuration_table[s->level].func != configuration_table[level].func` (the local `func` goes).

Why: VST's Floyd logic cannot prove the three function globals `deflate_stored`, `deflate_fast` and
`deflate_slow` distinct (function globals own no memory), and with aliased addresses every compressor
specification reaches undefined behaviour, so `x_deflate_api` and `x_deflate_roundtrip` were not derivable.
`DEFLATE_KIND` is `configuration_table`'s mapping (0 stored, 1-3 fast, 4-9 slow; also right with `FASTEST`), and
distinct functions have distinct addresses (C11 6.5.9p6), so the test has the same value on every implementation.
Only `deflateParams`' Clight changes; the macro adds no global. To be dropped if QuickProof gives `main` the
distinctness of function globals.

## Fixes

### F1: `total_in` on `Z_NEED_DICT` (`inflate.c`, `inflate()`, state `DICT`)

Change: `strm->total_in += in - strm->avail_in;` before `return Z_NEED_DICT;`.

Why: the return skips the common exit that adds the bytes read in the call to `total_in`; `total_in` then stays 6
bytes short for the rest of the stream. `x_inflate_buffers` states `total_in` exactly, so it fails without the fix.

### F2: `adler32_z` with a `Z_NULL` buffer (`adler32.c`)

Change: `if (buf == Z_NULL) return 1L;` moved before the one-byte fast path.

Why: `adler32(x, Z_NULL, 1)` reads `buf[0]` (a null-pointer read; the `Z_NULL` test comes after the `len == 1`
path), although zlib.h says a `Z_NULL` buffer returns the initial value. `x_adler32_ref` states the documented
result for any length. Every call with a non-null buffer gives the same result as before.

### F3: `deflateBound()` for `Z_FIXED` at levels 1-3 (`deflate.c`, `deflateBound_z()`)

Change: the tight bound of windowBits 15 and memLevel 8 is not returned for `strategy == Z_FIXED` at levels 1-3:
the condition `s->w_bits != 15 || s->hash_bits != 8 + 7` of the conservative bounds gets
`|| (s->strategy == Z_FIXED && s->level >= 1 && s->level <= 3)` (then `fixedlen`, since `w_bits <= hash_bits`).

Why: `x_deflate_bound` and `x_deflate_bound_split` need `deflateBound()` to be an upper bound in this case. Only
`deflateBound()`'s value changes, for this case only.

### F4: `inflate_fast` entry (`inflate.c`, `inflate()`, state `LEN`)

Change: `if (have >= 6 && left >= 258)` becomes `if (have >= 6 && left >= 258 && bits < 8)`: `inflate_fast` is
entered only when fewer than 8 bits are buffered.

Why: `inflate_fast()` assumes fewer than 8 bits buffered on entry ("on entry, bits < 8", `inffast.c`), and after
`inflatePrime()` there may be more. `x_inflate_buffers` states how `next_in`, `avail_in` and `total_in` move, and
holds only with the fix. For 8 or more buffered bits the slow path decodes the same symbols with the same output
(equivalence test over about 180000 random valid streams: no observable difference). zlib enters `inflate_fast`
with 8 or more bits buffered only after `inflatePrime`, so streams that do not prime are unaffected.

### F5: `Z_STREAM_END` when the last block exactly fills the output (`deflate.c`, `FLUSH_BLOCK`)

Change: `if (s->strm->avail_out == 0)` becomes
`if (s->strm->avail_out == 0 && (!(last) || s->pending != 0 || s->wrap != 0))` before
`return (last) ? finish_started : need_more;`, as madler/zlib PR #1326.

Why: known upstream (#1300) and fixed there by PR #1326. When the last block of a raw stream exactly fills the
output space, `deflate()` returned `Z_OK` although the stream is complete (and the next call `Z_STREAM_END` without
output). zlib.h guarantees `Z_STREAM_END` for one `deflate(Z_FINISH)` into `deflateBound()` bytes, and some inputs
meet the tight bound exactly (`x_deflate_bound`). Now the `deflate_*` functions go on to return `finish_done` and
`deflate()` returns `Z_STREAM_END`. Only the return code of that call changes: the output is the same, and later
calls return what they returned before (`Z_STREAM_END` for `Z_FINISH`, `Z_STREAM_ERROR` for other flush values,
`Z_BUF_ERROR` without output space).

### F6: the window size of a stream that `inflateSync()` makes raw (`inflate.c`, `inflateSync()`)

Change: when no header was processed (`state->flags == -1`), the stream that `inflateSync` makes raw also gets a
window size: `if (state->wbits == 0) state->wbits = 15;` after `state->wrap = 0;`.

Why: with windowBits 0, 16 or 32 (the window size from the zlib or gzip header), `wbits` is 0 until a header sets
it, and the rest of `inflate.c` assumes that no window is allocated while it is 0. A stream that `inflateSync()`
makes raw never gets a header, so the edit gives it the largest window, as `inflate()` does for a gzip header (which
has no window size); `wbits == 0` again implies no window. `x_inflate_buffers` needs the fix. Only streams that
`inflateSync` made raw with windowBits 0, 16 or 32 behave differently: their window has 32 KiB.

### F7: the window size of a zlib header checked before it is stored (`inflate.c`, `inflate()`, state `HEAD`)

Change: `if (len > 15 || (state->wbits != 0 && len > state->wbits))` rejects the header ("invalid window size"),
and only then `if (state->wbits == 0) state->wbits = len;` (was: store, then `if (len > 15 || len > state->wbits)`).

Why: with the check first, `wbits <= 15` always holds. `x_inflate_buffers` needs the fix. Every accepted header is
handled as before (it has `len <= 15`, and with windowBits 0 `wbits` still becomes `len`). `patch/difftest.sh` has
no switch that hides F7.

### F8: `inflateReset()` forgets a window size that a header set (`inflate.c`, `inflate.h`)

Change: `inflateReset2()` sets bit 3 of `state->wrap` when windowBits asks for the window size of the header (0, 16
or 32: `if (windowBits == 0) wrap |= 8;`). `inflateReset()` then frees the window and sets `wbits = 0`
(`if (state->wrap & 8) { if (state->window != Z_NULL) { ZFREE(strm, state->window); state->window = Z_NULL; }
state->wbits = 0; }`). `inflateSync()`, which calls `inflateReset()` for a stream that goes on, hides bit 3 from
that call (`wrap = state->wrap; state->wrap = wrap & ~8;` before it, `state->wrap = wrap;` after it). `inflate.h`
documents bit 3 next to bits 0-2 of `wrap`.

Why: with windowBits 0, 16 or 32, `wbits` is 0 until a header sets it to the stream's window size, and
`inflateReset()` kept that size, so a reset stream did not behave like a new one. zlib.h: `inflateReset()` "is
equivalent to inflateEnd followed by inflateInit ... The stream will keep attributes that may have been set by
inflateInit2"; `api_reset` states it. The fix needs one bit of memory across the reset (was the size requested or
found?). Bits 0-2 of `wrap` are taken (zlib, gzip, check), bit 3 was free, and every test of `wrap` (`== 0`,
`!= 0`, `& 1`, `& 2`, `& 4`, `|= 4`, `&= ~4`, `= 0`) gives the same result with it, so `struct inflate_state` keeps
its layout. The window is freed because the next header may need a larger one, and with `wbits == 0` no window may
be allocated (F6). Hiding bit 3 from the `inflateReset()` call of `inflateSync()` keeps that function's behaviour
exactly as before, window included. `inflateResetKeep()` (undocumented; keeps the window) is unchanged. Only streams
reset by `inflateReset()` after a header set their window size behave differently: like a new stream.

### F9: a 64-bit sum in `deflate_stored()` (`deflate.c`)

Change: the three comparisons of `len` with `left + s->strm->avail_in` compute the sum in `z_size_t`:
`len > (z_size_t)left + s->strm->avail_in` (was `(ulg)left`), `len != (z_size_t)left + s->strm->avail_in` and
`len == (z_size_t)left + s->strm->avail_in` (were 32-bit sums), as the patch offered upstream.

Why: found by a proof attempt of `res_compress_bound`, reported as madler/zlib#1348 and fixed upstream in
`2bed3d61`. `left` (window bytes not yet emitted) and `avail_in` are `unsigned`, and two of the comparisons added
them in 32 bits. On a `Z_FINISH` call where `left + avail_in` exceeds 2^32 - 1 the sum wraps, and when the block
that fits in `avail_out` has exactly the wrapped length, it is written as the last block while input is still
unread. Through `compress2_z()` (input in pieces of `(uInt)-1` bytes) this happens for some inputs over 51 TiB at
level 0 (56298431302699, 112592567638099, 168886703973499 bytes): `compress2_z()` into `compressBound_z()` bytes
returns `Z_BUF_ERROR`, so `res_compress_bound` is false without the fix. With direct `deflate()` calls it takes
about 4 GiB: raw, level 0, 10000 bytes kept in the window by `deflate(Z_NO_FLUSH)`, then `deflate(Z_FINISH)` with
`avail_in` 4294957396 and `avail_out` 105 returns `Z_STREAM_END` with all of that input unread. `z_size_t` rather
than `ulg`: `unsigned long` is 32 bits on LLP64 systems (64-bit Windows), where the existing `(ulg)` cast does not
prevent the wrap either. Here `z_size_t` and `ulg` are both `unsigned long` (64 bits): the generated Clight
changes only in the two 32-bit sums, and the object code is that of `(ulg)` casts (gcc -O0, -O2 and ccomp:
identical `deflate.o`). Checked on this code: the three sizes return `Z_OK` (a size-only run) and the direct case
reads all input. Every sum below 2^32 compares as before.

## Not an edit: `patch/interp_unity.c`

`patch/interp_unity.c` includes the ten zlib files in one unit, used only under CompCert's interpreter
(`quickproof.conf` lists it in `INTERP_UNITS`, which only `interp.sh` reads), because `interp.sh` renames the
struct tags that a unit's .c file defines (`struct static_tree_desc_s` of trees.c), which breaks deflate.h's
typedef of it.

## Differential test

Run it from the repository root with `ORIG` set to an unmodified zlib 1.3.2 tree:
`ORIG=<tree> patch/difftest.sh` (optional: `N`, the cases per seed, default 1500; `SEEDS`, default "1 2 3"). It
needs python3 and gcc with AddressSanitizer and UndefinedBehaviorSanitizer; it also uses CompCert's `ccomp` when
it is on the `PATH`.

The script builds `patch/difftest_drv.c` three times: against the unmodified zlib, against the idiom-patched zlib
(`zlibpatch.py --no-fix`) and against the patched zlib of this repository, each with gcc -O2, gcc -O1 with
ASan/UBSan, and ccomp. For each case the driver makes a stream with zlib's deflate from random data and random
parameters (zlib/gzip/raw, any level, strategy, memLevel, window, dictionary, gzip header, flushes of every kind,
deflateParams), or random bytes, or a header and random bytes; mutates it or not; and inflates it with a random
windowBits, a random split of input and output over the calls, random flush values, and between the calls
inflateGetHeader, inflateSetDictionary (right, wrong, raw), inflateGetDictionary, inflatePrime, inflateSync,
inflateMark, inflateCodesUsed, inflateSyncPoint, inflateReset(2) and inflateValidate. It prints every observable
after every call (return code, stream fields, output bytes, header fields and buffers, dictionary).

1. Unmodified against idiom-patched: the outputs must be byte-identical (the idiom edits change nothing).
2. Idiom-patched against patched, with `total_in` hidden after a `Z_NEED_DICT`
   (`GP_NO_TOTAL_IN_AFTER_NEED_DICT=1`): byte-identical (F1 changes nothing else; F2 only matters for adler32 with a
   `Z_NULL` buffer and length 1, which the driver, like zlib itself, never does). Without hiding `total_in`, they
   differ exactly when some stream returned `Z_NEED_DICT`.
3. F3, F4, F5 and F6 are shown one at a time with the others hidden (`GP_HIDE_DEFLATE_FIXES`, `GP_HIDE_F4`,
   `GP_HIDE_F6`): each changes the output exactly in its own cases. F4 and F6 have deterministic probes that run in
   every case (`inflateprime_probe`, `sync_window_probe`). Every run sets `GP_NO_F6_SYNC=1`: the driver does not
   call inflateSync while the stream's windowBits takes the window size from the header, since on the unmodified
   code that path is F6's case, where no comparison is possible.

The driver also prints every compressed stream that zlib's deflate made, so deflate's behaviour (I2, I5) is
compared too. F7, F8 and F9 have no switch: F7 and F8 change the window size only around a reset after a header
(the driver resets and then decodes the same stream again, so they rarely show), and F9 needs about 4 GiB of input
in one call. F8 was compared on its own: the driver, built against the code before F8 and F9 (F1-F7) and after
(F1-F9), with gcc -O2 and gcc -O1 with ASan/UBSan, with and without `GP_NO_F6_SYNC`, prints the same bytes (seeds
1-6, 1500 cases each).
