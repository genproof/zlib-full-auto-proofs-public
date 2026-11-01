# zlib: proved C specs

This repository proves 62 specs of the core of zlib 1.3.2 with
[QuickProof](https://github.com/genproof/quickproof-public) v0.1.0 (the `quickproof` submodule). Each spec is a small
C program, `harness/<name>.c`, that states a property and that you can compile and run. The Coq theorem of a spec
says that for every value the spec draws, no run has undefined behaviour (through VST's adequacy theorem, whose
instance for QuickProof's environment is upcoming) and every check in it holds. The code is zlib 1.3.2 with nine bug
fixes and some edits for the prover ([below](#the-code-under-test)). AI agents wrote the proofs, and Coq checks them,
so nothing the agents wrote in the proofs is trusted.

## Ten properties

What a user of zlib relies on, and the specs that prove it. A spec's first comment states its property in full,
with its bounds, and its checks quote `zlib.h` or the RFC they come from. The numbers are for the platform below.

1. **Compression is deterministic.** Two streams made by `deflateInit2` with the same parameters, given the same
   calls, return the same codes and write the same bytes. The calls cut the data into any pieces, use any flush
   from `Z_NO_FLUSH` to `Z_BLOCK` (`Z_FINISH` only with all the rest of the data), and may call `deflateParams`
   before each `deflate`. Spec: [`api_deterministic`](harness/api_deterministic.c).
2. **The compressed size is bounded.** For any level -1..9, `compress2_z` into
   `compressBound_z(n) = n + n/4096 + n/16384 + n/2^25 + 13` bytes returns `Z_OK` unless it reports `Z_MEM_ERROR`,
   and the length it reports is at most that. This needs fix F9: zlib 1.3.2 as released fails it at level 0 for
   some inputs over 51 TiB. Spec: [`res_compress_bound`](harness/res_compress_bound.c). For `deflateBound`, with a
   dictionary, a gzip header or neither, data under 4 GiB and a bound below 2^32: one `deflate(Z_FINISH)` into
   exactly that many bytes returns `Z_STREAM_END`. Spec: [`res_bound`](harness/res_bound.c). Both halves are proved
   on the patched code ([below](#the-code-under-test)).
3. **Compression memory is bounded.** Counted through the `zalloc` and `zfree` it is given, deflate never holds
   more than `(1 << (w + 2)) + (1 << (memLevel + 9)) + 5968` bytes. Here `w` is the window size in bits: windowBits
   without the minus sign of raw deflate or the 16 of gzip, and 9 for 8. The bound is checked after every call,
   over any number of `deflate` calls with any data, output space and flush. Spec:
   [`res_memory_deflate`](harness/res_memory_deflate.c).
4. **Compression is memory-safe and returns only documented codes.** For any parameters that `deflateInit2`
   accepts, any data in any pieces, any output space and any flush value (any `int`), with `deflateParams` (any
   level and strategy) before any call until the first `Z_FINISH`, and calls that follow `zlib.h`'s rule for
   `Z_FINISH`: every call returns a code that `zlib.h` documents (`Z_STREAM_ERROR` exactly for an invalid flush,
   level or strategy), and leaves the output space it did not write as it was. Spec:
   [`api_deflate_any`](harness/api_deflate_any.c). The round trip [`rt_stream`](harness/rt_stream.c) drives
   `deflate` with any parameters, pieces and flush values up to `Z_BLOCK`, without `deflateParams`.
5. **Decompression is deterministic.** With the 32 KiB window (windowBits -15, 15, 31 or 47) and input and output
   space under 4 GiB, one `inflate` call (any flush but `Z_BLOCK` and `Z_TREES`) and any split of the same input
   write the same bytes. When the one call returns `Z_STREAM_END`, `Z_NEED_DICT` or `Z_DATA_ERROR`, the split ends
   with the same code, and otherwise with none of the three. Spec:
   [`api_split_invariant`](harness/api_split_invariant.c). Two new streams with the same windowBits, fed any input
   in the same pieces with the same output space and flush, return the same codes and write the same bytes. Spec:
   [`api_inflate_deterministic`](harness/api_inflate_deterministic.c).
6. **Decompression does not consume what follows the stream.** Take a stream that zlib's deflate made (any
   parameters it accepts), followed by any bytes. When `inflate` returns `Z_STREAM_END`, `next_in` points just past
   the stream: none of the bytes after it were consumed. Spec: [`rt_stream_trailing`](harness/rt_stream_trailing.c),
   with the stream in any pieces and any output space (also [`rt_session`](harness/rt_session.c) and
   [`rfc_trailing_bytes`](harness/rfc_trailing_bytes.c)); for `uncompress2`, [`rt_roundtrip`](harness/rt_roundtrip.c); for streams of up to 2^19 bytes that a reference
   encoder builds from RFC 1951, followed by up to 16 bytes, [`x_inflate_decode`](harness/x_inflate_decode.c).
7. **Round trip.** For any data and any level -1..9, `compress2` into `compressBound` bytes returns `Z_OK`, and
   `uncompress2` of its output, followed by any bytes, into an output of at least the data's length returns `Z_OK`,
   gives back exactly the data, writes nothing after it and reports the stream's length as read. Spec:
   [`rt_roundtrip`](harness/rt_roundtrip.c). With streams, any parameters, any split and any bytes after the stream:
   [`rt_stream_trailing`](harness/rt_stream_trailing.c); in one session with a dictionary or a gzip header as well:
   [`rt_session`](harness/rt_session.c).
8. **Too little room gives `Z_BUF_ERROR` and the start of the data.** For what `compress2` made from one byte or
   more (any level -1..9), `uncompress2` with less output space than the data (even none, also with a `NULL` buffer)
   returns `Z_BUF_ERROR`, writes exactly the first bytes of the data and reads less than the whole stream. Spec:
   [`api_short_output`](harness/api_short_output.c).
9. **Decompression memory is bounded.** Counted through the `zalloc` and `zfree` it is given, inflate never holds
   more than `(1 << w) + 7160` bytes. Here `w` is the window size in bits: windowBits without the minus sign of raw
   inflate or the 16 or 32 added for gzip or header detection, and 15 when that leaves 0. The bound is checked after
   every call, over any number of `inflate` calls with any input, output space and flush. Spec:
   [`res_memory_inflate`](harness/res_memory_inflate.c).
10. **Decompression is memory-safe on any input.** For any windowBits that `inflateInit2` accepts, `inflate` on any
    bytes of any length, in any pieces, with any output space and any flush, and `inflateSetDictionary` with any
    bytes between calls: every `inflate` call returns a code that `zlib.h` documents, leaves the input and the output space it did not
    write as they were, and moves its pointers and counters by exactly what it read and wrote
    ([`api_inflate_any`](harness/api_inflate_any.c); [`rj_any_input`](harness/rj_any_input.c) and
    [`api_untouched_output`](harness/api_untouched_output.c) state parts of it on their own). For `uncompress2`,
    [`rj_uncompress_any`](harness/rj_uncompress_any.c) checks the return codes, the length bounds and that the output it
    did not write is unchanged. [`x_inflate_buffers`](harness/x_inflate_buffers.c)
    shows the same buffer discipline for the rest of the inflate API (`inflateSync`, `inflatePrime`,
    `inflateReset2`, `inflateGetDictionary` and others) with smaller bounds: at most 16 MiB of input in all and 1 MiB
    of output space per call. [`x_inflate_header`](harness/x_inflate_header.c) shows that `inflate` writes the buffers
    of `inflateGetHeader` only within their sizes (up to 64 KiB each), for gzip headers with any fields.

Memory safety is part of every theorem, not only of 4 and 10. Each theorem rules out, for its spec, a read or write
outside an object, a use after free, a double free, a null dereference, the use of an uninitialised value, a signed
overflow and a division by zero (QuickProof's `docs/GUARANTEES.md` has the exact list). An overlapping `memcpy` is
not ruled out: the proofs link QuickProof's `memcpy`, a byte-by-byte forward copy that is defined on overlapping
ranges. [SPECS.md](SPECS.md) summarizes each of the 62 specs and explains how to read one.

## What a theorem says, and its limits

For each spec, `Theorem <name> : harness_safe whole_prog`, where `whole_prog` is the spec linked with the zlib
files it uses. By VST's adequacy theorem this means: for every value the spec draws, no run has undefined
behaviour in CompCert's semantics of C, and every check in the spec holds. [CONTRACT.md](CONTRACT.md) states this
exactly.

- Termination is not proved (partial correctness). A theorem is about every run that finishes; a run that never
  returns is not a counterexample.
- The semantics is CompCert 3.15's for `x86_64-linux`, LP64 ([below](#the-platform)). A binary built by another
  compiler, or for another platform, is outside the theorems.
- Any `malloc` may return `NULL`, and the theorems cover those runs too: nothing up to the failure, or in zlib's
  handling of it, has undefined behaviour. After a failed allocation in the spec, or `Z_MEM_ERROR` from zlib, most
  specs stop and claim nothing more about that run (`rj_uncompress_any` and some `x_` specs check past it). With
  zlib's default allocator a spec cannot see whether `malloc` failed, so a `Z_MEM_ERROR` while memory was available
  would pass it. The specs with an allocator of their own (`res_memory_*`, `res_free_*`) check that `Z_MEM_ERROR`
  comes only after a failed allocation.
- The theorems are about zlib 1.3.2 with fixes F1-F9 and the edits of [patch/PATCH.md](patch/PATCH.md), as the C
  files at the root hold it. Nothing is proved about the unmodified code. The edits for the prover are tested
  against the original code, not proved equivalent.
- "Any" means any value within the bounds that the spec's first comment states. Lengths include 0. Only some specs
  pass a `NULL` buffer: `ck_adler32_null` and `ck_crc32_null` (any length), `api_short_output` and
  `rj_uncompress_any` (length 0), `rt_gzip_header` (`deflate` with no input) and some `x_` specs. In the others a
  `NULL` from `malloc` ends the run.
  Several specs check the documented error for invalid parameters (`rj_deflate_params`, `rj_inflate_params`,
  `rj_bad_level`, `api_deflate_any` and some `x_` specs); most others stop when `deflateInit2`, `inflateInit2` or
  `compress2` rejects its parameters. A flush value that a spec draws is any `int` unless its first comment says
  otherwise.
- Memory leaks are ruled out only where a spec counts allocations: `res_free_deflate` and `res_free_inflate`,
  after one call.
- The trusted base: the Coq 8.20.1 kernel; VST 2.15, with its malloc library's declarations, `QPlink_progs` and its
  adequacy theorem, which turns the proved judgement into "no run has undefined behaviour" and is not yet
  instantiated in Coq for QuickProof's environment (that instance is upcoming); CompCert 3.15's semantics of C;
  `clightgen` and QuickProof's translation scripts; the argument that linking only the units a spec uses changes
  nothing; QuickProof's model of the environment (`quickproof.h`, `Env.v`, `Contract.v`) and `qp verify`; and the
  text of each spec and of `quickproof.conf`. The system's libc plays no part: `memcpy`, `memset` and `malloc` are
  QuickProof's own. Running out of stack is not ruled out. QuickProof's `docs/GUARANTEES.md`, in the submodule, has
  the full list.

## The platform

x86_64, CompCert 3.15's `x86_64-linux` configuration, LP64:
- `sizeof(void *)` = `sizeof(size_t)` = `sizeof(long)` = 8 and `sizeof(int)` = 4, so one zlib call takes at most
  2^32 - 1 bytes (`uInt`), while `compress2`, `uncompress2` and the `_z` functions take any length;
- data lengths go up to `PTRDIFF_MAX` = 2^63 - 1 bytes; the output buffers sized by `compressBound` or
  `deflateBound` for such data are slightly larger, which CompCert's memory model allows (objects of almost 2^64
  bytes);
- `sizeof(struct inflate_state)` = 7160 and `sizeof(deflate_state)` = 5968, the same with gcc on x86_64; these
  are the constants of properties 3 and 9;
- crc32 is proved for its byte-at-a-time loop (built with `-DZ_TESTW=`). A default build on x86_64 uses the
  braided loop, which these proofs do not cover. Everything else is zlib's default configuration: static CRC
  tables, no `Z_SOLO`, no `LIT_MEM`, no assembly ([quickproof.conf](quickproof.conf)).

Details in [SPECS.md](SPECS.md#the-platform).

## Checking the proof

Check the proof with a QuickProof checkout of your own at the release this repository pins, v0.1.0 (see
"Installing" in QuickProof's README):

    git clone --recursive https://github.com/genproof/zlib-full-auto-proofs-public.git
    <your quickproof>/tools/qp verify zlib-full-auto-proofs-public --base contract

`qp verify` requires the files of the repository's `quickproof` submodule that decide what a theorem says (the
statement, the libc linked into every program, the translation scripts) to be byte for byte those of the verifier's
own framework. Run from your checkout, it compares them with a copy you trust. The submodule's own `qp`
(`quickproof/tools/qp verify . --base contract` inside the clone) works too, but it compares the submodule with
itself, and its report says so; the submodule copy is a convenience.

`qp verify` rebuilds every proof from a fresh clone. It checks that the specs, the code under test and the statements
are those of the tag `contract`, which holds the contract without any proof; that nothing is admitted; and that each
theorem rests only on Coq's standard axioms and the abstract predicates of VST's malloc library. It needs 64-bit x86
Linux with QuickProof's toolchain (Coq 8.20.1, CompCert 3.15, VST 2.15); QuickProof's Docker image has the same
toolchain. A run takes about 8 hours with 8 build jobs on 16 CPUs. `qp verify` builds the repository's Coq sources
with your rights, so run it in a container if you do not trust them.

## The code under test

zlib 1.3.2, upstream commit [`da607da739fa`](https://github.com/madler/zlib/commit/da607da739fa), the core
library without the gz* file API and without `infback.c`. Its C files are at the root of this repository, as
`patch/zlibpatch.py` leaves them. [patch/PATCH.md](patch/PATCH.md) describes every edit, and every changed line
keeps the original in a `quickproof:` comment.

- Idiom edits I1-I6 and deviations D1, D2 adapt the code to VST and CompCert. They are meant to change no
  behaviour. This is tested, not proved: a differential test (`patch/difftest.sh`) runs the edited and the original
  zlib on random streams and compares every output.
- Fixes F1-F9, one per bug. Each changes zlib's behaviour only in the case the table describes.

| fix | what was wrong | upstream | spec that needs the fix |
|---|---|---|---|
| F1 | `inflate()` misses header bytes in `total_in` on `Z_NEED_DICT` | fixed upstream (`066e0b68`, pull request [#1297](https://github.com/madler/zlib/pull/1297)) | `x_inflate_buffers` |
| F2 | `adler32(x, Z_NULL, 1)` reads `buf[0]` | issue [#1283](https://github.com/madler/zlib/issues/1283), closed without a change | `x_adler32_ref` |
| F3 | `deflateBound()` is not an upper bound for `Z_FIXED` at levels 1-3 | reported; not fixed upstream yet | `x_deflate_bound` |
| F4 | `inflate()`'s fast path rewinds `next_in` before the input after `inflatePrime()` | fixed upstream (`e7bb9788`) | `x_inflate_buffers` |
| F5 | raw `deflate(Z_FINISH)` returns `Z_OK` when the last block exactly fills the output | issue [#1300](https://github.com/madler/zlib/issues/1300), fixed upstream ([#1326](https://github.com/madler/zlib/pull/1326)) | `x_deflate_bound` |
| F6 | `inflate()` writes into a 1-byte window after `inflateSync()` + `inflateReset2()` | fixed upstream (`8179479c`) | `x_inflate_buffers` |
| F7 | `inflate()` stores a header's window size before checking it | upstream documents it instead (`dfa96642`) | `x_inflate_buffers` |
| F8 | `inflateReset()` keeps the previous stream's window size | fixed upstream (`c0424159`) | `api_reset` |
| F9 | a 32-bit sum in `deflate_stored()` ends a level-0 stream with input unread | issue [#1348](https://github.com/madler/zlib/issues/1348), fixed upstream (`2bed3d61`) | `res_compress_bound` |

The last column names one spec that needs the fix; other specs may need it too.

## Layout

- `harness/`: the 62 specs, one C file each, and the headers they share; `rt_roundtrip.c` is a good first read.
- `*.c`, `*.h` at the root: the code under test. `grep -n quickproof: *.c *.h` lists every edited line.
- `patch/`: the edit script `zlibpatch.py`, [PATCH.md](patch/PATCH.md) and the differential test.
- `src/contracts/`: the theorem statements. `src/proof/`: the proofs. `src/units/` and the `code.v` files under
  `src/`: the C files translated to Clight by `clightgen`.
- `env/`: value choices for native and interpreter test runs, not part of any theorem.
- `docs/`: [ROUNDTRIP.md](docs/ROUNDTRIP.md), and the scripts that wrote parts of the proof.
- `quickproof/`: the framework (submodule).

## What the proof contains

To see how one spec is proved, from the C file down to RFC 1951 written in Coq, read
[docs/ROUNDTRIP.md](docs/ROUNDTRIP.md). None of the following adds an axiom or a trusted component; Coq checks all
of it.

Some numeric bounds are proved with linear-programming certificates: that deflate's bit writer never overtakes the
unread symbols in its shared pending buffer, and the cost bound of the bit-length tree's repair.
`src/proof/huffman/CertData.v`, `CertD.v` and `Repair.v` hold 421 sets of integer multipliers that a solver found.
Coq checks each one by computation, and a proved lemma turns a checked certificate into the bound, so a wrong
certificate fails the build. `python3 docs/huffman-gen/certs.py --check` solves the linear programs again (it needs
numpy and scipy); the build does not need it. Many other lemmas are checked by computation over finite ranges:
every entry of zlib's static tables, every length and distance of deflate, and an `enough.c`-style count of table
sizes.

Scripts in `docs/` wrote some proof files. Each such file says so in its first line and names its script. The main
scripts (`certs.py`, the `port*.py` scripts of `docs/port-za/`, `docs/port-hl/` and `docs/port-wide/`,
`records.py`, `fixed.py`, `laws.py`) take `--check`, which compares instead of writing; without it they overwrite
the files. Most generated files are ports: a script copies part of
the proof declaration by declaration with some definitions replaced, and gives each copy a suffix (`_za`, `_w`,
...). The ports cover a caller-supplied allocator (`src/proof/za/`), calls of up to 2^32 - 1 bytes
(`src/proof/wide/`), `deflate()` with no input buffer (`src/proof/dnull/`), a gzip header held by the caller
(`src/proof/hl/`, `src/proof/hlza/`) and header buffers of any size (`src/proof/hl9h/`). `docs/inflate-gen/`
writes data files of the inflate model, and `docs/laws-gen/laws.py` writes `src/contracts/laws.v`.

Each spec's whole program is assembled with `QuickProof.Assembly`. Large functions (`inflate`, `deflate`,
`inflate_table`) are proved in pieces, glued back with VST's sequencing rules. deflate's specifications are stated
over executable models with a step budget (fuel). Some groups of lemmas were proved as copies of others under new
module names; a comment at each says what it copies, and merging them changes no theorem. A few files of an
earlier, bounded version of some proofs remain because the current proofs use their definitions; their first
comments say so, and comments that name files of that version refer to that earlier version, which is not in this
repository's history.

## Licence

Our files (the specs, the proofs, the scripts, the configuration and the documentation) are under the PolyForm
Noncommercial License 1.0.0 ([LICENSE.md](LICENSE.md), [NOTICE.md](NOTICE.md)), copyright 2026 GenProof. zlib's files
keep the zlib licence ([LICENSE](LICENSE)), and [NOTICE.md](NOTICE.md) lists them and the ones we altered; each
Clight file `src/**/code.v` has the licence of the C file `clightgen` generates it from.

We chose a noncommercial license to make QuickProof freely available for community use while reflecting CompCert’s
licensing restrictions. We remind users that commercial use of CompCert requires separate permission.

Maintained by Vladimir Kukharenko.
