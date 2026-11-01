# The specs

This repository proves properties of zlib. Each property is stated by a spec: a small C program in `harness/` (a
harness, in QuickProof's terms) that you can compile and run. QuickProof turns each spec into a Coq theorem:
for every input the spec allows, none of its checks (`gp_assert`) fails and nothing it runs has undefined
behaviour. This page explains zlib in a few lines, how to read a spec, and what each spec says.

## zlib in two minutes

- **What it does.** zlib compresses and decompresses data. It is inside PNG, HTTP, git, zip and much more.
- **Deflate.** The compression format is **deflate** (RFC 1951). A deflate stream is a sequence of blocks of three
  kinds:
  - *stored*: the bytes as they are;
  - *fixed Huffman*: compressed with a code table every decoder knows;
  - *dynamic Huffman*: compressed with a code table sent at the start of the block.

  Inside compressed blocks, a *back-reference* says "repeat 10 bytes, starting 300 bytes back".
- **Wrappers.** The stream is raw deflate, or wrapped:
  - **zlib** (RFC 1950): a 2-byte header, and an Adler-32 checksum at the end;
  - **gzip** (RFC 1952): a header with a file name, time and so on, and a CRC-32 and the length at the end.
- **One-call functions.** `compress2(dest, &destLen, data, len, level)` compresses, `uncompress2` decompresses,
  `compressBound(len)` says how much room the compressed data may need.
- **Streaming functions.** `deflateInit2`/`inflateInit2` set up a stream with its parameters (level, window size,
  wrapper, ...). `deflate`/`inflate` are then called again and again: each call is given some input
  (`next_in`/`avail_in`), some room for output (`next_out`/`avail_out`) and a *flush* value, and does as much as it
  can. `inflateReset` makes a stream new again; `deflateEnd`/`inflateEnd` free it.
- **Checksums.** `adler32` and `crc32` compute the checksums; `adler32_combine` and `crc32_combine` compute the
  checksum of two pieces put together from the checksums of the pieces.

## How to read a spec

```c
size_t n = upto(PTRDIFF_MAX);                     // any length the allocator provides
unsigned char *data = alloc_any_bytes(n);         // any n bytes
unsigned char *expected = copy_of(data, n);       // a copy, made before zlib sees data
... call zlib ...
gp_assert(out_len == n && bytes_eq(out, expected, n));   // what must hold
```

- The **first comment of each file is the claim**, in full; the tables below only summarize it. Where they differ,
  the comment is right. It starts with `Law <name>:`, the older word for a spec. The only other comments in a spec
  are short quotes of the RFC section or the `zlib.h` sentence a check comes from; everything else that explains a
  spec is on this page (the notes below).
- The call of the function under test stands between blank lines.
- `nondet_size()`, `nondet_u32()`, `nondet_u8()` and `nondet_bytes()` are QuickProof's: they stand for *any*
  value, and the theorem covers all of them. Wherever we can, the data, the parameters, the
  wrapper, the way the input and output are cut into pieces and the flush values are all arbitrary.
- `gp_assume(c)` restricts the inputs the spec talks about; every restriction is also written in the spec's first
  comment. `gp_assert(c)` is the property. Both are QuickProof's.
- The helpers of `harness/laws_common.h` (40 lines, included by every short spec; no models of zlib):
  - `upto(max)`: any value from 0 to `max`; `nondet_u32()` is any value from 0 to 2^32 - 1 (`UINT_MAX`);
  - `clip(n)`: `n`, but at most 2^32 - 1, the most one zlib call takes (`avail_in` and `avail_out` are `uInt`);
  - `alloc_any_bytes(n)`: a new object of `n` arbitrary bytes, or `NULL` if `malloc` fails;
  - `copy_of(p, n)`: a new object holding the `n` bytes at `p` (`NULL` if `malloc` fails);
  - `bytes_eq(a, b, n)`: the `n` bytes at `a` and at `b` are equal;
  - `set_buffer(strm, in, in_len, out, out_len)`: the input and the output space of the stream's next call;
  - `new_stream(strm)`: a stream with zlib's own allocator (`zalloc`, `zfree`, `opaque` all `Z_NULL`), nothing
    offered yet.
- **Copies.** Where a spec compares what zlib gives back with what it was given, it compares with a copy made before
  zlib saw the data (`expected`, `dict_copy`, ...), in an object of its own whose address zlib never gets. A
  function under test may write into its input (writing there is not undefined behaviour, whatever `const` its
  prototype says), and with one shared buffer a compressor could rewrite the data to match what decompression later
  returns. In CompCert's memory model no pointer arithmetic reaches from one object into another, so nothing zlib
  does can change the copy. Specs that run two streams side by side (`api_deterministic`, `api_reset`,
  `api_inflate_deterministic`, `api_split_invariant`) give each stream its own copy of the input for the same
  reason.
- **"Z_MEM_ERROR ends the run"**: when zlib reports that it could not get memory, the run stops and the spec claims
  nothing about that run. Two cases:
  - Specs that give zlib their own allocator (`res_memory_*`, `res_free_*`) check that zlib says so only when it is
    true: their allocator records whether it ever returned `Z_NULL` (`count.failed`), and the spec checks
    "`Z_MEM_ERROR` implies the allocator failed".
  - Specs on `compress2` and `uncompress2` (and the stream specs that use `new_stream`) run with zlib's own
    allocator: `compress2` and `uncompress2` set `zalloc` and `zfree` to `Z_NULL` themselves, and zlib then calls
    `malloc` through `zcalloc`, so the spec cannot see whether `malloc` failed. QuickProof's environment lets
    any `malloc` return `NULL` (C allows it); a run where zlib reports `Z_MEM_ERROR` while `malloc` succeeded would
    pass these specs. Telling the two apart needs a counter in QuickProof's environment, which v0.1.0 does
    not have. `rj_uncompress_any` does not end its run there: `Z_MEM_ERROR` is one of the codes it allows, and its
    other checks hold after it too.
- **Initialisation with valid parameters.** `rj_deflate_params` and `rj_inflate_params` prove that with valid
  parameters `deflateInit2` and `inflateInit2` return `Z_OK` or `Z_MEM_ERROR`, nothing else; they use zlib's
  default allocator. `res_memory_deflate` and `res_memory_inflate` prove that these functions return `Z_MEM_ERROR`
  only when the `zalloc` the spec passes has returned `Z_NULL` (`deflateInit2` with any level, windowBits, memLevel
  and strategy, `inflateInit2` with any windowBits; `res_free_deflate` and `res_free_inflate` check the same).
  Together they say that initialisation with valid parameters succeeds unless the allocator refuses. No single
  spec checks both halves with one allocator: with zlib's default allocator a spec cannot see whether `malloc`
  failed (above).
- **The counted allocator** of the `res_` specs gives zlib blocks of `malloc` that carry their size just in front of
  the block (`counted_alloc`), adds it to `count.now` and keeps the maximum in `count.peak`; `counted_free`
  subtracts it. A `zfree` of anything else than a block from `counted_alloc`, or of one block twice, would be
  undefined behaviour in the spec, which the theorem excludes. Counting through `zalloc` sees all of zlib's
  memory: in the code under test only `zcalloc` (zutil.c) calls `malloc` (and `calloc`, in its 16-bit branch), and
  `zcalloc` and `zcfree` are used only by `deflateInit2_` and `inflateInit2_`, as the allocator of a stream whose
  `zalloc` (`zfree`) is `Z_NULL` (checked in the generated Clight: `src/zutil/code.v` is the only zlib unit that
  calls `quickproof_malloc`, and `_zcalloc` and `_zcfree` occur only in those two functions). With the spec's own
  `zalloc` and `zfree` they are never called. We did not build these specs with `Z_SOLO` (zlib without `zcalloc`):
  it would prove them on a different `deflateInit2_` and `inflateInit2_`, and `compress2` and `uncompress2` do not
  exist there.
- The helpers of `harness/laws_session.h`, included by the specs that drive a stream (no models of zlib):
  - `deflate_params_ok(level, windowBits, memLevel, strategy)` and `inflate_window_ok(windowBits)`: the parameters
    are in the ranges of `zlib.h` for `deflateInit2` and `inflateInit2` (the ranges `rj_deflate_params` and
    `rj_inflate_params` are about); a spec draws any parameters and keeps these with `gp_assume`;
  - `struct position` and `position_of(strm, &at)`: `next_in`, `avail_in`, `next_out`, `avail_out`, `total_in` and
    `total_out` before a call;
  - after the call, `unmoved(strm, &at)`: none of them changed; `accounted(strm, &at)`: `next_in` and `next_out`
    moved exactly as far as `avail_in` and `avail_out` went down; `counted(strm, &at)`: `total_in` and `total_out`
    went up by as much.
- Each short spec plus its headers is about 50 to 300 lines; the line counts below include the headers.

## The platform

The theorems are about the C code as CompCert's semantics defines it for **x86_64** (CompCert 3.15's `x86_64-linux`
configuration: `arch=x86`, `model=64`, `system=linux`, **LP64**). What depends on the platform:

- `sizeof (void *)` = `sizeof (size_t)` = `sizeof (long)` = 8, `sizeof (int)` = 4: `uInt` (`unsigned int`) has 32
  bits, so one zlib call takes at most 2^32 - 1 bytes; `uLong` and `z_size_t` (`unsigned long`) have 64 bits,
  so `compress2`, `uncompress2`, `compressBound` and the `_z` functions take any length.
- Data lengths go up to `PTRDIFF_MAX` = 2^63 - 1 ("any length the allocator provides"). The output buffers that
  `res_compress_bound`, `rt_roundtrip`, `api_short_output` and `rfc_trailing_bytes` size by `compressBound` or
  `deflateBound` for such data are slightly larger; CompCert's memory model has objects of almost 2^64 bytes.
- `sizeof (struct inflate_state)` = 7160 and `sizeof (deflate_state)` = 5968 bytes (the same with gcc on x86_64):
  the exact sizes in `res_memory_inflate` and `res_memory_deflate`. `sizeof (z_stream)` = 112,
  `sizeof (gz_header)` = 80.
- The configuration of the code under test is in `quickproof.conf`: crc32 without braiding (the byte-at-a-time
  loop; a default build on x86_64 uses the braided one, which is not proved), static CRC tables, no `Z_SOLO`, no
  assembly.

## The code under test

zlib 1.3.2 (upstream commit `da607da739fa`; its C files at the root of this repository), with the edits listed in
[patch/PATCH.md](patch/PATCH.md) (the README has a table of the fixes with their upstream status): idiom edits that
VST needs, two deviations meant to change no behaviour (tested, not proved), and nine fixes, F1-F9. Every changed
line keeps the original in a `quickproof:` comment. The specs are about this version: zlib 1.3.2 rewrote some
functions (for example `uncompress2_z`, see the note on `api_short_output`), and a spec can be false on an older
one.

## The specs

The 45 short specs (prefixes `api_`, `ck_`, `res_`, `rfc_`, `rj_`, `rt_`) share `harness/laws_common.h`; the 17
longer `x_` specs come last. Every spec below was tested before any proof: native runs under AddressSanitizer and
UndefinedBehaviorSanitizer, runs in CompCert's interpreter, and broken versions of zlib that it must notice. All 62
specs are proved on the code with fixes F1-F9. Without a fix, the spec that the README's table names for it fails,
and other specs may fail too. [CONTRACT.md](CONTRACT.md) and `src/contracts/` state each theorem exactly.

### Round trip (`rt_`): what goes in comes back

| spec | lines | what it says |
|---|---|---|
| `rt_roundtrip` | 105 | Any data, any level -1..9: `compress2` succeeds, and `uncompress2` of its output followed by any bytes reads exactly the compressed bytes and gives back exactly the data. |
| `rt_stream` | 185 | The same with streams: any compression parameters, the data given in any pieces, any output room and any flush from `Z_NO_FLUSH` to `Z_BLOCK` on every call, decompressed in any pieces with any flush: exactly the data comes back. |
| `rt_stream_trailing` | 198 | `rt_stream` with any bytes after the stream: every call moves `next_in` and `next_out` exactly as far as it lowers `avail_in` and `avail_out`, a call offered no room (deflate) or neither input nor room (inflate) moves nothing, and decompression stops exactly at the end of the stream, reads none of the bytes after it and gives back exactly the data. |
| `rt_session` | 296 | One session with everything at once: any wrapper, a preset dictionary or a full gzip header, the data in any pieces with any flush and output room, any bytes after the stream: every call accounts for its pointers, the dictionary is asked for exactly when it should be, and the data and every header field come back exactly. |
| `rt_dictionary` | 126 | Compressed with any preset dictionary (zlib wrapper, windowBits 8..15): decompression asks for it, and once given it, returns exactly the data. |
| `rt_gzip_header` | 150 | Every field of a gzip header (text flag, OS, time, extra field, name, comment; each present or not) comes back as it was given. |
| `rt_partial` | 108 | Given any unfinished prefix of a compressed stream, decompression only ever writes the start of the data. |

### Checksums (`ck_`)

| spec | lines | what it says |
|---|---|---|
| `ck_adler32` | 63 | `adler32_z` equals the Adler-32 definition of RFC 1950, written out in the spec, for any bytes and any starting value whose halves are below 65521. |
| `ck_adler32_combine` | 63 | The checksum of the whole equals `adler32_combine` of the checksums of its two parts, for any cut and any starting value whose halves are below 65521. |
| `ck_adler32_null` | 54 | With no buffer (`Z_NULL`), `adler32_z` returns the initial value 1. |
| `ck_crc32` | 69 | `crc32_z` equals the bit-by-bit CRC-32 of RFC 1952, written out in the spec, for any bytes and any starting value. |
| `ck_crc32_combine` | 66 | The same for CRC-32, with each of zlib's three combine functions. |
| `ck_crc32_null` | 54 | With no buffer, `crc32_z` returns the initial value 0. |

### Rejects (`rj_`): bad parameters and bad input are refused

| spec | lines | what it says |
|---|---|---|
| `rj_bad_level` | 62 | A level outside -1..9 makes `compress2` fail with `Z_STREAM_ERROR`. |
| `rj_deflate_params` | 74 | `deflateInit2` accepts its parameters exactly when all are in the ranges of `zlib.h`. |
| `rj_inflate_params` | 66 | `inflateInit2` accepts exactly the window sizes of `zlib.h`. |
| `rj_crc32_negative` | 55 | Combining CRCs with a negative length returns 0. |
| `rj_any_input` | 152 | Any bytes given to decompression, in any pieces, with any flush and dictionaries in between: every call returns one of the documented codes. |
| `rj_uncompress_any` | 78 | The same for `uncompress2`: any bytes, any output size: only documented codes, and the output space after what it reports written is left as it was. |
| `rj_far_back` | 143 | In a raw stream whose first block is a fixed-Huffman block of fewer than 32768 literals, a back-reference to before the start of the output is an error (`Z_DATA_ERROR`), and nothing beyond the literals is output. |
| `rj_bad_header` | 85 | A zlib header that breaks RFC 1950 (check bits, method, window size) is refused before any output. |
| `rj_bad_block` | 131 | A first block of a raw stream that breaks RFC 1951 is refused: a stored block whose length check fails, the reserved block type, forbidden codes. |
| `rj_bad_checksum` | 119 | If the checksum or length at the end of the stream is changed, decompression never reports success. |
| `rj_bad_dictionary` | 82 | A zlib stream whose header asks for a dictionary makes `inflate` return `Z_NEED_DICT`, and a dictionary whose checksum is not the one the header names is refused. |
| `rj_truncated` | 107 | A truncated stream never reports success. |

### The standard on valid input (`rfc_`)

| spec | lines | what it says |
|---|---|---|
| `rfc_stored` | 143 | A stream of stored blocks built by hand from the RFCs (any data, any block sizes, any wrapper, any bytes after it) decompresses to exactly the data. |
| `rfc_trailing_bytes` | 174 | For a stream that zlib's deflate made, followed by any bytes: when decompression returns `Z_STREAM_END`, it has consumed exactly the stream and none of the bytes after it. |
| `rfc_level0_size` | 99 | At level 0 the output size is exactly the data plus 5 bytes per block plus the wrapper (the data given in pieces of whole 65535-byte blocks, one call or many). |
| `rfc_level0_blocks` | 117 | At level 0 the output is exactly stored blocks as RFC 1951 defines them, holding the data in order. |

### The stream interface (`api_`)

| spec | lines | what it says |
|---|---|---|
| `api_short_output` | 95 | Given less room than the data needs (any amount, even none), `uncompress2` says so (`Z_BUF_ERROR`), gives exactly the first bytes and has not read all of the compressed bytes (any bytes follow them). |
| `api_dict_id` | 106 | For data compressed with a preset dictionary (zlib wrapper), decompression asks for it and reports the dictionary's Adler-32. |
| `api_counters` | 90 | The stream's pointers and counters move by exactly the bytes read and written. |
| `api_untouched_output` | 157 | Decompression leaves the part of the output room it did not write as it was. |
| `api_split_invariant` | 116 | For any input under 4 GiB, one call or any pieces give the same bytes and the same end result (32 KiB window). |
| `api_reset` | 107 | After any use and `inflateReset`, a stream behaves exactly like a new one. Needs fix F8: without it, `inflateReset` keeps the window size that the previous stream's header set. |
| `api_deterministic` | 165 | Two streams with the same parameters, driven by the same calls, produce the same output. |
| `api_inflate_deterministic` | 150 | Two new decompression streams with the same windowBits, fed the same input (any bytes) in the same pieces with the same flush, return the same codes and write the same bytes. |
| `api_deflate_any` | 174 | Any accepted compression parameters, any data in any pieces, any flush and `deflateParams` between calls: `deflate` returns only the codes of `zlib.h` (`Z_STREAM_ERROR` exactly for an invalid flush), `deflateParams` returns `Z_STREAM_ERROR` exactly for an invalid level or strategy, and the output room not written is left as it was. |
| `api_inflate_any` | 163 | Any accepted windowBits, any input in any pieces (empty ones too), any flush, any output room (none too), dictionaries in between: only documented codes, the input and the unwritten output untouched, `next_*` and `total_*` move by exactly what was read and written, and no `Z_OK` when nothing could be done. |

### Sizes and memory (`res_`)

| spec | lines | what it says |
|---|---|---|
| `res_compress_bound` | 69 | `compress2_z` at any level -1..9 into `compressBound_z` bytes never runs out of room, and the output is at most that. Needs fix F9: without it, a 32-bit sum in `deflate_stored` wraps for some inputs over 51 TiB at level 0 (found by the proof). |
| `res_bound` | 169 | One `deflate(Z_FINISH)` into exactly `deflateBound` bytes returns `Z_STREAM_END`, with a dictionary, a gzip header or neither, for data under 4 GiB and a bound below 2^32. |
| `res_memory_deflate` | 185 | Compression, over any number of calls, never holds more memory than the formula of `zconf.h` plus the exact size of its state (5968 bytes); `Z_MEM_ERROR` only when the allocator failed. |
| `res_memory_inflate` | 179 | Nor does decompression: at most the window plus the exact size of its state (7160 bytes). |
| `res_free_deflate` | 109 | After one `deflate` call and `deflateEnd` (and after a failed `deflateInit2`) all memory is given back. |
| `res_free_inflate` | 106 | The same for decompression, after one `inflate` call. |

### Longer specs (`x_`)

The 17 specs whose names start with `x_` come from an earlier proof of zlib. They say much of the above in longer
files that share helpers and a reference encoder (`zlib_common.h`, `deflate_common.h`, `deflate_ref.h`). All are
bounded, most to 1 MiB of data or 16 MiB of input; each first comment ends with its bounds. One of them,
`x_inflate_decode`, checks inflate against a reference encoder written from RFC 1951 for all three block kinds,
which no short spec covers. Their first comments use the older names without `x_` (`Law inflate_buffers` for
`x_inflate_buffers`). The line counts below are of the file alone.

| spec | lines | what it says |
|---|---|---|
| `x_adler32_ref` | 49 | `adler32` and `adler32_z` equal the Adler-32 of RFC 1950 for any valid starting value and any buffer of up to 1 MiB, also when split into two calls; with a `Z_NULL` buffer they return 1. |
| `x_adler32_combine_ref` | 53 | `adler32_combine` gives the Adler-32 of a concatenation (two buffers of up to 1 MiB each), equals RFC 1950's algebraic combination for any valid checksums and any length of 0 or more, and returns `0xffffffff` for a negative length. |
| `x_crc32_ref` | 47 | `crc32` and `crc32_z` equal the bit-by-bit CRC-32 of RFC 1952 for any starting value and any buffer of up to 1 MiB, also when split into two calls; with a `Z_NULL` buffer they return 0; `get_crc_table` returns the CRC of every byte value. |
| `x_crc32_combine_ref` | 51 | `crc32_combine`, and `crc32_combine_op` with `crc32_combine_gen`, give the CRC-32 of a concatenation (two buffers of up to 1 MiB each); for a negative length they return 0. |
| `x_compress_roundtrip` | 77 | For data of up to 1 MiB and any level: `compress2` into `compressBound` bytes returns `Z_STREAM_ERROR` exactly for a level outside -1..9, else `Z_OK` with at most that many bytes; `uncompress` and `uncompress2` give back exactly the data; with one byte too little room `uncompress` returns `Z_BUF_ERROR`, and a truncated stream is never accepted. |
| `x_deflate_api` | 69 | `deflate`'s documented interface for any parameters, tuning, dictionary and gzip header, data of up to 1 MiB, and any sequence of `deflate` and `deflateParams` calls with any split: documented codes (`Z_STREAM_ERROR` exactly for invalid parameters), exact pointers and counters, the output space beyond what was produced unchanged, the right header and trailer at `Z_STREAM_END`, and `Z_STREAM_ERROR` from every call after `deflateEnd`. |
| `x_deflate_bound` | 97 | One `deflate(Z_FINISH)` into exactly `deflateBound` bytes returns `Z_STREAM_END`, for any accepted parameters, dictionary (up to 32 KiB) and gzip header (fields up to 4 KiB) and data of up to 1 MiB; `compressBound(n)` is at least n, and at the default parameters `deflateBound` is at most `compressBound`. |
| `x_deflate_bound_split` | 112 | With the data given in any pieces with `Z_NO_FLUSH`, then `Z_FINISH`, and any output space per call (up to 1 MiB), the total output never exceeds `deflateBound` (same bounds as `x_deflate_bound`). |
| `x_deflate_roundtrip` | 84 | One `inflate` call gives back exactly what `deflate` compressed, for any parameters, tuning, dictionary and gzip header (which comes back too) and any sequence of `deflate` (flush up to `Z_BLOCK`) and `deflateParams` calls with any split (data up to 1 MiB, output space up to 1 MiB per call, 4 MiB of compressed output). |
| `x_inflate_buffers` | 167 | Any sequence of calls of the inflate API (`inflate` with any flush, `inflateSync`, `inflateGetDictionary`, `inflateSetDictionary`, `inflatePrime`, `inflateReset`, `inflateReset2`, `inflateValidate`, `inflateMark`, `inflateCodesUsed`, `inflateSyncPoint`), any windowBits, input up to 16 MiB and output space up to 1 MiB per call: every call reads and writes only its buffers, pointers and counters move by exactly what was consumed and produced, and `inflate` leaves the output space it did not write unchanged. |
| `x_inflate_check` | 103 | With a zlib or gzip wrapper, once `inflate` has produced output, the stream's header is valid and after every call `adler` is the checksum of the output so far; `inflate` returns `Z_STREAM_END` only when the trailer matches it (input up to 16 MiB). |
| `x_inflate_codes` | 172 | `inflateInit2_`, `inflate`, `inflateSetDictionary`, `inflateEnd`, and every entry point after `inflateEnd`, return exactly the documented codes, for any input up to 16 MiB and any calls of `inflate` and `inflateSetDictionary`; the first comment gives each code's conditions. |
| `x_inflate_decode` | 289 | `inflate` decodes every stream that a reference encoder written from RFC 1951 builds from stored, fixed and dynamic Huffman blocks (data up to 256 KiB, stream up to 512 KiB; raw, zlib or gzip wrapper; up to 16 bytes after it): only `Z_OK`, `Z_BUF_ERROR` or `Z_STREAM_END`, the output is always the start of the data, and at the end exactly the stream was consumed. |
| `x_inflate_dict` | 219 | Preset dictionaries of up to 64 KiB: a zlib stream asks for the dictionary and reports its Adler-32, a wrong one gives `Z_DATA_ERROR`, the right one decodes the data, back-references into the dictionary included; `inflateGetDictionary` returns the window (data up to 256 KiB). |
| `x_inflate_header` | 229 | `inflateGetHeader` with buffers of any size up to 64 KiB, on a gzip member with any header fields: `inflate` writes the buffers only within their sizes, reports every field once the header is complete, and never accepts a reserved flag bit or a wrong header CRC. |
| `x_inflate_reset` | 110 | After any use, `inflateReset`, or `inflateReset2` with any windowBits, gives a stream that behaves like a new one from `inflateInit2` on the same input (up to 16 MiB). |
| `x_uncompress_any` | 51 | `uncompress` and `uncompress2` on any input of up to 16 MiB, with any output size up to 1 MiB: only documented codes, no write beyond the size they report, and on `Z_OK` a valid zlib header and a trailer that matches the output. |

## Notes on the specs

### Parameters, initialisation and empty buffers

The specs of the ten properties that open a stream draw its parameters only from the ranges of `zlib.h`
(`laws_session.h`; the same ranges as `rj_deflate_params` and `rj_inflate_params`) and check that `deflateInit2` or
`inflateInit2` returns `Z_OK`. Only `Z_MEM_ERROR` ends the run, and in `res_memory_deflate` and `res_memory_inflate`
only when their counting allocator really returned `NULL`. Invalid parameters are the subject of `rj_deflate_params`,
`rj_inflate_params` and `api_deflate_any` (`deflateParams` and the flush value).

The session specs also check calls with empty buffers. A `deflate()` call with no output space returns
`Z_BUF_ERROR` and changes none of `next_in`, `avail_in`, `next_out`, `avail_out`, `total_in`, `total_out` (`zlib.h`:
"Z_BUF_ERROR if no progress is possible (for example avail_in or avail_out was zero)"). An `inflate()` call with no
input and no output space never returns `Z_OK` and changes none of them; it may return `Z_BUF_ERROR`,
`Z_STREAM_END`, `Z_NEED_DICT` or `Z_DATA_ERROR` from the state an earlier call reached.

What a spec does not say in its comments, spec by spec.

- **The flush values.** `deflate` and `inflate` take the flush as an `int`, and the specs give them any `int`, not
  only the values `zlib.h` names: that is what a caller can pass. A spec's first comment states any exception.
  `rj_any_input` proves that `inflate` never answers `Z_STREAM_ERROR` for any flush value (it does not look at an
  unknown one), and `api_deflate_any` that `deflate` answers `Z_STREAM_ERROR` exactly for a flush outside
  `Z_NO_FLUSH`..`Z_BLOCK`, as `zlib.h` documents. Specs that drive compression to its end (`rt_stream`,
  `api_deterministic`) draw the flush from `Z_NO_FLUSH`..`Z_BLOCK` (0..5, `Z_FINISH` is 4), and give `Z_FINISH`
  only with the rest of the data, once one call can take it (at most 2^32 - 1 bytes), and then until
  `Z_STREAM_END`, as `zlib.h` asks.
- **`zlib.h`'s rule for `Z_FINISH`.** "If deflate returns with Z_OK or Z_BUF_ERROR, this function must be called
  again with Z_FINISH and more output space (updated avail_out) but no more input data"; after `Z_STREAM_END` "the
  only possible operations on the stream are deflateReset or deflateEnd". `api_deflate_any` follows it: after a
  call with `Z_FINISH`, every call has `Z_FINISH` and the input the previous call left, and no `deflateParams`
  (which would call `deflate(strm, Z_BLOCK)`); the run stops at `Z_STREAM_END`.
- **windowBits 8.** `zlib.h`: for deflate "a request for 8 will result in 9 (a 512-byte window)", and "use 9 with
  inflateInit2()": the round trips decompress with 9 when they compressed with 8, and `res_memory_deflate` counts a
  window of 9 bits.
- **`rt_roundtrip`.** The bytes after the compressed stream are a new object of any bytes (up to `PTRDIFF_MAX`
  minus the stream's length, as in `rfc_trailing_bytes`) into which the spec copies the stream, so that they do
  not depend on what `compress2` left in its buffer. `used_len` (zlib.h, uncompress2: "On return, *sourceLen is the
  number of source bytes consumed") must be exactly the stream's length: `uncompress2` stops at the end of the
  stream and does not count the bytes after it. The check of `used_len` meant nothing without those bytes.
- **`api_short_output` and zlib 1.3.2.** The spec says that `uncompress2` with less room than the data returns
  `Z_BUF_ERROR`, also with no room at all (`destLen` 0, and then also a `Z_NULL` buffer). An older `uncompress2`
  (zlib 1.3.1 and before) decompressed into a one-byte buffer of its own when `destLen` was 0, and descriptions of
  `uncompress2` written for those versions do not apply to this case here. zlib 1.3.2's `uncompress2_z` gives
  `inflate` the caller's empty output space (`&stream.reserved` when the buffer is `Z_NULL`), `inflate` cannot
  write the first byte, and `uncompress2_z` returns `Z_BUF_ERROR`, since input is left. The spec also checks
  `used_len < compressed_len`: decompression stopped inside the stream, before the end of the compressed bytes (and
  so before the bytes after them).
- **`api_deterministic`.** Why the same calls only: the output may depend on how the data and the output space are
  split. Level 0 sizes its stored blocks by `avail_in` and `avail_out` (deflate.c, `deflate_stored`), and zlib.h,
  deflate: "make sure that avail_out is greater than six when the flush marker begins, in order to avoid repeated
  flush markers upon calling deflate() again when avail_out == 0". `deflateParams` may compress what it is offered
  (with `Z_BLOCK`), so it is called on both streams with the same input and output space as the next `deflate`.
- **`api_split_invariant`.** Where the input is cut (a network packet, a file read in blocks) does not change what
  inflate returns or how it ends. The window is fixed at 32 KiB: with a smaller one, a distance past the window but
  inside one call's output is accepted by that call and refused once an earlier call returned that output; `zlib.h`
  promises neither. `Z_BLOCK` and `Z_TREES` make `inflate` stop at block boundaries, so the one call does not use
  them.
- **`api_reset`.** The loop runs twice: first on the stream alone (any use), then, after `inflateReset` of it and
  `inflateInit2` of a new stream, on both with the same calls.
- **`rt_stream`.** The buffer for the compressed bytes has any size, so it may be too small for the stream. When
  compression fills it before `Z_STREAM_END`, the run ends and the spec claims nothing about that run: there is no
  stream to decompress. Whether enough room always suffices is the subject of other specs: `res_bound` (one
  `deflate(Z_FINISH)` into `deflateBound` bytes ends the stream) and `res_compress_bound` (`compress2` into
  `compressBound` bytes succeeds). `clip` only limits each call to the 2^32 - 1 bytes that `avail_in` and
  `avail_out` can hold; longer data go over several calls.
- **`res_bound`: what it checks.** The output space is an object of exactly `deflateBound` bytes, so the compressed
  stream cannot be longer: a write past that object would be undefined behaviour, which the theorem rules out. The
  spec checks that one `deflate(Z_FINISH)` returns `Z_STREAM_END`, which `zlib.h` defines as "all input has been
  consumed and all output has been produced". `deflateBound` is part of zlib's documented API, and this is the
  guarantee `zlib.h` gives for it.
- **`rt_gzip_header`, `res_bound`.** One draw says which fields are present: bit 0 the extra field, bit 1 the name,
  bit 2 the comment (`res_bound`: bit 0 whether a dictionary or a header is set, bits 1-3 the fields).
  `any_string(n)` is `n` nonzero bytes and a zero byte.
- **`rfc_level0_size`, `rfc_level0_blocks`.** The data go in pieces of whole 65535-byte blocks: a call that runs
  out of output space ends its stored block early (deflate.c, `deflate_stored`), and 65531 blocks, 65540 bytes each
  when stored, and the wrapper fit in one call's 2^32 - 1 bytes. The wrapper is 0 bytes (raw), 2 + 4 (zlib: CMF,
  FLG and ADLER32, RFC 1950 2.2) or 10 + 8 (gzip: the header and CRC32, ISIZE, RFC 1952 2.3).
- **`rj_any_input`, `api_untouched_output`: why not a round trip.** A round trip only decompresses streams that
  zlib produced. These two specs give inflate arbitrary bytes, as an attacker can; with the theorem's exclusion of
  undefined behaviour (no read or write out of bounds, no use after free), they cover untrusted input. They say
  nothing about running time.
- **`rj_bad_block`.** The kind of broken block: 0 a stored block with a bad NLEN, 1 the reserved type, 2 a bad
  literal/length code (286, 287), 3 a bad distance code (30, 31) after the length code 257, 4 a dynamic block with
  HLIT 30 or 31; the first bit of the stream (BFINAL) is any.
- **`rj_bad_dictionary`.** The spec picks dictionaries whose Adler-32, computed by zlib's own `adler32_z`, is not
  the header's DICTID. `ck_adler32` proves that `adler32_z` computes RFC 1950's Adler-32, so these are exactly the
  wrong dictionaries.
- **`rfc_trailing_bytes`.** The spec calls `inflate` until it returns `Z_STREAM_END`. If `inflate` returned an
  error instead, the spec would loop forever; termination is not covered, so such a run is not a counterexample.
- **`rj_far_back`.** Two calls: the first with any first part of the stream and any output space, the second with
  the rest (at most 2^32 - 1 bytes of it) and room for the literals and one byte more.
- **`res_memory_inflate`, `res_memory_deflate`.** The bound is exact: zlib allocates for inflate the state (7160
  bytes) and the window of `1 << wbits` bytes, where `wbits` is at most the `w` of the spec (the header's window size
  when windowBits is 0, 16 or 32); for deflate the state (5968 bytes), the window (2 << w), `prev` (2 << w), `head`
  (2 << (memLevel + 7)) and the pending buffer (4 << (memLevel + 6)): `zconf.h`'s formula plus the state. Checked
  natively: every accepted (windowBits, memLevel) of deflate and every window of inflate reaches the bound exactly
  once the window is allocated. The specs state these exact sizes rather than `zconf.h`'s "about 7 kilobytes", for
  any number of calls, the bound checked after each.
- **`res_compress_bound`.** The spec also checks the length `compress2_z` reports: at most `compressBound_z` of the
  data's length.

## What the specs do not say

- **Time.** The theorem excludes undefined behaviour, not non-termination: it says what holds *if* a call returns,
  not that it returns. A spec whose loop never ends (for example a zlib that returned `Z_OK` forever without
  progress, where the spec waits for `Z_STREAM_END`) is not a counterexample.
- **Sizes.** Most short specs do not bound their data: they hold for any length the allocator provides.
  `api_split_invariant`, `res_bound`, `res_free_deflate`, `res_free_inflate` and `rj_bad_header` take under 2^32
  bytes (one call), and `rj_far_back` fewer than 32768 literals. `rfc_stored` takes data, blocks and trailing bytes
  of up to 2^60 each. One zlib call takes at most 2^32 - 1 bytes of input
  and of output (`avail_in`, `avail_out` are `uInt`), so the specs feed longer data in pieces; what zlib takes in
  one call only is limited to what that call accepts (a dictionary, the gzip header buffers of `inflateGetHeader`,
  and `res_bound`, whose `zlib.h` guarantee is about one call). The `x_` specs keep the bounds their first comments
  state (1 MiB of data for most).
- **Very large objects.** The proof covers objects as large as CompCert's semantics allows (almost 2^64 bytes), far
  beyond what native runs draw. Some specs carry bounds that matter only for objects of 4 GiB or more.
  `res_bound` takes a gzip name and a comment of at most 2^32 - 2 bytes each (as `rt_gzip_header`): longer ones
  make `deflateBound` exceed 2^32 - 1, outside the guarantee the spec checks, except when the two total about
  2^64 bytes, which no machine holds: then the `z_size_t` sum in `deflateBound_z` wraps. `rfc_level0_size` and `rfc_level0_blocks` give at most
  65531 blocks per call: 65532 stored blocks (4 GiB) and the gzip wrapper are 3 bytes more than one call's
  2^32 - 1 bytes of output, and the spec's loop would stop at a `Z_BUF_ERROR` that `zlib.h` documents.
  `rj_bad_block` writes at most (PTRDIFF_MAX - 5) / 9 literals, so that its own bit counter (a `size_t`) cannot wrap
  past 2^64 and turn the broken block into a valid one.
- **Functions no spec calls.** No spec calls `deflateInit` or `inflateInit` (they use `deflateInit2` and
  `inflateInit2`), `compress_z`, `uncompress_z`, `deflateCopy`, `inflateCopy`, `deflateGetDictionary`,
  `deflatePending`, `deflateUsed`, `deflateResetKeep`, `inflateResetKeep`, `inflateUndermine`, `zError`,
  `zlibVersion` or `zlibCompileFlags` directly. `deflateReset` and `deflatePrime` are called only on an ended
  stream (`x_deflate_api`). `inflateBack` and the gz* functions are not part of the code under test.
- **Memory errors of `compress2` and `uncompress2`.** See "Z_MEM_ERROR ends the run" above.
- **The binary.** The theorems are about the C code as CompCert's semantics defines it, not about a binary built by
  another compiler; one thread only.
- **Every Huffman stream.** Conformance to RFC 1951 is stated for stored blocks (`rfc_*`) and through the round trips;
  `x_inflate_decode` covers the rest, for streams of up to 2^19 bytes.
