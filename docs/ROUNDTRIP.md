# How the round trip is proved: a reading guide

This guide follows one property of zlib, "what is compressed comes back unchanged", from the C spec down to the
general theorems it rests on. It says which file to open at each step, what to look for there, and how to ask
Coq yourself.

## The short answer

- The round trip is proved for two of the longer `x_` specs (Qed, no axioms beyond the standard ones and VST's
  malloc library; see [step 7](#7-ask-coq-yourself)):
  - `x_compress_roundtrip`: the one-call functions `compress2` / `uncompress`;
  - `x_deflate_roundtrip`: streams, with any parameters, any calls and any flush value from `Z_NO_FLUSH` to
    `Z_BLOCK`.

  The short specs `rt_roundtrip` (`compress2` / `uncompress2`, data of any length) and `rt_stream` (streams, data
  of any length) rest on the same two theorems, with every call of up to 2^32 - 1 bytes: (A) through
  `src/proof/roundtrip/RTK7*.v` (`rt_roundtrip`: `RTC2WFinalProof.v`, compress2's loop) and (B) through the
  wide decode theory `src/proof/rfc1951/Decode7*.v` (`rt_roundtrip`: `uncompr/UTheoryWProof.v`, uncompress2's
  loop). The comments of `short_rt_roundtrip` and `short_rt_stream` in `src/contracts/suite.v` name the files.
- There is no single line `inflate (deflate x) = x` in the proof. The round trip goes through the standard
  itself: RFC 1951 (and RFC 1950 / 1952 for the wrappers) is written as a Coq definition, and two general
  theorems are proved about it:
  - **(A)** what `deflate` outputs is a well-formed RFC 1951 stream whose data is exactly its input;
  - **(B)** `inflate` decodes every well-formed stream to its data.

  The spec follows from (A), (B) and the proofs that the C functions do what their models say. Each half is a
  statement about the standard, so each is stronger than the round trip: (A) says zlib's output can be read by
  any correct decoder, (B) says zlib reads any correct stream, not only its own.

## The map

```
harness/x_compress_roundtrip.c            1. the spec, in C: what is claimed
        |  stated as
src/contracts/laws.v                      2. Theorem: harness_safe whole_prog
                                             (whole_prog: src/contracts/x_compress_roundtrip.v, frozen)
        |  proved from
src/contracts/suite.v                     3. suite_roundtrips
        |  which applies
src/proof/roundtrip/RoundTrips.v          4. roundtrip_laws: the glue
        |
        +-- src/proof/rfc1951/Format.v    5. the standard, in Coq (no link to zlib's code)
        +-- (A) roundtrip/RTFinal.v, RTDTheory.v   deflate's output is a well-formed stream of the data
        +-- (B) rfc1951/Decode.v                   inflate decodes every well-formed stream
        +-- C <-> model                   6. function specifications and their proofs
```

## 1. The spec, in C

Open `harness/x_compress_roundtrip.c`. Its first comment is the whole claim. The checks that make it a round trip:

```c
r = compress2(dest, &dlen, data, n, level);          // any data, n <= 2^20 bytes, any level
...
r = uncompress(out, &olen, dest, dlen);
gp_assert(r == Z_OK && olen == n && bytes_same(out, data, n));
```

`nondet_*` values are arbitrary: the theorem covers every one of them at once. `x_deflate_roundtrip.c` does the
same with streams (`deflateInit2` with any parameters, any sequence of `deflate` calls and flush values, a
dictionary or a gzip header), then checks that one `inflate` call gives back exactly the data.

## 2. The statement

Open `src/contracts/x_compress_roundtrip.v`. It defines `whole_prog` and says where the theorem is stated. The
statement, in `src/contracts/laws.v`, is one line:

```coq
Theorem x_compress_roundtrip : harness_safe Zlib.contracts.x_compress_roundtrip.whole_prog.
```

- `whole_prog` is the spec linked with the zlib files it uses, translated to CompCert's Clight by `clightgen`
  (`x_compress_roundtrip.v` lists the units).
- `harness_safe` (in `quickproof/coq/QuickProof/Contract.v`) is VST's `semax_prog` for that program. By VST's
  adequacy theorem: for every value the `nondet_*` functions return, no execution has undefined behaviour. (That
  step is VST's theorem; it is not yet instantiated in Coq for QuickProof's environment.) A failed `gp_assert` is
  undefined behaviour by construction, so every check holds in every execution.
- `CONTRACT.md` says what is frozen. `qp verify` checks that the statement is still the frozen one.

## 3. Where the proof starts

`src/contracts/laws.v` proves the theorem by taking it out of the suite:

```coq
Theorem x_compress_roundtrip : harness_safe Zlib.contracts.x_compress_roundtrip.whole_prog.
Proof. exact (proj1 (proj2 (proj2 Zlib.contracts.suite.suite_x))). Qed.
```

In `src/contracts/suite.v`, search for `suite_roundtrips`. It applies one theorem, `roundtrip_laws`, to proofs:

```coq
Lemma suite_roundtrips :
  harness_safe Zlib.contracts.x_compress_roundtrip.whole_prog /\
  harness_safe Zlib.contracts.x_deflate_roundtrip.whole_prog.
Proof.
  exact (Zlib.proof.roundtrip.RoundTrips.roundtrip_laws
    Zlib.proof.inflate_api.LibProof5.inflate_lib5_proof Zlib.proof.uncompr.UBodies5.uncompr_bodies5
    suite_decode_parts suite_trees_bodies suite_deflate_bodies9
    (proj1 Zlib.proof.huffman.Lemmas.huffman_lemmas) (proj2 Zlib.proof.huffman.Lemmas.huffman_lemmas)).
Qed.
```

## 4. The glue: `roundtrip_laws`

Open `src/proof/roundtrip/RoundTrips.v`. The theorem has seven hypotheses. Each one is a separate result that
`suite.v` proves:

| hypothesis | what it says | proved in `suite.v` by |
|---|---|---|
| `inflate_lib5_stmt` | the C functions of `inflate.c`, `inffast.c`, `inftrees.c` meet their specifications | `LibProof5.inflate_lib5_proof` |
| `uncompr_bodies5_stmt` | `uncompress`, `uncompress2` meet theirs | `UBodies5.uncompr_bodies5` |
| `decode_parts` | half (B), in parts | `suite_decode_parts` |
| `trees_bodies_ok` | the functions of `trees.c` meet theirs | `suite_trees_bodies` |
| `deflate_bodies_ok9` | the functions of `deflate.c` meet theirs | `suite_deflate_bodies9` |
| `overlay_statement` | deflate's output never overtakes the symbols it has still to read in their shared buffer (the bug of CVE-2018-25032) | `huffman_lemmas` |
| `block_bound_statement` | the per-block size bound behind `compressBound` | `huffman_lemmas` |

These are hypotheses of `roundtrip_laws` only. The final theorem does not keep them: `suite.v` proves each one,
and `Print Assumptions` (step 7) shows that none is left.

Inside the proof, `rt_kfacts` gives half (A), `rt_ufacts` and `rt_ifacts6` give half (B) in the form the two
specs use, and `rt_compress_law` / `rt_deflate_law6` prove the specs' `main` functions from all of it.

## 5. The standard, in Coq

Open `src/proof/rfc1951/Format.v`. It depends on nothing in zlib's code or in the specs, so you can check it
against the RFC text alone.

| definition | what it is | RFC |
|---|---|---|
| `block` | a stored, fixed-Huffman or dynamic-Huffman block, with its literals and back-references | 1951 §3.2.3-3.2.7 |
| `deflate_bytes bs` | the bits of the blocks, packed into bytes | 1951 §3.1.1, 3.2.2 |
| `expand hist bs`, `data hist bs` | what the blocks mean: the LZ77 expansion after a history `hist` (a preset dictionary, or nothing) | 1951 §3.2.5 |
| `wf wmax hist bs` | well-formed: complete codes, a code for end-of-block, back-references within the data and the window | 1951 §3.2 |
| `stream_bytes w hist bs` | the raw, zlib or gzip wrapper around the deflate bytes, with its checksum trailer | 1950, 1952 |

The checksums have their own reference definitions: `src/proof/adler32/Model.v` (`ref_adler32`, from RFC 1950)
and `src/proof/crc32/Model.v`.

## 5A. Half (A): what deflate outputs

Open `src/proof/roundtrip/RTFinal.v`. `dfinal` says what the bytes `O` that deflate produced are, for the data `D`:

```coq
(* abbreviated *)
dfinal dict wrap wb gh D O :=
  9 <= wb <= 15 /\
  exists bs,                    (* some list of RFC 1951 blocks *)
    wf (2 ^ wb) dict bs /\      (* well-formed *)
    data dict bs = D /\         (* whose data is exactly the input *)
    match wrap with
    | 0 => O = deflate_bytes bs                                             (* raw *)
    | 1 => O = [CMF; FLG] ++ (dictionary id) ++ deflate_bytes bs ++ adler32(D)   (* zlib *)
    | _ => O = stream_bytes (WGzip header) [] bs                           (* gzip *)
    end.
```

`src/proof/roundtrip/RTDIface.v` defines `kfacts K`: `K` is a property of a live deflate stream that every call
keeps, and the call that returns `Z_STREAM_END` ends in `dfinal` for all the data and all the output (field
`kf_deflate`). `src/proof/roundtrip/RTDTheory.v` proves it:

```coq
Theorem rt_kfacts : Zlib.proof.huffman.Overlay.overlay_statement -> exists K, kfacts K.
```

This is about the model of `deflate` (step 6), for every parameter set, call sequence and flush value.

## 5B. Half (B): inflate decodes every well-formed stream

Open `src/proof/rfc1951/Decode.v`, `decode_call_stmt`. `src/proof/rfc1951/DecodeDefs.v`, `dctx_ok`, fixes the
setting: the input starts with `stream_bytes w hist bs` for well-formed blocks `bs`, followed by any bytes. Then
one call of inflate's model, given the next input bytes, any output space and any flush:

- returns `Z_OK`, `Z_BUF_ERROR` or `Z_STREAM_END` (or `Z_MEM_ERROR` when the window cannot be allocated);
- writes exactly the next bytes of the stream's data;
- at `Z_STREAM_END`, has produced all the data and read exactly the stream, and none of the bytes after it;
- stops early only when the input or the output space ran out (or flush is `Z_BLOCK` / `Z_TREES`).

The header comment of `Decode.v` says the same in prose.

## 6. From the C code to the models

The theorems of 5A and 5B are about Coq models of the C functions. Two kinds of files tie the models to the C:

- **Function specifications.** `src/proof/deflate/DSpec.v`, `deflate_spec`: when the model `c_deflate`
  (`src/proof/deflate/DModel4.v`) of the stream's state gives a result, a call of the C `deflate` leaves memory
  exactly as that result says and returns its code. `src/proof/inflate_api/Spec5.v`, `inflate_spec` and
  `inflate_rel`: the C `inflate` does what the model `run2` (`src/proof/inflate/Model2.v`) does. `compress2` and
  `uncompress` have theirs in `src/proof/roundtrip/RTCSpec.v` and `src/proof/uncompr/USpec5.v`.
- **Body proofs.** For each C function, `semax_body` proves that its code meets its specification
  (`src/proof/deflate/Body_*.v`, `src/proof/inflate_api/`, `src/proof/inffast/`, `src/proof/trees/`). They are
  the `*_bodies` hypotheses of step 4.

The models are Coq functions that follow the C code step by step. They check every memory access and give no
result where the C would go wrong. That they always give a result in these specs is part of what is
proved (`src/proof/deflate/LawTheory.v`).

## 7. Ask Coq yourself

1. Build the proof with the README's command, `<your quickproof>/tools/qp verify <this repository> --base
   contract` (several hours). It builds in a cache directory, by default
   `~/.cache/quickproof/verify/<repository>-<commit>/`.
2. In that directory, save this as `Look.v` and run
   `coqc -Q quickproof/coq/QuickProof QuickProof -R src Zlib Look.v`:

```coq
From Coq Require Import ZArith List.
Require Zlib.contracts.laws Zlib.proof.roundtrip.RoundTrips Zlib.proof.roundtrip.RTDTheory
        Zlib.proof.roundtrip.RTFinal Zlib.proof.rfc1951.Format Zlib.proof.rfc1951.Decode.
Import ListNotations. Open Scope Z_scope.

(* the spec's theorem, and everything it rests on *)
Check Zlib.contracts.laws.x_compress_roundtrip.
Print Assumptions Zlib.contracts.laws.x_compress_roundtrip.

(* the glue *)
Check Zlib.proof.roundtrip.RoundTrips.roundtrip_laws.

(* the standard *)
Print Zlib.proof.rfc1951.Format.data.
Print Zlib.proof.rfc1951.Format.stream_bytes.

(* half (A) *)
Print Zlib.proof.roundtrip.RTFinal.dfinal.
Check Zlib.proof.roundtrip.RTDTheory.rt_kfacts.

(* half (B) *)
Print Zlib.proof.rfc1951.Decode.decode_call_stmt.
```

`Print Assumptions` lists what the theorem rests on beyond Coq itself. It lists:

- standard axioms of Coq's library: `classic`, functional extensionality, proof irrelevance, propositional
  extensionality, `Extensionality_Ensembles`, `eq_rect_eq`, and two from `ClassicalDedekindReals`;
- the abstract predicates of VST's malloc library and their stated facts: `mem_mgr`, `malloc_token`,
  `malloc_token_valid_pointer`, `malloc_token_local_facts`, `malloc_token_change_composite`, `create_mem_mgr`.

There are no other axioms, no `Admitted` and no hypothesis of steps 4-6.

## What the round trip does not say

- **Sizes.** `x_compress_roundtrip` is for data of at most 2^20 bytes. `x_deflate_roundtrip` is for at most 2^20
  bytes of data, at most 2^20 bytes of output space per call and 2^22 bytes of compressed output in all, a
  dictionary of at most 2^15 bytes and header fields of at most 2^12 bytes. Both specs state their bounds in their
  first comment. The short specs `rt_roundtrip` and `rt_stream` take data of any length.
- **Time.** A theorem says what holds when a call returns, not that it returns.
- **The binary.** The theorems are about the C code in CompCert's semantics, one thread, not about a binary built
  by another compiler.
- **What you trust.** The Coq kernel, VST (its adequacy theorem and malloc library) and CompCert's Clight
  semantics, the translation of C to Clight by `clightgen` and QuickProof's scripts, QuickProof's definitions
  (`Contract.v`, `Env.v`) and `qp verify`, and the text of the spec. The README and QuickProof's
  `docs/GUARANTEES.md` give the full list.
