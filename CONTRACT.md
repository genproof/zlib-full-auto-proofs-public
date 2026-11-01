# Contract: zlib 1.3.2 core

**The code under test.** zlib 1.3.2 (da607da739fa), the core library without the gz* file API and without
infback.c: `adler32.c`, `crc32.c`, `deflate.c`, `trees.c`, `inflate.c`, `inffast.c`, `inftrees.c`, `compress.c`,
`uncompr.c`, `zutil.c` and their headers, at the root of this repository, as `patch/zlibpatch.py` leaves them:
six idiom edits (I1-I6) and two deviations (D1, the field copies of `code` values; D2, deflateParams compares the
compressors' kinds instead of their function pointers), which are meant to change no behaviour (tested, not
proved), and nine fixes (F1-F9), each of which changes zlib's behaviour only in the
case `patch/PATCH.md` describes. Every changed line carries a `quickproof:` comment with the original;
[patch/PATCH.md](patch/PATCH.md) describes each edit and why it is there. The configuration is in `quickproof.conf`
(crc32 without braiding, static CRC tables).

**The programs.** One program per spec: `harness/<name>.c` linked with the units its contract lists
(`LINK=per-law`; `whole_prog_undefined` checks the link). The units are the ten zlib files,
`quickproof/libc/libc.c` and `quickproof/libc/malloc_unit.c`, one file each in `src/units/*.v`.
`quickproof/tools/clight.sh quickproof.conf` translates them with `clightgen -normalize`, maps malloc and free
to the externals `quickproof_malloc` and `quickproof_free`, and renames, consistently, the statics that clash
between units and the anonymous structs that units share.

**The specs.** 62 specs: 45 short ones (prefixes `api_`, `ck_`, `res_`, `rfc_`, `rj_`, `rt_`), each with the shared
header `harness/laws_common.h` (those that drive a stream also with `harness/laws_session.h`), and 17 longer ones
from an earlier proof (prefix `x_`).
[SPECS.md](SPECS.md) introduces them.

**The names.** The 17 longer specs carry the prefix `x_`: `harness/x_<name>.c`, `env/x_<name>.c`,
`src/contracts/x_<name>.v`, `Theorem x_<name>`. They were named without it in the earlier proof, and the comments
of the specs and env files and of `patch/zlibpatch.py` still use those names (`inflate_buffers` for
`x_inflate_buffers`). The rename changed no file's content; the names that `clight.sh` derives from a spec's file
name follow it (the spec's string literals `__stringlit_x_<name>_N`, and the statics renamed against a clash
between units, `x_inflate_decode__ref_*`, `x_inflate_dict__ref_*`).

**The claims.** `src/contracts/<name>.v`: `Theorem <name> : harness_safe whole_prog`
(`quickproof/coq/QuickProof/Contract.v`): VST's `semax_prog` for `whole_prog` in the honest external world
`QuickProof.Env`, no axioms. By VST's adequacy theorem, for every value the nondet_* functions return, no execution
has undefined behaviour in CompCert's Clight semantics; each spec has undefined behaviour exactly when one of its
checks fails. That step is VST's theorem; it is not yet instantiated in Coq for QuickProof's environment (that
instance is upcoming) (`quickproof/docs/GUARANTEES.md`). `src/contracts/suite.v` states all 62 specs in one theorem,
`suite` (no spec is marked as expected to fail: `BROKEN` in `quickproof.conf` is empty). Some specs hold only with a
fix of `patch/PATCH.md`; the README's table names, for each fix, one spec that needs it, and other specs may need it
too.

What the claims do not cover:
- what each spec leaves out: its first comment states its property, its bounds and its exclusions;
- termination (a run that never returns is not a counterexample).

**Frozen** after the contract commit (the commit tagged `contract`):
- `harness/**`, the code under test (the C files at the repository root (`*.c`, `*.h`)), `quickproof/**` (the
  framework), `quickproof.conf`;
- the generated `src/**/code.v`;
- `src/units/*.v`; in `src/contracts/*.v`: the module `Harness`, the `link_*` definitions, `whole_prog` and the
  statement (restated unchanged in `src/contracts/laws.v`; `qp verify` compares the elaborated statements).

`qp verify` also refuses any change since the contract commit outside the proof sources (`src/**.v`), Markdown
files, `docs/` and a few metadata paths that `quickproof/docs/QP.md` lists.

**Proved** means, for each theorem: it ends in `Qed`, it builds from a clean checkout, and
`Print Assumptions <name>` lists only standard axioms and the abstract predicates of VST's malloc library (mem_mgr,
malloc_token and its facts, create_mem_mgr). `qp verify` checks this, and that every statement is the one of the
contract.

**The contract commit.** The commit tagged `contract` holds the contract alone: the code under test, the specs,
the generated code and every contract file as `new_contract.py` generates it, without any proof. The proof is
checked against it: `qp verify <this repository> --base contract`, run from a QuickProof checkout at
v0.1.0 (the README's "Checking the proof").

**Status.** All 62 specs are proved on the code with fixes F1-F9: `suite`, and each spec as a theorem of its own,
with its generated name and statement, on its contract file's `whole_prog` (`src/contracts/laws.v`, generated by
`docs/laws-gen/laws.py`; `x_crc32_ref` in `src/contracts/laws_checksums.v`): their contract files keep only the
program; `qp verify` checks it.