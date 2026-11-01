"""Configuration of docs/port-za/port_rtig.py: the generalized decode theory of the round trip
(src/proof/roundtrip/RTIGDefs.v and its proofs RTIGDec*.v: any gzip header, a gz_header attached) WIDE, as
cfg_wide_decode.py does for src/proof/rfc1951/: calls of up to 2^32 - 1 bytes of input and of output space
(Inv.mwf's bounds) on inputs of up to 2^64 - 1 bytes (RTIGDefs.dctx_ok's bound).  Output:
src/proof/wide/roundtrip/RTIG*.v (modules Zlib.proof.wide.roundtrip.RTIG*), suffix _wide.

The RTIG modules require rfc1951/Decode.v, so the port also covers the modules of cfg_wide_decode.py; with the
same substitutions and patches (and those targets first, in the same order) their ports are exactly the files
of src/proof/wide/rfc1951/ and src/proof/wide/inflate/, which port_rtig.py checks and never rewrites."""
import importlib.util
import os

_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'cfg_wide_decode.py')
_spec = importlib.util.spec_from_file_location('cfg_wide_decode', _path)
base = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(base)

SUFFIX = base.SUFFIX
OUT = base.OUT
SECTION = base.SECTION
REQUIRES = base.REQUIRES
WHAT = base.WHAT

# the header of the RTIG modules (port_rtig.py puts it in place of WHAT there)
WHAT_RTIG = ('the\n   bounds of the machine invariant Inv.mwf and of RTIGDefs.dctx_ok, here raised to calls of up to '
             '2^32 - 1 bytes\n   on inputs of any length,')

PREFIXES = base.PREFIXES + ['Zlib.proof.roundtrip.RTIG']

RTIG_TARGETS = [
    'Zlib.proof.roundtrip.RTIGDecKit',
    'Zlib.proof.roundtrip.RTIGDecType',
    'Zlib.proof.roundtrip.RTIGDecTab',
    'Zlib.proof.roundtrip.RTIGDecDec',
    'Zlib.proof.roundtrip.RTIGDecFast',
    'Zlib.proof.roundtrip.RTIGDecTrl',
    'Zlib.proof.roundtrip.RTIGDecCall',
]

TARGETS = base.TARGETS + RTIG_TARGETS

SUBST = base.SUBST

PATCHES = base.PATCHES + [
    ('Zlib.proof.roundtrip.RTIGDefs',
     "slen G <= Zlength (dc_src G) /\\ Zlength (dc_src G) <= 2 ^ 31 - 1 /\\",
     "slen G <= Zlength (dc_src G) /\\ Zlength (dc_src G) <= 2 ^ 64 - 1 /\\"),
    # the one-pass invariant of the RTIG copies is DecodeDefs' stepf2_kd_stmt (the wide port of rfc1951), applied
    # to a machine at a loop head of the generalized theory, which is never in EXLEN or EXTRA either
    ('Zlib.proof.roundtrip.RTIGDefs',
     "    dstep_post G pos inp ob flush m (stepf2 flush lenfix_list distfix_list m).",
     """    dstep_post G pos inp ob flush m (stepf2 flush lenfix_list distfix_list m).

(* the machine at a loop head is never in EXLEN or EXTRA (the header modes are not loop heads here) *)
Lemma kd_not_ext G pos inp ob m : Kd G pos inp ob m -> m_mode m <> EXLEN /\\ m_mode m <> EXTRA.
Proof.
  intros K. destruct (kd_at _ _ _ _ _ K) as (_ & A). unfold m_mode.
  unfold HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, Zlib.proof.inflate.Model.TYPE, TYPEDO, STORED, COPY_, COPY, TABLE,
    LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, CHECK, LENGTH, DONE in *.
  repeat match goal with H: _ \\/ _ |- _ => destruct H end;
    repeat match goal with H: _ /\\ _ |- _ => destruct H end; try contradiction; split; lia.
Qed."""),
    ('Zlib.proof.roundtrip.RTIGDecDec',
     "split; [change Int.max_signed with (2 ^ 31 - 1) in A; lia|].",
     "split; [change Int.max_unsigned with (2 ^ 32 - 1) in A; lia|]."),
    ('Zlib.proof.roundtrip.RTIGDecTab',
     """  mwf3 m -> m_leave m = 0 ->
  (forall fl, stepf2 fl lenfix_list distfix_list m = ttab_run fl P) ->""",
     """  m_mode m <> EXLEN /\\ m_mode m <> EXTRA -> mwf3 m -> m_leave m = 0 ->
  (forall fl, stepf2 fl lenfix_list distfix_list m = ttab_run fl P) ->"""),
    ('Zlib.proof.roundtrip.RTIGDecTab', "  intros OK P0 PL E W L SE O.", "  intros OK P0 PL E NX W L SE O."),
    ('Zlib.proof.roundtrip.RTIGDecCall',
     "zf_ao z <= Int.max_signed ->\n  Zlength inp <= Int.max_signed -> bytes_ok inp ->",
     "zf_ao z <= Int.max_unsigned ->\n  Zlength inp <= Int.max_unsigned -> bytes_ok inp ->"),
    ('Zlib.proof.roundtrip.RTIGDecTrl',
     "change compcert.lib.Integers.Int.max_signed with 2147483647 in Hao. lia.",
     "change compcert.lib.Integers.Int.max_unsigned with 4294967295 in Hao. lia."),
    # the trailer: a zlib windowBits from the header's window to 15 gives wrap 5 too (RTIGDefs.dctx_ok uses
    # DecodeDefs.accepts, raised by cfg_wide_decode.py)
] + [('Zlib.proof.roundtrip.RTIGDecTrl', old, new) for (m, old, new) in base.PATCHES
     if m == 'Zlib.proof.rfc1951.DecTrl' and 'trl_wb_cases' in new]
