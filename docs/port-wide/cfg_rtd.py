"""Configuration of docs/port-wide/port.py for the deflate side of the round trips (src/proof/roundtrip/RTD*.v:
the functional theory of the compression functions, RTDSpecs / RTDFix / RTDV3 and their proofs, with the deflate
laws' safety theory they use, the verbatim copies RTDLT*.v) on streams of up to 2^32 - 1 bytes of input and of
output space, any total_in, total_out + avail_out below 2^64 (RTK7Defs.zin_ok7).  Used by RTK7Comp (RTK7Defs.comp_fspec7
0 .. 4) and RTK7Core (RTK7Defs.core_facts7).

deflate_stored compares len with `left + strm->avail_in` in 64 bits since fix F9: as in cfg_deflate.py, its
specifications need no bound on that sum."""

# modules whose declarations may be ported
PREFIXES = ['Zlib.proof.roundtrip.RTD']

# the compression functions, functional (RTD*) and safety (RTDLT*)
TARGETS = [
    'Zlib.proof.roundtrip.RTDStored2',
    'Zlib.proof.roundtrip.RTDFast',
    'Zlib.proof.roundtrip.RTDSlow3',
    'Zlib.proof.roundtrip.RTDHuff',
    'Zlib.proof.roundtrip.RTDRle',
    # the part specifications the compression functions take (RTDTheory.rt_kfacts gathers them)
    'Zlib.proof.roundtrip.RTDWriter',
    'Zlib.proof.roundtrip.RTDFill',
    'Zlib.proof.roundtrip.RTDLm2',
    'Zlib.proof.roundtrip.RTDFbo2',
]

# the bound 2^30 of the input and of the output space of a call (not the other uses of 2^30, e.g. w_size)
SUBST = [
    (r'\b(z_avail_(?:in|out) z0? <= |used <= )1073741824\b', r'\g<1>4294967295'),
]

# (module, old text after SUBST, new text)
PATCHES = [
    # the stream of a call (LTDefs.zin_ok): any total_in, total_out + avail_out below 2^64 (= RTK7Defs.zin_ok7)
    ('Zlib.proof.roundtrip.RTDLTDefs',
     '0 <= z_total_in z <= 1099511627776 /\\ 0 <= z_total_out z <= 1099511627776.',
     '0 <= z_total_in z <= 18446744073709551615 /\\\n  0 <= z_total_out z /\\ z_total_out z + z_avail_out z <= 18446744073709551615.'),
    # the output side inside a call (LTCSpecs.zout_ok): total_out + avail_out below 2^64
    ('Zlib.proof.roundtrip.RTDLTCSpecs',
     'z_total_out z + z_avail_out z <= 2199023255552.',
     'z_total_out z + z_avail_out z <= 18446744073709551615.'),
    # deflate_stored's clamp of len, `if (len > left + strm->avail_in) len = left + strm->avail_in;`, stores a
    # 32-bit value; the clamp is taken only when the sum is below MAX_STORED, so it does not wrap (as in
    # cfg_deflate.py; the two comparisons of len with the sum are in 64 bits since fix F9: no bound needed)
    ('Zlib.proof.roundtrip.RTDLTCStoredLoop',
     'Lemma ds_step : forall a, linv s0 z0 flush a ->',
     'Lemma ds_len_u32 (S : Z) : 0 <= S ->\n  (if MAX_STORED >? S then u32 S else MAX_STORED) = (if MAX_STORED >? S then S else MAX_STORED).\nProof.\n  intros H. unfold MAX_STORED. destruct (Z.gtb_spec 65535 S) as [L|L]; [apply u32_id; lia|reflexivity].\nQed.\n\nLemma ds_step : forall a, linv s0 z0 flush a ->'),
    ('Zlib.proof.roundtrip.RTDLTCStoredLoop',
     'rewrite !(u32_id (left + ai)) by lia.',
     'rewrite !(ds_len_u32 (left + ai)) by lia.'),
    # the generator renames the record core_facts but not its constructor
    ('Zlib.proof.roundtrip.RTDLTCore',
     "exact (Build_core_facts W3",
     "exact (Build_core_facts_w W3"),
    ('Zlib.proof.roundtrip.RTDV2Lemmas',
     "exact (Build_core_facts W3",
     "exact (Build_core_facts_w W3"),
    # RTDLTCStoredLoop.linv needs no port, but the generator cannot tell it from RTDLTCLiveKit.linv (ported):
    # the stored loop files name it ds_linv (RTK7GenAlias.v)
    ('Zlib.proof.roundtrip.RTDStoredLoopStep',
     "Require Import Zlib.proof.roundtrip.RTDLTCStoredSblk.",
     "Require Import Zlib.proof.roundtrip.RTDLTCStoredSblk.\nRequire Import Zlib.proof.roundtrip.RTK7GenAlias."),
    ('Zlib.proof.roundtrip.RTDStoredLoopStep',
     "forall a, linv s0 z0 flush a -> finv",
     "forall a, ds_linv s0 z0 flush a -> finv"),
    ('Zlib.proof.roundtrip.RTDStoredLoopStep',
     "| inl a' => linv s0 z0 flush a' /\\ finv",
     "| inl a' => ds_linv s0 z0 flush a' /\\ finv"),
    ('Zlib.proof.roundtrip.RTDStoredLoop',
     "assert (I0 : linv s z flush (s, z)).",
     "assert (I0 : ds_linv s z flush (s, z))."),
    ('Zlib.proof.roundtrip.RTDStoredLoop',
     "linv s z flush a -> finv s z p a -> ffin s z p b).",
     "ds_linv s z flush a -> finv s z p a -> ffin s z p b)."),
    ('Zlib.proof.roundtrip.RTDStoredLoop',
     "Require Import Zlib.proof.roundtrip.RTDStoredLoopStep.",
     "Require Import Zlib.proof.roundtrip.RTDStoredLoopStep.\nRequire Import Zlib.proof.roundtrip.RTK7GenAlias."),
    # the functional first phase of deflate_stored: the clamp of len as in the safety port
    ('Zlib.proof.roundtrip.RTDStoredLoopStep',
     "rewrite !(u32_id (left + ai)) by lia.",
     "rewrite !(ds_len_u32 (left + ai)) by lia."),
]

# fast / slow / huff / rle (RTK7Comp.v): the generator turns a fully qualified name of an unported lemma of a
# ported module (Zlib.proof.roundtrip.M.x) into Zlib.proof.wide.roundtrip.M.x, which does not exist (the wide
# module only re-exports x); the shorter qualified name M.x is left alone and still denotes the original
PATCHES += [
    ('Zlib.proof.roundtrip.RTDFastMatchLoop',
     "pose proof Zlib.proof.roundtrip.RTDLTCLmKit.ins_ok as Hins.",
     "pose proof RTDLTCLmKit.ins_ok as Hins."),
    ('Zlib.proof.roundtrip.RTDHuff',
     "Zlib.proof.roundtrip.RTDFix.ins_fspec2 -> lm_fspec",
     "RTDFix.ins_fspec2 -> lm_fspec"),
    ('Zlib.proof.roundtrip.RTDHuff',
     "destruct (Zlib.proof.roundtrip.RTDLTCTrees2.trees_ok2 Hov)",
     "destruct (RTDLTCTrees2.trees_ok2 Hov)"),
    ('Zlib.proof.roundtrip.RTDHuff',
     "(Zlib.proof.roundtrip.RTDHuffLit.hflit_ok Htal)",
     "(RTDHuffLit.hflit_ok Htal)"),
    ('Zlib.proof.roundtrip.RTDHuff',
     "(Zlib.proof.roundtrip.RTDFix.ins_fix Hins)",
     "(RTDFix.ins_fix Hins)"),
]
