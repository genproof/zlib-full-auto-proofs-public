"""Configuration of docs/port-wide/port.py for the core of the deflate laws' model theory: the compression
functions (deflate_stored, deflate_fast, deflate_slow, deflate_huff, deflate_rle with fill_window, longest_match,
_tr_tally, FLUSH_BLOCK, flush_pending) and the facts about calls that consume nothing (LTCStill*) or finish at
level 0 (LTCLive2), on the streams LTWIface.zin_okw: up to 2^32 - 1 bytes of input and of output space, any
total_in, total_out + avail_out below 2^64.  The assembly (LTWIface.core_facts_w, LTCore.core_compress3 /
W3_still / core_live3 for these streams) is written by hand next to the generated files (src/proof/deflate/
LTWCore.v)."""

# modules whose declarations may be ported
PREFIXES = ['Zlib.proof.deflate.LTC']

# what the compression stage needs: the imports of LTCore.v without deflateInit2_ and deflateSetDictionary,
# which do not depend on the stream of a call, and without LTCMisc, LTCLm and LTCTrees2, whose ports no proof uses
TARGETS = [
    'Zlib.proof.deflate.LTCHuffKit',
    'Zlib.proof.deflate.LTCSpecs2',
    'Zlib.proof.deflate.LTCFill',
    'Zlib.proof.deflate.LTCStored2',
    'Zlib.proof.deflate.LTCFast2',
    'Zlib.proof.deflate.LTCSlow2',
    'Zlib.proof.deflate.LTCHuff2',
    'Zlib.proof.deflate.LTCRle2',
    'Zlib.proof.deflate.LTCLive2',
    'Zlib.proof.deflate.LTCStillFill',
    'Zlib.proof.deflate.LTCStillStored',
    'Zlib.proof.deflate.LTCStillFast',
    'Zlib.proof.deflate.LTCStillSlow',
    'Zlib.proof.deflate.LTCStillHuff',
    'Zlib.proof.deflate.LTCStillRle',
]

# the bounds 2^30 of the input and of the output space (LTCSpecs.zin_in; the stored loop's hypotheses), and the
# stream of a call (LTDefs.zin_ok, outside these modules) replaced by its wide version LTWIface.zin_okw
SUBST = [
    (r'\b1073741824\b', '4294967295'),
    (r'\bzin_ok\b', 'zin_okw'),
]

# (module, old text after SUBST, new text)
PATCHES = [
    # the wide stream of a call is LTWIface's
    ('Zlib.proof.deflate.LTCSpecs',
     "Require Export Zlib.proof.deflate.LTCW.",
     "Require Export Zlib.proof.deflate.LTCW.\nRequire Export Zlib.proof.deflate.LTWIface."),
    # total_out + avail_out below 2^64 (LTDefs.zin_ok: total_out <= 2^40, avail_out <= 2^30)
    ('Zlib.proof.deflate.LTCSpecs',
     "z_total_out z + z_avail_out z <= 2199023255552.",
     "z_total_out z + z_avail_out z <= 18446744073709551615."),

    # deflate_stored's clamp of len, `if (len > left + strm->avail_in) len = left + strm->avail_in;`, stores a
    # 32-bit value; the clamp is taken only when the sum is below MAX_STORED, so it does not wrap.  (Its two
    # comparisons of len with the sum are in 64 bits since fix F9: no wrap either, whatever the input.)
    ('Zlib.proof.deflate.LTCStoredLoop',
     "Lemma ds_step : forall a, linv s0 z0 flush a ->",
     "Lemma ds_len_u32 (S : Z) : 0 <= S ->\n"
     "  (if MAX_STORED >? S then u32 S else MAX_STORED) = (if MAX_STORED >? S then S else MAX_STORED).\n"
     "Proof.\n"
     "  intros H. unfold MAX_STORED. destruct (Z.gtb_spec 65535 S) as [L|L]; [apply u32_id; lia|reflexivity].\n"
     "Qed.\n\n"
     "Lemma ds_step : forall a, linv s0 z0 flush a ->"),
    ('Zlib.proof.deflate.LTCStoredLoop',
     "rewrite !(u32_id (left + ai)) by lia.",
     "rewrite !(ds_len_u32 (left + ai)) by lia."),
]
