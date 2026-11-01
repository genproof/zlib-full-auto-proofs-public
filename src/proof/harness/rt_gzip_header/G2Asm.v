(* Law rt_gzip_header on the round-2 harness: the assembly of harness_safe (QuickProof.Assembly, as round 1's
   Asm.v for the bounded harness) from main's body (G2MainDefs.body_main2_stmt), the harness's helpers
   (G2MainDefs.rtg2_helpers_stmt), the laws_common.h helpers (laws_common_ok), inflate()'s and inflateGetHeader's
   bodies against the v9 / v8 header specs (RTH9Spec.inflate_body9_stmt), deflate()'s body against
   DSpecN.deflate_specN with its input-carrying callees (DSpecN.deflate_bodyN_stmt) and the model facts of the
   deflate loop (G2DFacts) and of the inflate loop (G2IFacts); every other body (deflate.c, trees.c, inflate.c's
   other functions with Spec5's specs, inftrees.c, adler32.c, crc32.c, zutil.c, libc.c) and the globals
   (G2MainDefs.rtg2_globals_stmt, G2Globals.v) are proved inside.  The pieces are in G2AsmKit.v, the slowest
   entries in G2AsmE1.v, G2AsmE2.v and G2AsmE3.v. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.deflate.DSpecN Zlib.proof.roundtrip.RTH9Spec.
Require Zlib.proof.harness.rt_gzip_header.G2DFacts Zlib.proof.harness.rt_gzip_header.G2IFacts.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainDefs.
Require Zlib.contracts.rt_gzip_header.

Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Zlib.proof.adler32.Body_adler32.
Require Zlib.proof.adler32.Body_adler32_z.
Require Zlib.proof.crc32.Body_crc32.
Require Zlib.proof.crc32.Body_crc32_z.
Require Zlib.proof.zutil.Spec.
Require Zlib.proof.zutil.Libc.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.deflate.Obligations9.
Require Zlib.proof.deflate.Body_leaf.
Require Zlib.proof.deflate.Body_window.
Require Zlib.proof.deflate.Body_api.
Require Zlib.proof.deflate.Body_api9.
Require Zlib.proof.inflate.BodySmall.
Require Zlib.proof.inflate_api.Body5_reset.
Require Zlib.proof.roundtrip.RTRSLaw.
Require Import Zlib.proof.harness.rt_gzip_header.CS.
Require Import Zlib.proof.harness.rt_gzip_header.G2AsmKit.
Require Zlib.proof.harness.rt_gzip_header.G2AsmE1.
Require Zlib.proof.harness.rt_gzip_header.G2AsmE2.
Require Zlib.proof.harness.rt_gzip_header.G2AsmE3.
Require Import Zlib.harness.rt_gzip_header.code.
#[local] Existing Instance Zlib.proof.harness.rt_gzip_header.CS.CS.

Lemma rtg2_core : body_main2_stmt -> rtg2_helpers_stmt -> laws_common_ok ->
  Zlib.proof.roundtrip.RTH9Spec.inflate_body9_stmt -> Zlib.proof.deflate.DSpecN.deflate_bodyN_stmt ->
  Zlib.proof.harness.rt_gzip_header.G2DFacts.g2_dfacts_stmt ->
  Zlib.proof.harness.rt_gzip_header.G2IFacts.g2_ifacts_stmt ->
  harness_safe Zlib.contracts.rt_gzip_header.whole_prog.
Proof.
  intros BMS HH LC I9 DN DF IF.
  destruct I9 as [fast [CC [Hfast9 [Hinflate9 Hgethead8]]]].
  destruct DN as (GN & HM & HCC & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
  destruct (gn_shape GN HM) as (g1 & g2 & g3 & g4 & g5 & g6 & g7 & g8 & ->).
  unfold GNc in HCC. rewrite !Forall_cons_iff in HCC. cbn [snd] in HCC.
  destruct HCC as (CC1 & CC2 & CC3 & CC4 & CC5 & CC6 & CC7 & CC8 & _).
  pose proof (N1 NullExtension.Espec) as B_read_buf.
  pose proof (N2 NullExtension.Espec) as B_flush_pending.
  pose proof (N3 NullExtension.Espec) as B_fill_window.
  pose proof (N4 NullExtension.Espec) as B_stored.
  pose proof (N5 NullExtension.Espec) as B_dfast.
  pose proof (N6 NullExtension.Espec) as B_slow.
  pose proof (N7 NullExtension.Espec) as B_rle.
  pose proof (N8 NullExtension.Espec) as B_huff.
  pose proof (N9 NullExtension.Espec) as B_deflate.
  change (Zlib.proof.deflate.DSpecN.gn_spec (GNc g1 g2 g3 g4 g5 g6 g7 g8) D._read_buf (snd read_buf_spec))
    with (D._read_buf, g1) in B_read_buf.
  change (Zlib.proof.deflate.DSpecN.gn_spec (GNc g1 g2 g3 g4 g5 g6 g7 g8) D._flush_pending
            (snd flush_pending_spec)) with (D._flush_pending, g2) in B_flush_pending.
  change (Zlib.proof.deflate.DSpecN.gn_spec (GNc g1 g2 g3 g4 g5 g6 g7 g8) D._fill_window (snd fill_window_spec))
    with (D._fill_window, g3) in B_fill_window.
  change (Zlib.proof.deflate.DSpecN.gn_spec (GNc g1 g2 g3 g4 g5 g6 g7 g8) D._deflate_stored
            (snd deflate_stored_spec)) with (D._deflate_stored, g4) in B_stored.
  change (Zlib.proof.deflate.DSpecN.gn_spec (GNc g1 g2 g3 g4 g5 g6 g7 g8) D._deflate_fast (snd deflate_fast_spec))
    with (D._deflate_fast, g5) in B_dfast.
  change (Zlib.proof.deflate.DSpecN.gn_spec (GNc g1 g2 g3 g4 g5 g6 g7 g8) D._deflate_slow (snd deflate_slow_spec))
    with (D._deflate_slow, g6) in B_slow.
  change (Zlib.proof.deflate.DSpecN.gn_spec (GNc g1 g2 g3 g4 g5 g6 g7 g8) D._deflate_rle (snd deflate_rle_spec))
    with (D._deflate_rle, g7) in B_rle.
  change (Zlib.proof.deflate.DSpecN.gn_spec (GNc g1 g2 g3 g4 g5 g6 g7 g8) D._deflate_huff (snd deflate_huff_spec))
    with (D._deflate_huff, g8) in B_huff.
  pose proof (Hgethead8 NullExtension.Espec) as B_gethead.
  destruct HH as [B_string B_same].
  destruct LC as (B_upto & B_clip & B_any & B_copy & B_eq & B_offer & B_new).
  destruct Zlib.proof.inflate_api.Body5_reset.api5_reset as [_ Hreset].
  destruct (Hreset NullExtension.Espec) as (B_resetkeep & _ & _ & _).
  pose proof (Zlib.proof.harness.rt_gzip_header.G2AsmE1.rtg2_entry_init2 fast g1 g2 g3 g4 g5 g6 g7 g8) as E_deflate_init2.
  pose proof (Zlib.proof.harness.rt_gzip_header.G2AsmE2.rtg2_entries2 fast g1 g2 g3 g4 g5 g6 g7 g8) as E2.
  rewrite !Forall_cons_iff in E2. destruct E2 as (E_deflate_end & E_inflate_init2 & E_reset2 & E_upd & _).
  pose proof (Hinflate9 NullExtension.Espec) as B_inflate.
  pose proof (Hfast9 NullExtension.Espec) as B_fast.
  pose proof (@Zlib.proof.inflate.BodySmall.body_inflate_fixed NullExtension.Espec) as B_fixed.
  pose proof (@Zlib.proof.inflate.BodySmall.body_inflateStateCheck NullExtension.Espec) as B_check.
  pose proof rtg2_trees_bodies as TB.
  destruct TB as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & T15 & T16 &
                  T17 & T18 & T19 & T20).
  destruct Zlib.proof.deflate.Body_leaf.deflate_leaf as (_ & D2 & _ & D4 & D6 & D13).
  destruct Zlib.proof.deflate.Body_window.deflate_window as (_ & D5).
  destruct Zlib.proof.deflate.Body_api.deflate_api_bodies as (_ & _ & D16 & _ & _ & D19 & D20 & _).
  destruct Zlib.proof.deflate.Body_api9.deflate_api_bodies9 as (D14 & D15 & _).
  unfold ob_bi_reverse, ob_bi_flush, ob_bi_windup, ob_tr_flush_bits, ob_tr_align, ob_tr_stored_block,
    ob_gen_codes, ob_pqdownheap, ob_gen_bitlen, ob_build_tree, ob_scan_tree, ob_build_bl_tree,
    ob_detect_data_type, ob_init_block, ob_send_tree, ob_send_all_trees, ob_compress_block, ob_tr_static_init,
    ob_tr_init, ob_tr_flush_block, ob_read_buf, ob_putShortMSB, ob_flush_pending, ob_slide_hash,
    ob_longest_match, ob_lm_init, ob_fill_window, ob_deflate_stored, ob_deflate_fast, ob_deflate_slow,
    ob_deflate_rle, ob_deflate_huff, ob_deflateStateCheck, ob_deflateResetKeep9, ob_deflateReset9,
    ob_deflateSetHeader, ob_deflateTune, ob_deflatePrime, ob_deflateBound_z, ob_deflateBound,
    ob_deflateSetDictionary, ob_deflateEnd, ob_deflateInit2_9, ob_deflate, ob_deflateParams in *.
  pose proof (Zlib.proof.harness.rt_gzip_header.G2AsmE3.rtg2_entry_main fast g1 g2 g3 g4 g5 g6 g7 g8 BMS DF IF)
    as E_main.
  pose proof (Zlib.proof.harness.rt_gzip_header.G2AsmE3.rtg2_entries3 fast g1 g2 g3 g4 g5 g6 g7 g8) as E3.
  rewrite !Forall_cons_iff in E3. destruct E3 as (E_reset & E_table & _).
  change Zlib.contracts.rt_gzip_header.whole_prog with p.
  harness_safe_by_specs CS (G fast g1 g2 g3 g4 g5 g6 g7 g8) main_post_TT.
  - reflexivity.
  - apply Forall_cons; [exact E_main | ].
    entry_fast T1. entry_fast T2. entry_fast T3. entry_fast T4. entry_fast T5.
    entry_fast T6. entry_fast T7. entry_fast T8. entry_fast T9. entry_fast T10.
    entry_fast T11. entry_fast T12. entry_fast T13. entry_fast T14. entry_fast T15.
    entry_fast T16. entry_fast T17. entry_fast T18. entry_fast T19. entry_fast T20.
    entry_cc B_read_buf CC1. entry_fast D2. entry_cc B_flush_pending CC2. entry_fast D4.
    entry_fast D5. entry_fast D6. entry_cc B_fill_window CC3. entry_cc B_stored CC4.
    entry_cc B_dfast CC5. entry_cc B_slow CC6. entry_cc B_rle CC7. entry_cc B_huff CC8.
    entry_fast D13. entry_fast D14. entry_fast D15.
    entry_fast D16. entry_fast D19. entry_fast D20.
    apply Forall_cons; [exact E_deflate_end | ]. apply Forall_cons; [exact E_deflate_init2 | ]. entry_fast B_deflate.
    apply Forall_cons; [exact E_inflate_init2 | ].
    entry_fast B_inflate.
    entry_fast B_gethead.
    apply Forall_cons; [exact E_reset | ].
    apply Forall_cons; [exact E_reset2 | ].
    entry_fast B_resetkeep.
    entry_fast B_check.
    apply Forall_cons; [exact E_upd | ].
    entry_cc B_fast CC.
    entry_fast B_fixed.
    apply Forall_cons; [exact E_table | ].
    entry_fast Zlib.proof.adler32.Body_adler32.body_adler32.
    entry_fast Zlib.proof.adler32.Body_adler32_z.body_adler32_z.
    entry_fast Zlib.proof.crc32.Body_crc32.body_crc32.
    entry_fast Zlib.proof.crc32.Body_crc32_z.body_crc32_z.
    entry_fast (@Zlib.proof.zutil.Spec.body_zcalloc CS).
    entry_fast (@Zlib.proof.zutil.Spec.body_zcfree CS).
    entry_fast (@Zlib.proof.zutil.Libc.body_memcpy CS).
    entry_fast (@Zlib.proof.zutil.Libc.body_memset CS).
    entry_fast B_string.
    entry_fast B_same.
    entry_fast B_upto.
    entry_fast B_clip.
    entry_fast B_any.
    entry_fast B_copy.
    entry_fast B_eq.
    entry_fast B_offer.
    entry_fast B_new.
    entry_external (@external_ok_malloc CS).
    entry_external (@external_ok_free CS).
    entry_external (@external_ok_u32 CS).
    entry_external (@external_ok_u8 CS).
    entry_external (@external_ok_size CS).
    entry_external (@external_ok_bytes CS).
    entry_external (@external_ok_assert CS).
    entry_external (@external_ok_assume CS).
    apply Forall_nil.
Qed.

