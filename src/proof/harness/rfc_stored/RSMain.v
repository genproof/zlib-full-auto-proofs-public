(* Law rfc_stored: the main of harness/rfc_stored.c, proved against MainLib.main_core_spec R (RSGlobals.v)
   for ANY invariant P of the inflate loop with the facts of RSFacts.v (rs_facts P).  main calls zlib through
   the shared specifications: inflateInit2_ (Spec5), inflate (SpecW.inflate_specW: avail up to UINT_MAX, a
   raw stream's strm->adler any value), adler32_z / crc32_z (adler32/Spec.v, crc32/Spec.v), and the helpers of
   laws_common.h (alloc_any_bytes, copy_of, bytes_eq, ...) through theirs (laws_common/Spec.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5 Zlib.proof.inflate_api.SpecW.
Require Zlib.proof.adler32.Spec Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rfc_stored.RSLawCS Zlib.proof.harness.rfc_stored.RSGlobals
               Zlib.proof.harness.rfc_stored.RSFacts.
Require Import Zlib.harness.rfc_stored.code.
Require Import Zlib.proof.harness.rfc_stored.RSMainKit.
Require Import Zlib.proof.harness.rfc_stored.RSMainPure.
Require Import Zlib.proof.harness.rfc_stored.RSMainPre.
Require Import Zlib.proof.harness.rfc_stored.RSMainHdr.
Require Import Zlib.proof.harness.rfc_stored.RSMainBlk.
Require Import Zlib.proof.harness.rfc_stored.RSMainTrl.
Require Import Zlib.proof.harness.rfc_stored.RSMainInit.
Require Import Zlib.proof.harness.rfc_stored.RSMainLoop.

Definition Gmain : funspecs :=
  [inflateInit2__spec; inflate_specW; zcalloc_i; zcfree_i;
   Zlib.proof.adler32.Spec.adler32_z_spec; Zlib.proof.crc32.Spec.crc32_z_spec;
   upto_spec; clip_spec; any_bytes_spec; copy_of_spec; bytes_eq_spec; new_stream_spec;
   (_quickproof_malloc, malloc_spec'); nondet_u32_spec; gp_assert_spec; gp_assume_spec].

Lemma body_main P : rs_facts P -> semax_body (QPvarspecs p) Gmain f_main (_main, main_core_spec R).
Proof.
  intros RF. change Gmain with Gmain_k.
  start_function.
  unfold R. Intros.
  make_func_ptr Zlib.inflate.code._zcalloc. make_func_ptr Zlib.inflate.code._zcfree.
  gather_SEP (func_ptr' _ (gv inflate.code._zcalloc)) (func_ptr' _ (gv inflate.code._zcfree)).
  fold (zfuncs gv).
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  apply semax_seq with FF; [ | apply semax_ff].
  (* the chain of main's statements, segment by segment (RSMainPre .. RSMainLoop) *)
  eapply semax_pre; [ | apply (seg_pre_ok gv v_strm v_window_bits)].
  { unfold rs_pre0. entailer!. }
  intros n nb na wr window stp s0 dp d op ep FA.
  apply seg_hdr_ok; auto. intros c Hc.
  apply seg_blk_ok; auto. intros lens HL.
  pose proof (rs_ok_of n nb na wr window stp s0 dp d op c lens FA Hc HL) as OK.
  assert (Hlen: Zlength (rs_src wr c s0 (rs_pads wr s0 lens) lens d) = Zlength s0).
  { destruct OK as (Hwr & _ & _ & _ & Hf & Hsum & Hsl & _).
    apply rs_src_len; auto. }
  destruct FA as (Hn & Hnb & Hna & Hwr & Hw & Hs0 & Hd & Bs & Bd & Pst & Pdp & Pop).
  apply seg_trl_ok; [unfold rs_A_facts; auto 20 | auto | auto | ].
  apply (seg_init_ok P); [auto | unfold rs_A_facts; auto 20 | auto | auto | auto | ].
  apply seg_loop_ok; auto.
  - apply (rs_src_bytes wr window). auto.
  - rewrite Hlen, Hs0. unfold rs_hl, rs_tl. destruct (wr =? 1), (wr =? 2); lia.
  - lia.
Qed.
