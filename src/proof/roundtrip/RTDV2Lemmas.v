(* RT-D: lemmas of the assembly over interface v2 (RTDV2.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDV2.
Require Import Zlib.proof.roundtrip.RTDLTCHuffKit Zlib.proof.roundtrip.RTDLTCMisc Zlib.proof.roundtrip.RTDLTCSpecs2 Zlib.proof.roundtrip.RTDLTCFill Zlib.proof.roundtrip.RTDLTCLm Zlib.proof.roundtrip.RTDLTCTrees2 Zlib.proof.roundtrip.RTDLTCStored2 Zlib.proof.roundtrip.RTDLTCFast2 Zlib.proof.roundtrip.RTDLTCSlow2 Zlib.proof.roundtrip.RTDLTCHuff2 Zlib.proof.roundtrip.RTDLTCRle2 Zlib.proof.roundtrip.RTDLTCLive2 Zlib.proof.roundtrip.RTDLTCInit Zlib.proof.roundtrip.RTDLTCDict Zlib.proof.roundtrip.RTDLTCDict3 Zlib.proof.roundtrip.RTDLTCStillFill Zlib.proof.roundtrip.RTDLTCStillStored Zlib.proof.roundtrip.RTDLTCStillFast Zlib.proof.roundtrip.RTDLTCStillSlow Zlib.proof.roundtrip.RTDLTCStillHuff Zlib.proof.roundtrip.RTDLTCStillRle.
Import ListNotations.
Local Open Scope Z_scope.

(* the deflate laws' core facts for the witness W3 (= the body of RTDLTCore.core_theory) *)
Lemma W3_facts : Zlib.proof.huffman.Overlay.overlay_statement -> core_facts W3.
Proof.
  intros Hov.
  destruct (trees_ok2 Hov) as (Htal & Htf & Hroom).
  pose proof (fbo_ok Htf Hroom) as Hfbo. pose proof fpend2_ok as Hfp.
  pose proof fill_ok as Hfill. destruct lm_ok as [Hins Hlm].
  exact (Build_core_facts W3 W3_prm W3_pos W3_frame W3_init W3_tune W3_dict
           (core_compress3 Hfill Hins Hlm Htal Hfbo Hfp) (W3_still Hfill Hins Hlm Htal Hfbo Hfp)
           (core_live3 Hfp) W3_full W3_params).
Qed.

Lemma fn_of_level : forall s, fn_of s <> 0 -> d_level s <> 0.
Proof. intros s H E. unfold fn_of in H. rewrite E in H. apply H. reflexivity. Qed.

(* a compression function of a level <> 0: the v1 spec gives the v2 spec *)
Lemma comp_fix : Zlib.proof.huffman.Overlay.overlay_statement ->
  forall f c, f <> 0 ->
  (forall s z flush, prm s -> fn_of s = f -> c_compress_func s z flush = c s z flush) ->
  comp_fspec f c -> comp_fspec2 f c.
Proof.
  intros Hov f c Hf Hd Hc s z flush s' z' bs dict D BS syms p HW Ho Hq Hfl Hz Hw Ha Hfn Hdi HD HK Hp Hp8 R.
  assert (Hl : d_level s <> 0) by (apply fn_of_level; congruence).
  apply (kcore2_iff _ _ _ _ _ Hl) in HK.
  destruct (Hc s z flush s' z' bs dict D BS syms p HW Ho Hq Hfl Hz Hw Ha Hfn Hdi HD HK Hp Hp8 R)
    as (k & x & BS' & syms' & A & B & C & E).
  pose proof (W3_facts Hov) as CF.
  destruct (cf_compress W3 CF s z flush HW Ho Hq Hfl Hz Hw Ha) as (s1 & z1 & bs1 & evs & R1 & P1).
  rewrite (Hd s z flush (W3_prm s HW) Hfn), R in R1. inversion R1; subst s1 z1 bs1.
  destruct P1 as (_ & _ & Hsp & _).
  destruct Hsp as (_ & _ & _ & _ & _ & Hlv & _).
  assert (Hl' : d_level s' <> 0) by congruence.
  exists k, x, BS', syms'. split; [exact A|]. split; [apply (kcore2_iff _ _ _ _ _ Hl'); exact B|].
  split; assumption.
Qed.

Lemma comp_fix_c : Zlib.proof.huffman.Overlay.overlay_statement ->
  comp_fspec 1 c_deflate_fast -> comp_fspec 2 c_deflate_slow -> comp_fspec 3 c_deflate_huff ->
  comp_fspec 4 c_deflate_rle ->
  comp_fspec2 1 c_deflate_fast /\ comp_fspec2 2 c_deflate_slow /\ comp_fspec2 3 c_deflate_huff /\
  comp_fspec2 4 c_deflate_rle.
Proof.
  intros Hov H1 H2 H3 H4.
  repeat split; (eapply comp_fix; [exact Hov| discriminate | | eassumption]);
    intros s z flush Hp E; rewrite (compress_dispatch s z flush Hp), E; reflexivity.
Qed.
