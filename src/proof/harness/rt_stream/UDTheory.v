(* Law rt_stream (data of any length): the deflate side's facts for main ([UDFacts.urts_dtheory_stmt]) from the
   deflate side of the round trips without size limits (RTK7: what the output of a run that ends is, for the
   invariant K7) and deflate() on the wide deflate_api invariant (RTK7Api.api7_deflate_stmt: every call is
   defined, its codes, Iapi7 kept). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.harness.rt_stream.UDFacts.
Require Import Zlib.proof.roundtrip.RTK7Api.
Require Import Zlib.proof.roundtrip.RTK7Init.
Require Import Zlib.proof.roundtrip.RTK7Deflate.
Require Import Zlib.proof.roundtrip.RTK7Fpend.
Require Import Zlib.proof.roundtrip.RTK7Core.
Require Import Zlib.proof.roundtrip.RTK7Hdr.
Require Import Zlib.proof.roundtrip.RTK7Comp.
Require Zlib.proof.huffman.Lemmas.
Require Zlib.proof.roundtrip.RTBTheory.
Require Zlib.proof.deflate.InitStrm.
Require Zlib.proof.deflate.LawFacts Zlib.proof.deflate.LTApiInit Zlib.proof.deflate.LTCInitKit.
Import ListNotations.
Local Open Scope Z_scope.

(** Each deflate() call keeps the round trip's invariant K7 or ends in [dfinal], given its run and its codes
    (as RTK7Proof.rt_kfacts7 assembles it, for K7 itself). *)
Lemma udt_k7_deflate : kf7_deflate_stmt K7.
Proof.
  pose proof (proj1 Zlib.proof.huffman.Lemmas.huffman_lemmas) as Hov.
  pose proof (rtk7_core_ok Hov) as Hc.
  destruct (rtk7_comp_ok Hov) as (Hst & H1 & H2 & H3 & H4).
  exact (rtk7_deflate_ok Hov Hc rtk7_hdr_ok rtk7_fpend_ok Hst H1 H2 H3 H4).
Qed.

(** The invariant between main's deflate() calls: the round trip's invariant K7 (what the output is) and the wide
    deflate_api invariant Iapi7 (every call is defined), both without a dictionary; deflate's w_bits and no gzip
    header (they fix the stream that [RTFinal.dfinal] describes at the end), the output at most PTRDIFF_MAX
    bytes (total_out is its length) and strm->adler 32 bits. *)
Definition udj : urts_dinv := fun wbits D O fin s tin tout adler =>
  K7 [] (rwrap_of wbits) D O fin s tin tout adler /\
  Iapi7 W3 hinv7 [] (rwrap_of wbits) D O fin s tin tout adler /\
  d_w_bits s = rwbe wbits /\ d_gzhead s = None /\ Zlength O <= max_size /\ 0 <= adler < 4294967296.

(** For parameters in zlib.h's ranges deflateInit2_ returns Z_OK or Z_MEM_ERROR: its Z_STREAM_ERROR answers
    rejected parameters only ([rparams_ok] is deflate/LawFacts.params_ok). *)
Lemma udt_init_code level wbits mem strategy a1 a2 a3 a4 a5 z os z' code :
  rparams_ok level 8 wbits mem strategy = true ->
  c_deflateInit2_ true true false level 8 wbits mem strategy a1 a2 a3 a4 a5 z = Some (os, z', code) ->
  code = Z_OK \/ code = Z_MEM_ERROR.
Proof.
  intros P H.
  assert (P' : Zlib.proof.deflate.LawFacts.params_ok level 8 wbits mem strategy = true) by exact P.
  rewrite Zlib.proof.deflate.LTApiInit.init_shape in H. rewrite P' in H.
  destruct a1. 2:{ inversion H; subst; auto. }
  destruct (a2 && a3 && a4 && a5)%bool. 2:{ inversion H; subst; auto. }
  rewrite (Zlib.proof.deflate.LTCInitKit.init_eq _ _ _ _ _ _ P') in H.
  inversion H; subst; auto.
Qed.

(** deflate() without output space, on a state that is not Z_STREAM_ERROR's: deflate's entry check returns
    Z_BUF_ERROR at once with the stream unchanged but for msg. *)
Lemma udt_no_out s z flush s' z' code :
  c_deflate s z flush = Some (s', z', code) -> z_avail_out z = 0 -> code <> Z_STREAM_ERROR ->
  code = Z_BUF_ERROR /\ z' = set_z_msg z (Some Z_BUF_ERROR).
Proof.
  intros E A N. unfold c_deflate in E.
  destruct (bad_state s || (flush >? Z_BLOCK) || (flush <? 0))%bool.
  { inversion E; subst. exfalso; apply N; reflexivity. }
  unfold c_deflate_entry in E. rewrite A in E.
  destruct ((d_status s =? FINISH_STATE) && negb (flush =? Z_FINISH))%bool.
  { cbn in E. inversion E; subst. exfalso; apply N; reflexivity. }
  cbn in E. inversion E; subst. split; reflexivity.
Qed.

Theorem urts_dtheory : api7_deflate_stmt -> urts_dtheory_stmt.
Proof.
  intros AD. exists udj. constructor.
  - (* deflateInit2 *)
    intros level wbits mem strategy a1 a2 a3 a4 a5 z Hl Hw Hm Hs.
    destruct Zlib.proof.huffman.Lemmas.huffman_lemmas as [Hov Hbb].
    destruct (Zlib.proof.roundtrip.RTBTheory.rt_b_facts Hov Hbb) as [Hinit _].
    assert (H8 : rs32 8) by (unfold rs32; lia).
    destruct (Hinit level 8 wbits mem strategy a1 a2 a3 a4 a5 z Hl H8 Hw Hm Hs) as [Hex Hcodes].
    split; [exact Hex|].
    intros os z' code E Ecode. subst code.
    destruct (Hcodes os z' Z_OK E) as (_ & Hse & Hsome).
    split.
    { destruct (rparams_ok level 8 wbits mem strategy) eqn:P; [reflexivity|].
      assert (C : Z_OK = Z_STREAM_ERROR) by (apply Hse; reflexivity). discriminate C. }
    destruct (Hsome eq_refl) as (s & -> & Hgz).
    destruct (rtk7_init_ok level 8 wbits mem strategy a1 a2 a3 a4 a5 z s z' Hl H8 Hw Hm Hs E)
      as (Hwb & _ & HK0).
    destruct (Zlib.proof.deflate.InitStrm.init_ok_strm _ _ _ _ _ _ _ _ _ _ _ _ _ E) as (Ti & To & Ad & _).
    exists s. split; [reflexivity|].
    split; [exact HK0|].
    split; [destruct HK0 as [[HI _] | (_ & R & HR & _)]; [exact HI | discriminate HR]|].
    split; [exact Hwb|]. split; [exact Hgz|].
    split; [cbn; unfold max_size; lia|]. destruct Ad as [-> | ->]; lia.
  - (* deflateInit2's code *)
    intros level wbits mem strategy a1 a2 a3 a4 a5 z os z' code P E. exact (udt_init_code _ _ _ _ _ _ _ _ _ _ _ _ _ P E).
  - (* the counters *)
    intros wbits D O fin s tin tout adler (_ & HI & _ & Hgz & LO & Ha).
    destruct HI as (_ & _ & _ & _ & _ & _ & _ & _ & Ht & _ & _ & _ & (k & _ & Htin) & _).
    pose proof (Zlength_nonneg O).
    rewrite Htin. unfold u64.
    pose proof (Z.mod_pos_bound (Zlength D + k) 18446744073709551616 ltac:(lia)).
    unfold max_size in LO. split; [lia|]. split; [lia|]. split; [lia|exact Hgz].
  - (* deflate *)
    intros wbits D O fin s tin tout adler inb aout flush msg (HK & HI & Hwb & Hgz & LO & Ha)
      Hfl Hb Hin Hdin Hao Hout Hfin.
    pose proof HI as (_ & _ & _ & _ & _ & _ & _ & _ & Ht & _ & _ & LD & (k & Hk & Htin) & _).
    rewrite Zlength_nil in Hk. assert (k = 0) by lia. subst k.
    pose proof (Zlength_nonneg D) as LD0. pose proof (Zlength_nonneg inb) as Li0.
    pose proof (Zlength_nonneg O) as LO0.
    unfold max_size in *.
    assert (Htin' : tin = Zlength D).
    { rewrite Htin, Z.add_0_r. unfold u64. apply Z.mod_small. lia. }
    assert (Hfin' : forall R, fin = Some R -> flush = Z_FINISH /\ R = sublist 0 (Zlength inb) inb).
    { intros R ER. destruct (Hfin R ER) as [F1 F2]. split; [exact F1|].
      rewrite sublist_same by lia. symmetry; exact F2. }
    destruct (AD [] (rwrap_of wbits) D O fin s tin tout adler inb 0 aout flush msg HI Hfl Hb
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hfin')
      as (s' & z' & code & E & G & Wb & C & A' & Hcode & Hend & Hbuf & Post).
    assert (E' : c_deflate s (rzcall inb 0 (Zlength inb) tin aout tout adler msg) flush = Some (s', z', code)).
    { rewrite <- E. rewrite Z.sub_0_r. reflexivity. }
    destruct C as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
    assert (Hu : Zlength inb - z_avail_in z' = z_next_in z') by lia.
    assert (Hok : rcall_ok inb aout tin tout z').
    { unfold rcall_ok. split; [exact C1|]. split; [lia|]. split; [lia|]. split.
      { rewrite C4, Z.sub_0_r. unfold u64. rewrite Z.mod_small by lia. lia. }
      split; [lia|]. split; [exact C6|]. split; [exact C7|exact C8]. }
    assert (Hbuf' : code = Z_BUF_ERROR -> z_avail_in z' = Zlength inb /\ z_avail_out z' = aout).
    { intros Hc. destruct (Hbuf Hc) as [N1 N2]. split; [lia|exact N2]. }
    destruct (udt_k7_deflate [] (rwrap_of wbits) D O fin s tin tout adler inb aout flush msg s' z' code HK
                Hfl Hb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hfin E' G Hok Hcode Hend Hbuf')
      as (Hwb' & Fin).
    exists s', z', code. split; [exact E'|]. split; [exact Hok|]. split; [rewrite G; exact Hgz|].
    split.
    { intros A0. subst aout.
      assert (Ns : code <> Z_STREAM_ERROR) by (destruct Hcode as [-> | [-> | ->]]; discriminate).
      destruct (udt_no_out _ _ _ _ _ _ E' eq_refl Ns) as [-> ->]. split; reflexivity. }
    split; [exact Hend|].
    cbv zeta in Fin |- *. rewrite Hu in Fin |- *.
    destruct (code =? Z_STREAM_END) eqn:Ec.
    + rewrite Hwb, Hgz in Fin. exact Fin.
    + assert (Hne : code <> Z_STREAM_END) by (intros X; rewrite X, Z.eqb_refl in Ec; discriminate).
      specialize (Post Hne).
      split; [exact Fin|]. split; [exact Post|]. split; [rewrite Wb; exact Hwb|].
      split; [rewrite G; exact Hgz|].
      split; [rewrite Zlength_app; unfold max_size; lia|]. apply A'; exact Ha.
Qed.
