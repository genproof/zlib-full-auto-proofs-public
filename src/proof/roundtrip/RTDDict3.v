(* RT-D part DICT over interface v3 (RTDV3.v, Krt3): deflateSetDictionary, from the v2
   result RTDDict2.rtd_dict_ok2: with nothing read and nothing produced, KF3 and KF2 agree. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDV3.
Require Import Zlib.proof.roundtrip.RTDLTCMisc Zlib.proof.roundtrip.RTDDict2.
Import ListNotations.
Local Open Scope Z_scope.

(* a zlib header byte FLG exists for every window size and FDICT *)
Lemma zflg_exists : forall wb fd, 9 <= wb <= 15 -> exists flg, zflg_ok wb fd flg.
Proof.
  intros wb fd Hwb.
  assert (Hc : wb = 9 \/ wb = 10 \/ wb = 11 \/ wb = 12 \/ wb = 13 \/ wb = 14 \/ wb = 15) by lia.
  destruct fd;
  destruct Hc as [->|[->|[->|[->|[->|[->| ->]]]]]];
  match goal with |- exists flg, zflg_ok ?w ?f flg =>
    let v := eval vm_compute in
      (32 * (if f then 1 else 0) + (31 - (zcmf w * 256 + 32 * (if f then 1 else 0)) mod 31) mod 31) in
    exists v; unfold zflg_ok; split; [lia|split; reflexivity] end.
Qed.

(* nothing produced, the header not started: some header of [khdr] (the bytes produced, none, are its prefix) *)
Lemma khdr_exists : forall dict wrap fin x tin tout adler,
  Iapi W3 hinv dict wrap [] [] fin x tin tout adler ->
  d_status x <> BUSY_STATE -> d_status x <> FINISH_STATE ->
  exists HDR, khdr dict wrap x HDR /\ [] ++ pend x = sublist 0 (Zlength ([] ++ pend x)) HDR.
Proof.
  intros dict wrap fin x tin tout adler HI Hb Hf.
  destruct HI as ([[HW _] _] & _ & Hwr & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hph).
  assert (Hpe : d_pending x = 0).
  { destruct Hph as [P0 | (_ & [P1 | [P2 | P3]])].
    - destruct P0 as (_ & _ & _ & _ & Hp & _). exact Hp.
    - destruct P1 as (_ & _ & Hne & _). congruence.
    - destruct P2 as (Hst & _). contradiction.
    - destruct P3 as (Hst & _). contradiction. }
  assert (Hpend : pend x = []).
  { unfold pend. rewrite Hpe, Z.add_0_r. apply sublist_nil'. reflexivity. }
  rewrite Hpend. cbn [app]. rewrite Zlength_nil.
  assert (Hwb : 9 <= d_w_bits x <= 15) by (destruct HW as ((A & _) & _); exact A).
  unfold khdr.
  destruct (Z.eqb_spec wrap 0) as [E0|E0].
  - exists []. split; reflexivity.
  - destruct (Z.eqb_spec wrap 1) as [E1|E1].
    + destruct (zflg_exists (d_w_bits x) (negb match dict with [] => true | _ => false end) Hwb) as [flg Hf'].
      eexists. split; [exists flg; split; [exact Hf'|reflexivity]|].
      rewrite sublist_nil'; reflexivity.
    + eexists. split; [exists 0; split; [left; reflexivity|reflexivity]|].
      rewrite sublist_nil'; reflexivity.
Qed.

Lemma KF3_KF2 : forall dict wrap fin x tin tout adler,
  Iapi W3 hinv dict wrap [] [] fin x tin tout adler ->
  (KF3 dict wrap [] [] fin x tin tout adler <-> KF2 dict wrap [] [] fin x tin tout adler).
Proof.
  intros dict wrap fin x tin tout adler HI.
  pose proof HI as ([[HW _] _] & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hdz & _).
  destruct (Hdz eq_refl) as (Hla & Hsb & _).
  pose proof HW as (_ & _ & _ & _ & _ & _ & _ & syms0 & Hwt).
  destruct (W_empty x syms0 HW Hwt Hla Hsb) as [Hma _].
  unfold KF3, KF2. split.
  - intros (G & BS & syms & K & P). split; [exact G|]. exists BS, syms.
    split; [apply (kcore3_iff _ _ _ _ _ Hma); exact K|].
    destruct P as [(P1 & P2 & P3 & P4 & _) | P]; [left; auto|right; exact P].
  - intros (G & BS & syms & K & P). split; [exact G|]. exists BS, syms.
    split; [apply (kcore3_iff _ _ _ _ _ Hma); exact K|].
    destruct P as [(P1 & P2 & P3 & P4) | P]; [left|right; exact P].
    split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|].
    exact (khdr_exists dict wrap fin x tin tout adler HI P1 P2).
Qed.

Theorem rtd_dict_ok3 : Zlib.proof.huffman.Overlay.overlay_statement -> fill_fspec -> ins_fspec2 ->
  kf_dict_stmt Krt3.
Proof.
  intros Hov Hff Hins wrap s tin tout adler d ain aout msg s' z' code [HI HK] Hd Hdl Hain Haout E Hc Hcw.
  apply (KF3_KF2 _ _ _ _ _ _ _ HI) in HK.
  destruct (rtd_dict_ok2 Hov Hff Hins wrap s tin tout adler d ain aout msg s' z' code (conj HI HK)
              Hd Hdl Hain Haout E Hc Hcw) as (Hwb & Hgz & HI' & HK').
  split; [exact Hwb|]. split; [exact Hgz|]. split; [exact HI'|].
  apply (KF3_KF2 _ _ _ _ _ _ _ HI'). exact HK'.
Qed.
