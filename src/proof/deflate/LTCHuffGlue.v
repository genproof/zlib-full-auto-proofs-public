(** * deflate_huff part: composition lemmas for [hcrel] / [HFI] (Qed). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTCHuffKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Lemma same_prm_refl s : same_prm s s.
Proof. unfold same_prm; repeat split; reflexivity. Qed.

Lemma api_eq_refl s : api_eq s s.
Proof. unfold api_eq; repeat split; reflexivity. Qed.

Lemma same_prm_trans s1 s2 s3 : same_prm s1 s2 -> same_prm s2 s3 -> same_prm s1 s3.
Proof.
  intros (A1 & A2 & A3 & A4 & A5 & A6 & A7) (B1 & B2 & B3 & B4 & B5 & B6 & B7).
  unfold same_prm. rewrite B1, B2, B3, B4, B5, B6, B7. auto 10.
Qed.

Lemma api_eq_trans s1 s2 s3 : api_eq s1 s2 -> api_eq s2 s3 -> api_eq s1 s3.
Proof.
  intros (A1 & A2 & A3 & A4 & A5 & A6) (B1 & B2 & B3 & B4 & B5 & B6).
  unfold api_eq. rewrite B1, B2, B3, B4, B5, B6. auto 10.
Qed.

Lemma ev_ok_same_prm s0 s flush e : same_prm s0 s -> ev_ok s flush e -> ev_ok s0 flush e.
Proof.
  intros (E1 & E2 & E3 & E4 & E5 & E6 & E7). unfold ev_ok. rewrite E2, E4, E5, E6, E7. exact (fun H => H).
Qed.

Lemma Forall_ev_ok_same_prm s0 s flush evs :
  same_prm s0 s -> Forall (ev_ok s flush) evs -> Forall (ev_ok s0 flush) evs.
Proof.
  intros E H. eapply Forall_impl; [|exact H]. intros e. apply ev_ok_same_prm. exact E.
Qed.

Lemma ev_chain_app g evs1 g1 evs2 g2 :
  ev_chain g evs1 g1 -> ev_chain g1 evs2 g2 -> ev_chain g (evs1 ++ evs2) g2.
Proof.
  revert g. induction evs1 as [|e evs1 IH]; intros g H1 H2; cbn [ev_chain app] in *.
  - subst. exact H2.
  - destruct H1 as [H1a H1b]. split; [exact H1a|]. exact (IH _ H1b H2).
Qed.

Lemma sum_len_app evs1 evs2 : sum_len (evs1 ++ evs2) = sum_len evs1 + sum_len evs2.
Proof.
  unfold sum_len. induction evs1 as [|e evs1 IH]; cbn [fold_right app]; [lia|]. rewrite IH. lia.
Qed.

Lemma hcrel_trans s0 z0 flush s1 z1 evs1 s2 z2 evs2 :
  zall z0 -> adler_ok (d_wrap s0) (z_adler z0) ->
  hcrel s0 z0 flush s1 z1 evs1 -> hcrel s1 z1 flush s2 z2 evs2 -> hcrel s0 z0 flush s2 z2 (evs1 ++ evs2).
Proof.
  intros [Hz0 _] Ha0 (A1 & A2 & A3 & A4 & A5 & (k1 & x1 & K1 & B1 & U1) & A7 & A8)
    (C1 & C2 & C3 & C4 & C5 & (k2 & x2 & K2 & B2 & U2) & C7 & C8).
  assert (Ew : d_wrap s1 = d_wrap s0) by (destruct A5 as (_ & W & _); exact W).
  rewrite Ew in K2.
  unfold hcrel. split; [exact C1|]. split; [exact C2|]. split; [exact C3|].
  split; [eapply same_prm_trans; eauto|]. split; [eapply api_eq_trans; eauto|].
  split.
  { exists (k1 + k2), (x1 ++ x2). split; [eapply zstep_trans; eauto|].
    split; [unfold bytes in *; apply Forall_app; auto|]. rewrite sum_len_app. lia. }
  split; [eapply ev_chain_app; eauto|].
  apply Forall_app. split; [exact A8|]. eapply Forall_ev_ok_same_prm; [exact A4|exact C8].
Qed.

(** A step [s -> s3] that changes nothing the relation sees. *)
Lemma hcrel_hfr s0 z0 flush s z evs s3 :
  hcrel s0 z0 flush s z evs -> hfr s s3 -> W s3 -> huff_extra s3 -> outok s3 -> hcrel s0 z0 flush s3 z evs.
Proof.
  intros (A1 & A2 & A3 & A4 & A5 & (k & x & K & B & U) & A7 & A8) (F1 & F2 & F3 & F4) HW He Ho.
  unfold hcrel. split; [exact HW|]. split; [exact He|]. split; [exact Ho|].
  split; [eapply same_prm_trans; eauto|]. split; [eapply api_eq_trans; eauto|].
  split; [exists k, x; split; [exact K|]; split; [exact B|]; rewrite F3; exact U|].
  split; [rewrite F4; exact A7|exact A8].
Qed.

Lemma hfr_trans s1 s2 s3 : hfr s1 s2 -> hfr s2 s3 -> hfr s1 s3.
Proof.
  intros (A1 & A2 & A3 & A4) (B1 & B2 & B3 & B4). unfold hfr.
  split; [eapply same_prm_trans; eauto|]. split; [eapply api_eq_trans; eauto|].
  split; [lia|]. intros t. rewrite B4. apply A4.
Qed.

Lemma hcrel_refl s z flush :
  W s -> huff_extra s -> outok s -> zall z -> adler_ok (d_wrap s) (z_adler z) -> hcrel s z flush s z [].
Proof.
  intros HW He Ho Hz Ha. unfold hcrel.
  split; [exact HW|]. split; [exact He|]. split; [exact Ho|].
  split; [apply same_prm_refl|]. split; [apply api_eq_refl|].
  split; [exists 0, []; split; [apply zstep_refl; auto|split; [constructor|cbn; lia]]|].
  split; [cbn; reflexivity|constructor].
Qed.

Lemma fn_of_hcrel s0 z0 flush s z evs : hcrel s0 z0 flush s z evs -> fn_of s = fn_of s0.
Proof. intros (_ & _ & _ & A4 & _). exact (fn_of_same_prm' _ _ A4). Qed.

Lemma wrap_hcrel s0 z0 flush s z evs : hcrel s0 z0 flush s z evs -> d_wrap s = d_wrap s0.
Proof. intros (_ & _ & _ & _ & (_ & W & _) & _). exact W. Qed.

(** [hcrel_trans] through a step [s1 -> s3] of [hfr] (s3 need not satisfy W: a full sym_buf). *)
Lemma hcrel_trans_fr s0 z0 flush s1 z1 evs1 s3 s2 z2 evs2 :
  zall z0 -> adler_ok (d_wrap s0) (z_adler z0) ->
  hcrel s0 z0 flush s1 z1 evs1 -> hfr s1 s3 -> hcrel s3 z1 flush s2 z2 evs2 ->
  hcrel s0 z0 flush s2 z2 (evs1 ++ evs2).
Proof.
  intros [Hz0 _] Ha0 (A1 & A2 & A3 & A4 & A5 & (k1 & x1 & K1 & B1 & U1) & A7 & A8) (F1 & F2 & F3 & F4)
    (C1 & C2 & C3 & C4 & C5 & (k2 & x2 & K2 & B2 & U2) & C7 & C8).
  assert (Ew : d_wrap s3 = d_wrap s0) by (destruct A5 as (_ & W & _); destruct F2 as (_ & W' & _); congruence).
  rewrite Ew in K2. rewrite F4 in C7. rewrite F3 in U2.
  assert (A4' := same_prm_trans _ _ _ A4 F1). assert (A5' := api_eq_trans _ _ _ A5 F2).
  unfold hcrel. split; [exact C1|]. split; [exact C2|]. split; [exact C3|].
  split; [eapply same_prm_trans; eauto|]. split; [eapply api_eq_trans; eauto|].
  split.
  { exists (k1 + k2), (x1 ++ x2). split; [eapply zstep_trans; eauto|].
    split; [unfold bytes in *; apply Forall_app; auto|]. rewrite sum_len_app. lia. }
  split; [eapply ev_chain_app; eauto|].
  apply Forall_app. split; [exact A8|]. eapply Forall_ev_ok_same_prm; [exact A4'|exact C8].
Qed.

Lemma Forall_last0_app evs e : Forall (fun e => ev_last e = 0) evs -> ev_last e = 0 ->
  Forall (fun e => ev_last e = 0) (evs ++ [e]).
Proof. intros H He. apply Forall_app. split; [exact H|]. constructor; [exact He|constructor]. Qed.

Lemma quiet_of_flush s z :
  outok s -> d_bi_valid s <= 7 -> (d_pending s = 0 \/ z_avail_out z = 0) -> z_avail_out z <> 0 -> quiet s.
Proof.
  intros (_ & _ & _ & _ & _ & Hpo) Hbv [Hp|Hz] Hn; [|contradiction].
  unfold quiet. split; [exact Hp|]. split; [exact (Hpo Hp)|exact Hbv].
Qed.
