(* The round trips without the limits of deflate_roundtrip: deflateSetHeader with a header of RTK7.rhdr_ok7 keeps
   K7 (RTK7Defs.v). *)
Require Import Zlib.proof.roundtrip.RTK7Defs.
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTDLTCore.
Import ListNotations.
Local Open Scope Z_scope.

(* The functional core and the expected gzip header bytes do not depend on the header record
   (as RTDPM3.pm3_kcore3_gzhead and RTDPM3.pm3_khdr2). *)
Lemma k7h_kcore3_gzhead : forall dict D BS syms s g,
  kcore3 dict D BS syms s -> kcore3 dict D BS syms (set_d_gzhead s g).
Proof. intros dict D BS syms s g H. destruct s. exact H. Qed.

Lemma k7h_khdr2 : forall dict s, exists HDR, khdr dict 2 s HDR.
Proof. intros dict s. unfold khdr. cbn. eexists. exists 0. split; [left; reflexivity|reflexivity]. Qed.

(* Before the first deflate() call (no output yet, not in the deflate or finish phase) nothing is pending:
   RTDPM3.pm3_pend0 for Iapi7. *)
Lemma k7h_pend0 : forall W HI dict wrap D fin s tin tout adler,
  Iapi7 W HI dict wrap D [] fin s tin tout adler -> d_status s <> BUSY_STATE -> d_status s <> FINISH_STATE ->
  pend s = [].
Proof.
  intros W HI dict wrap D fin s tin tout adler HI' N1 N2.
  destruct HI' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hph).
  destruct Hph as [P0 | (_ & [P1 | [P2 | P3]])].
  - destruct P0 as (_ & _ & _ & _ & Hp & _). unfold pend. rewrite Hp, Z.add_0_r.
    apply sublist_nil.
  - destruct P1 as (_ & _ & Hne & _). congruence.
  - destruct P2 as (Hs & _). contradiction.
  - destruct P3 as (Hs & _). contradiction.
Qed.

(* With no output yet, the stream is in its header phase (INIT_STATE or GZIP_STATE): RTDMiscKit.misc_status_O0
   for Iapi7. *)
Lemma k7h_status_O0 : forall W HI dict D fin s tin tout adler,
  Iapi7 W HI dict 2 D [] fin s tin tout adler -> d_status s <> BUSY_STATE /\ d_status s <> FINISH_STATE.
Proof.
  intros W HI dict D fin s tin tout adler HI'.
  destruct HI' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hph).
  destruct Hph as [P0 | (_ & [P1 | [P2 | P3]])].
  - destruct P0 as [[[-> _] | [-> _]] _]; split; discriminate.
  - destruct P1 as (_ & _ & Hne & _). congruence.
  - destruct P2 as (_ & _ & _ & Hne & _). exfalso. apply (Hne ltac:(discriminate)). reflexivity.
  - destruct P3 as (_ & _ & _ & _ & Hne & _). exfalso. apply (Hne ltac:(discriminate)). reflexivity.
Qed.

(* Setting the gzip header keeps the safety invariant: the header is the only field that changes, W3 is framed
   by core_eq, and the header phase does not look at the header (RTDLTApiInit.api_head for Iapi7). *)
Lemma k7h_iapi : forall dict s tin tout adler h,
  Iapi7 W3 hinv7 dict 2 [] [] None s tin tout adler -> rhdr_ok7 h ->
  Iapi7 W3 hinv7 dict 2 [] [] None (set_d_gzhead s (Some h)) tin tout adler.
Proof.
  intros dict s tin tout adler h HI' Hh.
  destruct HI' as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & Hph).
  assert (Hce : core_eq s (set_d_gzhead s (Some h))) by (unfold core_eq; repeat split; reflexivity).
  split; [exact (W3_frame s _ H1 Hce)|].
  split; [exact H2|]. do 5 (split; [assumption|]).
  split; [intros h' E; cbn in E; injection E as <-; exact Hh|].
  do 7 (split; [assumption|]).
  destruct Hph as [P0 | (Hlf & [P1 | [P2 | P3]])].
  - left; exact P0.
  - destruct P1 as (_ & _ & Hne & _). congruence.
  - right. split; [exact Hlf|]. right; left; exact P2.
  - right. split; [exact Hlf|]. right; right; exact P3.
Qed.

Theorem rtk7_head_ok : kf7_head_stmt K7.
Proof.
  intros dict s tin tout adler h HK Hh.
  destruct HK as [[HI HK] | (_ & R & HR & _)]; [|discriminate].
  left.
  pose proof (k7h_iapi dict s tin tout adler h HI Hh) as HI1.
  split; [exact HI1|].
  destruct (k7h_status_O0 _ _ _ _ _ _ _ _ _ HI1) as [N1 N2].
  destruct HK as (_ & BS & syms & Hk & Hph).
  split; [intros C; exfalso; apply C; reflexivity|].
  exists BS, syms. split; [apply k7h_kcore3_gzhead; exact Hk|].
  destruct Hph as [(P1 & P2 & P3 & P4 & _) | [(P & _) | (P & _)]]; [|contradiction|contradiction].
  left. split; [exact N1|]. split; [exact N2|]. split; [exact P3|]. split.
  { destruct s. exact P4. }
  destruct (k7h_khdr2 dict (set_d_gzhead s (Some h))) as (HDR & Hk2). exists HDR. split; [exact Hk2|].
  rewrite (k7h_pend0 _ _ _ _ _ _ _ _ _ _ HI1 N1 N2). reflexivity.
Qed.
