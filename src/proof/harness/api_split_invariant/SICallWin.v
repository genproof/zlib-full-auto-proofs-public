(* inf_leave's updatewindow keeps the window of the law's relation (SIDefs.swin_ok): when the window holds the
   last min(|O|, 32768) bytes of O (or is not allocated yet, empty, and O is empty), after the bytes d written by
   the call are copied into it, it holds the last min(|O ++ d|, 32768) bytes of O ++ d. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.harness.api_split_invariant.SIDefs.
Require Zlib.proof.rfc1951.DecCallWin.
Import ListNotations.
Local Open Scope Z_scope.

(* swin_ok from its structural facts and the read facts of DecCallWin (swin_at is dcw_wa on the fields) *)
Lemma sicw_of_post : forall s O, i_wsize s = 32768 -> i_win s = true -> 0 <= i_wnext s < 32768 ->
  (i_whave s < 32768 -> i_wnext s = i_whave s) -> Zlength (i_wdata s) = i_whave s ->
  DecCallWin.dcw_post 32768 (i_wnext s) (i_whave s) (i_wdata s) O -> swin_ok s O.
Proof.
  intros s O Hws Hwin Hwn Hval Hlen [Hwh Hwa]. right.
  repeat split; try assumption; try lia.
  intros d Hd. rewrite <- Hwa by exact Hd. unfold swin_at, DecCallWin.dcw_wa. rewrite Hws. reflexivity.
Qed.

(* updatewindow on an allocated window of 32768 bytes *)
Lemma sicw_core : forall s O d, i_wsize s = 32768 ->
  DecCallWin.dcw_pre 32768 (i_wnext s) (i_whave s) (i_wdata s) O ->
  swin_ok (set_i_win (updatewindow s d) true) (O ++ d).
Proof.
  intros s O d Hws Hpre. pose proof Hpre as (_ & Hwn & Hwh & Hval & Hw & _).
  pose proof (Zlength_nonneg d) as Hd0.
  unfold updatewindow. rewrite Hws. cbv zeta. cbn [Z.eqb Pos.eqb]. rewrite !Hws.
  destruct (32768 <=? Zlength d) eqn:E1.
  - apply sicw_of_post; cbn [i_wsize i_win i_wnext i_whave i_wdata set_i_win set_i_wdata set_i_whave set_i_wnext];
      try lia; try reflexivity.
    + rewrite Zlength_sublist; lia.
    + apply DecCallWin.dcw_br1; lia.
  - assert (Hfl : forall c, 0 <= c -> c <= 32768 - i_wnext s -> c <= Zlength d ->
      Zlength (sublist 0 (i_wnext s) (i_wdata s) ++ sublist 0 c d ++
               sublist (i_wnext s + c) (Zlength (i_wdata s)) (i_wdata s)) = Z.max (i_whave s) (i_wnext s + c)).
    { intros c Hc0 Hc1 Hc2. assert (i_wnext s <= i_whave s)
        by (destruct (Z.lt_ge_cases (i_whave s) 32768); [rewrite Hval by lia|]; lia).
      rewrite !Zlength_app, Hw. rewrite !Zlength_sublist by lia.
      destruct (Z.le_gt_cases (i_wnext s + c) (i_whave s)).
      - rewrite !Zlength_sublist by lia. lia.
      - rewrite sublist_over by lia. rewrite Zlength_nil. lia. }
    destruct (negb (Zlength d - Z.min (32768 - i_wnext s) (Zlength d) =? 0)) eqn:E2.
    + apply sicw_of_post; cbn [i_wsize i_win i_wnext i_whave i_wdata set_i_win set_i_wdata set_i_whave set_i_wnext];
        try lia; try reflexivity.
      * rewrite Hfl by lia. rewrite Zlength_app, Zlength_sublist by lia.
        apply negb_true_iff, Z.eqb_neq in E2. rewrite Zlength_sublist; try rewrite Hfl by lia; lia.
      * eapply DecCallWin.dcw_br2; [exact Hpre | lia | lia].
    + apply negb_false_iff, Z.eqb_eq in E2.
      apply sicw_of_post; cbn [i_wsize i_win i_wnext i_whave i_wdata set_i_win set_i_wdata set_i_whave set_i_wnext];
        try reflexivity; try exact Hws.
      all: try rewrite Hfl by lia.
      all: try (destruct (Z.lt_ge_cases (i_whave s) 32768) as [Hlt|]; [specialize (Hval Hlt)|];
                destruct (Z.eqb_spec (i_wnext s + Z.min (32768 - i_wnext s) (Zlength d)) 32768);
                destruct (Z.ltb_spec (i_whave s) 32768); lia).
      apply DecCallWin.dcw_br3; [exact Hpre | lia | lia].
Qed.

Lemma si_call_win : forall s O d,
  swin_ok s O -> (i_wsize s = 0 -> i_wdata s = []) -> i_wbits s = 15 ->
  swin_ok (set_i_win (updatewindow s d) true) (O ++ d).
Proof.
  intros s O d Hwin Hw0 Hwb.
  destruct Hwin as [(Hz & Hwh & ->) | (Hws & _ & Hwh & Hwn & Hval & Hlen & Hwa)].
  - (* not allocated yet: updatewindow allocates 2^15 bytes, empty, then copies *)
    specialize (Hw0 Hz).
    set (s0 := set_i_whave (set_i_wnext (set_i_wsize s (2 ^ i_wbits s)) 0) 0).
    assert (Hs0 : updatewindow s d = updatewindow s0 d).
    { unfold updatewindow at 1. rewrite Hz. cbn zeta. fold s0. unfold updatewindow.
      cbn [s0 i_wsize set_i_whave set_i_wnext set_i_wsize]. rewrite Hwb. reflexivity. }
    rewrite Hs0. apply sicw_core; unfold s0;
      cbn [i_wsize i_wbits i_wnext i_whave i_wdata set_i_whave set_i_wnext set_i_wsize]; rewrite ?Hwb; [reflexivity|].
    rewrite Hw0. unfold DecCallWin.dcw_pre. rewrite Zlength_nil. repeat split; try lia.
  - apply sicw_core; [exact Hws|].
    unfold DecCallWin.dcw_pre. repeat split; try lia.
    intros k Hk. rewrite <- Hwa by exact Hk. unfold swin_at, DecCallWin.dcw_wa. rewrite Hws. reflexivity.
Qed.
