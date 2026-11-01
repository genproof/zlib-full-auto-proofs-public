(* RT-I, part rti_zdict: the inflate() call after the right dictionary (zlib: DICT with
   havedict 1), with Z_FINISH and some input, is the call from the TYPE version of the state (check 1,
   adler 1).  Port of harness/inflate_dict/ITD1.v (itd1_call) without its leave case. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTIZDictDefs.
Import ListNotations.
Local Open Scope Z_scope.

Lemma rtzd1_pull_sm: forall m v, pull (set_mode m v) = set_mode (pull m) v.
Proof. reflexivity. Qed.

Lemma rtzd1_needbits_sm: forall k n m v, needbits_f k n (set_mode m v) = set_mode (needbits_f k n m) v.
Proof.
  induction k as [|k IH]; intros n m v; [reflexivity|].
  cbn [needbits_f].
  change (m_bits (set_mode m v)) with (m_bits m).
  change (m_have (set_mode m v)) with (m_have m).
  destruct (m_bits m <? n); [|reflexivity].
  destruct (m_have m =? 0); [reflexivity|].
  rewrite rtzd1_pull_sm. apply IH.
Qed.

Lemma rtzd1_typedo_sm: forall flush m v,
  i_last (m_s m) <> 0 \/ m_leave (needbits 3 m) <> 1 ->
  c_TYPEDO flush (set_mode m v) = c_TYPEDO flush m.
Proof.
  intros flush m v H. unfold c_TYPEDO.
  change (i_last (m_s (set_mode m v))) with (i_last (m_s m)).
  destruct (i_last (m_s m) =? 0) eqn:E; [|reflexivity].
  apply Z.eqb_eq in E.
  cbv zeta. unfold needbits. rewrite rtzd1_needbits_sm.
  set (X := needbits_f 4 3 m) in *.
  change (m_leave (set_mode X v)) with (m_leave X).
  destruct (m_leave X =? 1) eqn:E2.
  - apply Z.eqb_eq in E2. destruct H as [H|H]; contradiction.
  - reflexivity.
Qed.

(* needbits 3 leaves only when no input is there *)
Lemma rtzd1_needbits_leave: forall m,
  m_leave m = 0 -> 0 <= m_bits m <= 39 -> m_leave (needbits 3 m) = 1 -> m_have m = 0.
Proof.
  intros m L B H. unfold needbits in *. cbn [needbits_f] in *.
  destruct (m_bits m <? 3) eqn:E1.
  - destruct (m_have m =? 0) eqn:E2; [apply Z.eqb_eq in E2; exact E2|].
    cbn [needbits_f] in H.
    replace (m_bits (pull m) <? 3) with false in H.
    + exfalso. cbv iota in H. change (m_leave (pull m)) with (m_leave m) in H. lia.
    + symmetry. apply Z.ltb_ge. change (m_bits (pull m)) with (u32 (m_bits m + 8)).
      unfold u32. rewrite Z.mod_small; [lia|]. split; [lia|]. cbn. lia.
  - exfalso. rewrite L in H. discriminate.
Qed.

Lemma rtzd1_loop2_same: forall flush fx dx m m' o,
  stepf2 flush fx dx m = stepf2 flush fx dx m' -> loop2 flush fx dx m o -> loop2 flush fx dx m' o.
Proof.
  intros flush fx dx m m' o E H. inversion H; subst.
  - apply loop2_ret. rewrite <- E. assumption.
  - apply loop2_leave; [rewrite <- E; assumption | assumption].
  - eapply loop2_next; [rewrite <- E; eassumption | assumption | assumption].
Qed.

Lemma rtz_d1 : forall z L inp res,
  i_mode (l_s L) = DICT -> i_havedict (l_s L) = 1 -> 0 <= i_bits (l_s L) <= 39 -> 0 < Zlength inp ->
  run2 Z_FINISH lenfix_list distfix_list (m_init z L inp) res ->
  run2 Z_FINISH lenfix_list distfix_list (m_init (z_adl z 1) (set_l_s L (d1_ty (l_s L))) inp) res.
Proof.
  intros z L inp res MD HD BI LI [o [LP RS]].
  set (s := l_s L) in *.
  set (S := d1_ty s) in *.
  set (M2 := m_init (z_adl z 1) (set_l_s L S) inp).
  assert (E2: M2 = MS (set_i_mode S TYPEDO) (l_h L) inp (zf_ao z) 0 [] (i_hold s) (i_bits s) (Zlength inp)
                      (zf_ao z) Z_OK 0 1 (zf_msg z) (zf_tin z) (zf_tout z) 0 0) by reflexivity.
  assert (E0: m_init z L inp = MS s (l_h L) inp (zf_ao z) 0 [] (i_hold s) (i_bits s) (Zlength inp)
                      (zf_ao z) Z_OK 0 (zf_adler z) (zf_msg z) (zf_tin z) (zf_tout z) 0 0).
  { unfold m_init. cbv zeta. fold s. rewrite MD. reflexivity. }
  assert (St0: stepf2 Z_FINISH lenfix_list distfix_list (m_init z L inp) =
               c_TYPEDO Z_FINISH (set_mode M2 Zlib.proof.inflate.Model.TYPE)).
  { unfold stepf2, step2. rewrite E0. cbn [m_s]. unfold m_mode. cbn [m_s]. rewrite MD.
    cbv [DICT HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID]. cbn [Z.eqb Pos.eqb].
    unfold c_DICT. cbn [m_s]. rewrite HD. cbn [Z.eqb]. unfold c_TYPE. reflexivity. }
  assert (St2: stepf2 Z_FINISH lenfix_list distfix_list M2 = c_TYPEDO Z_FINISH M2) by reflexivity.
  exists o. split; [|exact RS].
  eapply rtzd1_loop2_same; [|exact LP]. rewrite St0, St2. apply rtzd1_typedo_sm.
  right. intro NL. apply rtzd1_needbits_leave in NL.
  - rewrite E2 in NL. unfold m_have in NL. cbn [m_inp m_nx] in NL. lia.
  - rewrite E2. reflexivity.
  - rewrite E2. cbn [m_bits]. exact BI.
Qed.
