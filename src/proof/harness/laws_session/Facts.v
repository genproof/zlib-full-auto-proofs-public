(* What the laws need about the results of laws_session.h's helpers (Spec.v): the range tests are the parameter
   checks of deflateInit2 (deflate/LawFacts.params_ok, its copy roundtrip/RTDLawFacts.params_ok, with method
   Z_DEFLATED) and of inflateInit2 (inflate_api/ApiModel.wbits_ok), so the facts proved for rj_deflate_params and
   rj_inflate_params ("valid => Z_OK or Z_MEM_ERROR") apply after gp_assume(deflate_params_ok(...)) and
   gp_assume(inflate_window_ok(...)); unmoved returns 1 exactly on equal positions; and the form in which a caller
   lends its memory to unmoved and accounted. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.laws_session.Spec.
Require Zlib.proof.deflate.LawFacts.
Require Zlib.proof.roundtrip.RTDLawFacts.
Require Zlib.proof.inflate_api.ApiModel.

(* deflate_params_ok's test is deflateInit2_'s parameter check with method Z_DEFLATED: windowBits 8 is accepted
   only with the zlib wrapper, -8 and 24 are rejected *)
Lemma deflate_params_valid_ok (level wbits mem strategy : Z) :
  deflate_params_valid level wbits mem strategy = Zlib.proof.deflate.LawFacts.params_ok level 8 wbits mem strategy.
Proof.
  unfold deflate_params_valid, LawFacts.params_ok, LawFacts.wb_of, LawFacts.wrap_of.
  destruct (wbits <? 0) eqn:E1; destruct (wbits >? 15) eqn:E2; destruct (level =? -1) eqn:E3;
  apply eq_iff_eq_true;
  repeat rewrite ?andb_true_iff, ?orb_true_iff, ?negb_true_iff, ?Z.leb_le, ?Z.ltb_lt, ?Z.eqb_eq, ?Z.gtb_ltb,
    ?Z.ltb_ge, ?Z.eqb_neq in *; lia.
Qed.

(* the same for the round-trip proofs' copy of params_ok *)
Lemma deflate_params_valid_rt (level wbits mem strategy : Z) :
  deflate_params_valid level wbits mem strategy =
  Zlib.proof.roundtrip.RTDLawFacts.params_ok level 8 wbits mem strategy.
Proof.
  unfold deflate_params_valid, RTDLawFacts.params_ok, RTDLawFacts.wb_of, RTDLawFacts.wrap_of.
  destruct (wbits <? 0) eqn:E1; destruct (wbits >? 15) eqn:E2; destruct (level =? -1) eqn:E3;
  apply eq_iff_eq_true;
  repeat rewrite ?andb_true_iff, ?orb_true_iff, ?negb_true_iff, ?Z.leb_le, ?Z.ltb_lt, ?Z.eqb_eq, ?Z.gtb_ltb,
    ?Z.ltb_ge, ?Z.eqb_neq in *; lia.
Qed.

(* inflate_window_ok's test is the windowBits inflateReset2 accepts *)
Lemma inflate_window_valid_ok (w : Z) : inflate_window_valid w = Zlib.proof.inflate_api.ApiModel.wbits_ok w.
Proof.
  symmetry.
  unfold ApiModel.wbits_ok, ApiModel.reset2_wb, inflate_window_valid.
  assert (B: 0 <= Z.land w 15 <= 15).
  { change (Z.land w 15) with (Z.land w (Z.ones 4)). rewrite Z.land_ones by lia.
    pose proof (Z.mod_pos_bound w (2 ^ 4) ltac:(lia)). simpl in *. lia. }
  destruct (w <? 0) eqn:E0.
  - apply Z.ltb_lt in E0. destruct (w <? -15) eqn:E1.
    + apply Z.ltb_lt in E1. destruct (-15 <=? w) eqn:E2; [apply Z.leb_le in E2; lia|].
      destruct (0 <=? w) eqn:E3; [apply Z.leb_le in E3; lia|]. reflexivity.
    + apply Z.ltb_ge in E1. destruct (0 <=? w) eqn:E3; [apply Z.leb_le in E3; lia|].
      rewrite andb_false_l, orb_false_r. rewrite (proj2 (Z.leb_le (-15) w) E1).
      destruct (8 <=? - w) eqn:E4, (- w <=? 15) eqn:E5, (w <=? -8) eqn:E6; simpl; try reflexivity;
        rewrite ?Z.leb_le, ?Z.leb_gt in *; lia.
  - apply Z.ltb_ge in E0.
    destruct (-15 <=? w) eqn:E2, (w <=? -8) eqn:E6; rewrite ?Z.leb_le, ?Z.leb_gt in E2, E6; try lia; simpl;
      rewrite (proj2 (Z.leb_le 0 w) E0); simpl.
    destruct (w <? 48) eqn:E7; simpl.
    * destruct (Z.land w 15 =? 0); simpl; [reflexivity|].
      destruct (8 <=? Z.land w 15) eqn:E8; simpl; [|reflexivity].
      apply Z.leb_le in E8. rewrite (proj2 (Z.leb_le (Z.land w 15) 15) ltac:(lia)). reflexivity.
    * apply Z.ltb_ge in E7. destruct (w =? 0) eqn:E9; [apply Z.eqb_eq in E9; lia|].
      destruct (8 <=? w) eqn:E8; simpl; [|reflexivity].
      rewrite (proj2 (Z.leb_gt w 15) ltac:(lia)). reflexivity.
Qed.

(* unmoved returns 1 exactly when the two positions are equal *)
Lemma unmoved_b_iff (c a : posz) : unmoved_b c a = true <-> c = a.
Proof.
  destruct c as [ni ai ti no ao to], a as [ni' ai' ti' no' ao' to']; unfold unmoved_b, ptr_eqb; simpl.
  destruct (Val.eq ni ni'), (Val.eq no no'); simpl;
    rewrite ?andb_true_iff, ?Z.eqb_eq; split; intros E;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    try discriminate; try (inversion E; subst; congruence); subst; auto;
    inversion E; subst; tauto.
Qed.

(* a caller lends its memory [B] to unmoved or accounted after proving the comparability in it *)
Lemma lend_cmp (B T : mpred) : B |-- T -> B |-- B && T.
Proof. intros H. apply andp_right; [apply derives_refl | exact H]. Qed.
