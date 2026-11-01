(* RT-D part FLUSH: the static trees and the length / distance tables are Format's (tabs2_stmt,
   RTDFlushDefs2.v).  Boolean checkers over all cases by vm_compute. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDFlushDefs2.
Import ListNotations.
Local Open Scope Z_scope.

Definition rtdt_bleq (a b : list bool) : bool := if list_eq_dec bool_dec a b then true else false.

Lemma rtdt_bleq_ok : forall a b, rtdt_bleq a b = true -> a = b.
Proof. intros a b. unfold rtdt_bleq. destruct (list_eq_dec bool_dec a b); congruence. Qed.

Definition rtdt_cimpl (codes lens fl : list Z) (c : Z) : bool :=
  (Znth c lens =? Znth c fl) && (1 <=? Znth c lens) && (Znth c lens <=? 15) &&
  (0 <=? Znth c codes) && (Znth c codes <? 2 ^ Znth c lens) &&
  rtdt_bleq (F.bits_le (Znth c codes) (Znth c lens)) (F.send_sym fl c).

Lemma rtdt_cimpl_ok : forall codes lens fl c, rtdt_cimpl codes lens fl c = true -> cimpl codes lens fl c.
Proof.
  intros codes lens fl c H. unfold rtdt_cimpl in H.
  repeat rewrite andb_true_iff in H. destruct H as [[[[[H1 H2] H3] H4] H5] H6].
  apply Z.eqb_eq in H1. apply Z.leb_le in H2, H3, H4. apply Z.ltb_lt in H5. apply rtdt_bleq_ok in H6.
  unfold cimpl. repeat split; auto; lia.
Qed.

Definition rtdt_len_ok (lc : Z) : bool :=
  let code := Znth lc length_code_tab in
  (code =? F.len_code (lc + 3)) && (0 <=? code) && (code <? 29) &&
  (Znth code extra_lbits =? Znth code F.len_extra) &&
  ((Znth code F.len_extra =? 0) || (Znth code base_length_tab =? Znth code F.len_base - 3)) &&
  (0 <=? Znth code F.len_extra) && (Znth code F.len_extra <=? 5) &&
  (0 <=? lc + 3 - Znth code F.len_base) && (lc + 3 - Znth code F.len_base <? 2 ^ Znth code F.len_extra).

Definition rtdt_dist_ok (dist : Z) : bool :=
  let code := d_code (dist - 1) in
  (code =? F.dist_code dist) && (0 <=? code) && (code <? 30) &&
  (Znth code extra_dbits =? Znth code F.dist_extra) && (Znth code base_dist_tab =? Znth code F.dist_base - 1) &&
  (0 <=? Znth code F.dist_extra) && (Znth code F.dist_extra <=? 13) &&
  (0 <=? dist - Znth code F.dist_base) && (dist - Znth code F.dist_base <? 2 ^ Znth code F.dist_extra).

Lemma rtdt_l_all : check_from (rtdt_cimpl static_ltree_code static_ltree_len F.fixed_ll) 0 288 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma rtdt_d_all : check_from (rtdt_cimpl static_dtree_code static_dtree_len F.fixed_dl) 0 30 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma rtdt_len_all : check_from rtdt_len_ok 0 256 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma rtdt_dist_all : check_from rtdt_dist_ok 1 (Z.to_nat 32768) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Theorem rtd_tabs2_ok : tabs2_stmt.
Proof.
  unfold tabs2_stmt. split; [|split; [|split]].
  - intros c Hc. apply rtdt_cimpl_ok. apply (check_from_spec _ _ _ rtdt_l_all). simpl; lia.
  - intros c Hc. apply rtdt_cimpl_ok. apply (check_from_spec _ _ _ rtdt_d_all). simpl; lia.
  - intros lc Hlc. cbv zeta.
    assert (H := check_from_spec _ _ _ rtdt_len_all lc ltac:(simpl; lia)).
    unfold rtdt_len_ok in H. cbv zeta in H.
    repeat rewrite andb_true_iff in H. rewrite orb_true_iff in H. rewrite !Z.eqb_eq, !Z.leb_le, !Z.ltb_lt in H.
    intuition lia.
  - intros dist Hd. cbv zeta.
    assert (H := check_from_spec _ _ _ rtdt_dist_all dist ltac:(rewrite Z2Nat.id; lia)).
    unfold rtdt_dist_ok in H. cbv zeta in H.
    repeat rewrite andb_true_iff in H. rewrite !Z.eqb_eq, !Z.leb_le, !Z.ltb_lt in H. lia.
Qed.
