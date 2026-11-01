(* Round-trip laws, part RT-CB: compress2_z's destination around a deflate call: the bytes written so far,
   the output space offered (the rest), and the witness that next_out is weakly valid when the rest is empty
   (deflate_spec's wv_at: the byte before next_out). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.DSpec.
Local Open Scope logic.

#[local] Existing Instance DCS.CS.

Definition kp (k cap : Z) : Z := if k =? cap then k - 1 else k.
Definition wv_of (k cap : Z) (D : list val) : wvw := if k =? cap then WVbefore Ews (Znth (k - 1) D) else WVnone.

Lemma wv_of_ok k cap D : cap - k = 0 -> wv_ok (wv_of k cap D).
Proof. intros H. unfold wv_of. rewrite (proj2 (Z.eqb_eq k cap)) by lia. simpl. auto. Qed.

Lemma fc_tuchar_off cap i dp :
  field_compatible (tarray tuchar cap) [] dp -> 0 <= i <= cap ->
  field_address0 (Tarray tuchar cap noattr) (SUB i) dp = offset_val i dp.
Proof.
  intros FC Hi. change (Tarray tuchar cap noattr) with (tarray tuchar cap).
  rewrite arr_field_address0 by (auto; lia). simpl sizeof. f_equal. lia.
Qed.

Lemma dest_open k cap (D : list val) dp :
  0 <= k <= cap -> 0 < cap -> Zlength D = cap ->
  data_at Ews (tarray tuchar cap) D dp |--
  data_at Ews (tarray tuchar (kp k cap)) (sublist 0 (kp k cap) D) dp *
  data_at Ews (tarray tuchar (cap - k)) (sublist k cap D) (offset_val k dp) *
  wv_at (wv_of k cap D) (offset_val k dp).
Proof.
  intros Hk Hc HD. unfold kp, wv_of, wv_at.
  assert_PROP (field_compatible (tarray tuchar cap) [] dp) as FC by entailer!.
  destruct (k =? cap) eqn:E.
  - apply Z.eqb_eq in E. subst k.
    unfold tarray at 1.
    rewrite (split3_data_at_Tarray_tuchar Ews cap (cap - 1) cap D dp) by lia.
    rewrite !fc_tuchar_off by (auto; lia).
    replace (sublist (cap - 1) cap D) with [Znth (cap - 1) D]
      by (rewrite <- sublist_len_1 by lia; f_equal; lia).
    replace (cap - (cap - 1)) with 1 by lia.
    change (Tarray tuchar 1 noattr) with (tarray tuchar 1). erewrite data_at_singleton_array_eq by reflexivity.
    rewrite offset_offset_val. replace (cap + -1) with (cap - 1) by lia.
    unfold tarray. cancel.
  - apply Z.eqb_neq in E.
    unfold tarray at 1.
    rewrite (split2_data_at_Tarray_tuchar Ews cap k D dp) by lia.
    rewrite !fc_tuchar_off by (auto; lia).
    unfold tarray. cancel.
Qed.

Lemma dest_close k cap (D R : list val) dp :
  0 <= k <= cap -> 0 < cap -> Zlength D = cap -> Zlength R = cap - k ->
  field_compatible (tarray tuchar cap) [] dp ->
  data_at Ews (tarray tuchar (kp k cap)) (sublist 0 (kp k cap) D) dp *
  data_at Ews (tarray tuchar (cap - k)) R (offset_val k dp) *
  wv_at (wv_of k cap D) (offset_val k dp)
  |-- data_at Ews (tarray tuchar cap) (sublist 0 k D ++ R) dp.
Proof.
  intros Hk Hc HD HR FC. unfold kp, wv_of, wv_at.
  assert (Hl : Zlength (sublist 0 k D ++ R) = cap) by (rewrite Zlength_app, Zlength_sublist by lia; lia).
  destruct (k =? cap) eqn:E.
  - apply Z.eqb_eq in E. subst k.
    assert (R = []) by (apply Zlength_nil_inv; lia). subst R.
    rewrite app_nil_r, (sublist_same 0 cap D) by lia.
    change (tarray tuchar cap) with (Tarray tuchar cap noattr).
    rewrite (split3_data_at_Tarray_tuchar Ews cap (cap - 1) cap D dp) by lia.
    rewrite !fc_tuchar_off by (auto; lia).
    replace (sublist (cap - 1) cap D) with [Znth (cap - 1) D]
      by (rewrite <- sublist_len_1 by lia; f_equal; lia).
    replace (cap - (cap - 1)) with 1 by lia.
    change (Tarray tuchar 1 noattr) with (tarray tuchar 1). erewrite data_at_singleton_array_eq by reflexivity.
    rewrite offset_offset_val. replace (cap + -1) with (cap - 1) by lia.
    rewrite sublist_nil.
    unfold tarray. cancel.
  - apply Z.eqb_neq in E.
    unfold tarray at 3.
    rewrite (split2_data_at_Tarray_tuchar Ews cap k (sublist 0 k D ++ R) dp) by lia.
    rewrite !fc_tuchar_off by (auto; lia).
    rewrite sublist0_app1, sublist_sublist00 by (rewrite ?Zlength_sublist; lia).
    rewrite sublist_app2 by (rewrite Zlength_sublist; lia).
    rewrite Zlength_sublist by lia. rewrite Z.sub_0_r, Z.sub_diag.
    rewrite (sublist_same 0 (cap - k) R) by lia.
    unfold tarray. cancel.
Qed.
