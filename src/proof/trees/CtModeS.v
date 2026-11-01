(** * Switching the union members of ct_data arrays (the array version of Ct.ct_data_rec_mode; a second
    copy of CtMode.v, the same statements with their own proofs, under another module name)

    [data_at] of an array of ct_data does not depend on the members its entries are presented in
    ([data_at_ct_ext], [ct_arr_mode]); the presentation [ct_arr mf md t] after a load / store of one member of
    one entry ([ct_arr_set_fc], [ct_arr_set_dl]). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Rep.
Require Import Zlib.proof.huffman.Model.
Require Export Zlib.proof.trees.Ct.

#[local] Existing Instance DCS.CS.

(** Two entries with the same numbers, in any members. *)
Definition ct_same (a b : reptype t_ct) : Prop :=
  exists bf bd bf' bd' f d, a = ctv_of bf bd f d /\ b = ctv_of bf' bd' f d.

Lemma data_at_ct_ext sh n (l1 l2 : list (reptype t_ct)) p :
  Zlength l1 = Zlength l2 ->
  (forall i, 0 <= i < Zlength l1 -> ct_same (Znth i l1) (Znth i l2)) ->
  @data_at DCS.CS sh (tarray t_ct n) l1 p = @data_at DCS.CS sh (tarray t_ct n) l2 p.
Proof.
  intros Hl Hs. unfold data_at, field_at. f_equal.
  cbn [nested_field_type nested_field_offset]. rewrite !data_at_rec_eq. cbv beta iota.
  unfold tarray. simpl. unfold at_offset.
  apply array_pred_ext; [exact Hl|].
  intros i Hi. rewrite Z.sub_0_r.
  match goal with |- ?a = ?b =>
    match a with context [Znth i ?u] => change u with l1 end;
    match b with context [Znth i ?u] => change u with l2 end end.
  destruct (zlt i (Zlength l1)) as [Hlt|Hge].
  - destruct (Hs i ltac:(lia)) as (bf & bd & bf' & bd' & f & d & E1 & E2).
    rewrite E1, E2. rewrite (ct_data_rec_mode sh bf bd bf' bd' f d). reflexivity.
  - rewrite !Znth_overflow by lia. reflexivity.
Qed.

Lemma ct_arr_mode sh n mf md mf' md' t p :
  @data_at DCS.CS sh (tarray t_ct n) (ct_arr mf md t) p = @data_at DCS.CS sh (tarray t_ct n) (ct_arr mf' md' t) p.
Proof.
  apply data_at_ct_ext; [rewrite !Zlength_ct_arr; reflexivity|].
  intros i Hi. rewrite Zlength_ct_arr in Hi. rewrite !Znth_ct_arr by lia.
  do 6 eexists; split; reflexivity.
Qed.

(** The canonical presentation and any other. *)
Lemma ct_canon_mode sh n mf md t p :
  @data_at DCS.CS sh (tarray t_ct n) (ct_arr ffalse ffalse t) p = @data_at DCS.CS sh (tarray t_ct n) (ct_arr mf md t) p.
Proof. apply ct_arr_mode. Qed.

(** A pointwise update of a mode function. *)
Definition fupd (f : Z -> bool) (i : Z) (b : bool) : Z -> bool := fun j => if Z.eq_dec j i then b else f j.

Lemma ct_arr_ext mf md mf' md' t t' :
  fc t = fc t' -> dl t = dl t' -> (forall i, mf i = mf' i) -> (forall i, md i = md' i) ->
  ct_arr mf md t = ct_arr mf' md' t'.
Proof.
  intros Hf Hd Hmf Hmd. unfold ct_arr. rewrite Hf, Hd.
  apply map_ext. intros i. rewrite Hmf, Hmd. reflexivity.
Qed.

Lemma ct_arr_upd mf md t i bf bd f d :
  0 <= i < Zlength (fc t) -> Zlength (dl t) = Zlength (fc t) ->
  upd_Znth i (ct_arr mf md t) (ctv_of bf bd f d) =
  ct_arr (fupd mf i bf) (fupd md i bd) (mkTree (upd_Znth i (fc t) f) (upd_Znth i (dl t) d)).
Proof.
  intros Hi Hl. apply Znth_eq_ext.
  - rewrite Zlength_upd_Znth, !Zlength_ct_arr. cbn. rewrite Zlength_upd_Znth. reflexivity.
  - intros j Hj. rewrite Zlength_upd_Znth, Zlength_ct_arr in Hj.
    rewrite Znth_ct_arr by (cbn; rewrite Zlength_upd_Znth; lia). cbn [fc dl].
    unfold fupd. destruct (Z.eq_dec j i) as [->|ne].
    + rewrite upd_Znth_same by (rewrite Zlength_ct_arr; lia). rewrite !upd_Znth_same by lia. reflexivity.
    + rewrite upd_Znth_diff by (rewrite ?Zlength_ct_arr; lia).
      rewrite Znth_ct_arr by lia. rewrite !upd_Znth_diff by lia. reflexivity.
Qed.

(** A store into the [fc] member [Freq]/[Code] (bf) of entry [i], leaving [dl]'s presentation. *)
Lemma ct_arr_set_fc mf md t i bf v :
  0 <= i < Zlength (fc t) -> Zlength (dl t) = Zlength (fc t) ->
  upd_Znth i (ct_arr mf md t) (ctv_of bf (md i) v (Znth i (dl t))) =
  ct_arr (fupd mf i bf) md (mkTree (upd_Znth i (fc t) v) (dl t)).
Proof.
  intros Hi Hl. rewrite ct_arr_upd by auto.
  apply ct_arr_ext; cbn; auto.
  - rewrite upd_Znth_triv by (auto; lia). reflexivity.
  - intros j. unfold fupd. destruct (Z.eq_dec j i); subst; reflexivity.
Qed.

(** A store into the [dl] member [Dad]/[Len] (bd) of entry [i]. *)
Lemma ct_arr_set_dl mf md t i bd v :
  0 <= i < Zlength (fc t) -> Zlength (dl t) = Zlength (fc t) ->
  upd_Znth i (ct_arr mf md t) (ctv_of (mf i) bd (Znth i (fc t)) v) =
  ct_arr mf (fupd md i bd) (mkTree (fc t) (upd_Znth i (dl t) v)).
Proof.
  intros Hi Hl. rewrite ct_arr_upd by auto.
  apply ct_arr_ext; cbn; auto.
  - rewrite upd_Znth_triv by (auto; lia). reflexivity.
  - intros j. unfold fupd. destruct (Z.eq_dec j i); subst; reflexivity.
Qed.

(** [c_set_fc] / [c_set_dl] trees are the [mkTree] above. *)
