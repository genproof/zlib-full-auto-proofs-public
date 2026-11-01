(** * Kit for the body of trees.c's send_tree (Body_send_tree.v)

    - the four branch statements of the loop body (the do-while of [count < min_count], the [curlen != 0]
      branch, the REPZ_3_10 and REPZ_11_138 branches), cut out of [f_send_tree] by matching;
    - the common pre/postconditions of the branches ([st_locals], [st_sep]);
    - [s->bl_tree] in its Code/Len members ([bl_codes_eq]);
    - [st_apply]: use a branch lemma at a [forward_if] branch goal. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.trees.TSpec.
Require Import Zlib.proof.trees.SendKit2.
Require Import Zlib.trees.code.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

(** ** Model helpers *)

Lemma rd_inv l i x : rd l i = Some x -> 0 <= i < Zlength l /\ x = Znth i l.
Proof.
  unfold rd, in_range. destruct (andb (0 <=? i) (i <? Zlength l)) eqn:E; [|discriminate].
  apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  intros H; inversion H; auto.
Qed.

(** ** The branch statements *)

Definition st_body : statement := Eval cbv [f_send_tree fn_body] in fn_body f_send_tree.

(** [do { send_code(s, curlen, s->bl_tree); } while (--count != 0);] *)
Definition st_dw : statement := ltac:(
  let b := eval cbv [st_body] in st_body in
  lazymatch b with
  | context [Sifthenelse (Ebinop Olt (Etempvar _count tint) (Etempvar _min_count tint) tint) ?a _] => exact a
  end).

(** [if (curlen != prevlen) { send_code(s, curlen, s->bl_tree); count--; }
     send_code(s, REP_3_6, s->bl_tree); send_bits(s, count - 3, 2);] *)
Definition st_rep : statement := ltac:(
  let b := eval cbv [st_body] in st_body in
  lazymatch b with
  | context [Sifthenelse (Ebinop Cop.One (Etempvar _curlen tint) (Econst_int (Int.repr 0) tint) tint) ?a _] => exact a
  end).

(** [send_code(s, REPZ_3_10, s->bl_tree); send_bits(s, count - 3, 3);] *)
Definition st_z10 : statement := ltac:(
  let b := eval cbv [st_body] in st_body in
  lazymatch b with
  | context [Sifthenelse (Ebinop Cop.Ole (Etempvar _count tint) (Econst_int (Int.repr 10) tint) tint) ?a _] => exact a
  end).

(** [send_code(s, REPZ_11_138, s->bl_tree); send_bits(s, count - 11, 7);] *)
Definition st_z138 : statement := ltac:(
  let b := eval cbv [st_body] in st_body in
  lazymatch b with
  | context [Sifthenelse (Ebinop Cop.Ole (Etempvar _count tint) (Econst_int (Int.repr 10) tint) tint) _ ?a] => exact a
  end).

Definition Delta_st : tycontext := func_tycontext f_send_tree Vprog Gprog_send_tree nil.

(** ** Pre/postconditions of the branches *)

(** The locals of the loop body besides [count] (and the macro temporaries). *)
Definition st_locals (i pl cl nl xc nc : Z) (sp tp : val) (max_code : Z) : list localdef :=
  [temp _curlen (vi cl); temp _nextlen (vi nl); temp _n (vi i); temp _prevlen (vi pl);
   temp _max_count (vi xc); temp _min_count (vi nc); temp _s sp; temp _tree tp; temp _max_code (vi max_code)].

(** The resources: the output fields, the tree argument (Len presentation), [s->bl_tree] (Code/Len). *)
Definition st_sep (om : cout) (sp pbp : val) (tsh : share) (n : Z) (t : tree) (tp : val) (bl : tree)
  : list mpred :=
  [out_at (fst om) (snd om) sp pbp;
   @data_at DCS.CS tsh (tarray t_ct n) (ct_arr ffalse ftrue t) tp;
   @field_at DCS.CS Ews t_ds (DOT _bl_tree) (ct_arr ftrue ftrue bl) sp].

(** The pre/postcondition shape of a branch. *)
Definition st_pre (cnt : Z) (i pl cl nl xc nc : Z) (sp tp : val) (max_code : Z)
    (om : cout) (pbp : val) (tsh : share) (n : Z) (t : tree) (bl : tree) : environ -> mpred :=
  PROPx [] (LOCALx (temp _count (vi cnt) :: st_locals i pl cl nl xc nc sp tp max_code)
                   (SEPx (st_sep om sp pbp tsh n t tp bl))).
Definition st_post (i pl cl nl xc nc : Z) (sp tp : val) (max_code : Z)
    (om : cout) (pbp : val) (tsh : share) (n : Z) (t : tree) (bl : tree) : environ -> mpred :=
  PROPx [] (LOCALx (st_locals i pl cl nl xc nc sp tp max_code) (SEPx (st_sep om sp pbp tsh n t tp bl))).

(** ** The branch lemmas (statements) *)

Definition st_dw_stmt : Prop :=
  forall {Espec : OracleKind} (cnt i pl cl nl xc nc : Z) (sp tp : val) (max_code : Z)
    (om r : cout) (pbp : val) (tsh : share) (n : Z) (t : tree) (bl : tree),
  readable_share tsh -> tree_ok bl (2 * BL_CODES + 1) -> 1 <= cnt <= 138 ->
  c_send_codes (Z.to_nat cnt) om cl (fc bl) (dl bl) cnt = Some r ->
  semax Delta_st (st_pre cnt i pl cl nl xc nc sp tp max_code om pbp tsh n t bl) st_dw
    (normal_ret_assert (st_post i pl cl nl xc nc sp tp max_code r pbp tsh n t bl)).

Definition st_rep_stmt : Prop :=
  forall {Espec : OracleKind} (cnt i pl cl nl xc nc : Z) (sp tp : val) (max_code : Z)
    (om r : cout) (pbp : val) (tsh : share) (n : Z) (t : tree) (bl : tree),
  readable_share tsh -> tree_ok bl (2 * BL_CODES + 1) -> 1 <= cnt <= 138 ->
  -1 <= pl < 65536 -> 0 <= cl < 65536 ->
  (let* (om, cnt) :=
     (if negb (cl =? pl) then
        let* om := c_send_code om cl (fc bl) (dl bl) in Some (om, cnt - 1)
      else Some (om, cnt)) in
   let* om := c_send_code om REP_3_6 (fc bl) (dl bl) in
   c_send_bits om (cnt - 3) 2) = Some r ->
  semax Delta_st (st_pre cnt i pl cl nl xc nc sp tp max_code om pbp tsh n t bl) st_rep
    (normal_ret_assert (st_post i pl cl nl xc nc sp tp max_code r pbp tsh n t bl)).

Definition st_z10_stmt : Prop :=
  forall {Espec : OracleKind} (cnt i pl cl nl xc nc : Z) (sp tp : val) (max_code : Z)
    (om r : cout) (pbp : val) (tsh : share) (n : Z) (t : tree) (bl : tree),
  readable_share tsh -> tree_ok bl (2 * BL_CODES + 1) -> 1 <= cnt <= 138 ->
  (let* om := c_send_code om REPZ_3_10 (fc bl) (dl bl) in c_send_bits om (cnt - 3) 3) = Some r ->
  semax Delta_st (st_pre cnt i pl cl nl xc nc sp tp max_code om pbp tsh n t bl) st_z10
    (normal_ret_assert (st_post i pl cl nl xc nc sp tp max_code r pbp tsh n t bl)).

Definition st_z138_stmt : Prop :=
  forall {Espec : OracleKind} (cnt i pl cl nl xc nc : Z) (sp tp : val) (max_code : Z)
    (om r : cout) (pbp : val) (tsh : share) (n : Z) (t : tree) (bl : tree),
  readable_share tsh -> tree_ok bl (2 * BL_CODES + 1) -> 1 <= cnt <= 138 ->
  (let* om := c_send_code om REPZ_11_138 (fc bl) (dl bl) in c_send_bits om (cnt - 11) 7) = Some r ->
  semax Delta_st (st_pre cnt i pl cl nl xc nc sp tp max_code om pbp tsh n t bl) st_z138
    (normal_ret_assert (st_post i pl cl nl xc nc sp tp max_code r pbp tsh n t bl)).

(** ** Using a branch lemma at a forward_if branch *)

Lemma st_apply {Espec : OracleKind} Delta (P P' : environ -> mpred) c (Q : environ -> mpred) R :
  ENTAIL Delta, P |-- P' ->
  semax Delta P' c (normal_ret_assert Q) -> semax Delta P c (overridePost Q R).
Proof.
  intros HP H. eapply semax_pre; [exact HP|].
  eapply semax_post; [| | | | exact H]; destruct R; simpl.
  - intros x. apply andp_left2, derives_refl.
  - intros x. apply andp_left2. apply prop_left. intros [].
  - intros x. apply andp_left2. apply prop_left. intros [].
  - intros vl x. apply andp_left2. apply prop_left. intros [].
Qed.

(** ** [s->bl_tree] in its Code/Len members *)

Lemma bl_mode_eq mf md mf' md' bl sp :
  @field_at DCS.CS Ews t_ds (DOT _bl_tree) (ct_arr mf md bl) sp =
  @field_at DCS.CS Ews t_ds (DOT _bl_tree) (ct_arr mf' md' bl) sp.
Proof.
  rewrite !field_at_data_at.
  change (nested_field_type t_ds (DOT _bl_tree)) with (tarray t_ct 39).
  apply sk_ct_arr_mode.
Qed.

Lemma bltree_codes bl sp :
  bltree_at bl sp =
  (!! tree_ok bl (2 * BL_CODES + 1) && @field_at DCS.CS Ews t_ds (DOT _bl_tree) (ct_arr ftrue ftrue bl) sp)%logic.
Proof. unfold bltree_at, ct_canon. rewrite (bl_mode_eq ffalse ffalse ftrue ftrue). reflexivity. Qed.

Lemma tree_arr_len tsh n t tp :
  tree_arr tsh n t tp =
  (!! tree_ok t n && @data_at DCS.CS tsh (tarray t_ct n) (ct_arr ffalse ftrue t) tp)%logic.
Proof. unfold tree_arr, ct_canon. rewrite (sk_ct_arr_mode tsh n ffalse ffalse ffalse ftrue). reflexivity. Qed.
