(** * Body proofs: _tr_flush_block.

    The target: every function's body satisfies its shared specification (see Obligations.v: ob_X =
    semax_body Vprog Gprog_X f_X X_spec; specs in src/proof/trees/TSpec.v, src/proof/deflate/DSpec.v,
    src/proof/compress/CSpec.v; checked models in src/proof/trees/CModel.v, src/proof/deflate/DModel*.v).
    Prove each body as its own lemma (in this file or in new files it imports) and conclude. *)
Require Import Zlib.proof.deflate.Obligations.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.trees.TSpec.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.trees.code.

(** ** The send_bits step kit (a verbatim copy of SendKit.v) *)
(** * The send_bits macro of trees.c against [out_at]: one reusable step for every inlined instance

    trees.c's [send_bits(s, value, length)] (and [send_code(s, c, tree)] = [send_bits(s, tree[c].Code,
    tree[c].Len)]) is a macro, inlined by clightgen with fresh temporaries at every use:

      { int len = LENGTH;                                     -- one Sset (a constant, a temp or a tree load)
        if (s->bi_valid > (int)Buf_size - len) {               -- Sset tv bi_valid; Sifthenelse
          int val = (int)VALUE;                                -- Ssets (with tree loads for send_code)
          s->bi_buf |= (ush)val << s->bi_valid;  put_short(s, s->bi_buf);
          s->bi_buf = (ush)val >> (Buf_size - s->bi_valid);  s->bi_valid += len - Buf_size;
        } else { s->bi_buf |= (ush)(VALUE) << s->bi_valid;  s->bi_valid += len; } }

    Since the temporaries differ at every instance, the reusable step is the tactic [sb_block] together with the
    lemmas it uses:
    - model: [c_send_bits_then] / [c_send_bits_else] give the result of [c_send_bits] explicitly in each branch;
    - C values: [sb_or_eq] ([bi_buf |= (ush)val << bi_valid] is [sb_bb1]), [sb_shr_eq];
    - [sb_then_close] / [sb_else_close]: the fields after each branch are [out_at] of the model's result;
    - trees: [sk_tree_arr_codes] presents a [tree_arr] in the Code/Len members (send_code reads those members).

    Usage, at a goal whose first statement is the macro's block, with [out_at (mkOut buf p bb bv bu) m sp pbp]
    (or [out_at o m sp pbp] with [o] a variable) in SEP and [Hsb : c_send_bits (o, m) v l = Some r] ([r] a
    variable):

      sb_block Hsb ltac:(normv) ltac:(valtac).

    [normv] runs after every forward of the length and of the value statements (e.g. to rewrite a loaded tree
    entry to the model's number: the length temp must end as [Vint (Int.repr l)]); [valtac] proves
    [Int.zero_ext 16 iv = Int.repr (u16 v)] for the C value [iv] of VALUE ([sb_val_default] covers constants
    and [Int.repr v]).  Needs [0 <= l <= 65535] provable by [rep_lia] (e.g. a hypothesis).  Afterwards SEP holds
    [out_at o1 m1 sp pbp] for fresh [o1 m1] with [Hsb : c_send_bits (o, m) v l = Some (o1, m1)]. *)

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

(** ** The model *)

(** [s->bi_buf | (ush)value << s->bi_valid], truncated to the ush field. *)
Definition sb_bb1 (bb bv v : Z) : Z := u16 (Z.lor bb (Z.shiftl (u16 v) bv)).

Lemma u16_range v : 0 <= u16 v < 65536.
Proof. unfold u16. apply Z.mod_pos_bound. lia. Qed.

Lemma sb_bb1_range bb bv v : 0 <= sb_bb1 bb bv v < 65536.
Proof. unfold sb_bb1. apply u16_range. Qed.

Lemma c_send_bits_then buf p bb bv bu m v l r :
  c_send_bits (mkOut buf p bb bv bu, m) v l = Some r -> bv > 16 - l ->
  0 <= bv <= 16 /\ 0 <= p /\ p + 1 < Zlength buf /\
  r = (mkOut (upd_Znth (p + 1) (upd_Znth p buf (u8 (Z.land (sb_bb1 bb bv v) 255)))
                (u8 (Z.shiftr (u16 (sb_bb1 bb bv v)) 8)))
             (p + 2) (Z.shiftr (u16 v) (16 - bv)) (bv + l - 16) bu,
       upd_Znth (p + 1) (upd_Znth p m true) true).
Proof.
  intros H Hc. unfold c_send_bits in H. inv_bind H. destruct x.
  apply guard_inv in Ha. cbn [o_bi_valid] in Ha. apply andb_prop in Ha. destruct Ha as [Hg1 Hg2].
  apply Z.leb_le in Hg1. apply Z.leb_le in Hg2. unfold Buf_size in *. cbn [o_bi_valid o_bi_buf] in H.
  rewrite Z.gtb_ltb, (proj2 (Z.ltb_lt _ _)) in H by lia.
  inv_bind H. destruct x as [o1 m1]. unfold c_put_short in Ha. inv_bind Ha.
  apply c_put_byte_inv' in Ha0. cbn [fst snd set_bits o_buf o_pending] in Ha0. destruct Ha0 as [Hi1 ->].
  apply c_put_byte_inv' in Ha. cbn [fst snd put_byte_c set_bits o_buf o_pending o_bi_buf o_bi_valid o_bi_used] in Ha.
  destruct Ha as [Hi2 Ha]. inversion Ha; subst o1 m1; clear Ha.
  cbn [set_bits put_byte_c o_buf o_pending o_bi_used] in H. inversion H; subst r; clear H.
  rewrite Zlength_upd_Znth in Hi2.
  split; [lia|]. split; [lia|]. split; [lia|].
  unfold sb_bb1. replace (p + 1 + 1) with (p + 2) by lia. reflexivity.
Qed.

Lemma c_send_bits_else buf p bb bv bu m v l r :
  c_send_bits (mkOut buf p bb bv bu, m) v l = Some r -> bv <= 16 - l ->
  0 <= bv <= 16 /\ r = (mkOut buf p (sb_bb1 bb bv v) (bv + l) bu, m).
Proof.
  intros H Hc. unfold c_send_bits in H. inv_bind H. destruct x.
  apply guard_inv in Ha. cbn [o_bi_valid] in Ha. apply andb_prop in Ha. destruct Ha as [Hg1 Hg2].
  apply Z.leb_le in Hg1. apply Z.leb_le in Hg2. unfold Buf_size in *. cbn [o_bi_valid o_bi_buf] in H.
  rewrite Z.gtb_ltb, (proj2 (Z.ltb_ge _ _)) in H by lia.
  inversion H; subst r. split; [lia|]. reflexivity.
Qed.

(** ** The C values *)

Lemma sb_or_eq bb bv iv v : 0 <= bb < 65536 -> 0 <= bv <= 16 -> Int.zero_ext 16 iv = Int.repr (u16 v) ->
  Int.zero_ext 16 (Int.or (Int.repr bb) (Int.shl (Int.zero_ext 16 iv) (Int.repr bv))) = Int.repr (sb_bb1 bb bv v).
Proof.
  intros Hb Hv E. rewrite E. pose proof (u16_range v).
  unfold Int.shl. rewrite !Int.unsigned_repr by rep_lia.
  rewrite or_repr32, zext16_repr. reflexivity.
Qed.

Lemma sb_shr_range bv v : 0 <= bv <= 16 -> 0 <= Z.shiftr (u16 v) (16 - bv) < 65536.
Proof.
  intros Hv. pose proof (u16_range v). rewrite Z.shiftr_div_pow2 by lia.
  split; [apply Z.div_pos; lia|].
  apply Z.le_lt_trans with (u16 v); [apply Z.div_le_upper_bound; [lia|] | lia].
  assert (0 < 2 ^ (16 - bv)) by (apply Z.pow_pos_nonneg; lia). nia.
Qed.

Lemma sb_shr_eq bv iv v : 0 <= bv <= 16 -> Int.zero_ext 16 iv = Int.repr (u16 v) ->
  Int.zero_ext 16 (Int.shr (Int.zero_ext 16 iv) (Int.sub (Int.repr 16) (Int.repr bv))) =
  Int.repr (Z.shiftr (u16 v) (16 - bv)).
Proof.
  intros Hv E. rewrite E, sub_repr32. pose proof (u16_range v). pose proof (sb_shr_range bv v Hv).
  rewrite shr_repr by (cbn; rep_lia). rewrite two_p_equiv, <- Z.shiftr_div_pow2 by lia.
  rewrite zext16_repr, Z.mod_small by lia. reflexivity.
Qed.

(** The usual value facts. *)
Lemma sb_val_repr v : Int.zero_ext 16 (Int.repr v) = Int.repr (u16 v).
Proof. apply zext16_repr. Qed.

Ltac sb_val_default :=
  first [ apply sb_val_repr | reflexivity | (rewrite ?sb_val_repr; f_equal; reflexivity) ].

(** ** The ranges kept by [out_ok] *)
Lemma out_ok_bb buf p bb bv bu m : out_ok (mkOut buf p bb bv bu) m -> 0 <= bb < 65536.
Proof. intros (_ & _ & _ & H & _). exact H. Qed.
Lemma out_ok_bu buf p bb bv bu m : out_ok (mkOut buf p bb bv bu) m -> Int.min_signed <= bu <= Int.max_signed.
Proof. intros (_ & _ & _ & _ & _ & H). exact H. Qed.
Lemma out_ok_bv buf p bb bv bu m : out_ok (mkOut buf p bb bv bu) m -> Int.min_signed <= bv <= Int.max_signed.
Proof. intros (_ & _ & _ & _ & H & _). exact H. Qed.
Lemma out_ok_p buf p bb bv bu m : out_ok (mkOut buf p bb bv bu) m -> 0 <= p <= Int64.max_unsigned.
Proof. intros (_ & _ & H & _). exact H. Qed.

(** ** The fields after each branch *)

Lemma sb_then_close buf p bb bv bu m v l sp pbp :
  out_ok (mkOut buf p bb bv bu) m -> 0 <= p -> p + 1 < Zlength buf -> 0 <= bv <= 16 -> 16 - l < bv ->
  l <= Int.max_signed ->
  @field_at DCS.CS Ews t_ds (DOT _pending) (Vlong (Int64.repr (p + 1 + 1))) sp *
  @field_at DCS.CS Ews t_ds (DOT _pending_buf) pbp sp *
  @field_at DCS.CS Ews t_ds (DOT _bi_buf) (Vint (Int.repr (Z.shiftr (u16 v) (16 - bv)))) sp *
  @field_at DCS.CS Ews t_ds (DOT _bi_valid) (Vint (Int.add (Int.repr bv) (Int.sub (Int.repr l) (Int.repr 16)))) sp *
  @field_at DCS.CS Ews t_ds (DOT _bi_used) (Vint (Int.repr bu)) sp *
  @data_at DCS.CS Ews (tarray tuchar (Zlength (upd_Znth (p + 1) (upd_Znth p buf (u8 (Z.land (sb_bb1 bb bv v) 255)))
                (u8 (Z.shiftr (u16 (sb_bb1 bb bv v)) 8)))))
    (pb_vals (upd_Znth (p + 1) (upd_Znth p buf (u8 (Z.land (sb_bb1 bb bv v) 255)))
                (u8 (Z.shiftr (u16 (sb_bb1 bb bv v)) 8))) (upd_Znth (p + 1) (upd_Znth p m true) true)) pbp
  |-- out_at (mkOut (upd_Znth (p + 1) (upd_Znth p buf (u8 (Z.land (sb_bb1 bb bv v) 255)))
                (u8 (Z.shiftr (u16 (sb_bb1 bb bv v)) 8)))
             (p + 2) (Z.shiftr (u16 v) (16 - bv)) (bv + l - 16) bu)
         (upd_Znth (p + 1) (upd_Znth p m true) true) sp pbp.
Proof.
  intros Hok Hp0 Hp1 Hbv Hl Hl'.
  pose proof (sb_shr_range bv v Hbv).
  pose proof (sb_bb1_range bb bv v).
  pose proof (out_ok_bu _ _ _ _ _ _ Hok) as Hbu.
  assert (Hok1 : out_ok (mkOut buf p (sb_bb1 bb bv v) bv bu) m) by (eapply out_ok_set_bits; eauto; rep_lia).
  pose proof (out_ok_put_byte _ _ (Z.land (sb_bb1 bb bv v) 255) Hok1 ltac:(cbn; lia)) as Hok2.
  cbn [fst snd put_byte_c o_buf o_pending o_bi_buf o_bi_valid o_bi_used] in Hok2.
  pose proof (out_ok_put_byte _ _ (Z.shiftr (u16 (sb_bb1 bb bv v)) 8) Hok2
                ltac:(cbn [o_buf o_pending]; rewrite Zlength_upd_Znth; lia)) as Hok3.
  cbn [fst snd put_byte_c o_buf o_pending o_bi_buf o_bi_valid o_bi_used] in Hok3.
  rewrite sub_repr32, add_repr32. replace (p + 2) with (p + 1 + 1) by lia.
  replace (bv + l - 16) with (bv + (l - 16)) by lia.
  apply out_at_fields.
  eapply out_ok_set_bits; eauto; rep_lia.
Qed.

Lemma sb_else_close buf p bb bv bu m v l sp pbp :
  out_ok (mkOut buf p bb bv bu) m -> 0 <= bv <= 16 -> bv <= 16 - l -> 0 <= l ->
  @field_at DCS.CS Ews t_ds (DOT _pending) (Vlong (Int64.repr p)) sp *
  @field_at DCS.CS Ews t_ds (DOT _pending_buf) pbp sp *
  @field_at DCS.CS Ews t_ds (DOT _bi_buf) (Vint (Int.repr (sb_bb1 bb bv v))) sp *
  @field_at DCS.CS Ews t_ds (DOT _bi_valid) (Vint (Int.add (Int.repr bv) (Int.repr l))) sp *
  @field_at DCS.CS Ews t_ds (DOT _bi_used) (Vint (Int.repr bu)) sp *
  @data_at DCS.CS Ews (tarray tuchar (Zlength buf)) (pb_vals buf m) pbp
  |-- out_at (mkOut buf p (sb_bb1 bb bv v) (bv + l) bu) m sp pbp.
Proof.
  intros Hok Hbv Hl Hl0.
  pose proof (sb_bb1_range bb bv v). pose proof (out_ok_bu _ _ _ _ _ _ Hok).
  rewrite add_repr32. apply out_at_fields.
  eapply out_ok_set_bits; eauto; rep_lia.
Qed.

(** ** Trees in the Code/Len members (send_code reads [tree[c].Len], [tree[c].Code]) *)

Definition sk_ct_same (a b : reptype t_ct) : Prop :=
  exists bf bd bf' bd' f d, a = ctv_of bf bd f d /\ b = ctv_of bf' bd' f d.

Lemma sk_data_at_ct_ext sh n (l1 l2 : list (reptype t_ct)) p :
  Zlength l1 = Zlength l2 ->
  (forall i, 0 <= i < Zlength l1 -> sk_ct_same (Znth i l1) (Znth i l2)) ->
  @data_at DCS.CS sh (tarray t_ct n) l1 p = @data_at DCS.CS sh (tarray t_ct n) l2 p.
Proof.
  intros Hl Hs. unfold data_at, field_at. f_equal.
  unfold at_offset. change (nested_field_type (tarray t_ct n) []) with (tarray t_ct n).
  rewrite !data_at_rec_eq. cbv beta iota. unfold tarray.
  apply array_pred_ext; [exact Hl|].
  intros i Hi. rewrite Z.sub_0_r.
  match goal with |- context [Znth i ?u] => change u with l1 end.
  match goal with |- _ = ?R => match R with context [Znth i ?u] => change u with l2 end end.
  destruct (zlt i (Zlength l1)) as [Hlt|Hge].
  - destruct (Hs i ltac:(lia)) as (bf & bd & bf' & bd' & f & d & E1 & E2).
    rewrite E1, E2. rewrite (ct_data_rec_mode sh bf bd bf' bd' f d). reflexivity.
  - rewrite !Znth_overflow by lia. reflexivity.
Qed.

Lemma sk_ct_arr_mode sh n mf md mf' md' t p :
  @data_at DCS.CS sh (tarray t_ct n) (ct_arr mf md t) p = @data_at DCS.CS sh (tarray t_ct n) (ct_arr mf' md' t) p.
Proof.
  apply sk_data_at_ct_ext; [rewrite !Zlength_ct_arr; reflexivity|].
  intros i Hi. rewrite Zlength_ct_arr in Hi. rewrite !Znth_ct_arr by lia.
  do 6 eexists; split; reflexivity.
Qed.

(** The tree as an array in its Code/Len members. *)
Definition tree_codes (sh : share) (n : Z) (t : tree) (p : val) : mpred :=
  @data_at DCS.CS sh (tarray t_ct n) (ct_arr ftrue ftrue t) p.

Lemma sk_tree_arr_codes sh n t p :
  tree_arr sh n t p = (!! tree_ok t n && tree_codes sh n t p)%logic.
Proof. unfold tree_arr, tree_codes, ct_canon. rewrite (sk_ct_arr_mode sh n ffalse ffalse ftrue ftrue). reflexivity. Qed.

Lemma Znth_tree_codes t i : 0 <= i < Zlength (fc t) ->
  Znth i (ct_arr ftrue ftrue t) = (inr (Vint (Int.repr (Znth i (fc t)))), inr (Vint (Int.repr (Znth i (dl t))))).
Proof. intros. rewrite Znth_ct_arr by auto. reflexivity. Qed.

(** ** The tactic *)

(** The constants of trees.c (Model.v). *)
Ltac sk_consts :=
  unfold LENGTH_CODES, LITERALS, L_CODES, D_CODES, BL_CODES, HEAP_SIZE, MAX_BITS, END_BLOCK in *.

(** [0 <= i < Zlength (fc t)] from a [tree_ok t n] hypothesis. *)
Ltac sk_idx :=
  lazymatch goal with
  | |- 0 <= ?i < Zlength (fc ?t) =>
    lazymatch goal with
    | Ht : tree_ok t ?n |- _ =>
      let E1 := fresh "E" in let E2 := fresh "E" in
      pose proof Ht as (E1 & E2 & _); rewrite E1; clear E1 E2; sk_consts; lia
    end
  end.

(** A load [tree[i].Len] / [tree[i].Code] from [tree_codes] leaves [Znth i (ct_arr ftrue ftrue t)] under the
    union projections: rewrite it to [Vint (Int.repr (Znth i (dl t)))] / [... (fc t)]. *)
Ltac sk_norm_tree :=
  lazymatch goal with
  | |- context [Znth _ (ct_arr ftrue ftrue _)] =>
      repeat (rewrite Znth_tree_codes by sk_idx); cbv beta iota
  end.

(** Side conditions of forward: tc_val of ush/uch loads, typechecks of stores (shift amounts, overflows),
    array indices. *)
Ltac sb_side :=
  lazymatch goal with
  | |- _ |-- local _ => first [tc_side | entailer!]
  | |- _ |-- denote_tc_assert _ => entailer!; try (change (Int.unsigned Int.iwordsize) with 32; lia)
  | |- _ |-- !! _ => entailer!; try (sk_consts; lia)
  end.
Ltac sfwd := forward; try (idtac; sk_norm_tree); try (idtac; sb_side).

(** The SEP list without the six items of an opened [out_at]. *)
Ltac sb_rm_out R :=
  lazymatch R with
  | nil => constr:(@nil mpred)
  | @field_at _ _ _ (DOT _pending) _ _ :: ?R' => sb_rm_out R'
  | @field_at _ _ _ (DOT _pending_buf) _ _ :: ?R' => sb_rm_out R'
  | @field_at _ _ _ (DOT _bi_buf) _ _ :: ?R' => sb_rm_out R'
  | @field_at _ _ _ (DOT _bi_valid) _ _ :: ?R' => sb_rm_out R'
  | @field_at _ _ _ (DOT _bi_used) _ _ :: ?R' => sb_rm_out R'
  | @data_at _ _ (tarray tuchar (Zlength _)) (pb_vals _ _) _ :: ?R' => sb_rm_out R'
  | ?x :: ?R' => let r := sb_rm_out R' in constr:(x :: r)
  end.

(** The branch condition of forward_if as a comparison of numbers. *)
Ltac sb_cond :=
  repeat match goal with H : context [Int.sub (Int.repr _) (Int.repr _)] |- _ => rewrite sub_repr32 in H end;
  repeat match goal with H : context [Int.signed (Int.repr ?x)] |- _ => rewrite (Int.signed_repr x) in H by rep_lia end.

(** forward_if, joining both branches at [out_at o1 m1] in place of the opened fields. *)
Ltac sb_forward_if o1 m1 :=
  lazymatch goal with
  | |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    let R' := sb_rm_out R in
    lazymatch R with
    | context [@field_at _ _ _ (DOT _pending_buf) ?pbp ?sp] =>
      forward_if (PROPx P (LOCALx Q (SEPx (out_at o1 m1 sp pbp :: R'))))
    end
  end.

(** Forward until the store [s->bi_buf = ... | (ush)VALUE << ...] has been made. *)
Ltac sb_to_or normv :=
  repeat (lazymatch goal with
          | |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
              lazymatch R with
              | context [Int.or (Int.repr _) (Int.shl _ _)] => fail
              | _ => sfwd; normv
              end
          end).

Ltac sb_rw_or valtac :=
  lazymatch goal with
  | |- context [Int.zero_ext 16 (Int.or (Int.repr ?bb) (Int.shl (Int.zero_ext 16 ?iv) (Int.repr ?bv)))] =>
    lazymatch goal with
    | Hsb : c_send_bits (mkOut _ _ bb bv _, _) ?v _ = Some _, Hok : out_ok (mkOut _ _ bb bv _) _ |- _ =>
      let Hval := fresh "Hval" in
      assert (Hval : Int.zero_ext 16 iv = Int.repr (u16 v)) by valtac;
      rewrite (sb_or_eq bb bv iv v (out_ok_bb _ _ _ _ _ _ Hok) ltac:(lia) Hval)
    end
  end.

Ltac sb_then normv valtac :=
  lazymatch goal with
  | Hsb : c_send_bits (mkOut ?buf ?p ?bb ?bv ?bu, ?m) ?v ?l = Some (?o1, ?m1),
    Hok : out_ok (mkOut ?buf ?p ?bb ?bv ?bu) ?m |- _ =>
    let Hbv' := fresh "Hbv" in let Hp0 := fresh "Hp0" in let Hp1 := fresh "Hp1" in let Hr := fresh "Hr" in
    pose proof (c_send_bits_then _ _ _ _ _ _ _ _ _ Hsb ltac:(lia)) as (Hbv' & Hp0 & Hp1 & Hr);
    injection Hr as -> ->;
    sb_to_or normv;
    sb_rw_or valtac;
    let Hval := match goal with H : Int.zero_ext 16 _ = Int.repr (u16 v) |- _ => H end in
    let Hok1 := fresh "Hok1" in let Hi0 := fresh "Hi0" in
    pose proof (sb_bb1_range bb bv v);
    assert (Hok1 : out_ok (mkOut buf p (sb_bb1 bb bv v) bv bu) m)
      by (eapply out_ok_set_bits; [exact Hok | lia | lia | exact (out_ok_bu _ _ _ _ _ _ Hok)]);
    assert (Hi0 : 0 <= p < Zlength buf) by lia;
    fwd; fwd; fwd; fwd; fwd;
    fold_put_byte; open_out_at;
    let Hi1 := fresh "Hi1" in
    assert (Hi1 : 0 <= p + 1 < Zlength (upd_Znth p buf (u8 (Z.land (sb_bb1 bb bv v) 255))))
      by (rewrite Zlength_upd_Znth; lia);
    fwd; fwd; fwd; fwd; fwd;
    fold_put_byte; open_out_at;
    sfwd; sfwd;
    rewrite (sb_shr_eq bv _ v Hbv' Hval);
    sfwd; forward; try (idtac; sb_side);
    lazymatch goal with |- context [@field_at _ _ _ (DOT _pending_buf) ?pbp ?sp] =>
      sep_apply (sb_then_close buf p bb bv bu m v l sp pbp Hok Hp0 Hp1 Hbv' ltac:(lia) ltac:(rep_lia)) end;
    entailer!
  end.

Ltac sb_else normv valtac :=
  lazymatch goal with
  | Hsb : c_send_bits (mkOut ?buf ?p ?bb ?bv ?bu, ?m) ?v ?l = Some (?o1, ?m1),
    Hok : out_ok (mkOut ?buf ?p ?bb ?bv ?bu) ?m |- _ =>
    let Hbv' := fresh "Hbv" in let Hr := fresh "Hr" in
    pose proof (c_send_bits_else _ _ _ _ _ _ _ _ _ Hsb ltac:(lia)) as (Hbv' & Hr);
    injection Hr as -> ->;
    sb_to_or normv;
    sb_rw_or valtac;
    sfwd; forward; try (idtac; sb_side);
    lazymatch goal with |- context [@field_at _ _ _ (DOT _pending_buf) ?pbp ?sp] =>
      sep_apply (sb_else_close buf p bb bv bu m v l sp pbp Hok Hbv' ltac:(lia) ltac:(rep_lia)) end;
    entailer!
  end.

Ltac sb_block Hsb normv valtac :=
  lazymatch type of Hsb with
  | c_send_bits (?o, ?m) ?v ?l = Some ?r =>
    lazymatch o with mkOut _ _ _ _ _ => idtac | _ => is_var o; destruct o as [?buf ?p ?bb ?bv ?bu] end;
    is_var r;
    let o1 := fresh "o" in let m1 := fresh "m" in destruct r as [o1 m1];
    assert (0 <= l <= 65535) by rep_lia;
    sfwd; normv;
    open_out_at;
    lazymatch goal with Hok : out_ok (mkOut _ _ _ _ _) _ |- _ =>
      pose proof (out_ok_bv _ _ _ _ _ _ Hok); pose proof (out_ok_bb _ _ _ _ _ _ Hok) end;
    sfwd;
    sb_forward_if o1 m1;
    [ sb_cond; sb_then normv valtac | sb_cond; sb_else normv valtac | idtac .. ]
  end.

(** ** _tr_flush_block *)

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

(** ** The trees and descriptors of the state as the stand-alone arguments of the callees *)
Lemma ltree_arr t sp :
  ltree_at t sp = tree_arr Ews HEAP_SIZE t (field_address t_ds (DOT _dyn_ltree) sp).
Proof. unfold ltree_at, tree_arr. rewrite field_at_data_at. reflexivity. Qed.

Lemma dtree_arr t sp :
  dtree_at t sp = tree_arr Ews (2 * D_CODES + 1) t (field_address t_ds (DOT _dyn_dtree) sp).
Proof. unfold dtree_at, tree_arr. rewrite field_at_data_at. reflexivity. Qed.

Lemma ldesc_td treep maxc statp sp :
  ldesc_at treep maxc statp sp = td_at Ews treep maxc statp (field_address t_ds (DOT _l_desc) sp).
Proof. unfold ldesc_at, td_at. rewrite field_at_data_at. reflexivity. Qed.

Lemma ddesc_td treep maxc statp sp :
  ddesc_at treep maxc statp sp = td_at Ews treep maxc statp (field_address t_ds (DOT _d_desc) sp).
Proof. unfold ddesc_at, td_at. rewrite field_at_data_at. reflexivity. Qed.

(** ** Local facts (saturate_local) *)
Lemma ldesc_local_facts a b c sp :
  ldesc_at a b c sp |-- !! (field_compatible t_ds (DOT _l_desc) sp /\ Int.min_signed <= b <= Int.max_signed).
Proof. unfold ldesc_at. entailer!. Qed.
Lemma ddesc_local_facts a b c sp :
  ddesc_at a b c sp |-- !! (field_compatible t_ds (DOT _d_desc) sp /\ Int.min_signed <= b <= Int.max_signed).
Proof. unfold ddesc_at. entailer!. Qed.
Lemma ltree_local_facts t sp :
  ltree_at t sp |-- !! (field_compatible t_ds (DOT _dyn_ltree) sp /\ tree_ok t HEAP_SIZE).
Proof. unfold ltree_at. entailer!. Qed.
Lemma dtree_local_facts t sp :
  dtree_at t sp |-- !! (field_compatible t_ds (DOT _dyn_dtree) sp /\ tree_ok t (2 * D_CODES + 1)).
Proof. unfold dtree_at. entailer!. Qed.
#[local] Hint Resolve ldesc_local_facts ddesc_local_facts ltree_local_facts dtree_local_facts : saturate_local.

Lemma work_fold w sp : work_ok w ->
  @field_at DCS.CS Ews t_ds (DOT _heap) (map vi (w_heap w)) sp *
  @field_at DCS.CS Ews t_ds (DOT _heap_len) (vi (w_heap_len w)) sp *
  @field_at DCS.CS Ews t_ds (DOT _heap_max) (vi (w_heap_max w)) sp *
  @field_at DCS.CS Ews t_ds (DOT _depth) (map vi (w_depth w)) sp *
  @field_at DCS.CS Ews t_ds (DOT _bl_count) (map vi (w_bl_count w)) sp *
  @field_at DCS.CS Ews t_ds (DOT _opt_len) (vl (w_opt_len w)) sp *
  @field_at DCS.CS Ews t_ds (DOT _static_len) (vl (w_static_len w)) sp |-- work_at w sp.
Proof. intros. unfold work_at. apply andp_right; [apply prop_right; auto | cancel]. Qed.

(** ** Facts about the model *)
Lemma detect_range lf r : c_detect_data_type lf = Some r -> 0 <= r <= 1.
Proof.
  unfold c_detect_data_type. intros H.
  repeat match goal with
  | H : bind ?a _ = Some _ |- _ => let x := fresh "x" in let Ha := fresh "Ha" in
      apply bind_inv in H; destruct H as [x [Ha H]]
  | H : (if ?b then _ else _) = Some _ |- _ => destruct b
  | H : Some _ = Some _ |- _ => injection H as <-
  end; try discriminate;
  try match goal with |- context [if ?b then _ else _] => destruct b end; unfold Z_BINARY, Z_TEXT; lia.
Qed.

Lemma rd_some l i x : rd l i = Some x -> 0 <= i < Zlength l /\ x = Znth i l.
Proof.
  unfold rd, in_range. destruct (andb (0 <=? i) (i <? Zlength l)) eqn:E; [|discriminate].
  apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  intros H; injection H as <-. auto.
Qed.

Lemma find_max_blindex_range f bl i r : c_find_max_blindex f bl i = Some r -> i - Z.of_nat f <= r <= i.
Proof.
  revert i. induction f as [|f IH]; intros i H; cbn [c_find_max_blindex] in H.
  - destruct (i >=? 3); [discriminate|]. injection H as <-. lia.
  - destruct (i >=? 3).
    + inv_bind H. inv_bind H. destruct (negb (x0 =? 0)).
      * injection H as <-. lia.
      * apply IH in H. lia.
    + injection H as <-. lia.
Qed.

Lemma send_tree_loop_bound f t mc blc bll om n prev next count maxc minc r :
  c_send_tree_loop f t mc blc bll om n prev next count maxc minc = Some r -> n <= mc ->
  mc + 1 < Zlength (dl t).
Proof.
  revert om n prev next count maxc minc. induction f as [|f IH]; intros om n prev next count maxc minc H Hn;
    cbn [c_send_tree_loop] in H.
  - rewrite (proj2 (Z.leb_le n mc) Hn) in H. discriminate.
  - rewrite (proj2 (Z.leb_le n mc) Hn) in H.
    inv_bind H. apply rd_some in Ha. destruct Ha as [Hr _].
    destruct (Z.le_gt_cases (n + 1) mc) as [Hlt|Hge]; [|lia].
    destruct (andb (count + 1 <? maxc) (next =? x)).
    + eapply IH; eauto.
    + inv_bind H.
      destruct (if x =? 0 then (138, 3) else if next =? x then (6, 3) else (7, 4)) as [a b].
      eapply IH; eauto.
Qed.

Lemma send_tree_bound om t mc bl r : c_send_tree om t mc bl = Some r -> mc < 0 \/ mc + 1 < Zlength (dl t).
Proof.
  unfold c_send_tree. intros H. inv_bind H. inv_bind H.
  destruct (if x0 =? 0 then (138, 3) else (7, 4)) as [a b].
  destruct (Z.lt_ge_cases mc 0); [auto|right].
  eapply send_tree_loop_bound; eauto.
Qed.

Lemma send_all_trees_bounds om lt dt bl lc dc blc r :
  c_send_all_trees om lt dt bl lc dc blc = Some r ->
  (lc - 1 < 0 \/ lc < Zlength (dl lt)) /\ (dc - 1 < 0 \/ dc < Zlength (dl dt)).
Proof.
  unfold c_send_all_trees. intros H.
  inv_bind H. inv_bind H. inv_bind H. inv_bind H. inv_bind H. inv_bind H.
  apply send_tree_bound in Ha4. apply send_tree_bound in H. split; lia.
Qed.

Lemma build_bl_tree_frame s s' mbi : c_build_bl_tree s = Some (s', mbi) ->
  -2 <= mbi <= 18 /\ tr_out s' = tr_out s /\ tr_sym_next s' = tr_sym_next s /\ tr_sym_end s' = tr_sym_end s /\
  tr_matches s' = tr_matches s /\ tr_lit_bufsize s' = tr_lit_bufsize s /\ tr_level s' = tr_level s /\
  tr_strategy s' = tr_strategy s /\ tr_data_type s' = tr_data_type s /\ tr_lmax s' = tr_lmax s /\
  tr_dmax s' = tr_dmax s.
Proof.
  unfold c_build_bl_tree. intros H.
  inv_bind H. destruct x as [lt bl]. inv_bind H. destruct x as [dt bl']. inv_bind H. destruct x as [[bl'' blmax] w].
  inv_bind H. apply find_max_blindex_range in Ha2. injection H as <- <-.
  cbn. unfold BL_CODES in Ha2. repeat split; lia || reflexivity.
Qed.

Lemma lenb_eq x :
  Int64.shru (Int64.add (Int64.add (Int64.repr x) (Int64.repr (Int.signed (Int.repr 3))))
                        (Int64.repr (Int.signed (Int.repr 7)))) (Int64.repr (Int.unsigned (Int.repr 3))) =
  Int64.repr (Z.shiftr (u64 (x + 3 + 7)) 3).
Proof.
  change (Int.signed (Int.repr 3)) with 3. change (Int.signed (Int.repr 7)) with 7.
  change (Int.unsigned (Int.repr 3)) with 3.
  rewrite !add64_repr. unfold Int64.shru. rewrite Int64.unsigned_repr_eq. reflexivity.
Qed.

Lemma lenb_range x : 0 <= Z.shiftr (u64 x) 3 <= Int64.max_unsigned.
Proof.
  unfold u64. rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.mod_pos_bound x 18446744073709551616 ltac:(lia)).
  split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|]. rep_lia.
Qed.

Lemma u64_repr x : Int64.repr (u64 x) = Int64.repr x.
Proof.
  rewrite <- (Int64.repr_unsigned (Int64.repr x)), Int64.unsigned_repr_eq. reflexivity.
Qed.

Lemma set_data_type_eta s : set_data_type s (tr_data_type s) = s.
Proof. destruct s; reflexivity. Qed.

Definition is_some {A} (o : option A) : bool := match o with Some _ => true | None => false end.

Lemma sym_at_eq s s' sp pbp :
  tr_sym_next s = tr_sym_next s' -> tr_sym_end s = tr_sym_end s' -> tr_matches s = tr_matches s' ->
  tr_lit_bufsize s = tr_lit_bufsize s' -> sym_at s sp pbp = sym_at s' sp pbp.
Proof. intros. unfold sym_at. rewrite H, H0, H1, H2. reflexivity. Qed.

Lemma match_bo_split {A} (bo : option (list Z)) (c : bool) (F : list Z -> option A) (G : option A) x :
  match bo with Some b => if c then F b else G | None => G end = Some x ->
  (andb c (is_some bo) = true /\ exists b, bo = Some b /\ F b = Some x) \/
  (andb c (is_some bo) = false /\ G = Some x).
Proof.
  destruct bo as [b|]; destruct c; cbn; intros H; auto.
  left. split; [reflexivity|]. exists b. auto.
Qed.

Lemma phase1_facts s stored_len s1 olb slb mbi :
  0 <= stored_len <= Int64.max_unsigned ->
  (if tr_level s >? 0 then
     let* s := (if tr_data_type s =? Z_UNKNOWN then
                  let* dt := c_detect_data_type (fc (tr_ltree s)) in Some (set_data_type s dt)
                else Some s) in
     let* (lt, lmax, w) := c_build_tree static_l_desc (tr_ltree s) (tr_wk s) in
     let s := set_wk (set_lmax (set_ltree s lt) lmax) w in
     let* (dt, dmax, w) := c_build_tree static_d_desc (tr_dtree s) (tr_wk s) in
     let s := set_wk (set_dmax (set_dtree s dt) dmax) w in
     let* (s, max_blindex) := c_build_bl_tree s in
     let opt_lenb := Z.shiftr (u64 (w_opt_len (tr_wk s) + 3 + 7)) 3 in
     let static_lenb := Z.shiftr (u64 (w_static_len (tr_wk s) + 3 + 7)) 3 in
     let opt_lenb := if orb (static_lenb <=? opt_lenb) (tr_strategy s =? Z_FIXED) then static_lenb else opt_lenb in
     Some (s, opt_lenb, static_lenb, max_blindex)
   else Some (s, u64 (stored_len + 5), u64 (stored_len + 5), 0)) = Some (s1, olb, slb, mbi) ->
  tr_out s1 = tr_out s /\ tr_sym_next s1 = tr_sym_next s /\ tr_sym_end s1 = tr_sym_end s /\
  tr_matches s1 = tr_matches s /\ tr_lit_bufsize s1 = tr_lit_bufsize s /\ tr_level s1 = tr_level s /\
  tr_strategy s1 = tr_strategy s /\ 0 <= olb <= Int64.max_unsigned /\ 0 <= slb <= Int64.max_unsigned /\
  -2 <= mbi <= 18.
Proof.
  intros Hs H. destruct (tr_level s >? 0).
  - inv_bind H. rename x into s0.
    assert (E0 : s0 = set_data_type s (tr_data_type s0)).
    { destruct (tr_data_type s =? Z_UNKNOWN).
      - inv_bind Ha. injection Ha as <-. reflexivity.
      - injection Ha as <-. rewrite set_data_type_eta. auto. }
    rewrite E0 in H. clear Ha E0.
    inv_bind H. destruct x as [[lt lmax] w1].
    inv_bind H. destruct x as [[dt dmax] w2].
    inv_bind H. destruct x as [s2 mb].
    injection H as <- <- <- <-.
    apply build_bl_tree_frame in Ha1. cbn in Ha1.
    destruct Ha1 as [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]].
    repeat split; try assumption; try lia;
      try (destruct (orb _ _)); apply lenb_range.
  - injection H as <- <- <- <-.
    pose proof (Z.mod_pos_bound (stored_len + 5) 18446744073709551616 ltac:(lia)).
    unfold u64. repeat split; try reflexivity; rep_lia.
Qed.

Lemma init_block_frame s s' : c_init_block s = Some s' ->
  tr_out s' = tr_out s /\ tr_lmax s' = tr_lmax s /\ tr_dmax s' = tr_dmax s /\ tr_blmax s' = tr_blmax s /\
  tr_level s' = tr_level s /\ tr_strategy s' = tr_strategy s /\ tr_data_type s' = tr_data_type s /\
  tr_lit_bufsize s' = tr_lit_bufsize s.
Proof.
  unfold c_init_block. intros H.
  inv_bind H. inv_bind H. inv_bind H. inv_bind H. injection H as <-. cbn. repeat split; reflexivity.
Qed.

Lemma opt_buf_split bsh b stored_len bufp :
  opt_buf_at bsh (Some b) bufp =
  (buf_at bsh stored_len b bufp * (if stored_len =? 0 then opt_buf_at bsh (Some b) bufp else emp))%logic.
Proof.
  unfold buf_at. destruct (stored_len =? 0); [rewrite emp_sepcon | rewrite sepcon_emp]; reflexivity.
Qed.

(** The value of the block header [(K<<1) + last] cast to ush. *)
Lemma hdr_val_eq k last : 0 <= k <= 4 ->
  Int.zero_ext 16 (Int.add (Int.shl (Int.repr k) (Int.repr 1)) (Int.repr last)) =
  Int.repr (u16 (Z.shiftl k 1 + last)).
Proof.
  intros Hk. rewrite <- sb_val_repr. f_equal. unfold Int.shl.
  rewrite !Int.unsigned_repr by rep_lia. apply add_repr32.
Qed.

Ltac hdr_val := first [ apply hdr_val_eq; unfold STATIC_TREES, DYN_TREES; lia | sb_val_default ].



(** The overflow side condition of [(K<<1) + last]. *)
Ltac hdr_arith :=
  try match goal with
  | |- context [Int.signed (Int.shl (Int.repr ?a) (Int.repr ?b))] =>
    let v := eval vm_compute in (Int.signed (Int.shl (Int.repr a) (Int.repr b))) in
    change (Int.signed (Int.shl (Int.repr a) (Int.repr b))) with v
  end;
  try change (Int.unsigned Int.iwordsize) with 32; rep_lia.

Ltac hdr_norm :=
  try (lazymatch goal with
       | |- ENTAIL _, _ |-- tc_expr _ _ => entailer!; hdr_arith
       | |- semax _ _ _ _ => fail
       | |- _ |-- _ => fail
       | |- _ => hdr_arith
       end).

Lemma set_out_eta s : set_out s (tr_out s) = s.
Proof. destruct s; reflexivity. Qed.

Lemma trees_at_close s1 s3 s0 s' o m sp pbp strmp gv :
  s' = set_out s3 o ->
  tr_lmax s3 = tr_lmax s1 -> tr_dmax s3 = tr_dmax s1 -> tr_blmax s3 = tr_blmax s1 ->
  tr_level s3 = tr_level s1 -> tr_strategy s3 = tr_strategy s1 -> tr_data_type s3 = tr_data_type s1 ->
  tr_level s1 = tr_level s0 -> tr_strategy s1 = tr_strategy s0 ->
  Int.min_signed <= tr_level s0 <= Int.max_signed -> Int.min_signed <= tr_strategy s0 <= Int.max_signed ->
  (ltree_at (tr_ltree s3) sp * dtree_at (tr_dtree s3) sp * bltree_at (tr_bltree s3) sp *
   ldesc_at (field_address t_ds (DOT _dyn_ltree) sp) (tr_lmax s1) (gv _static_l_desc) sp *
   ddesc_at (field_address t_ds (DOT _dyn_dtree) sp) (tr_dmax s1) (gv _static_d_desc) sp *
   bldesc_at (field_address t_ds (DOT _bl_tree) sp) (tr_blmax s1) (gv _static_bl_desc) sp *
   work_at (tr_wk s3) sp * out_at o m sp pbp * sym_at s3 sp pbp *
   @field_at DCS.CS Ews t_ds (DOT _level) (vi (tr_level s0)) sp *
   @field_at DCS.CS Ews t_ds (DOT _strategy) (vi (tr_strategy s0)) sp *
   dtype_at s1 sp strmp)%logic
  |-- trees_at (s', m) sp pbp strmp gv.
Proof.
  intros -> E1 E2 E3 E4 E5 E6 E7 E8 R1 R2.
  unfold trees_at, lvl_at, dtype_at. cbn [fst snd set_out tr_ltree tr_dtree tr_bltree tr_lmax tr_dmax tr_blmax
    tr_wk tr_out tr_level tr_strategy tr_data_type].
  rewrite E1, E2, E3, E4, E5, E6, E7, E8.
  rewrite (sym_at_eq (set_out s3 o) s3 sp pbp) by reflexivity.
  entailer!.
Qed.

Lemma body_tr_flush_block : semax_body Vprog Gprog_tr_flush_block f__tr_flush_block tr_flush_block_spec.
Proof.
  start_function.
  destruct cs as [s m].
  unfold c_tr_flush_block in H1.
  inv_bind H1. destruct x as [[[s1 olb] slb] mbi]. rename Ha into Hp1.
  inv_bind H1. destruct x as [[o2 m2] kind]. rename Ha into Hp2.
  inv_bind H1. rename x into s3. rename Ha into Hib.
  inv_bind H1. destruct x as [s4 m4]. rename Ha into Hwu.
  injection H1 as <-.
  pose proof (phase1_facts _ _ _ _ _ _ H Hp1) as Hf1.
  unfold trees_at. cbn [fst snd]. Intros.
  forward.
  unfold lvl_at. Intros.
  forward.
  forward_if (PROP ()
    LOCAL (temp _opt_lenb (vl olb); temp _static_lenb (vl slb); temp _max_blindex (vi mbi); gvars gv;
           temp _s sp; temp _buf bufp; temp _stored_len (vl stored_len); temp _last (vi last))
    SEP (ltree_at (tr_ltree s1) sp; dtree_at (tr_dtree s1) sp; bltree_at (tr_bltree s1) sp;
         ldesc_at (field_address t_ds (DOT _dyn_ltree) sp) (tr_lmax s1) (gv _static_l_desc) sp;
         ddesc_at (field_address t_ds (DOT _dyn_dtree) sp) (tr_dmax s1) (gv _static_d_desc) sp;
         bldesc_at (field_address t_ds (DOT _bl_tree) sp) (tr_blmax s1) (gv _static_bl_desc) sp;
         work_at (tr_wk s1) sp; out_at (tr_out s) m sp pbp; sym_at s sp pbp;
         field_at Ews t_ds (DOT _level) (vi (tr_level s)) sp;
         field_at Ews t_ds (DOT _strategy) (vi (tr_strategy s)) sp;
         dtype_at s1 sp strmp; trees_globals gv; opt_buf_at bsh bo bufp)).
  - (* level > 0: build the trees *)
    destruct (Z.gtb_spec (tr_level s) 0); [|lia].
    inv_bind Hp1. rename x into s0. rename Ha into Hdt.
    unfold dtype_at. Intros.
    forward. forward.
    assert (Hs0 : s0 = set_data_type s (tr_data_type s0) /\ Int.min_signed <= tr_data_type s0 <= Int.max_signed).
    { destruct (tr_data_type s =? Z_UNKNOWN).
      - inv_bind Hdt. injection Hdt as <-. apply detect_range in Ha. cbn. split; [reflexivity|rep_lia].
      - injection Hdt as <-. rewrite set_data_type_eta. auto. }
    destruct Hs0 as [Hs0 Hd0].
    forward_if (PROP ()
      LOCAL (temp _max_blindex (vi 0); gvars gv; temp _s sp; temp _buf bufp; temp _stored_len (vl stored_len);
             temp _last (vi last))
      SEP (ltree_at (tr_ltree s) sp; dtree_at (tr_dtree s) sp; bltree_at (tr_bltree s) sp;
           ldesc_at (field_address t_ds (DOT _dyn_ltree) sp) (tr_lmax s) (gv _static_l_desc) sp;
           ddesc_at (field_address t_ds (DOT _dyn_dtree) sp) (tr_dmax s) (gv _static_d_desc) sp;
           bldesc_at (field_address t_ds (DOT _bl_tree) sp) (tr_blmax s) (gv _static_bl_desc) sp;
           work_at (tr_wk s) sp; out_at (tr_out s) m sp pbp; sym_at s sp pbp;
           field_at Ews t_ds (DOT _level) (vi (tr_level s)) sp;
           field_at Ews t_ds (DOT _strategy) (vi (tr_strategy s)) sp;
           field_at Ews t_ds (DOT _strm) strmp sp;
           field_at Ews t_strm (DOT _data_type) (vi (tr_data_type s0)) strmp;
           trees_globals gv; opt_buf_at bsh bo bufp)).
    + (* data_type == Z_UNKNOWN: detect_data_type *)
      rewrite H6 in Hdt. change (2 =? Z_UNKNOWN) with true in Hdt. cbv beta iota in Hdt.
      inv_bind Hdt. injection Hdt as <-.
      forward_call (sp, tr_ltree s, x).
      forward. forward.
      entailer!.
    + rewrite (proj2 (Z.eqb_neq (tr_data_type s) Z_UNKNOWN) H6) in Hdt.
      injection Hdt as <-.
      forward. entailer!.
    + rewrite Hs0 in Hp1. clear Hdt Hs0. set (d0 := tr_data_type s0) in *. clearbody d0.
      inv_bind Hp1. destruct x as [[lt lmax] w1]. rename Ha into Hbl.
      inv_bind Hp1. destruct x as [[dt dmax] w2]. rename Ha into Hbd.
      inv_bind Hp1. destruct x as [s2 mbi']. rename Ha into Hbb.
      injection Hp1 as -> Holb Hslb ->.
      cbn [set_data_type set_ltree set_lmax set_wk set_dtree set_dmax tr_ltree tr_dtree tr_wk] in Hbl, Hbd.
      assert_PROP (field_compatible t_ds (DOT _l_desc) sp /\ field_compatible t_ds (DOT _d_desc) sp) as Hfc
        by entailer!.
      destruct Hfc as [Hfl Hfd].
      rewrite ltree_arr, ldesc_td.
      forward_call (sp, field_address t_ds (DOT _l_desc) sp, field_address t_ds (DOT _dyn_ltree) sp, HEAP_SIZE,
                    tr_ltree s, tr_lmax s, gv _static_l_desc, static_l_desc, tr_wk s, (lt, lmax, w1), gv).
      { left; auto. }
      change (snd (fst (lt, lmax, w1))) with lmax. change (fst (fst (lt, lmax, w1))) with lt.
      change (snd (lt, lmax, w1)) with w1.
      rewrite <- ltree_arr, <- ldesc_td, dtree_arr, ddesc_td.
      forward_call (sp, field_address t_ds (DOT _d_desc) sp, field_address t_ds (DOT _dyn_dtree) sp,
                    2 * D_CODES + 1, tr_dtree s, tr_dmax s, gv _static_d_desc, static_d_desc, w1, (dt, dmax, w2), gv).
      { right; left; auto. }
      change (snd (fst (dt, dmax, w2))) with dmax. change (fst (fst (dt, dmax, w2))) with dt.
      change (snd (dt, dmax, w2)) with w2.
      rewrite <- dtree_arr, <- ddesc_td.
      pose (s2 := set_wk (set_dmax (set_dtree (set_wk (set_lmax (set_ltree (set_data_type s d0) lt) lmax) w1) dt) dmax) w2).
      fold s2 in Hbb.
      change (ltree_at lt sp) with (ltree_at (tr_ltree s2) sp).
      change (dtree_at dt sp) with (dtree_at (tr_dtree s2) sp).
      change (bltree_at (tr_bltree s) sp) with (bltree_at (tr_bltree s2) sp).
      change (ldesc_at (field_address t_ds (DOT _dyn_ltree) sp) lmax (gv _static_l_desc) sp)
        with (ldesc_at (field_address t_ds (DOT _dyn_ltree) sp) (tr_lmax s2) (gv _static_l_desc) sp).
      change (ddesc_at (field_address t_ds (DOT _dyn_dtree) sp) dmax (gv _static_d_desc) sp)
        with (ddesc_at (field_address t_ds (DOT _dyn_dtree) sp) (tr_dmax s2) (gv _static_d_desc) sp).
      change (bldesc_at (field_address t_ds (DOT _bl_tree) sp) (tr_blmax s) (gv _static_bl_desc) sp)
        with (bldesc_at (field_address t_ds (DOT _bl_tree) sp) (tr_blmax s2) (gv _static_bl_desc) sp).
      change (work_at w2 sp) with (work_at (tr_wk s2) sp).
      forward_call (sp, s2, (s1, mbi), gv).
      change (fst (s1, mbi)) with s1. change (snd (s1, mbi)) with mbi.
      pose proof (build_bl_tree_frame _ _ _ Hbb) as Hfr.
      unfold work_at. Intros.
      forward. forward. forward. forward.
      rewrite !lenb_eq.
      pose proof (lenb_range (w_opt_len (tr_wk s1) + 3 + 7)).
      pose proof (lenb_range (w_static_len (tr_wk s1) + 3 + 7)).
      sep_apply (work_fold (tr_wk s1) sp H6).
      set (ob := Z.shiftr (u64 (w_opt_len (tr_wk s1) + 3 + 7)) 3) in *.
      set (sb := Z.shiftr (u64 (w_static_len (tr_wk s1) + 3 + 7)) 3) in *.
      forward_if (PROP ()
        LOCAL (temp _t'3 (Val.of_bool ((sb <=? ob) || (tr_strategy s =? Z_FIXED)));
               temp _opt_lenb (vl ob); temp _static_lenb (vl sb); temp _max_blindex (vi mbi); gvars gv;
               temp _s sp; temp _buf bufp; temp _stored_len (vl stored_len); temp _last (vi last))
        SEP (ltree_at (tr_ltree s1) sp; dtree_at (tr_dtree s1) sp; bltree_at (tr_bltree s1) sp;
             ldesc_at (field_address t_ds (DOT _dyn_ltree) sp) (tr_lmax s1) (gv _static_l_desc) sp;
             ddesc_at (field_address t_ds (DOT _dyn_dtree) sp) (tr_dmax s1) (gv _static_d_desc) sp;
             bldesc_at (field_address t_ds (DOT _bl_tree) sp) (tr_blmax s1) (gv _static_bl_desc) sp;
             work_at (tr_wk s1) sp; trees_globals gv; out_at (tr_out s) m sp pbp; sym_at s sp pbp;
             field_at Ews t_ds (DOT _level) (vi (tr_level s)) sp;
             field_at Ews t_ds (DOT _strategy) (vi (tr_strategy s)) sp;
             field_at Ews t_ds (DOT _strm) strmp sp;
             field_at Ews t_strm (DOT _data_type) (vi d0) strmp; opt_buf_at bsh bo bufp)).
      * forward. entailer!.
        rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
      * forward. forward.
        entailer!.
        rewrite (proj2 (Z.leb_gt _ _)) by lia. cbn [orb]. unfold Z_FIXED.
        destruct (Z.eq_dec (tr_strategy s) 4) as [E|E].
        -- rewrite E, Z.eqb_refl. reflexivity.
        -- rewrite (proj2 (Z.eqb_neq _ _) E), Int.eq_false; [reflexivity|].
           intro E'. apply repr_inj_signed in E'; rep_lia.
      * destruct Hfr as [Hmbi [Hfo [Hfs1 [Hfs2 [Hfs3 [Hfs4 [Hfl1 [Hfst [Hfd1 [Hflm Hfdm]]]]]]]]]].
        cbn [s2 set_wk set_dmax set_dtree set_lmax set_ltree set_data_type tr_out tr_sym_next tr_sym_end
             tr_matches tr_lit_bufsize tr_level tr_strategy tr_data_type tr_lmax tr_dmax] in *.
        rewrite Hfst in Holb.
        forward_if.
        -- destruct (orb (sb <=? ob) (tr_strategy s =? Z_FIXED)) eqn:Eb;
             [|unfold typed_true in H9; cbv in H9; discriminate].
           subst olb slb. forward. unfold dtype_at. rewrite Hfd1. entailer!.
        -- destruct (orb (sb <=? ob) (tr_strategy s =? Z_FIXED)) eqn:Eb;
             [unfold typed_false in H9; cbv in H9; discriminate|].
           subst olb slb. forward. unfold dtype_at. rewrite Hfd1. entailer!.
  - (* level <= 0: a stored block is forced *)
    destruct (Z.gtb_spec (tr_level s) 0); [lia|].
    injection Hp1 as <- <- <- <-.
    forward. forward. forward.
    unfold dtype_at. entailer!.
    unfold vl. rewrite u64_repr. auto.
  - (* the block *)
    clear Hp1.
    destruct Hf1 as [Hfo [Hfs1 [Hfs2 [Hfs3 [Hfs4 [Hfl1 [Hfst [Holb [Hslb Hmbi]]]]]]]]].
    rewrite <- Hfo, <- (sym_at_eq s1 s sp pbp Hfs1 Hfs2 Hfs3 Hfs4).
    apply match_bo_split in Hp2.
    forward_if (temp _t'9 (Val.of_bool (andb (u64 (stored_len + 4) <=? olb) (is_some bo)))).
    + destruct bo as [b|].
      * unfold opt_buf_at. Intros.
        destruct (Z.eq_dec (Zlength b) 0) as [Hb0|Hb0].
        { (* b = []: excluded by the model's guard 0 < Zlength b *)
          exfalso. unfold Int64.add in H3. rewrite (Int64.unsigned_repr olb) in H3 by lia.
          rewrite (Int64.unsigned_repr stored_len) in H3 by lia. rewrite (Int64.unsigned_repr 4) in H3 by rep_lia.
          rewrite Int64.unsigned_repr_eq in H3.
          assert (Hle : (u64 (stored_len + 4) <=? olb) = true).
          { unfold u64. apply Z.leb_le. change 18446744073709551616 with Int64.modulus in *; lia. }
          destruct Hp2 as [[_ [b0 [Eb Hg]]] | [Hf _]].
          { injection Eb as <-. rewrite Hb0 in Hg. cbn in Hg. discriminate. }
          { rewrite Hle in Hf. cbn in Hf. discriminate. } }
        forward.
        entailer!.
        -- rewrite Int64.unsigned_repr in H3 by lia. rewrite Int64.unsigned_repr_eq in H3.
           unfold u64. rewrite (proj2 (Z.leb_le _ _)) by (change 18446744073709551616 with Int64.modulus; lia).
           assert (Hpb : isptr bufp)
             by (match goal with Hf : field_compatible (Tarray tuchar _ _) _ bufp |- _ => apply Hf end).
           destruct bufp; try contradiction. reflexivity.
        -- unfold opt_buf_at. entailer!.
      * unfold opt_buf_at. Intros. subst bufp.
        forward.
        entailer!.
        -- cbn [is_some]. rewrite andb_false_r. reflexivity.
        -- unfold opt_buf_at. entailer!.
    + forward. entailer!.
      rewrite Int64.unsigned_repr in H3 by lia. rewrite Int64.unsigned_repr_eq in H3.
      unfold u64. rewrite (proj2 (Z.leb_gt _ _)) by (change 18446744073709551616 with Int64.modulus; lia).
      reflexivity.
    + forward_if (PROP ()
        LOCAL (gvars gv; temp _s sp; temp _last (vi last))
        SEP (ltree_at (tr_ltree s1) sp; dtree_at (tr_dtree s1) sp; bltree_at (tr_bltree s1) sp;
             ldesc_at (field_address t_ds (DOT _dyn_ltree) sp) (tr_lmax s1) (gv _static_l_desc) sp;
             ddesc_at (field_address t_ds (DOT _dyn_dtree) sp) (tr_dmax s1) (gv _static_d_desc) sp;
             bldesc_at (field_address t_ds (DOT _bl_tree) sp) (tr_blmax s1) (gv _static_bl_desc) sp;
             work_at (tr_wk s1) sp; out_at o2 m2 sp pbp; sym_at s1 sp pbp;
             field_at Ews t_ds (DOT _level) (vi (tr_level s)) sp;
             field_at Ews t_ds (DOT _strategy) (vi (tr_strategy s)) sp;
             dtype_at s1 sp strmp; trees_globals gv; opt_buf_at bsh bo bufp)).
      * (* the stored block *)
        destruct Hp2 as [[Hc [b [-> Hsb]]] | [Hc _]];
          [| rewrite Hc in H3; unfold typed_true in H3; cbv in H3; discriminate].
        inv_bind Hsb. destruct x. inv_bind Hsb. injection Hsb as Hx Hk. subst x kind.
        rewrite (opt_buf_split bsh b stored_len bufp). Intros.
        forward_call (sp, pbp, tr_out s1, m, bufp, bsh, b, stored_len, last, (o2, m2)).
        entailer!. unfold buf_at, opt_buf_at. destruct (stored_len =? 0); entailer!.
      * destruct Hp2 as [[Hc _] | [Hc Hp2]];
          [rewrite Hc in H3; unfold typed_false in H3; cbv in H3; discriminate|].
        forward_if.
        -- (* the static trees *)
           assert (Hso : slb = olb)
             by (apply Int64.same_if_eq in H4; apply repr_inj_unsigned64 in H4; rep_lia).
           rewrite (proj2 (Z.eqb_eq _ _) Hso) in Hp2.
           inv_bind Hp2. destruct x. apply guard_inv, Z.leb_le in Ha. rename Ha into Hg.
           inv_bind Hp2. rename x into om. rename Ha into Hsb.
           inv_bind Hp2. rename x into om'. rename Ha into Hcb. injection Hp2 as Hx Hk. subst om' kind.
           destruct (tr_out s1) as [buf p bb bv bu] eqn:Eo1.
           change (Z.shiftl STATIC_TREES 1 + last) with (2 + last) in Hsb.
           destruct om as [o1 m1]. assert (0 <= 3 <= 65535) by rep_lia. sfwd. open_out_at. pose proof (out_ok_bv _ _ _ _ _ _ H6); pose proof (out_ok_bb _ _ _ _ _ _ H6). sfwd. sb_forward_if o1 m1. sb_cond. pose proof (c_send_bits_then _ _ _ _ _ _ _ _ _ Hsb ltac:(lia)) as (Hbv' & Hp0 & Hp1 & Hr). injection Hr as -> ->. sb_to_or hdr_norm. sb_rw_or hdr_val. pose proof (sb_bb1_range bb bv (2 + last)). assert (Hok1 : out_ok (mkOut buf p (sb_bb1 bb bv (2 + last)) bv bu) m) by (eapply out_ok_set_bits; [exact H6 | lia | lia | exact (out_ok_bu _ _ _ _ _ _ H6)]). assert (Hi0 : 0 <= p < Zlength buf) by lia. fwd. fwd. fwd. fwd.
           fwd.
           fold_put_byte.
           open_out_at.
           assert (Hi1 : 0 <= p + 1 < Zlength (upd_Znth p buf (u8 (Z.land (sb_bb1 bb bv (2 + last)) 255))))
             by (rewrite Zlength_upd_Znth; lia).
           fwd. fwd. fwd. fwd. fwd.
           fold_put_byte.
           open_out_at.
           sfwd. sfwd.
           rewrite (sb_shr_eq bv _ (2 + last) Hbv' Hval).
           sfwd. forward. try (idtac; sb_side).
           sep_apply (sb_then_close buf p bb bv bu m (2 + last) 3 sp pbp H6 Hp0 Hp1 Hbv' ltac:(lia) ltac:(rep_lia)).
           entailer!.
           sb_cond.
           pose proof (c_send_bits_else _ _ _ _ _ _ _ _ _ Hsb ltac:(lia)) as (Hbv' & Hr).
           injection Hr as -> ->.
           sb_to_or hdr_norm. sb_rw_or hdr_val.
           sfwd. forward. try (idtac; sb_side).
           sep_apply (sb_else_close buf p bb bv bu m (2 + last) 3 sp pbp H6 Hbv' ltac:(lia) ltac:(rep_lia)).
           entailer!.
           (* compress_block with the static trees *)
           unfold trees_globals, static_trees. Intros.
           forward_call (sp, pbp, o1, m1, s1, gv _static_ltree, Ers, L_CODES + 2, static_ltree_t,
                         gv _static_dtree, Ers, D_CODES, static_dtree_t, (o2, m2), gv).
           all: try (exact Hcb).
           unfold trees_globals, static_trees. entailer!.
           apply derives_refl.
        -- (* the dynamic trees *)
           assert (Hso : slb <> olb)
             by (intro E; rewrite E in H4; contradiction).
           rewrite (proj2 (Z.eqb_neq _ _) Hso) in Hp2.
           inv_bind Hp2. destruct x. apply guard_inv, Z.leb_le in Ha. rename Ha into Hg.
           inv_bind Hp2. rename x into om. rename Ha into Hsb.
           inv_bind Hp2. rename x into om3. rename Ha into Hsat.
           inv_bind Hp2. rename x into om'. rename Ha into Hcb. injection Hp2 as Hx Hk. subst om' kind.
           assert (Hg4 : last <= 2147483643) by exact Hg.
           destruct (tr_out s1) as [buf p bb bv bu] eqn:Eo1.
           change (Z.shiftl DYN_TREES 1 + last) with (4 + last) in Hsb.
           destruct om as [o1 m1]. assert (0 <= 3 <= 65535) by rep_lia. sfwd. open_out_at.
           pose proof (out_ok_bv _ _ _ _ _ _ H6); pose proof (out_ok_bb _ _ _ _ _ _ H6). sfwd.
           sb_forward_if o1 m1.
           sb_cond. pose proof (c_send_bits_then _ _ _ _ _ _ _ _ _ Hsb ltac:(lia)) as (Hbv' & Hp0 & Hp1 & Hr).
           injection Hr as -> ->. sb_to_or hdr_norm. sb_rw_or hdr_val.
           pose proof (sb_bb1_range bb bv (4 + last)).
           assert (Hok1 : out_ok (mkOut buf p (sb_bb1 bb bv (4 + last)) bv bu) m)
             by (eapply out_ok_set_bits; [exact H6 | lia | lia | exact (out_ok_bu _ _ _ _ _ _ H6)]).
           assert (Hi0 : 0 <= p < Zlength buf) by lia.
           fwd. fwd. fwd. fwd. fwd.
           fold_put_byte.
           open_out_at.
           assert (Hi1 : 0 <= p + 1 < Zlength (upd_Znth p buf (u8 (Z.land (sb_bb1 bb bv (4 + last)) 255))))
             by (rewrite Zlength_upd_Znth; lia).
           fwd. fwd. fwd. fwd. fwd.
           fold_put_byte.
           open_out_at.
           sfwd. sfwd.
           rewrite (sb_shr_eq bv _ (4 + last) Hbv' Hval).
           sfwd. forward. try (idtac; sb_side).
           sep_apply (sb_then_close buf p bb bv bu m (4 + last) 3 sp pbp H6 Hp0 Hp1 Hbv' ltac:(lia) ltac:(rep_lia)).
           entailer!.
           sb_cond.
           pose proof (c_send_bits_else _ _ _ _ _ _ _ _ _ Hsb ltac:(lia)) as (Hbv' & Hr).
           injection Hr as -> ->.
           sb_to_or hdr_norm. sb_rw_or hdr_val.
           sfwd. forward. try (idtac; sb_side).
           sep_apply (sb_else_close buf p bb bv bu m (4 + last) 3 sp pbp H6 Hbv' ltac:(lia) ltac:(rep_lia)).
           entailer!.
           (* send_all_trees *)
           pose proof (send_all_trees_bounds _ _ _ _ _ _ _ _ Hsat) as [Hlb Hdb].
           assert_PROP (tree_ok (tr_ltree s1) HEAP_SIZE /\ tree_ok (tr_dtree s1) (2 * D_CODES + 1)) as Htok
             by entailer!.
           destruct Htok as [[_ [Hlt _]] [_ [Hdt _]]].
           unfold ldesc_at, ddesc_at. Intros.
           forward. forward.
           unfold trees_globals. Intros.
           forward_call (sp, pbp, o1, m1, tr_ltree s1, tr_dtree s1, tr_bltree s1, tr_lmax s1 + 1, tr_dmax s1 + 1,
                         mbi + 1, om3, gv).
           all: try (unfold HEAP_SIZE, D_CODES in *; repeat split; rep_lia).
           destruct om3 as [o3 m3].
           replace (out_at (fst (o3, m3)) (snd (o3, m3)) sp pbp) with (out_at o3 m3 sp pbp) by reflexivity.
           assert_PROP (field_compatible t_ds (DOT _dyn_ltree) sp /\ field_compatible t_ds (DOT _dyn_dtree) sp)
             as Hfc by entailer!.
           destruct Hfc as [Hfl Hfd].
           rewrite ltree_arr, dtree_arr.
           forward_call (sp, pbp, o3, m3, s1, field_address t_ds (DOT _dyn_ltree) sp, Ews, HEAP_SIZE, tr_ltree s1,
                         field_address t_ds (DOT _dyn_dtree) sp, Ews, 2 * D_CODES + 1, tr_dtree s1, (o2, m2), gv).
           all: try (exact Hcb).
           rewrite <- ltree_arr, <- dtree_arr. unfold trees_globals, ldesc_at, ddesc_at. entailer!.
           all: try apply derives_refl.
      * (* init_block, then bi_windup on last *)
        pose proof (init_block_frame _ _ Hib) as Hif.
        cbn [set_out tr_out tr_lmax tr_dmax tr_blmax tr_level tr_strategy tr_data_type tr_lit_bufsize] in Hif.
        destruct Hif as (Hio & Hil & Hid & Hib' & Hilv & Hist & Hidt & Hilb).
        change (ltree_at (tr_ltree s1) sp) with (ltree_at (tr_ltree (set_out s1 o2)) sp).
        change (dtree_at (tr_dtree s1) sp) with (dtree_at (tr_dtree (set_out s1 o2)) sp).
        change (bltree_at (tr_bltree s1) sp) with (bltree_at (tr_bltree (set_out s1 o2)) sp).
        change (work_at (tr_wk s1) sp) with (work_at (tr_wk (set_out s1 o2)) sp).
        rewrite (sym_at_eq s1 (set_out s1 o2) sp pbp) by reflexivity.
        forward_call (sp, pbp, set_out s1 o2, s3).
        forward_if.
        -- rewrite (proj2 (Z.eqb_neq last 0)) in Hwu by assumption. cbn [negb] in Hwu.
           inv_bind Hwu. destruct x as [o4 m4']. injection Hwu as <- <-.
           rewrite Hio in Ha.
           forward_call (sp, pbp, o2, m2, (o4, m4')).
           try change (fst (o4, m4')) with o4. try change (snd (o4, m4')) with m4'.
           sep_apply (trees_at_close s1 s3 s (set_out s3 o4) o4 m4' sp pbp strmp gv eq_refl
                        Hil Hid Hib' Hilv Hist Hidt Hfl1 Hfst H1 H2).
           entailer!.
        -- assert (Hl0 : last = 0).
           { match goal with Hr : Int.repr last = Int.zero |- _ =>
               apply repr_inj_signed in Hr; [exact Hr | rep_lia | rep_lia] end. }
           rewrite (proj2 (Z.eqb_eq last 0) Hl0) in Hwu. cbn [negb] in Hwu.
           injection Hwu as <- <-.
           forward.
           assert (E : s3 = set_out s3 o2) by (rewrite <- Hio; symmetry; apply set_out_eta).
           sep_apply (trees_at_close s1 s3 s s3 o2 m2 sp pbp strmp gv E
                        Hil Hid Hib' Hilv Hist Hidt Hfl1 Hfst H1 H2).
           entailer!.
Qed.

Theorem trees_flush : ob_tr_flush_block.
Proof. exact body_tr_flush_block. Qed.
