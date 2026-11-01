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
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.trees.TSpec.
Require Export Zlib.proof.trees.TLemmas.
Require Import Zlib.trees.code.

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
