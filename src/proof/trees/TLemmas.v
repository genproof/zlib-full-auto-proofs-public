(** * Helper lemmas for the body proofs of trees.c against TSpec.v

    - the option monad of the checked model: inversion of [bind]/[guard] equations ([bind_inv], [inv_bind]);
    - pending_buf as [pb_vals] (the bytes where the mask is true, Vundef elsewhere): length, reads, the store
      of one byte ([pb_vals_upd]);
    - [put_byte] (the store [s->pending_buf[s->pending++] = c]): the model step [c_put_byte] as an explicit
      result [put_byte_c] ([c_put_byte_inv], [c_put_byte_eq]), [out_ok] preserved, and the entailment that
      folds the six fields after the C store back into [out_at] ([out_at_put_byte]);
    - [unfold_out_at]: open an [out_at] in the precondition into its fields. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Export Zlib.proof.trees.TRep.
Require Export Zlib.proof.trees.CModel.
Require Import Zlib.trees.code.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

(** ** The option monad *)

Lemma bind_inv {A B} (a : option A) (f : A -> option B) r :
  bind a f = Some r -> exists x, a = Some x /\ f x = Some r.
Proof. destruct a; simpl; [eauto | discriminate]. Qed.

Lemma guard_inv b : guard b = Some tt -> b = true.
Proof. destruct b; simpl; congruence. Qed.

(** Split the first [bind] of a hypothesis [H : bind a f = Some r]. *)
Ltac inv_bind H :=
  let x := fresh "x" in let Ha := fresh "Ha" in
  apply bind_inv in H; destruct H as [x [Ha H]].

(** ** pending_buf as [pb_vals] *)

Lemma Zlength_pb_vals b m : Zlength m = Zlength b -> Zlength (pb_vals b m) = Zlength b.
Proof.
  intros. unfold pb_vals. rewrite Zlength_map, Zlength_combine. lia.
Qed.

Lemma Znth_pb_vals b m i : Zlength m = Zlength b -> 0 <= i < Zlength b ->
  Znth i (pb_vals b m) = if Znth i m then vi (Znth i b) else Vundef.
Proof.
  intros. unfold pb_vals. rewrite Znth_map by (rewrite Zlength_combine; lia).
  rewrite Znth_combine by lia. reflexivity.
Qed.

(** The store of one byte into pending_buf, against the mask. *)
Lemma pb_vals_upd b m i v : Zlength m = Zlength b -> 0 <= i < Zlength b ->
  pb_vals (upd_Znth i b v) (upd_Znth i m true) = upd_Znth i (pb_vals b m) (vi v).
Proof.
  intros. unfold pb_vals. rewrite combine_upd_Znth by lia.
  rewrite <- upd_Znth_map. reflexivity.
Qed.

(** ** put_byte *)

(** The result of [put_byte] (when the index is in range). *)
Definition put_byte_c (o : outbuf) (m : list bool) (c : Z) : cout :=
  (mkOut (upd_Znth (o_pending o) (o_buf o) (u8 c)) (o_pending o + 1) (o_bi_buf o) (o_bi_valid o) (o_bi_used o),
   upd_Znth (o_pending o) m true).

Lemma c_put_byte_inv o m c r : c_put_byte (o, m) c = Some r ->
  0 <= o_pending o < Zlength (o_buf o) /\ r = put_byte_c o m c.
Proof.
  unfold c_put_byte, wr, in_range, bind. intros H.
  destruct (andb (0 <=? o_pending o) (o_pending o <? Zlength (o_buf o))) eqn:E; [|discriminate].
  apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  inversion H. split; [lia | reflexivity].
Qed.

Lemma c_put_byte_inv' om c r : c_put_byte om c = Some r ->
  0 <= o_pending (fst om) < Zlength (o_buf (fst om)) /\ r = put_byte_c (fst om) (snd om) c.
Proof. destruct om as [o m]. apply c_put_byte_inv. Qed.

Lemma c_put_byte_eq o m c : 0 <= o_pending o < Zlength (o_buf o) -> c_put_byte (o, m) c = Some (put_byte_c o m c).
Proof.
  intros. unfold c_put_byte, wr, in_range, bind.
  rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

Lemma u8_range c : 0 <= u8 c < 256.
Proof. unfold u8. apply Z.mod_pos_bound. lia. Qed.

Lemma out_ok_put_byte o m c : out_ok o m -> 0 <= o_pending o < Zlength (o_buf o) ->
  out_ok (fst (put_byte_c o m c)) (snd (put_byte_c o m c)).
Proof.
  intros [[Hm Hd] [Hb [Hp [Hbb [Hbv Hbu]]]]] Hi. cbn in *.
  split; [split|]; cbn.
  - rewrite !Zlength_upd_Znth. auto.
  - intros i Hi' Hdi. rewrite Zlength_upd_Znth in Hi'.
    destruct (Z.eq_dec i (o_pending o)) as [->|ne].
    + rewrite upd_Znth_same by lia. apply u8_range.
    + rewrite upd_Znth_diff in Hdi by lia. rewrite upd_Znth_diff by lia. auto.
  - rewrite Zlength_upd_Znth. rep_lia.
Qed.

(** The six fields after the C store of [put_byte] (pending already incremented, the byte stored) are
    [out_at] of [put_byte_c]. *)
Lemma out_at_put_byte o m c sp pbp :
  out_ok o m -> 0 <= o_pending o < Zlength (o_buf o) ->
  @field_at DCS.CS Ews t_ds (DOT _pending) (vl (o_pending o + 1)) sp *
  @field_at DCS.CS Ews t_ds (DOT _pending_buf) pbp sp *
  @field_at DCS.CS Ews t_ds (DOT _bi_buf) (vi (o_bi_buf o)) sp *
  @field_at DCS.CS Ews t_ds (DOT _bi_valid) (vi (o_bi_valid o)) sp *
  @field_at DCS.CS Ews t_ds (DOT _bi_used) (vi (o_bi_used o)) sp *
  @data_at DCS.CS Ews (tarray tuchar (Zlength (o_buf o)))
     (upd_Znth (o_pending o) (pb_vals (o_buf o) m) (vi (u8 c))) pbp
  |-- out_at (fst (put_byte_c o m c)) (snd (put_byte_c o m c)) sp pbp.
Proof.
  intros Hok Hi. pose proof (out_ok_put_byte o m c Hok Hi) as Hok'.
  destruct Hok as [[Hm _] _]. cbn in Hm.
  unfold out_at. apply andp_right; [apply prop_right; exact Hok'|].
  cbn [fst snd put_byte_c o_buf o_pending o_bi_buf o_bi_valid o_bi_used].
  rewrite Zlength_upd_Znth, pb_vals_upd by lia.
  cancel.
Qed.

(** The same with the state given by its components, and the values as VST's forward steps leave them
    (vi, vl unfolded). *)
Lemma out_at_put_byte' buf p bb bv bu m c sp pbp :
  out_ok (mkOut buf p bb bv bu) m -> 0 <= p < Zlength buf ->
  @field_at DCS.CS Ews t_ds (DOT _pending) (Vlong (Int64.repr (p + 1))) sp *
  @field_at DCS.CS Ews t_ds (DOT _pending_buf) pbp sp *
  @field_at DCS.CS Ews t_ds (DOT _bi_buf) (Vint (Int.repr bb)) sp *
  @field_at DCS.CS Ews t_ds (DOT _bi_valid) (Vint (Int.repr bv)) sp *
  @field_at DCS.CS Ews t_ds (DOT _bi_used) (Vint (Int.repr bu)) sp *
  @data_at DCS.CS Ews (tarray tuchar (Zlength buf)) (upd_Znth p (pb_vals buf m) (Vint (Int.repr (u8 c)))) pbp
  |-- out_at (mkOut (upd_Znth p buf (u8 c)) (p + 1) bb bv bu) (upd_Znth p m true) sp pbp.
Proof.
  intros Hok Hi. exact (out_at_put_byte (mkOut buf p bb bv bu) m c sp pbp Hok Hi).
Qed.

(** Open an [out_at] of the precondition: its fields, and its [out_ok] as a hypothesis. *)
Ltac unfold_out_at :=
  match goal with
  | |- context [out_at ?o ?m ?sp ?pbp] =>
      unfold out_at; Intros
  end.

(** The C values of the byte stored by put_byte. *)
Lemma byte_and255 (x : Z) :
  Int.zero_ext 8 (Int.zero_ext 8 (Int.and (Int.repr x) (Int.repr 255))) = Int.repr (u8 (Z.land x 255)).
Proof.
  unfold u8. rewrite and255_repr, !zext8_repr, !Zmod_mod.
  f_equal. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. rewrite Zmod_mod. reflexivity.
Qed.

(** The other byte values of put_byte's stores: [(Byte)x] and [(uch)((ush)x >> 8)] (after the casts' zero_ext 8
    are collapsed by [Int.zero_ext_idem]). *)
Lemma byte_and255' (x : Z) :
  Int.zero_ext 8 (Int.and (Int.repr x) (Int.repr 255)) = Int.repr (u8 (Z.land x 255)).
Proof. rewrite and_repr32, zext8_repr. reflexivity. Qed.

Lemma byte_shr8 (x : Z) :
  Int.zero_ext 8 (Int.shr (Int.zero_ext 16 (Int.repr x)) (Int.repr 8)) = Int.repr (u8 (Z.shiftr (u16 x) 8)).
Proof.
  rewrite zext16_repr. pose proof (Z.mod_pos_bound x 65536 ltac:(lia)).
  rewrite shr_repr by (cbn; rep_lia). rewrite zext8_repr. unfold u8, u16.
  rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma byte_zext8 (x : Z) : Int.zero_ext 8 (Int.repr x) = Int.repr (u8 x).
Proof. apply zext8_repr. Qed.

(** Normalize the value stored by put_byte to [Int.repr (u8 c)]. *)
Ltac norm_byte_val :=
  rewrite ?Int.zero_ext_idem by lia;
  rewrite ?byte_and255', ?byte_shr8, ?byte_zext8.

(** All fields of [out_at] (with vi, vl unfolded, as forward steps leave them) are [out_at]. *)
Lemma out_at_fields buf p bb bv bu m sp pbp :
  out_ok (mkOut buf p bb bv bu) m ->
  @field_at DCS.CS Ews t_ds (DOT _pending) (Vlong (Int64.repr p)) sp *
  @field_at DCS.CS Ews t_ds (DOT _pending_buf) pbp sp *
  @field_at DCS.CS Ews t_ds (DOT _bi_buf) (Vint (Int.repr bb)) sp *
  @field_at DCS.CS Ews t_ds (DOT _bi_valid) (Vint (Int.repr bv)) sp *
  @field_at DCS.CS Ews t_ds (DOT _bi_used) (Vint (Int.repr bu)) sp *
  @data_at DCS.CS Ews (tarray tuchar (Zlength buf)) (pb_vals buf m) pbp
  |-- out_at (mkOut buf p bb bv bu) m sp pbp.
Proof.
  intros Hok. unfold out_at. apply andp_right; [apply prop_right; exact Hok|]. cbn. cancel.
Qed.

Lemma out_ok_set_bits buf p bb bv bu m bb' bv' bu' :
  out_ok (mkOut buf p bb bv bu) m -> 0 <= bb' < 65536 ->
  Int.min_signed <= bv' <= Int.max_signed -> Int.min_signed <= bu' <= Int.max_signed ->
  out_ok (mkOut buf p bb' bv' bu') m.
Proof. intros [H1 [H2 [H3 _]]] ? ? ?. split; [exact H1|]. cbn in *. repeat split; lia. Qed.

(** Open an [out_at] of the precondition into its fields (projections simplified, vi/vl unfolded); its
    [out_ok] becomes a hypothesis. *)
Ltac open_out_at :=
  unfold out_at; Intros;
  cbn [o_buf o_pending o_bi_buf o_bi_valid o_bi_used] in *; unfold vi, vl.

(** After the C store of [put_byte] ([s->pending_buf[s->pending++] = c]): fold the six fields back into
    [out_at] of the model's result [put_byte_c].  Needs the [out_ok] of the state before and its index range
    [0 <= pending < Zlength buf] as hypotheses. *)
Ltac fold_put_byte :=
  try (change (Int.signed (Int.repr 1)) with 1; rewrite add64_repr);
  norm_byte_val;
  match goal with
  | |- context [@data_at _ _ (tarray tuchar (Zlength ?buf)) (upd_Znth ?p (pb_vals ?buf ?m) (Vint (Int.repr (u8 ?c)))) ?pbp] =>
    match goal with
    | |- context [@field_at _ _ _ (DOT _bi_buf) (Vint (Int.repr ?bb)) ?sp] =>
    match goal with
    | |- context [@field_at _ _ _ (DOT _bi_valid) (Vint (Int.repr ?bv)) _] =>
    match goal with
    | |- context [@field_at _ _ _ (DOT _bi_used) (Vint (Int.repr ?bu)) _] =>
      sep_apply (out_at_put_byte' buf p bb bv bu m c sp pbp ltac:(assumption) ltac:(assumption))
    end end end
  end.

(** A forward step; the side condition [tc_val tushort/tuchar (Vint (Int.repr x))] that loads of the ush/uch
    fields (bi_buf) leave is closed cheaply from a hypothesis [0 <= x <= 65535] / [0 <= x <= 255] (entailer!
    takes seconds on it and does not even finish it). *)
Ltac tc_side :=
  lazymatch goal with
  | |- _ |-- local _ =>
      go_lower; apply prop_right; first [apply tc_val_tushort_repr | apply tc_val_tuchar_repr]; rep_lia
  end.
Ltac fwd := forward; try tc_side.

(** put_byte / put_short keep the bit fields. *)
Lemma c_put_byte_bits om c r : c_put_byte om c = Some r ->
  o_bi_buf (fst r) = o_bi_buf (fst om) /\ o_bi_valid (fst r) = o_bi_valid (fst om) /\
  o_bi_used (fst r) = o_bi_used (fst om).
Proof. intros H. apply c_put_byte_inv' in H. destruct H as [_ ->]. cbn. auto. Qed.

Lemma c_put_short_bits om w r : c_put_short om w = Some r ->
  o_bi_buf (fst r) = o_bi_buf (fst om) /\ o_bi_valid (fst r) = o_bi_valid (fst om) /\
  o_bi_used (fst r) = o_bi_used (fst om).
Proof.
  unfold c_put_short. intros H. apply bind_inv in H. destruct H as [x [H1 H2]].
  apply c_put_byte_bits in H1. apply c_put_byte_bits in H2. destruct H1 as [? [? ?]], H2 as [? [? ?]].
  repeat split; congruence.
Qed.

(** [(x >> 8)] stored into an ush field, for [x] an ush. *)
Lemma ush_shr8 bb : 0 <= bb < 65536 ->
  Int.zero_ext 16 (Int.shr (Int.repr bb) (Int.repr 8)) = Int.repr (Z.shiftr bb 8).
Proof.
  intros. rewrite shr_repr by (cbn; rep_lia). change (two_p 8) with 256.
  rewrite zext16_repr, Z.mod_small by (pose proof (div256_ush bb H); lia).
  rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

(** ** bi_reverse *)
Lemma c_bi_reverse_loop_S f c rs l :
  c_bi_reverse_loop (S f) c rs l =
  if l - 1 >? 0 then c_bi_reverse_loop f (Z.shiftr c 1) (Z.shiftl (Z.lor rs (Z.land c 1)) 1) (l - 1)
  else Some (Z.shiftl (Z.lor rs (Z.land c 1)) 1).
Proof. reflexivity. Qed.

Lemma lor_lt_pow2 a b k : 0 <= a < 2 ^ k -> 0 <= b < 2 ^ k -> 0 <= Z.lor a b < 2 ^ k.
Proof.
  intros Ha Hb. split; [apply Z.lor_nonneg; lia|].
  destruct (Z.eq_dec a 0) as [->|Na]; [rewrite Z.lor_0_l; lia|].
  destruct (Z.eq_dec b 0) as [->|Nb]; [rewrite Z.lor_0_r; lia|].
  assert (0 < Z.lor a b).
  { assert (0 <= Z.lor a b) by (apply Z.lor_nonneg; lia).
    destruct (Z.eq_dec (Z.lor a b) 0) as [E|]; [apply Z.lor_eq_0_iff in E; lia | lia]. }
  apply Z.log2_lt_pow2; auto. rewrite Z.log2_lor by lia.
  apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.

Lemma land1_range c : 0 <= Z.land c 1 < 2.
Proof. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.

Lemma shru1_repr c : 0 <= c <= Int.max_unsigned ->
  Int.shru (Int.repr c) (Int.repr 1) = Int.repr (Z.shiftr c 1).
Proof. intros. rewrite shru_repr by (cbn; rep_lia). rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma shl1_repr x : Int.shl (Int.repr x) (Int.repr 1) = Int.repr (Z.shiftl x 1).
Proof.
  rewrite Int.shl_mul_two_p. rewrite Int.unsigned_repr by rep_lia. change (two_p 1) with 2.
  rewrite mul_repr. rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Lemma shiftr1_range c : 0 <= c <= Int.max_unsigned -> 0 <= Z.shiftr c 1 <= Int.max_unsigned.
Proof.
  intros. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2.
  split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia].
Qed.

(** One iteration of bi_reverse's loop keeps [res] below [2^(k+1)] when it was below [2^k] ([k >= 1]). *)
Lemma bi_reverse_res_step rs c k : 1 <= k -> 0 <= rs < 2 ^ k ->
  0 <= Z.shiftl (Z.lor rs (Z.land c 1)) 1 < 2 ^ (k + 1).
Proof.
  intros Hk Hr. pose proof (land1_range c).
  assert (2 <= 2 ^ k) by (change 2 with (2 ^ 1); apply Z.pow_le_mono_r; lia).
  pose proof (lor_lt_pow2 rs (Z.land c 1) k Hr ltac:(lia)).
  rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2. lia.
Qed.
