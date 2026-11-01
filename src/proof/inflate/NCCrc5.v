(* inflate(), cases NAME (6) and COMMENT (7): after the string's do-while,
   `if ((state->flags & 0x0200) && (state->wrap & 4)) state->check = crc32(state->check, next, copy);`
   in a minimal context (flags, wrap, check, the crc table, the input object). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.NCKit5.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Definition nc_crcblk (ta tb tf tc tr: ident) : statement :=
  Ssequence
    (Ssequence
      (Sset ta (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr))) (Tstruct _inflate_state noattr)) _flags tint))
      (Sifthenelse (Ebinop Cop.Oand (Etempvar ta tint) (Econst_int (Int.repr 512) tint) tint)
        (Ssequence
          (Sset tb (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr))) (Tstruct _inflate_state noattr)) _wrap tint))
          (Sset tf (Ecast (Ebinop Cop.Oand (Etempvar tb tint) (Econst_int (Int.repr 4) tint) tint) tbool)))
        (Sset tf (Econst_int (Int.repr 0) tint))))
    (Sifthenelse (Etempvar tf tint)
      (Ssequence
        (Ssequence
          (Sset tc (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr))) (Tstruct _inflate_state noattr)) _check tulong))
          (Scall (Some tr)
            (Evar _crc32 (Tfunction (tulong :: (tptr tuchar) :: tuint :: nil) tulong cc_default))
            ((Etempvar tc tulong) :: (Etempvar _next (tptr tuchar)) :: (Etempvar _copy tuint) :: nil)))
        (Sassign (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr))) (Tstruct _inflate_state noattr)) _check tulong)
          (Etempvar tr tulong)))
      Sskip).

Definition crcv (fl wr ck: Z) (d: list Z) : Z :=
  if andb (negb (Z.land fl 512 =? 0)) (negb (Z.land wr 4 =? 0)) then ref_crc32 ck d else ck.

Lemma crc_val_crcv: forall s d, crc_val s d = crcv (i_flags s) (i_wrap s) (i_check s) d.
Proof. reflexivity. Qed.

Lemma ncc_da_cs: forall sh n (v: list val) p,
  @data_at Zlib.units.Inflate.CS sh (tarray tuchar n) v p = @data_at Zlib.units.Crc32.CS sh (tarray tuchar n) v p.
Proof.
  intros.
  assert (E: @data_at Zlib.units.Crc32.CS sh (tarray tuchar n) v = @data_at Zlib.units.Inflate.CS sh (tarray tuchar n) v).
  { apply (@data_at_change_composite _ _ Zlib.proof.inflate.Callees.CCE_crc32); [apply JMeq_refl | reflexivity]. }
  rewrite E. reflexivity.
Qed.

Lemma ncc_and_repr: forall a b, Int.and (Int.repr a) (Int.repr b) = Int.repr (Z.land a b).
Proof.
  intros. apply Int.same_bits_eq; intros i Hi.
  rewrite Int.bits_and by auto. rewrite !Int.testbit_repr by auto. rewrite Z.land_spec. reflexivity.
Qed.

Lemma ncc_land_range: forall a b, 0 <= b -> 0 <= Z.land a b <= b.
Proof.
  intros a b H. split.
  - apply Z.land_nonneg; auto.
  - apply Zbits.Ztestbit_le; auto. intros i _ T. rewrite Z.land_spec in T. apply andb_prop in T. tauto.
Qed.

Lemma ncc_flagbit: forall a b, Int.and (Int.repr a) (Int.repr b) <> Int.zero -> (Z.land a b =? 0) = false.
Proof.
  intros a b H. rewrite ncc_and_repr in H. apply Z.eqb_neq. intro E. rewrite E in H. apply H. reflexivity.
Qed.

Lemma ncc_flagbit0: forall a b, Int.and (Int.repr a) (Int.repr b) = Int.zero -> 0 <= b <= Int.max_signed ->
  (Z.land a b =? 0) = true.
Proof.
  intros a b H Hb. rewrite ncc_and_repr in H. apply Z.eqb_eq.
  pose proof (ncc_land_range a b ltac:(lia)).
  apply (f_equal Int.unsigned) in H. rewrite Int.unsigned_repr in H by rep_lia. exact H.
Qed.

Lemma ncc_tbool: forall x, 0 <= x <= Int.max_signed ->
  Vint (if Int.eq (Int.repr x) Int.zero then Int.zero else Int.one) = Vint (Int.repr (if x =? 0 then 0 else 1)).
Proof.
  intros x H. destruct (Z.eqb_spec x 0).
  - subst. reflexivity.
  - rewrite Int.eq_false; [reflexivity | ]. intro E. apply (f_equal Int.unsigned) in E.
    rewrite Int.unsigned_repr in E by rep_lia. apply n. exact E.
Qed.

(* NAME: temps t'372, t'373, t'37, t'371, t'36 *)
Lemma semax_crc_name {Espec: OracleKind} sp cpy gv tsh fl wr ck ish ip q inn icont data:
  readable_share tsh -> readable_share ish -> isptr ip ->
  0 <= q -> q + cpy <= inn -> Zlength icont = inn -> 0 < inn ->
  sublist q (q + cpy) icont = byte_vals data -> Zlength data = cpy -> bytes_ok data ->
  0 <= cpy <= Int.max_unsigned -> srange fl -> 0 <= wr <= 15 -> lrange ck ->
  semax Delta_cases5
   (PROP () LOCAL (temp _state sp; temp _next (offset_val q ip); temp _copy (zv cpy); gvars gv)
    SEP (field_at Ews t_state (DOT _flags) (zv fl) sp; field_at Ews t_state (DOT _wrap) (zv wr) sp;
         field_at Ews t_state (DOT _check) (lv ck) sp; crc_table_at tsh gv;
         data_at ish (tarray tuchar inn) icont ip))
   (nc_crcblk _t'372 _t'373 _t'37 _t'371 _t'36)
   (normal_ret_assert
    (PROP () LOCAL (temp _state sp; temp _next (offset_val q ip); temp _copy (zv cpy); gvars gv)
     SEP (field_at Ews t_state (DOT _flags) (zv fl) sp; field_at Ews t_state (DOT _wrap) (zv wr) sp;
          field_at Ews t_state (DOT _check) (lv (crcv fl wr ck data)) sp; crc_table_at tsh gv;
          data_at ish (tarray tuchar inn) icont ip))).
Proof.
  intros RT RI PI Q0 QC LI NP SB LD BD CR FR WR KR.
  unfold nc_crcblk, crcv. abbreviate_semax.
  forward.
  match goal with |- semax _ (PROPx ?A (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx A (LOCALx (temp _t'37 (Vint (Int.repr (if andb (negb (Z.land fl 512 =? 0)) (negb (Z.land wr 4 =? 0)) then 1 else 0))) :: Q) (SEPx R))) end.
  - forward. forward. entailer!.
    match goal with H: Int.and _ _ <> Int.zero |- _ => rewrite (ncc_flagbit _ _ H) end.
    cbn [negb andb]. unfold srange in FR.
    rewrite ncc_tbool by (pose proof (ncc_land_range wr 4 ltac:(lia)); rep_lia).
    destruct (Z.land wr 4 =? 0); reflexivity.
  - forward. entailer!.
    match goal with H: Int.and _ _ = Int.zero |- _ => rewrite (ncc_flagbit0 _ _ H) by rep_lia end.
    reflexivity.
  - destruct (andb (negb (Z.land fl 512 =? 0)) (negb (Z.land wr 4 =? 0))).
    + forward_if; [ | match goal with H: Int.repr 1 = Int.zero |- _ => discriminate H end].
      forward.
      forward_call (ck, offset_val q ip, cpy, false, ish, ip, q, inn, icont, data, false, Tsh, gv, tsh).
      { rewrite <- ncc_da_cs. cancel. }
      { try (split; [ | apply cbuf_valid_pos; lia]).
        unfold cbuf_ok. split; [reflexivity | ]. split; [auto | ]. split; [lia | ]. split; [lia | ].
        split; [exact LD | ]. split; [exact BD | ]. exact SB. }
      try rewrite <- ncc_da_cs.
      forward.
      entailer!.
    + forward_if; [ match goal with H: Int.repr 0 <> Int.zero |- _ => exfalso; apply H; reflexivity end | ].
      forward. entailer!.
Qed.

(* COMMENT: temps t'357, t'358, t'44, t'356, t'43 *)
Lemma semax_crc_comm {Espec: OracleKind} sp cpy gv tsh fl wr ck ish ip q inn icont data:
  readable_share tsh -> readable_share ish -> isptr ip ->
  0 <= q -> q + cpy <= inn -> Zlength icont = inn -> 0 < inn ->
  sublist q (q + cpy) icont = byte_vals data -> Zlength data = cpy -> bytes_ok data ->
  0 <= cpy <= Int.max_unsigned -> srange fl -> 0 <= wr <= 15 -> lrange ck ->
  semax Delta_cases5
   (PROP () LOCAL (temp _state sp; temp _next (offset_val q ip); temp _copy (zv cpy); gvars gv)
    SEP (field_at Ews t_state (DOT _flags) (zv fl) sp; field_at Ews t_state (DOT _wrap) (zv wr) sp;
         field_at Ews t_state (DOT _check) (lv ck) sp; crc_table_at tsh gv;
         data_at ish (tarray tuchar inn) icont ip))
   (nc_crcblk _t'357 _t'358 _t'44 _t'356 _t'43)
   (normal_ret_assert
    (PROP () LOCAL (temp _state sp; temp _next (offset_val q ip); temp _copy (zv cpy); gvars gv)
     SEP (field_at Ews t_state (DOT _flags) (zv fl) sp; field_at Ews t_state (DOT _wrap) (zv wr) sp;
          field_at Ews t_state (DOT _check) (lv (crcv fl wr ck data)) sp; crc_table_at tsh gv;
          data_at ish (tarray tuchar inn) icont ip))).
Proof.
  intros RT RI PI Q0 QC LI NP SB LD BD CR FR WR KR.
  unfold nc_crcblk, crcv. abbreviate_semax.
  forward.
  match goal with |- semax _ (PROPx ?A (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx A (LOCALx (temp _t'44 (Vint (Int.repr (if andb (negb (Z.land fl 512 =? 0)) (negb (Z.land wr 4 =? 0)) then 1 else 0))) :: Q) (SEPx R))) end.
  - forward. forward. entailer!.
    match goal with H: Int.and _ _ <> Int.zero |- _ => rewrite (ncc_flagbit _ _ H) end.
    cbn [negb andb]. unfold srange in FR.
    rewrite ncc_tbool by (pose proof (ncc_land_range wr 4 ltac:(lia)); rep_lia).
    destruct (Z.land wr 4 =? 0); reflexivity.
  - forward. entailer!.
    match goal with H: Int.and _ _ = Int.zero |- _ => rewrite (ncc_flagbit0 _ _ H) by rep_lia end.
    reflexivity.
  - destruct (andb (negb (Z.land fl 512 =? 0)) (negb (Z.land wr 4 =? 0))).
    + forward_if; [ | match goal with H: Int.repr 1 = Int.zero |- _ => discriminate H end].
      forward.
      forward_call (ck, offset_val q ip, cpy, false, ish, ip, q, inn, icont, data, false, Tsh, gv, tsh).
      { rewrite <- ncc_da_cs. cancel. }
      { try (split; [ | apply cbuf_valid_pos; lia]).
        unfold cbuf_ok. split; [reflexivity | ]. split; [auto | ]. split; [lia | ]. split; [lia | ].
        split; [exact LD | ]. split; [exact BD | ]. exact SB. }
      try rewrite <- ncc_da_cs.
      forward.
      entailer!.
    + forward_if; [ match goal with H: Int.repr 0 <> Int.zero |- _ => exfalso; apply H; reflexivity end | ].
      forward. entailer!.
Qed.
