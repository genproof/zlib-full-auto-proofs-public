(* Helpers of Body5_reset.v (v5 specs): the struct inflate_state split into the fields a function touches
   and the rest (opaque), the whole object for zcfree, the invariants of the reset states. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate_api.Bodies5.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.
(* contiguous memory blocks *)
Fixpoint mbs (sh: share) (p: val) (a: Z) (l: list Z) : mpred :=
  match l with
  | nil => emp
  | n :: r => memory_block sh n (offset_val a p) * mbs sh p (a + n) r
  end.

Fixpoint sumz (l: list Z) : Z := match l with nil => 0 | n :: r => n + sumz r end.

Lemma ptrofs_add_small: forall i a, 0 <= a -> Ptrofs.unsigned i + a < Ptrofs.modulus ->
  Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr a)) = Ptrofs.unsigned i + a.
Proof.
  intros. unfold Ptrofs.add. pose proof (Ptrofs.unsigned_range i).
  rewrite (Ptrofs.unsigned_repr a) by (unfold Ptrofs.max_unsigned; lia).
  apply Ptrofs.unsigned_repr. unfold Ptrofs.max_unsigned; lia.
Qed.

Lemma mbs_join: forall sh b i l a,
  0 <= a -> Forall (fun n => 0 <= n) l -> Ptrofs.unsigned i + a + sumz l < Ptrofs.modulus ->
  mbs sh (Vptr b i) a l |-- memory_block sh (sumz l) (offset_val a (Vptr b i)).
Proof.
  intros sh b i l. induction l as [ | n r IH]; intros a Ha Hl Hm.
  - simpl. rewrite memory_block_zero. entailer!.
  - inversion Hl; subst. simpl in Hm |- *.
    assert (0 <= sumz r) by (clear - H2; induction H2; simpl; lia).
    pose proof (Ptrofs.unsigned_range i).
    sep_apply (IH (a + n)); try lia.
    assert (Ho: Ptrofs.add i (Ptrofs.repr a) = Ptrofs.repr (Ptrofs.unsigned i + a)).
    { unfold Ptrofs.add. rewrite (Ptrofs.unsigned_repr a) by (unfold Ptrofs.max_unsigned; lia). reflexivity. }
    rewrite Ho. rewrite memory_block_split by lia.
    unfold offset_val.
    replace (Ptrofs.add i (Ptrofs.repr (a + n))) with (Ptrofs.repr (Ptrofs.unsigned i + a + n)).
    + cancel.
    + unfold Ptrofs.add. rewrite (Ptrofs.unsigned_repr (a + n)) by (unfold Ptrofs.max_unsigned; lia).
      f_equal. lia.
Qed.

Lemma fa_mb: forall sh f v p n o,
  n = sizeof (nested_field_type t_state (DOT f)) -> o = nested_field_offset t_state (DOT f) ->
  field_at sh t_state (DOT f) v p |-- memory_block sh n (offset_val o p).
Proof.
  intros. subst n o. assert_PROP (field_compatible t_state (DOT f) p) by entailer!.
  sep_apply field_at_field_at_. rewrite field_at__memory_block.
  rewrite field_compatible_field_address by auto. apply derives_refl.
Qed.

Lemma sizeof_state: sizeof t_state = 7160.
Proof. vm_compute. reflexivity. Qed.

(* the trailing padding of struct inflate_state *)
Lemma assoc36: forall a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36: mpred,
  a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34 * a35 * a36 =
  a1 * (a2 * (a3 * (a4 * (a5 * (a6 * (a7 * (a8 * (a9 * (a10 * (a11 * (a12 * (a13 * (a14 * (a15 * (a16 * (a17 * (a18 * (a19 * (a20 * (a21 * (a22 * (a23 * (a24 * (a25 * (a26 * (a27 * (a28 * (a29 * (a30 * (a31 * (a32 * (a33 * (a34 * (a35 * (a36 * (emp)))))))))))))))))))))))))))))))))))).
Proof. intros. rewrite sepcon_emp. rewrite !sepcon_assoc. reflexivity. Qed.

Lemma fa_mb': forall sh f v b i n o,
  n = sizeof (nested_field_type t_state (DOT f)) -> o = nested_field_offset t_state (DOT f) ->
  field_at sh t_state (DOT f) v (Vptr b i) |-- memory_block sh n (Vptr b (Ptrofs.add i (Ptrofs.repr o))).
Proof. intros. exact (fa_mb sh f v (Vptr b i) n o H H0). Qed.

Lemma fa_fc: forall sh f v p, field_at sh t_state (DOT f) v p |-- !! field_compatible t_state (DOT f) p.
Proof. intros. entailer!. Qed.

Lemma extract_first: forall (a r S: mpred) (Q: Prop), (a |-- !! Q) -> (Q -> a * r |-- S) -> a * r |-- S.
Proof.
  intros. apply derives_trans with (!! Q && (a * r)).
  - apply andp_right; [ | apply derives_refl]. sep_apply H. entailer!.
  - apply derives_extract_prop. auto.
Qed.

Definition state_sizes : list Z :=
  [8;4;4;4;4;4;4;8;8;8;4;4;4;4;8;8;4;4;4;4;8;8;4;4;4;4;4;4;8;640;576;5776;4;4;4;4].

Ltac fa_step :=
  apply sepcon_derives;
  [ first [ apply fa_mb'; vm_compute; reflexivity
          | unfold field_at_; apply fa_mb'; vm_compute; reflexivity
          | apply derives_refl ]
  | ].

Lemma state_free: forall gv sp strmp headp winp s,
  state_rep gv sp strmp headp winp s * state_pad sp |-- data_at_ Ews t_state sp.
Proof.
  intros. unfold state_rep, state_pad. rewrite assoc36.
  apply extract_first with (Q := field_compatible t_state (DOT _strm) sp); [apply fa_fc | intro H].
  assert (FC: field_compatible t_state [] sp) by (destruct H as (?&?&?&?&?); repeat split; auto).
  destruct sp as [ | | | | | b i]; try (destruct H; contradiction).
  assert (SZ: Ptrofs.unsigned i + 7160 < Ptrofs.modulus)
    by (destruct FC as (_&_&SC&_); unfold size_compatible in SC; rewrite sizeof_state in SC; exact SC).
  rewrite <- memory_block_data_at_ by auto.
  rewrite sizeof_state.
  eapply derives_trans; [ | eapply derives_trans; [apply (mbs_join Ews b i state_sizes 0) | ] ].
  - unfold state_sizes. simpl mbs.
    do 36 fa_step. apply derives_refl.
  - lia.
  - repeat constructor; lia.
  - simpl sumz. lia.
  - simpl sumz. unfold offset_val. rewrite Ptrofs.add_zero. apply derives_refl.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the invariants of the reset states                                                              *)

Ltac rk_simpl := unfold reset_keep_s; cbn [l_s set_l_s i_mode i_last i_wrap i_havedict i_flags i_dmax i_check i_total i_head i_wbits i_wsize i_whave i_wnext i_win i_wdata i_hold i_bits i_length i_offset i_extra i_lencode i_distcode i_lenbits i_distbits i_ncode i_nlen i_ndist i_have i_next i_lens i_codes i_sane i_back i_was set_i_mode set_i_last set_i_wrap set_i_havedict set_i_flags set_i_dmax set_i_check set_i_total set_i_head set_i_wbits set_i_wsize set_i_whave set_i_wnext set_i_win set_i_wdata set_i_hold set_i_bits set_i_length set_i_offset set_i_extra set_i_lencode set_i_distcode set_i_lenbits set_i_distbits set_i_ncode set_i_nlen set_i_ndist set_i_have set_i_next set_i_lens set_i_codes set_i_sane set_i_back set_i_was].

Lemma head_not_decode: ~ decode_mode HEAD.
Proof. unfold decode_mode, HEAD, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT. lia. Qed.

Ltac rs_simpl := unfold reset_s, reset_keep_s; cbn [l_s set_l_s i_mode i_last i_wrap i_havedict i_flags i_dmax i_check i_total i_head i_wbits i_wsize i_whave i_wnext i_win i_wdata i_hold i_bits i_length i_offset i_extra i_lencode i_distcode i_lenbits i_distbits i_ncode i_nlen i_ndist i_have i_next i_lens i_codes i_sane i_back i_was set_i_mode set_i_last set_i_wrap set_i_havedict set_i_flags set_i_dmax set_i_check set_i_total set_i_head set_i_wbits set_i_wsize set_i_whave set_i_wnext set_i_win set_i_wdata set_i_hold set_i_bits set_i_length set_i_offset set_i_extra set_i_lencode set_i_distcode set_i_lenbits set_i_distbits set_i_ncode set_i_nlen set_i_ndist set_i_have set_i_next set_i_lens set_i_codes set_i_sane set_i_back set_i_was].

Lemma live_reset_ok: forall L, live_ok L -> live_ok (set_l_s L (reset_s (l_s L))).
Proof.
  intros [sp winp s h headp hsh xb nb cb] (P & W & M & HW & W3 & HS & WB0 & HD & WF).
  cbn [l_s l_sp l_h l_hsh l_xb l_nb l_cb set_l_s] in *.
  split; [exact P | ]. split; [ | split; [ | split; [exact HW | split; [ | split; [exact HS | ]]]]].
  - destruct W. constructor; rs_simpl; auto;
      try (unfold HEAD, SYNC, srange, urange, lrange, tref_ok, ENOUGH_CODES in *; rep_lia).
    split; [reflexivity | constructor].
  - constructor; rs_simpl; repeat split; intros; exfalso;
      try (apply head_not_decode; assumption);
      unfold HEAD, LENLENS, CODELENS, LENEXT, DISTEXT, MATCH, DIST in *; lia.
  - destruct W3. constructor; rs_simpl; auto; intros HM;
      try (exfalso; apply head_not_decode; exact HM);
      try (unfold HEAD, LENEXT, DISTEXT in *; lia).
    intros HB HR. split; [reflexivity | ]. exact (proj2 (WB0 HB)).
  - rs_simpl. split; [exact WB0 | ]. split; [intro; discriminate | ].
    intros _ _. split; [reflexivity | left; reflexivity].
Qed.

(* &state->codes (the array decayed to a pointer) is codes_at sp 0 *)
Lemma codes_addr0: forall sp, field_compatible t_state (DOT _codes) sp ->
  field_address t_state (DOT _codes) sp = codes_at sp 0.
Proof.
  intros. unfold codes_at, field_address0, field_address.
  rewrite if_true by auto.
  rewrite if_true by (eapply field_compatible0_cons_Tarray; [reflexivity | auto | lia]).
  f_equal.
Qed.
