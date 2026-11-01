(** * The body of trees.c's _tr_stored_block against its shared specification (TSpec.tr_stored_block_spec).

    The inlined send_bits macro block: [SendKit.sb_block] (see SendKit.v's header); bi_windup by its spec;
    put_short as two put_byte stores ([TLemmas.fold_put_byte]); the zmemcpy by Libc.memcpy_spec. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.trees.TSpec.
Require Import Zlib.proof.trees.SendKit2.
Require Import Zlib.proof.zutil.Libc.
Require Import Zlib.trees.code.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

(** ** The stored-block copy on pending_buf ([copy_bytes], [mask_set_n]) *)

Lemma mask_set_n_eq n m lo : 0 <= lo -> lo + Z.of_nat n <= Zlength m ->
  mask_set_n n m lo = sublist 0 lo m ++ repeat true n ++ sublist (lo + Z.of_nat n) (Zlength m) m.
Proof.
  revert m lo. induction n as [|n IH]; intros m lo H0 H1; cbn [mask_set_n].
  - cbn [repeat app]. rewrite Z.add_0_r, <- sublist_split, sublist_same by lia; auto.
  - rewrite IH by (rewrite ?Zlength_upd_Znth; lia). rewrite Zlength_upd_Znth.
    replace (lo + 1 + Z.of_nat n) with (lo + Z.of_nat (S n)) by lia.
    replace (repeat true (S n)) with ([true] ++ repeat true n) by reflexivity. list_solve.
Qed.

Lemma pb_vals_sublist lo hi b m : sublist lo hi (pb_vals b m) = pb_vals (sublist lo hi b) (sublist lo hi m).
Proof. unfold pb_vals. rewrite sublist_map, sublist_combine. reflexivity. Qed.

Lemma pb_vals_true src : pb_vals src (repeat true (length src)) = byte_vals src.
Proof. induction src; cbn; auto. unfold pb_vals in IHsrc. rewrite IHsrc. reflexivity. Qed.

Lemma copy_bytes_sublists B M P src :
  0 <= P -> P + Zlength src <= Zlength B -> Zlength M = Zlength B ->
  let B' := pb_vals (copy_bytes B P src) (mask_set_n (Z.to_nat (Zlength src)) M P) in
  sublist 0 P B' = sublist 0 P (pb_vals B M) /\
  sublist P (P + Zlength src) B' = byte_vals src /\
  sublist (P + Zlength src) (Zlength B) B' = sublist (P + Zlength src) (Zlength B) (pb_vals B M).
Proof.
  intros H0 H1 H2 B'. subst B'. pose proof (Zlength_nonneg src).
  rewrite mask_set_n_eq by lia. rewrite Z2Nat.id by lia. rewrite !pb_vals_sublist. unfold copy_bytes.
  split; [|split].
  - f_equal; list_solve.
  - rewrite <- pb_vals_true. rewrite <- ZtoNat_Zlength. f_equal; list_solve.
  - f_equal; list_solve.
Qed.

Lemma Zlength_repeat_nat {A} (x : A) n : Zlength (repeat x n) = Z.of_nat n.
Proof. rewrite Zlength_correct, repeat_length. reflexivity. Qed.

Lemma Zlength_copy_bytes B P src : 0 <= P -> P + Zlength src <= Zlength B ->
  Zlength (copy_bytes B P src) = Zlength B.
Proof. intros. pose proof (Zlength_nonneg src). unfold copy_bytes. list_solve. Qed.

Lemma Zlength_mask_set_n n M P : 0 <= P -> P + Z.of_nat n <= Zlength M -> Zlength (mask_set_n n M P) = Zlength M.
Proof.
  intros. rewrite mask_set_n_eq by lia.
  rewrite !Zlength_app, !Zlength_sublist by lia. rewrite Zlength_correct, repeat_length. lia.
Qed.

Lemma out_ok_copy B P bb bv bu M src :
  out_ok (mkOut B P bb bv bu) M -> P + Zlength src <= Zlength B -> Forall (fun x => 0 <= x < 256) src ->
  out_ok (mkOut (copy_bytes B P src) (P + Zlength src) bb bv bu) (mask_set_n (Z.to_nat (Zlength src)) M P).
Proof.
  intros [[Hm Hd] [Hb [Hp [Hbb [Hbv Hbu]]]]] H1 Hs.
  cbn [o_buf o_pending o_bi_buf o_bi_valid o_bi_used mb_val mb_def] in *. pose proof (Zlength_nonneg src).
  unfold out_ok, mb_ok. cbn [o_buf o_pending o_bi_buf o_bi_valid o_bi_used mb_val mb_def].
  rewrite Zlength_copy_bytes by lia.
  split; [split|].
  - rewrite Zlength_mask_set_n by (rewrite ?Z2Nat.id; lia). lia.
  - intros i Hi Hdi.
    rewrite mask_set_n_eq in Hdi by (rewrite ?Z2Nat.id; lia). rewrite Z2Nat.id in Hdi by lia.
    unfold copy_bytes.
    destruct (zlt i P).
    { assert (E1 : Znth i (sublist 0 P M ++ repeat true (Z.to_nat (Zlength src)) ++
                           sublist (P + Zlength src) (Zlength M) M) = Znth i M) by list_solve.
      assert (E2 : Znth i (sublist 0 P B ++ src ++ sublist (P + Zlength src) (Zlength B) B) = Znth i B)
        by list_solve.
      rewrite E1 in Hdi; rewrite E2; apply Hd; auto; lia. }
    destruct (zlt i (P + Zlength src)).
    { assert (E2 : Znth i (sublist 0 P B ++ src ++ sublist (P + Zlength src) (Zlength B) B) = Znth (i - P) src)
        by list_solve.
      rewrite E2; rewrite Forall_forall in Hs; apply Hs; apply Znth_In; lia. }
    assert (E1 : Znth i (sublist 0 P M ++ repeat true (Z.to_nat (Zlength src)) ++
                         sublist (P + Zlength src) (Zlength M) M) = Znth i M).
    { pose proof (Zlength_repeat_nat true (Z.to_nat (Zlength src))) as Lr. rewrite Z2Nat.id in Lr by lia.
      rewrite app_assoc. rewrite Znth_app2 by (rewrite Zlength_app, Zlength_sublist; lia).
      rewrite Zlength_app, Zlength_sublist, Lr by lia. rewrite Znth_sublist by lia. f_equal. lia. }
    assert (E2 : Znth i (sublist 0 P B ++ src ++ sublist (P + Zlength src) (Zlength B) B) = Znth i B)
      by list_solve.
    rewrite E1 in Hdi; rewrite E2; apply Hd; auto; lia.
  - repeat split; rep_lia.
Qed.

Lemma pb_copy_split B M P src pbp :
  0 <= P -> P + Zlength src <= Zlength B -> Zlength M = Zlength B ->
  @data_at DCS.CS Ews (tarray tuchar (Zlength B)) (pb_vals B M) pbp |--
  @data_at_ DCS.CS Ews (tarray tuchar (Zlength src)) (offset_val P pbp) *
  (@data_at DCS.CS Ews (tarray tuchar (Zlength src)) (byte_vals src) (offset_val P pbp) -*
   @data_at DCS.CS Ews (tarray tuchar (Zlength B))
     (pb_vals (copy_bytes B P src) (mask_set_n (Z.to_nat (Zlength src)) M P)) pbp).
Proof.
  intros H0 H1 H2. pose proof (Zlength_nonneg src).
  destruct (copy_bytes_sublists B M P src H0 H1 H2) as (E1 & E2 & E3). cbv zeta in E1, E2, E3.
  assert (L1 : Zlength (pb_vals B M) = Zlength B) by (apply Zlength_pb_vals; auto).
  assert (L2 : Zlength (pb_vals (copy_bytes B P src) (mask_set_n (Z.to_nat (Zlength src)) M P)) = Zlength B).
  { rewrite Zlength_pb_vals; rewrite ?Zlength_copy_bytes, ?Zlength_mask_set_n; rewrite ?Z2Nat.id; lia. }
  assert_PROP (field_compatible (tarray tuchar (Zlength B)) nil pbp) as Hfc by entailer!.
  unfold tarray.
  rewrite (split3_data_at_Tarray_tuchar Ews (Zlength B) P (P + Zlength src) (pb_vals B M)) by lia.
  rewrite (split3_data_at_Tarray_tuchar Ews (Zlength B) P (P + Zlength src)
             (pb_vals (copy_bytes B P src) (mask_set_n (Z.to_nat (Zlength src)) M P))) by lia.
  rewrite E1, E2, E3. replace (P + Zlength src - P) with (Zlength src) by lia.
  rewrite (field_address0_offset (Tarray tuchar (Zlength B) noattr) [ArraySubsc P])
    by auto with field_compatible.
  cbn [nested_field_offset nested_field_rec nested_field_type]. simpl sizeof.
  replace (0 + 1 * P) with P by lia.
  sep_apply (data_at_data_at_ Ews (Tarray tuchar (Zlength src) noattr)).
  cancel. rewrite <- !wand_sepcon_adjoint. cancel.
Qed.

Lemma src_split bsh b sl bufp : 0 <= sl <= Zlength b ->
  @data_at DCS.CS bsh (tarray tuchar (Zlength b)) (map vi b) bufp |--
  @data_at DCS.CS bsh (tarray tuchar (Zlength (sublist 0 sl b))) (byte_vals (sublist 0 sl b)) bufp *
  (@data_at DCS.CS bsh (tarray tuchar (Zlength (sublist 0 sl b))) (byte_vals (sublist 0 sl b)) bufp -*
   @data_at DCS.CS bsh (tarray tuchar (Zlength b)) (map vi b) bufp).
Proof.
  intros Hs. unfold tarray.
  rewrite (split2_data_at_Tarray_tuchar bsh (Zlength b) sl (map vi b) bufp) by (rewrite ?Zlength_map; lia).
  rewrite Zlength_sublist by lia. replace (sl - 0) with sl by lia.
  replace (byte_vals (sublist 0 sl b)) with (sublist 0 sl (map vi b))
    by (unfold byte_vals, vi; rewrite sublist_map; reflexivity).
  cancel. rewrite <- !wand_sepcon_adjoint. cancel.
Qed.

Lemma tsb_val last : Int.zero_ext 16 (Int.add (Int.shl (Int.repr 0) (Int.repr 1)) (Int.repr last)) =
  Int.repr (u16 (0 + last)).
Proof. change (Int.shl (Int.repr 0) (Int.repr 1)) with (Int.repr 0). rewrite add_repr32. apply sb_val_repr. Qed.

Lemma u16_l2i s : Int.zero_ext 16 (Int.repr (Int64.unsigned (Int64.repr s))) = Int.repr (u16 s).
Proof.
  rewrite zext16_repr. f_equal. unfold u16. rewrite Int64.unsigned_repr_eq.
  symmetry. apply Znumtheory.Zmod_div_mod; [lia | reflexivity | exists (2 ^ 48); reflexivity].
Qed.

Lemma u16_zmm s : Int.zero_ext 16 (Int.repr (Int64.Z_mod_modulus s)) = Int.repr (u16 s).
Proof. rewrite Int64.Z_mod_modulus_eq. rewrite <- Int64.unsigned_repr_eq. apply u16_l2i. Qed.

Lemma not64_repr s : Int64.not (Int64.repr s) = Int64.repr (Z.lnot s).
Proof.
  apply Int64.same_bits_eq; intros i Hi. rewrite Int64.bits_not by auto.
  rewrite !Int64.testbit_repr by auto. rewrite Z.lnot_spec by lia. reflexivity.
Qed.

Lemma u16_l2i_not s : Int.zero_ext 16 (Int.repr (Int64.unsigned (Int64.not (Int64.repr s)))) = Int.repr (u16 (Z.lnot s)).
Proof. rewrite not64_repr. apply u16_l2i. Qed.

Lemma u16_not_zmm s :
  Int.zero_ext 16 (Int.repr (Int64.Z_mod_modulus (Z.lxor (Int64.Z_mod_modulus s) 18446744073709551615))) =
  Int.repr (u16 (Z.lnot s)).
Proof.
  change (Int64.Z_mod_modulus (Z.lxor (Int64.Z_mod_modulus s) 18446744073709551615))
    with (Int64.unsigned (Int64.not (Int64.repr s))).
  apply u16_l2i_not.
Qed.

Ltac tsb_valtac := first [ apply tsb_val | sb_val_default ].

Lemma body_tr_stored_block : semax_body TSpec.Vprog Gprog_tr_stored_block f__tr_stored_block tr_stored_block_spec.
Proof.
  start_function.
  unfold c_tr_stored_block in H1. inv_bind H1. rename Ha into Hsb.
  change (Z.shiftl STORED_BLOCK 1) with 0 in Hsb.
  inv_bind H1. rename Ha into Hw. inv_bind H1. rename Ha into Hs1. inv_bind H1. rename Ha into Hs2.
  unfold vi, vl.
  sb_block Hsb ltac:(idtac) ltac:(tsb_valtac).
  forward_call (sp, pbp, o, m0, x0).
  destruct x0 as [o2 m2]. cbn [fst snd].
  unfold c_put_short in Hs1. inv_bind Hs1.
  apply c_put_byte_inv' in Ha. cbn [fst snd] in Ha. destruct Ha as [Hi1 ->].
  apply c_put_byte_inv' in Hs1. cbn [fst snd put_byte_c o_buf o_pending o_bi_buf] in Hs1. destruct Hs1 as [Hi2 ->].
  destruct o2 as [buf2 p2 bb2 bv2 bu2].
  cbn [fst snd put_byte_c o_buf o_pending o_bi_buf o_bi_valid o_bi_used] in Hi1, Hi2, Hs2.
  open_out_at. rename H6 into Hok2.
  fwd. fwd. fwd. fwd.
  rewrite u16_zmm. fold_put_byte. open_out_at.
  fwd. fwd. fwd. fwd.
  rewrite u16_zmm. fold_put_byte. open_out_at.
  unfold c_put_short in Hs2. inv_bind Hs2.
  apply c_put_byte_inv' in Ha. cbn [fst snd put_byte_c o_buf o_pending o_bi_buf o_bi_valid o_bi_used] in Ha.
  destruct Ha as [Hi3 ->].
  apply c_put_byte_inv' in Hs2. cbn [fst snd put_byte_c o_buf o_pending o_bi_buf o_bi_valid o_bi_used] in Hs2.
  destruct Hs2 as [Hi4 ->]. rename H7 into Hok3.
  fwd. fwd. fwd. fwd.
  rewrite u16_not_zmm. fold_put_byte. open_out_at.
  fwd. fwd. fwd. fwd.
  rewrite u16_not_zmm. fold_put_byte.
  cbn [put_byte_c o_buf o_pending o_bi_buf o_bi_valid o_bi_used] in H1.
  match goal with |- context [out_at (mkOut ?B0 ?P0 _ _ _) ?M0 sp pbp] =>
    set (B := B0) in *; set (M := M0) in *; set (P := P0) in * end.
  clearbody B M P.
  clear Hi1 Hi2 Hi3 Hi4 Hok2 Hok3 H6 H7 Hw Hsb.
  inv_bind H1. destruct x as [B' M'].
  open_out_at. rename H6 into Hok4.
  forward_if (PROP (out_ok (mkOut B' (P + stored_len) bb2 bv2 bu2) M')
              LOCAL (temp _s sp; temp _stored_len (Vlong (Int64.repr stored_len)))
              SEP (@field_at DCS.CS Ews t_ds (DOT _pending) (Vlong (Int64.repr P)) sp;
                   @field_at DCS.CS Ews t_ds (DOT _pending_buf) pbp sp;
                   @field_at DCS.CS Ews t_ds (DOT _bi_buf) (Vint (Int.repr bb2)) sp;
                   @field_at DCS.CS Ews t_ds (DOT _bi_valid) (Vint (Int.repr bv2)) sp;
                   @field_at DCS.CS Ews t_ds (DOT _bi_used) (Vint (Int.repr bu2)) sp;
                   @data_at DCS.CS Ews (tarray tuchar (Zlength B')) (pb_vals B' M') pbp;
                   buf_at bsh stored_len b bufp)).
  - (* stored_len != 0: the copy *)
    rewrite (proj2 (Z.eqb_neq _ _) H6') in Ha. cbn [negb] in Ha.
    apply bind_inv in Ha; destruct Ha as [[] [Hg1 Ha]]; apply guard_inv in Hg1.
    apply bind_inv in Ha; destruct Ha as [[] [Hg2 Ha]]; apply guard_inv in Hg2.
    injection Ha as <- <-.
    apply andb_prop in Hg1 as [Hg1a Hg1b]. apply Z.ltb_lt in Hg1a. apply Z.leb_le in Hg1b.
    apply Z.leb_le in Hg2.
    unfold buf_at. rewrite (proj2 (Z.eqb_neq _ _) H6'). Intros.
    assert (HmB : Zlength M = Zlength B) by (destruct Hok4 as [[Hm _] _]; exact Hm).
    assert (HP : 0 <= P) by (destruct Hok4 as (_ & _ & Hp & _); cbn in Hp; lia).
    assert (Hzl : Zlength (sublist 0 stored_len b) = stored_len) by (rewrite Zlength_sublist; lia).
    pose proof (out_ok_copy B P bb2 bv2 bu2 M (sublist 0 stored_len b) Hok4 ltac:(lia)
                  (Forall_sublist _ _ _ _ H8)) as Hok'.
    rewrite Hzl in Hok'.
    fwd. fwd.
    sep_apply (src_split bsh b stored_len bufp ltac:(lia)).
    sep_apply (pb_copy_split B M P (sublist 0 stored_len b) pbp HP ltac:(lia) HmB).
    forward_call (Ews, offset_val P pbp, bsh, bufp, sublist 0 stored_len b).
    { rewrite Hzl; entailer!. }
    { cancel. }
    { unfold bytes_ok; apply Forall_sublist; eapply Forall_impl; [|exact H8]; intros; simpl in *; rep_lia. }
    sep_apply (wand_frame_elim (@data_at DCS.CS Ews (tarray tuchar (Zlength (sublist 0 stored_len b)))
                                  (byte_vals (sublist 0 stored_len b)) (offset_val P pbp))).
    sep_apply (wand_frame_elim (@data_at DCS.CS bsh (tarray tuchar (Zlength (sublist 0 stored_len b)))
                                  (byte_vals (sublist 0 stored_len b)) bufp)).
    rewrite Hzl. rewrite Zlength_copy_bytes by lia.
    unfold buf_at. rewrite (proj2 (Z.eqb_neq _ _) H6').
    entailer!.
  - (* stored_len == 0 *)
    assert (Hz : stored_len = 0).
    { apply (f_equal Int64.unsigned) in H6. rewrite Int64.unsigned_repr in H6 by rep_lia. exact H6. }
    subst stored_len. change (negb (0 =? 0)) with false in Ha. injection Ha as <- <-.
    forward.
    assert (out_ok (mkOut B (P + 0) bb2 bv2 bu2) M) by (rewrite Z.add_0_r; exact Hok4).
    entailer!.
  - Intros. fwd. fwd.
    rewrite add64_repr. injection H1 as <-. cbn [fst snd].
    sep_apply (out_at_fields B' (P + stored_len) bb2 bv2 bu2 M' sp pbp H6).
    entailer!.
Qed.

