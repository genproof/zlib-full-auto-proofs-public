(* Bodies of inflate.c's API functions, version 5: api_init_stmt (Bodies5.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require VST.veric.mapsto_memory_block VST.veric.res_predicates.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.ResetFacts.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* zmemzero: an object of zero bytes (memset's postcondition) is the zero value of any type. *)

Lemma byte_zero_data_at: forall {cs: compspecs} sh b ofs, readable_share sh ->
  data_at sh tuchar (Vint Int.zero) (Vptr b (Ptrofs.repr ofs)) |--
  res_predicates.address_mapsto Mint8unsigned (Vint Int.zero) sh (b, Ptrofs.unsigned (Ptrofs.repr ofs)).
Proof.
  intros. unfold data_at, field_at, at_offset. simpl. rewrite data_at_rec_eq. simpl. unfold mapsto. simpl.
  rewrite if_true by auto. apply derives_extract_prop; intros _. apply orp_left.
  - apply derives_extract_prop; intros _. rewrite Ptrofs.add_zero. apply derives_refl.
  - apply derives_extract_prop; intros X. discriminate.
Qed.

Lemma bytes_zero_amz: forall {cs: compspecs} sh b k ofs, readable_share sh -> 0 <= ofs ->
  ofs + Z.of_nat k < Ptrofs.modulus ->
  data_at sh (tarray tuchar (Z.of_nat k)) (Zrepeat (Vint Int.zero) (Z.of_nat k)) (Vptr b (Ptrofs.repr ofs)) |--
  mapsto_memory_block.address_mapsto_zeros sh k (b, ofs).
Proof.
  intros cs sh b k. revert sh b. induction k as [|k IH]; intros sh b ofs Hsh Hofs Hlt.
  - simpl. rewrite data_at_zero_array_eq; auto. apply derives_refl. exact I.
  - simpl. change (predicates_sl.sepcon ?A ?B) with (A*B).
    assert (E: Zrepeat (Vint Int.zero) (Z.pos (Pos.of_succ_nat k)) =
               [Vint Int.zero] ++ Zrepeat (Vint Int.zero) (Z.of_nat k)).
    { unfold Zrepeat. rewrite Zpos_P_of_succ_nat, Z2Nat.inj_succ by lia. reflexivity. }
    rewrite E. clear E. rewrite Zpos_P_of_succ_nat.
    assert_PROP (field_compatible (tarray tuchar (Z.succ (Z.of_nat k))) [] (Vptr b (Ptrofs.repr ofs))) as FC.
    { unfold data_at, field_at. Intros. apply prop_right; auto. }
    rewrite (split2_data_at_Tarray_app 1).
    2: reflexivity. 2: rewrite Zlength_Zrepeat; lia.
    erewrite data_at_singleton_array_eq by reflexivity.
    apply sepcon_derives.
    { rewrite <- (Ptrofs.unsigned_repr ofs) at 2 by rep_lia. apply byte_zero_data_at; auto. }
    rewrite field_address0_offset by (apply field_compatible_field_compatible0 in FC; auto with field_compatible).
    simpl. rewrite ptrofs_add_repr.
    replace (Z.succ ofs) with (ofs + 1) by lia. replace (Z.succ (Z.of_nat k) - 1) with (Z.of_nat k) by lia.
    apply IH; auto; lia.
Qed.

(* the zero bytes of an object of type t are its zero value *)
Lemma zero_bytes_data_at: forall {cs: compspecs} sh t p,
  readable_share sh -> complete_legal_cosu_type t = true ->
  fully_nonvolatile (rank_type cenv_cs t) t = true ->
  field_compatible t [] p ->
  data_at sh (tarray tuchar (sizeof t)) (Zrepeat (Vint Int.zero) (sizeof t)) p |-- data_at sh t (zero_val t) p.
Proof.
  intros cs sh t p Hsh HC HV FC.
  destruct p; try (destruct FC; contradiction).
  pose proof FC as FC'. destruct FC' as (_ & _ & SZ & AL & _). simpl in SZ, AL.
  pose proof (sizeof_pos t). pose proof (Ptrofs.unsigned_range i).
  rewrite <- (Ptrofs.repr_unsigned i).
  assert (X := bytes_zero_amz sh b (Z.to_nat (sizeof t)) (Ptrofs.unsigned i) Hsh ltac:(lia)
                 ltac:(rewrite Z2Nat.id; lia)).
  rewrite Z2Nat.id in X by lia. eapply derives_trans; [exact X | ]. clear X.
  unfold data_at, field_at. rewrite prop_true_andp by (rewrite Ptrofs.repr_unsigned; auto).
  unfold at_offset. simpl. rewrite <- (Ptrofs.repr_unsigned i) in AL. rewrite Ptrofs.unsigned_repr in AL by rep_lia.
  rewrite Ptrofs.add_zero.
  eapply derives_trans; [ | apply mapsto_zeros_data_at_rec_zero_val; auto; rewrite ?Ptrofs.unsigned_repr; lia].
  unfold mapsto_zeros. rewrite Ptrofs.unsigned_repr by rep_lia. apply andp_right; [apply prop_right; lia | apply derives_refl].
Qed.

(* inflateInit2_: the zmemzero'd struct inflate_state, field by field. *)
Definition zbytes (n: Z) : list val := Zrepeat (Vint Int.zero) n.

Lemma zbytes_split: forall sh n k p, 0 <= k <= n -> field_compatible (tarray tuchar n) [] p ->
  data_at sh (tarray tuchar n) (zbytes n) p =
  data_at sh (tarray tuchar k) (zbytes k) p * data_at sh (tarray tuchar (n - k)) (zbytes (n - k)) (offset_val k p).
Proof.
  intros. unfold zbytes.
  replace (Zrepeat (Vint Int.zero) n) with (Zrepeat (Vint Int.zero) k ++ Zrepeat (Vint Int.zero) (n - k))
    by (rewrite Zrepeat_app by lia; f_equal; lia).
  rewrite (split2_data_at_Tarray_app k n sh tuchar) by (rewrite Zlength_Zrepeat; lia).
  rewrite field_address0_offset.
  - simpl. rewrite Z.mul_1_l. reflexivity.
  - apply field_compatible_field_compatible0 in H0. auto with field_compatible.
Qed.

(* one field of struct inflate_state from its zero bytes *)
Lemma peel: forall sh f n o p,
  readable_share sh -> field_compatible t_state [] p ->
  in_members f (co_members (get_co _inflate_state)) ->
  o = nested_field_offset t_state (DOT f) ->
  complete_legal_cosu_type (nested_field_type t_state (DOT f)) = true ->
  fully_nonvolatile (rank_type cenv_cs (nested_field_type t_state (DOT f))) (nested_field_type t_state (DOT f)) = true ->
  0 <= sizeof (nested_field_type t_state (DOT f)) <= n ->
  o + n <= sizeof t_state ->
  data_at sh (tarray tuchar n) (zbytes n) (offset_val o p) |--
  field_at sh t_state (DOT f) (zero_val (nested_field_type t_state (DOT f))) p *
  data_at sh (tarray tuchar (n - sizeof (nested_field_type t_state (DOT f))))
    (zbytes (n - sizeof (nested_field_type t_state (DOT f))))
    (offset_val (o + sizeof (nested_field_type t_state (DOT f))) p).
Proof.
  intros sh f n o p Hsh FC IM Ho HC HV Hn Hon.
  set (ft := nested_field_type t_state (DOT f)) in *.
  assert_PROP (field_compatible (tarray tuchar n) [] (offset_val o p)) as FC2 by entailer!.
  rewrite (zbytes_split sh n (sizeof ft)) by auto.
  rewrite offset_offset_val. apply sepcon_derives; [ | apply derives_refl].
  assert (FCf: field_compatible t_state (DOT f) p).
  { apply field_compatible_cons; split; auto. }
  rewrite field_at_data_at. rewrite field_compatible_field_address by auto. rewrite <- Ho.
  apply zero_bytes_data_at; auto.
  subst o. apply field_compatible_nested_field. auto.
Qed.

Lemma peel2: forall sh f n o p n' o' (v: reptype (nested_field_type t_state (DOT f))),
  readable_share sh -> field_compatible t_state [] p ->
  in_members f (co_members (get_co _inflate_state)) ->
  o = nested_field_offset t_state (DOT f) ->
  complete_legal_cosu_type (nested_field_type t_state (DOT f)) = true ->
  fully_nonvolatile (rank_type cenv_cs (nested_field_type t_state (DOT f))) (nested_field_type t_state (DOT f)) = true ->
  0 <= sizeof (nested_field_type t_state (DOT f)) <= n ->
  o + n <= sizeof t_state ->
  zero_val (nested_field_type t_state (DOT f)) = v ->
  n' = n - sizeof (nested_field_type t_state (DOT f)) ->
  o' = o + sizeof (nested_field_type t_state (DOT f)) ->
  data_at sh (tarray tuchar n) (zbytes n) (offset_val o p) |--
  field_at sh t_state (DOT f) v p * data_at sh (tarray tuchar n') (zbytes n') (offset_val o' p).
Proof.
  intros. subst v n' o'. apply peel; auto.
Qed.

Ltac sd := first [ reflexivity | split; vm_compute; congruence | vm_compute; congruence | cbv; tauto ].
Ltac zv1 := first [ apply zero_val_Tint | apply zero_val_Tlong | apply zero_val_Tpointer
                  | rewrite zero_val_eq; unfold fold_reptype; simpl; unfold struct_zero_val; simpl;
                    rewrite ?zero_val_eq; reflexivity ].
Ltac zv := first [ zv1
                 | etransitivity; [apply zero_val_tarray | ];
                   unfold Zrepeat; rewrite ?map_repeat; f_equal; zv1 ].

(* the struct inflate_state right after zmemzero (all fields zero, the pointers NULL) *)
Definition zstate (sp: val) : mpred :=
  field_at Ews t_state (DOT _strm) nullval sp *
  field_at Ews t_state (DOT _mode) (Vint (Int.repr 0)) sp *
  field_at Ews t_state (DOT _last) (Vint (Int.repr 0)) sp *
  field_at Ews t_state (DOT _wrap) (Vint (Int.repr 0)) sp *
  field_at Ews t_state (DOT _havedict) (Vint (Int.repr 0)) sp *
  field_at Ews t_state (DOT _flags) (Vint (Int.repr 0)) sp *
  field_at Ews t_state (DOT _dmax) (Vint (Int.repr 0)) sp *
  field_at Ews t_state (DOT _check) (Vlong (Int64.repr 0)) sp *
  field_at Ews t_state (DOT _total) (Vlong (Int64.repr 0)) sp *
  field_at Ews t_state (DOT _head) nullval sp *
  field_at Ews t_state (DOT _wbits) (Vint (Int.repr 0)) sp *
  field_at Ews t_state (DOT _wsize) (Vint (Int.repr 0)) sp *
  field_at Ews t_state (DOT _whave) (Vint (Int.repr 0)) sp *
  field_at Ews t_state (DOT _wnext) (Vint (Int.repr 0)) sp *
  field_at Ews t_state (DOT _window) nullval sp *
  field_at Ews t_state (DOT _hold) (Vlong (Int64.repr 0)) sp *
  field_at Ews t_state (DOT _bits) (Vint (Int.repr 0)) sp *
  field_at Ews t_state (DOT _length) (Vint (Int.repr 0)) sp *
  field_at Ews t_state (DOT _offset) (Vint (Int.repr 0)) sp *
  field_at Ews t_state (DOT _extra) (Vint (Int.repr 0)) sp *
  field_at Ews t_state (DOT _lencode) nullval sp *
  field_at Ews t_state (DOT _distcode) nullval sp *
  field_at Ews t_state (DOT _lenbits) (Vint (Int.repr 0)) sp *
  field_at Ews t_state (DOT _distbits) (Vint (Int.repr 0)) sp *
  field_at Ews t_state (DOT _ncode) (Vint (Int.repr 0)) sp *
  field_at Ews t_state (DOT _nlen) (Vint (Int.repr 0)) sp *
  field_at Ews t_state (DOT _ndist) (Vint (Int.repr 0)) sp *
  field_at Ews t_state (DOT _have) (Vint (Int.repr 0)) sp *
  field_at Ews t_state (DOT _next) nullval sp *
  field_at Ews t_state (DOT _lens) (map (fun z => Vint (Int.repr z)) (Zrepeat 0 320)) sp *
  field_at_ Ews t_state (DOT _work) sp *
  field_at Ews t_state (DOT _codes) (map ent (Zrepeat (mkE 0 0 0) ENOUGH_CODES)) sp *
  field_at Ews t_state (DOT _sane) (Vint (Int.repr 0)) sp *
  field_at Ews t_state (DOT _back) (Vint (Int.repr 0)) sp *
  field_at Ews t_state (DOT _was) (Vint (Int.repr 0)) sp.

Lemma zero_state: forall sp, field_compatible t_state [] sp ->
  data_at Ews (tarray tuchar 7160) (zbytes 7160) sp |--
  zstate sp * data_at Ews (tarray tuchar 4) (zbytes 4) (offset_val 7156 sp).
Proof.
  intros sp FC.
  assert (E: sp = offset_val 0 sp) by (destruct sp; try (destruct FC; contradiction); simpl; rewrite Ptrofs.add_zero; auto).
  rewrite E at 1. clear E.
  sep_apply (peel2 Ews _strm 7160 0 sp 7152 8 nullval ltac:(auto) FC ltac:(sd) eq_refl eq_refl eq_refl ltac:(sd) ltac:(sd) ltac:(zv) eq_refl eq_refl).
  sep_apply (peel2 Ews _mode 7152 8 sp 7148 12 (Vint (Int.repr 0)) ltac:(auto) FC ltac:(sd) eq_refl eq_refl eq_refl ltac:(sd) ltac:(sd) ltac:(zv) eq_refl eq_refl).
  sep_apply (peel2 Ews _last 7148 12 sp 7144 16 (Vint (Int.repr 0)) ltac:(auto) FC ltac:(sd) eq_refl eq_refl eq_refl ltac:(sd) ltac:(sd) ltac:(zv) eq_refl eq_refl).
  sep_apply (peel2 Ews _wrap 7144 16 sp 7140 20 (Vint (Int.repr 0)) ltac:(auto) FC ltac:(sd) eq_refl eq_refl eq_refl ltac:(sd) ltac:(sd) ltac:(zv) eq_refl eq_refl).
  sep_apply (peel2 Ews _havedict 7140 20 sp 7136 24 (Vint (Int.repr 0)) ltac:(auto) FC ltac:(sd) eq_refl eq_refl eq_refl ltac:(sd) ltac:(sd) ltac:(zv) eq_refl eq_refl).
  sep_apply (peel2 Ews _flags 7136 24 sp 7132 28 (Vint (Int.repr 0)) ltac:(auto) FC ltac:(sd) eq_refl eq_refl eq_refl ltac:(sd) ltac:(sd) ltac:(zv) eq_refl eq_refl).
  sep_apply (peel2 Ews _dmax 7132 28 sp 7128 32 (Vint (Int.repr 0)) ltac:(auto) FC ltac:(sd) eq_refl eq_refl eq_refl ltac:(sd) ltac:(sd) ltac:(zv) eq_refl eq_refl).
  sep_apply (peel2 Ews _check 7128 32 sp 7120 40 (Vlong (Int64.repr 0)) ltac:(auto) FC ltac:(sd) eq_refl eq_refl eq_refl ltac:(sd) ltac:(sd) ltac:(zv) eq_refl eq_refl).
  sep_apply (peel2 Ews _total 7120 40 sp 7112 48 (Vlong (Int64.repr 0)) ltac:(auto) FC ltac:(sd) eq_refl eq_refl eq_refl ltac:(sd) ltac:(sd) ltac:(zv) eq_refl eq_refl).
  sep_apply (peel2 Ews _head 7112 48 sp 7104 56 nullval ltac:(auto) FC ltac:(sd) eq_refl eq_refl eq_refl ltac:(sd) ltac:(sd) ltac:(zv) eq_refl eq_refl).
  sep_apply (peel2 Ews _wbits 7104 56 sp 7100 60 (Vint (Int.repr 0)) ltac:(auto) FC ltac:(sd) eq_refl eq_refl eq_refl ltac:(sd) ltac:(sd) ltac:(zv) eq_refl eq_refl).
  sep_apply (peel2 Ews _wsize 7100 60 sp 7096 64 (Vint (Int.repr 0)) ltac:(auto) FC ltac:(sd) eq_refl eq_refl eq_refl ltac:(sd) ltac:(sd) ltac:(zv) eq_refl eq_refl).
  sep_apply (peel2 Ews _whave 7096 64 sp 7092 68 (Vint (Int.repr 0)) ltac:(auto) FC ltac:(sd) eq_refl eq_refl eq_refl ltac:(sd) ltac:(sd) ltac:(zv) eq_refl eq_refl).
  sep_apply (peel2 Ews _wnext 7092 68 sp 7088 72 (Vint (Int.repr 0)) ltac:(auto) FC ltac:(sd) eq_refl eq_refl eq_refl ltac:(sd) ltac:(sd) ltac:(zv) eq_refl eq_refl).
  sep_apply (peel2 Ews _window 7088 72 sp 7080 80 nullval ltac:(auto) FC ltac:(sd) eq_refl eq_refl eq_refl ltac:(sd) ltac:(sd) ltac:(zv) eq_refl eq_refl).
  sep_apply (peel2 Ews _hold 7080 80 sp 7072 88 (Vlong (Int64.repr 0)) ltac:(auto) FC ltac:(sd) eq_refl eq_refl eq_refl ltac:(sd) ltac:(sd) ltac:(zv) eq_refl eq_refl).
  sep_apply (peel2 Ews _bits 7072 88 sp 7068 92 (Vint (Int.repr 0)) ltac:(auto) FC ltac:(sd) eq_refl eq_refl eq_refl ltac:(sd) ltac:(sd) ltac:(zv) eq_refl eq_refl).
  sep_apply (peel2 Ews _length 7068 92 sp 7064 96 (Vint (Int.repr 0)) ltac:(auto) FC ltac:(sd) eq_refl eq_refl eq_refl ltac:(sd) ltac:(sd) ltac:(zv) eq_refl eq_refl).
  sep_apply (peel2 Ews _offset 7064 96 sp 7060 100 (Vint (Int.repr 0)) ltac:(auto) FC ltac:(sd) eq_refl eq_refl eq_refl ltac:(sd) ltac:(sd) ltac:(zv) eq_refl eq_refl).
  sep_apply (peel2 Ews _extra 7060 100 sp 7056 104 (Vint (Int.repr 0)) ltac:(auto) FC ltac:(sd) eq_refl eq_refl eq_refl ltac:(sd) ltac:(sd) ltac:(zv) eq_refl eq_refl).
  sep_apply (peel2 Ews _lencode 7056 104 sp 7048 112 nullval ltac:(auto) FC ltac:(sd) eq_refl eq_refl eq_refl ltac:(sd) ltac:(sd) ltac:(zv) eq_refl eq_refl).
  sep_apply (peel2 Ews _distcode 7048 112 sp 7040 120 nullval ltac:(auto) FC ltac:(sd) eq_refl eq_refl eq_refl ltac:(sd) ltac:(sd) ltac:(zv) eq_refl eq_refl).
  sep_apply (peel2 Ews _lenbits 7040 120 sp 7036 124 (Vint (Int.repr 0)) ltac:(auto) FC ltac:(sd) eq_refl eq_refl eq_refl ltac:(sd) ltac:(sd) ltac:(zv) eq_refl eq_refl).
  sep_apply (peel2 Ews _distbits 7036 124 sp 7032 128 (Vint (Int.repr 0)) ltac:(auto) FC ltac:(sd) eq_refl eq_refl eq_refl ltac:(sd) ltac:(sd) ltac:(zv) eq_refl eq_refl).
  sep_apply (peel2 Ews _ncode 7032 128 sp 7028 132 (Vint (Int.repr 0)) ltac:(auto) FC ltac:(sd) eq_refl eq_refl eq_refl ltac:(sd) ltac:(sd) ltac:(zv) eq_refl eq_refl).
  sep_apply (peel2 Ews _nlen 7028 132 sp 7024 136 (Vint (Int.repr 0)) ltac:(auto) FC ltac:(sd) eq_refl eq_refl eq_refl ltac:(sd) ltac:(sd) ltac:(zv) eq_refl eq_refl).
  sep_apply (peel2 Ews _ndist 7024 136 sp 7020 140 (Vint (Int.repr 0)) ltac:(auto) FC ltac:(sd) eq_refl eq_refl eq_refl ltac:(sd) ltac:(sd) ltac:(zv) eq_refl eq_refl).
  sep_apply (peel2 Ews _have 7020 140 sp 7016 144 (Vint (Int.repr 0)) ltac:(auto) FC ltac:(sd) eq_refl eq_refl eq_refl ltac:(sd) ltac:(sd) ltac:(zv) eq_refl eq_refl).
  sep_apply (peel2 Ews _next 7016 144 sp 7008 152 nullval ltac:(auto) FC ltac:(sd) eq_refl eq_refl eq_refl ltac:(sd) ltac:(sd) ltac:(zv) eq_refl eq_refl).
  sep_apply (peel2 Ews _lens 7008 152 sp 6368 792 (map (fun z => Vint (Int.repr z)) (Zrepeat 0 320)) ltac:(auto) FC ltac:(sd) eq_refl eq_refl eq_refl ltac:(sd) ltac:(sd) ltac:(zv) eq_refl eq_refl).
  sep_apply (peel2 Ews _work 6368 792 sp 5792 1368 (Zrepeat (Vint (Int.repr 0)) 288) ltac:(auto) FC ltac:(sd) eq_refl eq_refl eq_refl ltac:(sd) ltac:(sd) ltac:(zv) eq_refl eq_refl).
  sep_apply (peel2 Ews _codes 5792 1368 sp 16 7144 (map ent (Zrepeat (mkE 0 0 0) ENOUGH_CODES)) ltac:(auto) FC ltac:(sd) eq_refl eq_refl eq_refl ltac:(sd) ltac:(sd) ltac:(zv) eq_refl eq_refl).
  sep_apply (peel2 Ews _sane 16 7144 sp 12 7148 (Vint (Int.repr 0)) ltac:(auto) FC ltac:(sd) eq_refl eq_refl eq_refl ltac:(sd) ltac:(sd) ltac:(zv) eq_refl eq_refl).
  sep_apply (peel2 Ews _back 12 7148 sp 8 7152 (Vint (Int.repr 0)) ltac:(auto) FC ltac:(sd) eq_refl eq_refl eq_refl ltac:(sd) ltac:(sd) ltac:(zv) eq_refl eq_refl).
  sep_apply (peel2 Ews _was 8 7152 sp 4 7156 (Vint (Int.repr 0)) ltac:(auto) FC ltac:(sd) eq_refl eq_refl eq_refl ltac:(sd) ltac:(sd) ltac:(zv) eq_refl eq_refl).
  sep_apply (field_at_field_at_ Ews t_state (DOT _work)). unfold zstate. cancel.
Qed.

Lemma mb_split: forall sh n k m o o' p, field_compatible t_state [] p -> 0 <= o -> 0 <= k <= n ->
  o + n <= sizeof t_state -> m = n - k -> o' = o + k ->
  memory_block sh n (offset_val o p) = memory_block sh k (offset_val o p) * memory_block sh m (offset_val o' p).
Proof.
  intros sh n k m o o' p FC Ho Hk Hn Hm Ho'. subst m o'.
  destruct p; try (destruct FC; contradiction). destruct FC as (_ & _ & SZ & _). simpl in SZ.
  change (sizeof t_state) with 7160 in *. pose proof (Ptrofs.unsigned_range i).
  simpl offset_val.
  rewrite !Ptrofs.add_unsigned, !Ptrofs.unsigned_repr by rep_lia.
  replace n with (k + (n - k)) at 1 by lia.
  rewrite (memory_block_split sh b (Ptrofs.unsigned i + o) k (n - k)) by lia.
  replace (Ptrofs.unsigned i + (o + k)) with (Ptrofs.unsigned i + o + k) by lia. reflexivity.
Qed.

Lemma mb_field: forall f s o p, field_compatible t_state [] p ->
  in_members f (co_members (get_co _inflate_state)) ->
  s = sizeof (nested_field_type t_state (DOT f)) -> o = nested_field_offset t_state (DOT f) ->
  field_at_ Ews t_state (DOT f) p = memory_block Ews s (offset_val o p).
Proof.
  intros. subst. rewrite field_at__memory_block.
  rewrite field_compatible_field_address; auto.
  apply field_compatible_cons; split; auto.
Qed.

(* every field of struct inflate_state, contents anything *)
Definition state_fields_ (sp: val) : mpred :=
  field_at_ Ews t_state (DOT _strm) sp *
  field_at_ Ews t_state (DOT _mode) sp *
  field_at_ Ews t_state (DOT _last) sp *
  field_at_ Ews t_state (DOT _wrap) sp *
  field_at_ Ews t_state (DOT _havedict) sp *
  field_at_ Ews t_state (DOT _flags) sp *
  field_at_ Ews t_state (DOT _dmax) sp *
  field_at_ Ews t_state (DOT _check) sp *
  field_at_ Ews t_state (DOT _total) sp *
  field_at_ Ews t_state (DOT _head) sp *
  field_at_ Ews t_state (DOT _wbits) sp *
  field_at_ Ews t_state (DOT _wsize) sp *
  field_at_ Ews t_state (DOT _whave) sp *
  field_at_ Ews t_state (DOT _wnext) sp *
  field_at_ Ews t_state (DOT _window) sp *
  field_at_ Ews t_state (DOT _hold) sp *
  field_at_ Ews t_state (DOT _bits) sp *
  field_at_ Ews t_state (DOT _length) sp *
  field_at_ Ews t_state (DOT _offset) sp *
  field_at_ Ews t_state (DOT _extra) sp *
  field_at_ Ews t_state (DOT _lencode) sp *
  field_at_ Ews t_state (DOT _distcode) sp *
  field_at_ Ews t_state (DOT _lenbits) sp *
  field_at_ Ews t_state (DOT _distbits) sp *
  field_at_ Ews t_state (DOT _ncode) sp *
  field_at_ Ews t_state (DOT _nlen) sp *
  field_at_ Ews t_state (DOT _ndist) sp *
  field_at_ Ews t_state (DOT _have) sp *
  field_at_ Ews t_state (DOT _next) sp *
  field_at_ Ews t_state (DOT _lens) sp *
  field_at_ Ews t_state (DOT _work) sp *
  field_at_ Ews t_state (DOT _codes) sp *
  field_at_ Ews t_state (DOT _sane) sp *
  field_at_ Ews t_state (DOT _back) sp *
  field_at_ Ews t_state (DOT _was) sp.

(* the struct as its fields and the trailing padding (4 bytes after was) *)
Lemma state_fields_eq: forall sp, field_compatible t_state [] sp ->
  data_at_ Ews t_state sp = state_fields_ sp * memory_block Ews 4 (offset_val 7156 sp).
Proof.
  intros sp FC.
  rewrite data_at__memory_block, prop_true_andp by auto. change (sizeof t_state) with 7160.
  assert (E: sp = offset_val 0 sp) by (destruct sp; try (destruct FC; contradiction); simpl; rewrite Ptrofs.add_zero; auto).
  rewrite E at 1. clear E.
  rewrite (mb_split Ews 7160 8 7152 0 8 sp FC ltac:(lia) ltac:(lia) ltac:(sd) eq_refl eq_refl).
  rewrite <- (mb_field _strm 8 0 sp FC ltac:(sd) eq_refl eq_refl).
  rewrite (mb_split Ews 7152 4 7148 8 12 sp FC ltac:(lia) ltac:(lia) ltac:(sd) eq_refl eq_refl).
  rewrite <- (mb_field _mode 4 8 sp FC ltac:(sd) eq_refl eq_refl).
  rewrite (mb_split Ews 7148 4 7144 12 16 sp FC ltac:(lia) ltac:(lia) ltac:(sd) eq_refl eq_refl).
  rewrite <- (mb_field _last 4 12 sp FC ltac:(sd) eq_refl eq_refl).
  rewrite (mb_split Ews 7144 4 7140 16 20 sp FC ltac:(lia) ltac:(lia) ltac:(sd) eq_refl eq_refl).
  rewrite <- (mb_field _wrap 4 16 sp FC ltac:(sd) eq_refl eq_refl).
  rewrite (mb_split Ews 7140 4 7136 20 24 sp FC ltac:(lia) ltac:(lia) ltac:(sd) eq_refl eq_refl).
  rewrite <- (mb_field _havedict 4 20 sp FC ltac:(sd) eq_refl eq_refl).
  rewrite (mb_split Ews 7136 4 7132 24 28 sp FC ltac:(lia) ltac:(lia) ltac:(sd) eq_refl eq_refl).
  rewrite <- (mb_field _flags 4 24 sp FC ltac:(sd) eq_refl eq_refl).
  rewrite (mb_split Ews 7132 4 7128 28 32 sp FC ltac:(lia) ltac:(lia) ltac:(sd) eq_refl eq_refl).
  rewrite <- (mb_field _dmax 4 28 sp FC ltac:(sd) eq_refl eq_refl).
  rewrite (mb_split Ews 7128 8 7120 32 40 sp FC ltac:(lia) ltac:(lia) ltac:(sd) eq_refl eq_refl).
  rewrite <- (mb_field _check 8 32 sp FC ltac:(sd) eq_refl eq_refl).
  rewrite (mb_split Ews 7120 8 7112 40 48 sp FC ltac:(lia) ltac:(lia) ltac:(sd) eq_refl eq_refl).
  rewrite <- (mb_field _total 8 40 sp FC ltac:(sd) eq_refl eq_refl).
  rewrite (mb_split Ews 7112 8 7104 48 56 sp FC ltac:(lia) ltac:(lia) ltac:(sd) eq_refl eq_refl).
  rewrite <- (mb_field _head 8 48 sp FC ltac:(sd) eq_refl eq_refl).
  rewrite (mb_split Ews 7104 4 7100 56 60 sp FC ltac:(lia) ltac:(lia) ltac:(sd) eq_refl eq_refl).
  rewrite <- (mb_field _wbits 4 56 sp FC ltac:(sd) eq_refl eq_refl).
  rewrite (mb_split Ews 7100 4 7096 60 64 sp FC ltac:(lia) ltac:(lia) ltac:(sd) eq_refl eq_refl).
  rewrite <- (mb_field _wsize 4 60 sp FC ltac:(sd) eq_refl eq_refl).
  rewrite (mb_split Ews 7096 4 7092 64 68 sp FC ltac:(lia) ltac:(lia) ltac:(sd) eq_refl eq_refl).
  rewrite <- (mb_field _whave 4 64 sp FC ltac:(sd) eq_refl eq_refl).
  rewrite (mb_split Ews 7092 4 7088 68 72 sp FC ltac:(lia) ltac:(lia) ltac:(sd) eq_refl eq_refl).
  rewrite <- (mb_field _wnext 4 68 sp FC ltac:(sd) eq_refl eq_refl).
  rewrite (mb_split Ews 7088 8 7080 72 80 sp FC ltac:(lia) ltac:(lia) ltac:(sd) eq_refl eq_refl).
  rewrite <- (mb_field _window 8 72 sp FC ltac:(sd) eq_refl eq_refl).
  rewrite (mb_split Ews 7080 8 7072 80 88 sp FC ltac:(lia) ltac:(lia) ltac:(sd) eq_refl eq_refl).
  rewrite <- (mb_field _hold 8 80 sp FC ltac:(sd) eq_refl eq_refl).
  rewrite (mb_split Ews 7072 4 7068 88 92 sp FC ltac:(lia) ltac:(lia) ltac:(sd) eq_refl eq_refl).
  rewrite <- (mb_field _bits 4 88 sp FC ltac:(sd) eq_refl eq_refl).
  rewrite (mb_split Ews 7068 4 7064 92 96 sp FC ltac:(lia) ltac:(lia) ltac:(sd) eq_refl eq_refl).
  rewrite <- (mb_field _length 4 92 sp FC ltac:(sd) eq_refl eq_refl).
  rewrite (mb_split Ews 7064 4 7060 96 100 sp FC ltac:(lia) ltac:(lia) ltac:(sd) eq_refl eq_refl).
  rewrite <- (mb_field _offset 4 96 sp FC ltac:(sd) eq_refl eq_refl).
  rewrite (mb_split Ews 7060 4 7056 100 104 sp FC ltac:(lia) ltac:(lia) ltac:(sd) eq_refl eq_refl).
  rewrite <- (mb_field _extra 4 100 sp FC ltac:(sd) eq_refl eq_refl).
  rewrite (mb_split Ews 7056 8 7048 104 112 sp FC ltac:(lia) ltac:(lia) ltac:(sd) eq_refl eq_refl).
  rewrite <- (mb_field _lencode 8 104 sp FC ltac:(sd) eq_refl eq_refl).
  rewrite (mb_split Ews 7048 8 7040 112 120 sp FC ltac:(lia) ltac:(lia) ltac:(sd) eq_refl eq_refl).
  rewrite <- (mb_field _distcode 8 112 sp FC ltac:(sd) eq_refl eq_refl).
  rewrite (mb_split Ews 7040 4 7036 120 124 sp FC ltac:(lia) ltac:(lia) ltac:(sd) eq_refl eq_refl).
  rewrite <- (mb_field _lenbits 4 120 sp FC ltac:(sd) eq_refl eq_refl).
  rewrite (mb_split Ews 7036 4 7032 124 128 sp FC ltac:(lia) ltac:(lia) ltac:(sd) eq_refl eq_refl).
  rewrite <- (mb_field _distbits 4 124 sp FC ltac:(sd) eq_refl eq_refl).
  rewrite (mb_split Ews 7032 4 7028 128 132 sp FC ltac:(lia) ltac:(lia) ltac:(sd) eq_refl eq_refl).
  rewrite <- (mb_field _ncode 4 128 sp FC ltac:(sd) eq_refl eq_refl).
  rewrite (mb_split Ews 7028 4 7024 132 136 sp FC ltac:(lia) ltac:(lia) ltac:(sd) eq_refl eq_refl).
  rewrite <- (mb_field _nlen 4 132 sp FC ltac:(sd) eq_refl eq_refl).
  rewrite (mb_split Ews 7024 4 7020 136 140 sp FC ltac:(lia) ltac:(lia) ltac:(sd) eq_refl eq_refl).
  rewrite <- (mb_field _ndist 4 136 sp FC ltac:(sd) eq_refl eq_refl).
  rewrite (mb_split Ews 7020 4 7016 140 144 sp FC ltac:(lia) ltac:(lia) ltac:(sd) eq_refl eq_refl).
  rewrite <- (mb_field _have 4 140 sp FC ltac:(sd) eq_refl eq_refl).
  rewrite (mb_split Ews 7016 8 7008 144 152 sp FC ltac:(lia) ltac:(lia) ltac:(sd) eq_refl eq_refl).
  rewrite <- (mb_field _next 8 144 sp FC ltac:(sd) eq_refl eq_refl).
  rewrite (mb_split Ews 7008 640 6368 152 792 sp FC ltac:(lia) ltac:(lia) ltac:(sd) eq_refl eq_refl).
  rewrite <- (mb_field _lens 640 152 sp FC ltac:(sd) eq_refl eq_refl).
  rewrite (mb_split Ews 6368 576 5792 792 1368 sp FC ltac:(lia) ltac:(lia) ltac:(sd) eq_refl eq_refl).
  rewrite <- (mb_field _work 576 792 sp FC ltac:(sd) eq_refl eq_refl).
  rewrite (mb_split Ews 5792 5776 16 1368 7144 sp FC ltac:(lia) ltac:(lia) ltac:(sd) eq_refl eq_refl).
  rewrite <- (mb_field _codes 5776 1368 sp FC ltac:(sd) eq_refl eq_refl).
  rewrite (mb_split Ews 16 4 12 7144 7148 sp FC ltac:(lia) ltac:(lia) ltac:(sd) eq_refl eq_refl).
  rewrite <- (mb_field _sane 4 7144 sp FC ltac:(sd) eq_refl eq_refl).
  rewrite (mb_split Ews 12 4 8 7148 7152 sp FC ltac:(lia) ltac:(lia) ltac:(sd) eq_refl eq_refl).
  rewrite <- (mb_field _back 4 7148 sp FC ltac:(sd) eq_refl eq_refl).
  rewrite (mb_split Ews 8 4 4 7152 7156 sp FC ltac:(lia) ltac:(lia) ltac:(sd) eq_refl eq_refl).
  rewrite <- (mb_field _was 4 7152 sp FC ltac:(sd) eq_refl eq_refl).
  unfold state_fields_. apply pred_ext; cancel.
Qed.

Lemma body_inflateInit_ {Es: OracleKind}: semax_body Vprog_inflate Gp_init f_inflateInit_ inflateInit__spec.
Proof.
  start_function.
  forward_call (gv, shs, strmp, r, msgv, stv, opq, 15, ver, vsh, vc, c, ssize).
  Intros vret. destruct vret as [aok sp]. forward. Exists aok sp. entailer!.
Qed.

(* struct z_stream before inflateInit2_ (raw_strm) and while it sets it up *)
Definition strm_v (r: rawf) (msgv stv za zf opq: val) : reptype t_strm :=
  (rf_ni r, (rf_ai r, (rf_tin r, (rf_no r, (rf_ao r, (rf_tout r, (msgv, (stv, (za, (zf, (opq,
   (rf_dt r, (rf_adler r, rf_res r))))))))))))).

Lemma byte_vals_zero n: 0 <= n ->
  byte_vals (repeat (0 mod 256) (Z.to_nat n)) = zbytes n.
Proof. intros. unfold byte_vals, zbytes, Zrepeat. rewrite map_repeat. reflexivity. Qed.

(* the accepted windowBits *)
Lemma reset2_wb_range: forall w wrap wb, reset2_wb w = Some (wrap, wb) ->
  0 <= wrap <= 7 /\ (wb = 0 \/ 8 <= wb <= 15).
Proof.
  intros w wrap wb H. unfold reset2_wb in H.
  destruct (Z.ltb_spec w 0).
  - destruct (Z.ltb_spec w (-15)); [discriminate | ].
    destruct (andb (8 <=? - w) (- w <=? 15)) eqn:E; [ | discriminate].
    inv H. apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1, E2. lia.
  - destruct (Z.ltb_spec w 48).
    + destruct (orb (Z.land w 15 =? 0) (andb (8 <=? Z.land w 15) (Z.land w 15 <=? 15))) eqn:E; [ | discriminate].
      inv H. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
      assert (0 <= w / 16) by (apply Z.div_pos; lia).
      assert (w / 16 < 3) by (apply Z.div_lt_upper_bound; lia).
      split; [lia | ].
      apply orb_prop in E. destruct E as [E | E]; [left; apply Z.eqb_eq in E; lia | right].
      apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1, E2. lia.
    + destruct (orb (w =? 0) (andb (8 <=? w) (w <=? 15))) eqn:E; [ | discriminate].
      exfalso. apply orb_prop in E. destruct E as [E | E]; [apply Z.eqb_eq in E; lia | ].
      apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1, E2. lia.
Qed.

(* wbits 0 (size from the header) only with a wrapper *)
Lemma reset2_wb_wrap: forall w wrap wb, reset2_wb w = Some (wrap, wb) -> wb = 0 -> 5 <= wrap.
Proof.
  intros w wrap wb H Hz. unfold reset2_wb in H.
  destruct (Z.ltb_spec w 0).
  - destruct (w <? -15); [discriminate | ].
    destruct (andb (8 <=? - w) (- w <=? 15)) eqn:E; [ | discriminate].
    inv H. apply andb_prop in E. destruct E as [E1 _]. apply Z.leb_le in E1. lia.
  - destruct (orb _ _); [ | discriminate].
    inv H. rewrite Z.shiftr_div_pow2 by lia. assert (0 <= w / 2 ^ 4) by (apply Z.div_pos; lia). lia.
Qed.

Lemma init_live_ok: forall sp w wrap wb, isptr sp -> reset2_wb w = Some (wrap, wb) ->
  live_ok (init_live sp w).
Proof.
  intros sp w wrap wb Hsp Hw. destruct (reset2_wb_range w wrap wb Hw) as [Hwr Hwb].
  destruct (reset2_wrap_ok w wrap wb Hw) as (RW1 & RW2 & RW3 & RW4).
  assert (RW5: Z.land (reset2_wrap wrap wb) 3 = Z.land wrap 3).
  { transitivity (Z.land (Z.land (reset2_wrap wrap wb) 7) 3); [rewrite <- Z.land_assoc; reflexivity | rewrite RW3; reflexivity]. }
  unfold live_ok, init_live. rewrite Hw. simpl l_sp; simpl l_s; simpl l_h; simpl l_hsh.
  rewrite (init_s_eq wrap wb Hwr).
  set (rw := reset2_wrap wrap wb) in *. clearbody rw.
  assert (Hl: Forall (fun x => 0 <= x <= 65535) (Zrepeat 0 320)).
  { apply Forall_forall. intros x Hx. apply repeat_spec in Hx. lia. }
  assert (Hc: Forall entry_ok (Zrepeat (mkE 0 0 0) ENOUGH_CODES)).
  { apply Forall_forall. intros x Hx. apply repeat_spec in Hx. subst. cbv; repeat split; congruence. }
  unfold reset_s, reset_keep_s, zero_s. simpl.
  split; [exact Hsp | ]. split; [ | split; [ | split; [ | split; [ | split]]]].
  - constructor; simpl; unfold urange, srange, lrange, tref_ok, ENOUGH_CODES, HEAD, SYNC in *; try rep_lia.
    all: try (split; [reflexivity | auto]).
    all: try (left; reflexivity).
    all: try (destruct Hwb; lia).
    all: try (intros; lia).
    all: try exact RW1.
  - constructor; simpl; intros; try discriminate; unfold decode_mode in *; unfold HEAD, LENLENS, CODELENS,
      LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT in *; lia.
  - constructor; simpl; unfold urange, srange, lrange; try rep_lia; try (split; [reflexivity | constructor]).
  - constructor; simpl; intros; try discriminate; unfold decode_mode in *; unfold HEAD, LENLENS, CODELENS,
      LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT in *; try lia; auto.
  - apply writable_Ews.
  - simpl. pose proof (reset2_wb_wrap w wrap wb Hw) as Hwr0.
    split; [intros H0; specialize (Hwr0 H0); split; [ | reflexivity]; rewrite RW5;
      assert (Hw3: wrap = 5 \/ wrap = 6 \/ wrap = 7) by lia; destruct Hw3 as [-> | [-> | ->]]; discriminate | ].
    split; [discriminate | ].
    intros; split; [reflexivity | left; reflexivity].
Qed.

(* the fields of the state, back to the struct (inflateInit2_'s ZFREE after a failed inflateReset2) *)
Lemma state_rep_v_free: forall gv sp strmp headp winp s vl vd vn vs, field_compatible t_state [] sp ->
  state_rep_v gv sp strmp headp winp s vl vd vn vs * state_pad sp |-- data_at_ Ews t_state sp.
Proof.
  intros. rewrite state_fields_eq by auto. unfold state_rep_v, state_fields_, state_pad.
  sep_apply (field_at_field_at_ Ews t_state (DOT _strm)).
  sep_apply (field_at_field_at_ Ews t_state (DOT _mode)).
  sep_apply (field_at_field_at_ Ews t_state (DOT _last)).
  sep_apply (field_at_field_at_ Ews t_state (DOT _wrap)).
  sep_apply (field_at_field_at_ Ews t_state (DOT _havedict)).
  sep_apply (field_at_field_at_ Ews t_state (DOT _flags)).
  sep_apply (field_at_field_at_ Ews t_state (DOT _dmax)).
  sep_apply (field_at_field_at_ Ews t_state (DOT _check)).
  sep_apply (field_at_field_at_ Ews t_state (DOT _total)).
  sep_apply (field_at_field_at_ Ews t_state (DOT _head)).
  sep_apply (field_at_field_at_ Ews t_state (DOT _wbits)).
  sep_apply (field_at_field_at_ Ews t_state (DOT _wsize)).
  sep_apply (field_at_field_at_ Ews t_state (DOT _whave)).
  sep_apply (field_at_field_at_ Ews t_state (DOT _wnext)).
  sep_apply (field_at_field_at_ Ews t_state (DOT _window)).
  sep_apply (field_at_field_at_ Ews t_state (DOT _hold)).
  sep_apply (field_at_field_at_ Ews t_state (DOT _bits)).
  sep_apply (field_at_field_at_ Ews t_state (DOT _length)).
  sep_apply (field_at_field_at_ Ews t_state (DOT _offset)).
  sep_apply (field_at_field_at_ Ews t_state (DOT _extra)).
  sep_apply (field_at_field_at_ Ews t_state (DOT _lencode)).
  sep_apply (field_at_field_at_ Ews t_state (DOT _distcode)).
  sep_apply (field_at_field_at_ Ews t_state (DOT _lenbits)).
  sep_apply (field_at_field_at_ Ews t_state (DOT _distbits)).
  sep_apply (field_at_field_at_ Ews t_state (DOT _ncode)).
  sep_apply (field_at_field_at_ Ews t_state (DOT _nlen)).
  sep_apply (field_at_field_at_ Ews t_state (DOT _ndist)).
  sep_apply (field_at_field_at_ Ews t_state (DOT _have)).
  sep_apply (field_at_field_at_ Ews t_state (DOT _next)).
  sep_apply (field_at_field_at_ Ews t_state (DOT _lens)).
  sep_apply (field_at_field_at_ Ews t_state (DOT _codes)).
  sep_apply (field_at_field_at_ Ews t_state (DOT _sane)).
  sep_apply (field_at_field_at_ Ews t_state (DOT _back)).
  sep_apply (field_at_field_at_ Ews t_state (DOT _was)).
  cancel.
Qed.

Lemma body_inflateInit2_ {Es: OracleKind}: semax_body Vprog_inflate Gp_init2 f_inflateInit2_ inflateInit2__spec.
Proof.
  start_function.
  forward_if (temp _t'1 (Vint (if c =? 49 then Int.zero else Int.one))).
  { destruct ver; try contradiction. inv H6. }
  { forward.
    { entailer!. setoid_rewrite H1. simpl. rewrite Int.signed_repr by rep_lia. split; cbn; lia. }
    unfold version_lit. simpl map. forward. forward. entailer!.
    setoid_rewrite H1. change (Znth 0 _) with (Vint (Int.repr 49)). simpl.
    destruct (Z.eqb_spec c 49).
    - subst. reflexivity.
    - rewrite (Int.eq_false (Int.repr c) (Int.repr 49)); [reflexivity | ].
      intro E; apply (f_equal Int.signed) in E; rewrite !Int.signed_repr in E by rep_lia; lia. }
  forward_if (temp _t'2 (Vint (if andb (c =? 49) (ssize =? sizeof_z_stream) then Int.zero else Int.one))).
  { forward. entailer!. destruct (c =? 49); simpl in *; [contradiction | reflexivity]. }
  { forward. entailer!. destruct (c =? 49); simpl in *; [ | discriminate].
    change (Int64.unsigned (Int64.repr (sizeof (Tstruct _z_stream_s noattr)))) with 112.
    unfold sizeof_z_stream. destruct (Z.eqb_spec ssize 112).
    - subst. reflexivity.
    - rewrite (Int.eq_false (Int.repr ssize) (Int.repr 112)); [reflexivity | ].
      intro E; apply (f_equal Int.signed) in E; rewrite !Int.signed_repr in E by rep_lia; lia. }
  forward_if.
  { assert (Hv: orb (negb (c =? 49)) (negb (ssize =? sizeof_z_stream)) = true).
    { destruct (c =? 49), (ssize =? sizeof_z_stream); simpl in *; auto; contradiction. }
    forward. Exists false nullval. unfold init_ret, init_mem. rewrite Hv, Z.eqb_refl. entailer!. }
  assert (Hcs: c = 49 /\ ssize = sizeof_z_stream).
  { destruct (Z.eqb_spec c 49), (Z.eqb_spec ssize sizeof_z_stream); simpl in H6; auto;
      contradiction Int.one_not_zero. }
  destruct Hcs as [-> ->]. clear H6.
  destruct (eq_dec strmp nullval) as [Hn | Hn].
  { subst strmp. forward_if.
    - forward. Exists false nullval. unfold init_ret, init_mem. simpl. entailer!.
    - contradiction. }
  pose proof (H5 Hn) as Wshs.
  unfold raw_strm. change (data_at shs t_strm _ strmp) with (data_at shs t_strm (strm_v r msgv stv nullval nullval opq) strmp).
  forward_if.
  { contradiction. }
  unfold strm_v. forward. forward.
  change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with nullval.
  forward_if (PROP () LOCAL (gvars gv; temp _strm strmp; temp _windowBits (Vint (Int.repr w)))
    SEP (data_at shs t_strm (strm_v r nullval stv (gv _zcalloc) nullval nullval) strmp;
         data_at vsh (tarray tschar (Zlength vc)) vc ver; version_lit gv; mem_mgr gv; zfuncs gv)).
  { forward. forward. entailer!. }
  { exfalso. auto. }
  unfold strm_v. forward.
  forward_if (PROP () LOCAL (gvars gv; temp _strm strmp; temp _windowBits (Vint (Int.repr w)))
    SEP (data_at shs t_strm (strm_v r nullval stv (gv _zcalloc) (gv _zcfree) nullval) strmp;
         data_at vsh (tarray tschar (Zlength vc)) vc ver; version_lit gv; mem_mgr gv; zfuncs gv)).
  { forward. entailer!. }
  { exfalso. auto. }
  unfold strm_v. forward. forward.
  unfold zfuncs. flatten_sepcon_in_SEP.
  forward_call (t_state, gv, nullval, 1, 7160).
  Intros sp. forward.
  destruct (eq_dec sp nullval) as [Hsp | Hsp].
  { subst sp. forward_if.
    - forward. Exists false nullval. unfold init_ret, init_mem. simpl.
      rewrite if_false by auto. simpl. unfold raw_strm, zfuncs. entailer!.
      rewrite if_false by auto. cancel. apply derives_refl.
    - contradiction. }
  Intros. forward_if.
  { contradiction. }
  assert_PROP (field_compatible t_state [] sp) as FCs by entailer!.
  rewrite data_at__memory_block. Intros. change (sizeof t_state) with 7160.
  rewrite memory_block_data_at__tarray_tuchar_eq by rep_lia.
  forward_call (Ews, sp, 7160, 0).
  rewrite byte_vals_zero by lia. sep_apply (zero_state sp FCs). unfold zstate. Intros.
  forward. forward. forward. forward.
  change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with nullval.
  assert (Psp: isptr sp) by (destruct FCs; auto).
  sep_apply (data_at_memory_block Ews (tarray tuchar 4) (zbytes 4) (offset_val 7156 sp)).
  change (sizeof (tarray tuchar 4)) with 4.
  set (L0 := Live sp nullval zero_s (HS 0 0 0 0 false 0 0 [] false 0 [] false 0 [] 0 0) nullval Ews nullval nullval nullval).
  set (z0 := ZF nullval 0 0 nullval 0 0 None 0 0 nullval).
  set (R0 := RRaw L0 r nullval nullval nullval (Vint (Int.repr 0))).
  forward_call (gv, shs, strmp, z0, R0, w).
  { unfold rstream_opt. rewrite if_false by auto. unfold R0, rstream, raw_strm, state_rep_v, win_rep, state_pad, zfuncs.
    cbn [l_sp l_s l_winp l_headp zero_s i_mode i_last i_wrap i_havedict i_flags i_dmax i_check i_total i_head i_wbits
         i_wsize i_whave i_wnext i_win i_hold i_bits i_length i_offset i_extra i_lenbits i_distbits i_ncode i_nlen
         i_ndist i_have i_lens i_codes i_back i_was L0].
    rewrite prop_true_andp.
    2: { split; auto. split; auto. unfold HEAD, SYNC. lia. }
    cancel. }
  { unfold reset_pre, rs_live. rewrite if_false by auto. unfold R0, reset2_f.
    destruct (reset2_wb w) as [[wrap wb] | ] eqn:Hw; [ | intros Hc; unfold fst3 in Hc; simpl in Hc; discriminate].
    intros _. pose proof (init_live_ok sp w wrap wb Psp Hw) as HL. unfold init_live in HL. rewrite Hw in HL. exact HL. }
  assert (Er: rs_live strmp R0 = Some L0) by (unfold rs_live; rewrite if_false by auto; reflexivity).
  destruct (reset2_wb w) as [[wrap wb] | ] eqn:Hw.
  - (* accepted windowBits: the live stream *)
    assert (E1: reset_ret strmp R0 (reset2_f w) z0 = Z_OK)
      by (unfold reset_ret, reset2_f; rewrite Er, Hw; reflexivity).
    assert (E2: reset_post gv shs strmp z0 R0 (reset2_f w) =
                istream_raw gv shs strmp (raw_after_init r (l_s (init_live sp w))) (init_live sp w))
      by (unfold reset_post, reset2_f, init_live; rewrite Er, Hw; reflexivity).
    rewrite E1, E2. clear E1 E2.
    forward_if (PROP () LOCAL (temp _ret (Vint (Int.repr Z_OK)); gvars gv; temp _strm strmp)
      SEP (istream_raw gv shs strmp (raw_after_init r (l_s (init_live sp w))) (init_live sp w); mem_mgr gv; zfuncs gv;
           data_at vsh (tarray tschar (Zlength vc)) vc ver; version_lit gv)).
    { exfalso; congruence. }
    { forward. entailer!. }
    assert (Ei: init_ret strmp 49 sizeof_z_stream w true = Z_OK)
      by (unfold init_ret, wbits_ok; rewrite if_false by auto; rewrite Hw; reflexivity).
    forward. Exists true sp. rewrite Ei. unfold init_mem. rewrite if_false by auto. simpl (_ =? _).
    entailer!.
  - (* rejected windowBits: ZFREE, strm->state = Z_NULL *)
    assert (E1: reset_ret strmp R0 (reset2_f w) z0 = Z_STREAM_ERROR)
      by (unfold reset_ret, reset2_f; rewrite Er, Hw; reflexivity).
    assert (E2: reset_post gv shs strmp z0 R0 (reset2_f w) = rstream_opt gv shs strmp z0 R0)
      by (unfold reset_post, reset2_f; rewrite Er, Hw; reflexivity).
    rewrite E1, E2. clear E1 E2.
    forward_if (PROP () LOCAL (temp _ret (Vint (Int.repr Z_STREAM_ERROR)); gvars gv; temp _strm strmp)
      SEP (raw_strm gv shs strmp r nullval nullval (gv _zcalloc) (gv _zcfree) nullval; mem_mgr gv; zfuncs gv;
           data_at vsh (tarray tschar (Zlength vc)) vc ver; version_lit gv)).
    { unfold rstream_opt. rewrite if_false by auto. unfold R0, rstream, raw_strm.
      change (win_rep (l_winp L0) (l_s L0)) with emp.
      cbn [l_sp l_s l_winp l_headp L0].
      Intros. forward. forward.
      sep_apply (state_rep_v_free gv sp strmp nullval nullval zero_s nullval nullval nullval (Vint (Int.repr 0)) FCs).
      unfold zfuncs. flatten_sepcon_in_SEP.
      forward_call (t_state, sp, gv, nullval).
      { rewrite if_false by auto. cancel. }
      forward. unfold zfuncs. entailer!. }
    { exfalso; congruence. }
    assert (Ei: init_ret strmp 49 sizeof_z_stream w true = Z_STREAM_ERROR)
      by (unfold init_ret, wbits_ok; rewrite if_false by auto; rewrite Hw; reflexivity).
    forward. Exists true sp. rewrite Ei. unfold init_mem. rewrite if_false by auto. simpl (_ =? _).
    entailer!.
Qed.

Lemma api5_init : api_init_stmt.
Proof.
  intros Espec. split; [apply body_inflateInit2_ | apply body_inflateInit_].
Qed.
