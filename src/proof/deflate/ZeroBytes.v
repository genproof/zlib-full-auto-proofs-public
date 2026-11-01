(** * Zeroed memory as typed zero values (for deflateInit2_'s zmemzero). *)
Require Import VST.floyd.proofauto.
Require VST.veric.mapsto_memory_block VST.veric.res_predicates.
Require Import Zlib.proof.zutil.Libc.
Local Open Scope logic.

Local Lemma zb_byte_zero {cs : compspecs} sh b ofs : readable_share sh ->
  data_at sh tuchar (Vint Int.zero) (Vptr b (Ptrofs.repr ofs)) |--
  res_predicates.address_mapsto Mint8unsigned (Vint Int.zero) sh (b, Ptrofs.unsigned (Ptrofs.repr ofs)).
Proof.
  intros. unfold data_at, field_at, at_offset. simpl. rewrite data_at_rec_eq. simpl. unfold mapsto. simpl.
  rewrite if_true by auto. apply derives_extract_prop; intros _. apply orp_left.
  - apply derives_extract_prop; intros _. rewrite Ptrofs.add_zero. apply derives_refl.
  - apply derives_extract_prop; intros X. discriminate.
Qed.

Local Lemma zb_amz {cs : compspecs} sh b k ofs : readable_share sh -> 0 <= ofs ->
  ofs + Z.of_nat k < Ptrofs.modulus ->
  data_at sh (tarray tuchar (Z.of_nat k)) (Zrepeat (Vint Int.zero) (Z.of_nat k)) (Vptr b (Ptrofs.repr ofs)) |--
  mapsto_memory_block.address_mapsto_zeros sh k (b, ofs).
Proof.
  revert sh b ofs. induction k as [|k IH]; intros sh b ofs Hsh Hofs Hlt.
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
    { rewrite <- (Ptrofs.unsigned_repr ofs) at 2 by rep_lia. apply zb_byte_zero; auto. }
    rewrite field_address0_offset by (apply field_compatible_field_compatible0 in FC; auto with field_compatible).
    simpl. rewrite ptrofs_add_repr.
    replace (Z.succ ofs) with (ofs + 1) by lia. replace (Z.succ (Z.of_nat k) - 1) with (Z.of_nat k) by lia.
    apply IH; auto; lia.
Qed.

Local Lemma zb_byte_vals n : 0 <= n -> byte_vals (repeat 0 (Z.to_nat n)) = Zrepeat (Vint Int.zero) n.
Proof. intros. unfold byte_vals, Zrepeat. rewrite map_repeat. reflexivity. Qed.

(** A byte array of zeros is [mapsto_zeros]. *)
Lemma data_at_zero_bytes_mapsto_zeros {cs : compspecs} (sh : share) (n : Z) (p : val) :
  readable_share sh -> 0 <= n ->
  data_at sh (tarray tuchar n) (byte_vals (repeat 0 (Z.to_nat n))) p |-- mapsto_zeros n sh p.
Proof.
  intros Hsh Hn. rewrite zb_byte_vals by lia.
  assert_PROP (field_compatible (tarray tuchar n) [] p) as FC by entailer!.
  destruct p; try (destruct FC; contradiction).
  pose proof FC as FC'. destruct FC' as (_ & _ & SZ & _). simpl in SZ. rewrite Z.max_r in SZ by lia.
  pose proof (Ptrofs.unsigned_range i).
  rewrite <- (Ptrofs.repr_unsigned i).
  assert (X := zb_amz sh b (Z.to_nat n) (Ptrofs.unsigned i) Hsh ltac:(lia) ltac:(rewrite Z2Nat.id; lia)).
  rewrite Z2Nat.id in X by lia. eapply derives_trans; [exact X | ].
  unfold mapsto_zeros. rewrite Ptrofs.unsigned_repr by rep_lia.
  apply andp_right; [apply prop_right; split; [lia | rep_lia] | apply derives_refl].
Qed.

(** memset's result on the bytes of an object of type [t] gives the typed zero value. *)
Lemma data_at_zero_bytes {cs : compspecs} (sh : share) (t : type) (p : val) :
  readable_share sh -> complete_legal_cosu_type t = true ->
  fully_nonvolatile (rank_type cenv_cs t) t = true -> field_compatible t nil p ->
  data_at sh (tarray tuchar (sizeof t)) (byte_vals (repeat 0 (Z.to_nat (sizeof t)))) p
  |-- data_at sh t (zero_val t) p.
Proof.
  intros Hsh HC HV FC.
  assert (Hpos : 0 <= sizeof t) by (pose proof (sizeof_pos t); lia).
  sep_apply (data_at_zero_bytes_mapsto_zeros sh (sizeof t) p Hsh Hpos).
  destruct p; try (destruct FC; contradiction).
  pose proof FC as FC'. destruct FC' as (_ & _ & SZ & AL & _). simpl in SZ, AL.
  pose proof (Ptrofs.unsigned_range i).
  unfold data_at, field_at. rewrite prop_true_andp by auto. unfold at_offset.
  replace (offset_val (nested_field_offset t []) (Vptr b i)) with (Vptr b (Ptrofs.repr (Ptrofs.unsigned i)))
    by (simpl; rewrite Ptrofs.add_zero, Ptrofs.repr_unsigned; auto).
  replace (Vptr b i) with (Vptr b (Ptrofs.repr (Ptrofs.unsigned i))) by (rewrite Ptrofs.repr_unsigned; auto).
  apply (mapsto_zeros_data_at_rec_zero_val sh Hsh t b (Ptrofs.unsigned i) HC ltac:(lia) AL HV).
Qed.

(** The allocated object of type [t] as bytes, for memset. *)
Lemma data_at__bytes {cs : compspecs} (sh : share) (t : type) (p : val) :
  field_compatible t nil p ->
  data_at_ sh t p |-- data_at_ sh (tarray tuchar (sizeof t)) p.
Proof.
  intros FC.
  pose proof (sizeof_pos t).
  rewrite data_at__memory_block. Intros.
  rewrite <- memory_block_data_at__tarray_tuchar_eq; [apply derives_refl |].
  destruct p; try (destruct FC; contradiction). destruct FC as (_ & _ & SZ & _). simpl in SZ.
  pose proof (Ptrofs.unsigned_range i). lia.
Qed.
