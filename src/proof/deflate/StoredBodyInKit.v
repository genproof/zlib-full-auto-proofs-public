(** * Helpers for sb_in_frag (StoredBodyIn.v): the model c_in unfolded, with the ranges of the result. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.proof.deflate.StoredKit.
Require Import Zlib.proof.deflate.StoredFacts.
Require Import Zlib.proof.deflate.StoredBodyKit.
Require Zlib.proof.crc32.Combine.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

(** The stream after [read_buf] and the three output-field updates. *)
Definition in_res (z1 : strm) (out : list Z) (aout tout : Z) : strm :=
  set_z_total_out (set_z_avail_out (set_z_out z1 out) aout) tout.

Lemma c_in_some s z len z' : strm_ranges z -> len <> 0 -> c_in s z len = Some z' ->
  exists z1 data, c_read_buf s z len = Some (z1, data) /\ Zlength data = len /\ len <= z_avail_out z /\
   z_out z1 = z_out z /\ z_avail_out z1 = z_avail_out z /\ z_total_out z1 = z_total_out z /\
   z_msg z1 = z_msg z /\
   z' = in_res z1 (z_out z ++ data) (z_avail_out z - len) (u64 (z_total_out z + len)) /\
   strm_ranges z'.
Proof.
  intros Hr Hl H. unfold c_in in H. destruct (len =? 0) eqn:E0; [apply Z.eqb_eq in E0; contradiction|].
  destruct (c_read_buf s z len) as [[z1 data]|] eqn:Er; [|discriminate]. cbn [bind] in H.
  destruct (Zlength data =? len) eqn:El; [|discriminate]. cbn [bind guard] in H. apply Z.eqb_eq in El.
  destruct (out_put z1 data) as [z2|] eqn:Eo; [|discriminate]. cbn [bind] in H. injection H as <-.
  pose proof Er as Er0.
  destruct z as [zi zn za zt zo zao zto zad zm]. unfold strm_ranges in Hr;
    cbn [z_in z_next_in z_avail_in z_total_in z_out z_avail_out z_total_out z_adler z_msg] in Hr.
  unfold c_read_buf in Er; cbn [z_in z_next_in z_avail_in z_total_in z_out z_avail_out z_total_out z_adler z_msg] in Er.
  assert (Hn : (if za >? len then len else za) = len).
  { destruct (za >? len); auto. destruct (za =? 0) eqn:Ez.
    - injection Er as _ <-. rewrite Zlength_nil in El. lia.
    - destruct (rds _ _ _) eqn:Erd; [|discriminate]. cbn [bind] in Er. injection Er as _ <-.
      unfold rds in Erd. cbn [z_in z_next_in z_avail_in set_z_avail_in] in Erd;
      match type of Erd with (if ?c then _ else _) = _ => destruct c eqn:Ec end; [|discriminate].
      injection Erd as <-.
      rewrite !andb_true_iff, !Z.leb_le in Ec.
      rewrite Zlength_sublist in El by lia. lia. }
  rewrite Hn, E0 in Er.
  destruct (rds _ _ _) as [l|] eqn:Erd; [|discriminate]. cbn [bind] in Er.
  unfold rds in Erd. cbn [z_in z_next_in z_avail_in set_z_avail_in] in Erd;
  match type of Erd with (if ?c then _ else _) = _ => destruct c eqn:Ec end; [|discriminate].
  injection Erd as <-.
  rewrite !andb_true_iff, !Z.leb_le in Ec.
  assert (Hza : len <= za) by (destruct (za >? len) eqn:X; [apply Z.gtb_lt in X|]; lia).
  assert (Hb : Forall (fun b => 0 <= b < 256) (sublist zn (zn + len) zi)) by (apply Forall_sublist; tauto).
  set (d := sublist zn (zn + len) zi) in *.
  assert (Hbb : Zlib.proof.adler32.Bytes.is_bytes d) by (eapply Forall_impl; [|exact Hb]; cbn; intros; rep_lia).
  assert (Hz1 : exists ad, u64_ok ad /\ z1 = mkST zi (zn + len) (za - len) (u64 (zt + len)) zo zao zto ad zm /\ data = d).
  { destruct (d_wrap s =? 1); [|destruct (d_wrap s =? 2)]; injection Er as <- <-.
    - exists (Zlib.proof.adler32.Model.adler32_z_val zad d). split; [|split; reflexivity].
      pose proof (Zlib.proof.adler32.Model.adler32_z_val_range zad d Hbb). unfold u64_ok; rep_lia.
    - exists (Zlib.proof.crc32.Model.ref_crc32 zad d). split; [|split; reflexivity].
      pose proof (Zlib.proof.crc32.Combine.ref_crc32_range zad d Hbb).
      unfold Zlib.proof.crc32.GF2.is32 in *. unfold u64_ok; rep_lia.
    - exists zad. split; [|split; reflexivity]. tauto. }
  clear Er. destruct Hz1 as (ad & Had & -> & ->).
  unfold out_put in Eo. cbn [z_avail_out z_out] in Eo.
  destruct (Zlength d <=? zao) eqn:Elo; [|discriminate]. apply Z.leb_le in Elo. injection Eo as <-.
  assert (Hzao : zao <= Int.max_unsigned) by (destruct Hr as (_ & _ & _ & _ & _ & _ & X & _); exact (proj2 X)).
  exists (mkST zi (zn + len) (za - len) (u64 (zt + len)) zo zao zto ad zm), d.
  split; [first [exact Er0 | reflexivity]|].
  cbn [z_in z_next_in z_avail_in z_total_in z_out z_avail_out z_total_out z_adler z_msg].
  split; [assumption|]. split; [lia|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  match goal with |- context [u32 ?x] => replace (u32 x) with (zao - len)
    by (cbn [z_avail_out set_z_out]; unfold u32; rewrite Z.mod_small; [reflexivity|]; rep_lia) end.
  split; [reflexivity|].
  destruct Hr as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12).
  unfold u32_ok, u64_ok in *. unfold u64.
  pose proof (Z.mod_pos_bound (zt + len) 18446744073709551616 ltac:(lia)).
  pose proof (Z.mod_pos_bound (zto + len) 18446744073709551616 ltac:(lia)).
  change (strm_ranges (mkST zi (zn + len) (za - len) ((zt + len) mod 18446744073709551616) (zo ++ d) (zao - len)
            ((zto + len) mod 18446744073709551616) ad zm)).
  unfold strm_ranges, u32_ok, u64_ok; cbn [z_in z_next_in z_avail_in z_total_in z_out z_avail_out z_total_out z_adler z_msg].
  rewrite Zlength_app.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [rep_lia|]. split; [rep_lia|].
  split; [rep_lia|]. split; [rep_lia|]. split; [rep_lia|]. split; [exact Had|]. split; [exact H11|].
  apply Forall_app; split; assumption.
Qed.

Lemma rest_after_in z z' rest data :
  z_out z' = z_out z ++ data -> Zlength data <= Zlength rest ->
  rest_after z z' rest = sublist (Zlength data) (Zlength rest) rest.
Proof.
  intros E Hl. unfold rest_after. rewrite E, Zlength_app. f_equal. lia.
Qed.

Lemma nfo_tuchar m i : @nested_field_offset DCS.CS (Tarray tuchar m noattr) (SUB i) = i.
Proof. unfold nested_field_offset; simpl. lia. Qed.

(** The output space split around the slice [Zlength (z_out z), + len) that read_buf writes. *)
Lemma out_split z pout (rest : list val) len :
  0 <= len <= z_avail_out z ->
  out_space z pout rest |--
  !! (Zlength rest = z_avail_out z /\
      field_compatible (tarray tuchar (Zlength (z_out z) + Zlength rest)) [] pout) &&
  (@data_at DCS.CS Ews (tarray tuchar (Zlength (z_out z))) (map vi (z_out z)) pout *
   @data_at DCS.CS Ews (tarray tuchar len) (sublist 0 len rest) (offset_val (Zlength (z_out z)) pout) *
   @data_at DCS.CS Ews (tarray tuchar (Zlength rest - len)) (sublist len (Zlength rest) rest)
     (offset_val (Zlength (z_out z) + len) pout)).
Proof.
  intros Hl. unfold out_space. Intros. rewrite <- H in Hl |- *.
  set (n := Zlength (z_out z)).
  assert (Hn : 0 <= n) by apply Zlength_nonneg.
  assert_PROP (field_compatible (tarray tuchar (n + Zlength rest)) [] pout) by entailer!.
  rewrite (split3_data_at_Tarray_tuchar Ews (n + Zlength rest) n (n + len)) by
    (try rewrite Zlength_app, Zlength_map; lia).
  rewrite !field_address0_offset by auto with field_compatible.
  rewrite !nfo_tuchar.
  rewrite sublist_app1 by (rewrite ?Zlength_map; lia).
  rewrite sublist_same by (rewrite ?Zlength_map; lia).
  rewrite !sublist_app2 by (rewrite ?Zlength_map; lia).
  rewrite Zlength_map. fold n.
  replace (n - n) with 0 by lia. replace (n + len - n) with len by lia.
  replace (n + Zlength rest - n) with (Zlength rest) by lia.
  replace (n + Zlength rest - (n + len)) with (Zlength rest - len) by lia.
  replace (n + len - n) with len by lia.
  entailer!.
Qed.

Lemma out_join z z' pout (rest : list val) len (data : list Z) :
  field_compatible (tarray tuchar (Zlength (z_out z) + Zlength rest)) [] pout ->
  Zlength rest = z_avail_out z -> Zlength data = len -> 0 <= len <= Zlength rest ->
  z_out z' = z_out z ++ data -> z_avail_out z' = z_avail_out z - len ->
  (@data_at DCS.CS Ews (tarray tuchar (Zlength (z_out z))) (map vi (z_out z)) pout *
   @data_at DCS.CS Ews (tarray tuchar len) (map vi data) (offset_val (Zlength (z_out z)) pout) *
   @data_at DCS.CS Ews (tarray tuchar (Zlength rest - len)) (sublist len (Zlength rest) rest)
     (offset_val (Zlength (z_out z) + len) pout))
  |-- out_space z' pout (sublist len (Zlength rest) rest).
Proof.
  intros Hf Hr Hd Hl Eo Ea. unfold out_space.
  rewrite Zlength_sublist by lia. apply andp_right; [apply prop_right; lia|].
  rewrite Eo, Ea, Zlength_app, map_app, <- app_assoc.
  set (n := Zlength (z_out z)).
  assert (Hn : 0 <= n) by apply Zlength_nonneg.
  replace (n + Zlength data + (z_avail_out z - len)) with (n + Zlength rest) by lia.
  rewrite (split3_data_at_Tarray_tuchar Ews (n + Zlength rest) n (n + len)) by
    (try rewrite !Zlength_app, !Zlength_map, Zlength_sublist; lia).
  rewrite !field_address0_offset by auto with field_compatible.
  rewrite !nfo_tuchar.
  replace (n + len - n) with len by lia.
  replace (n + Zlength rest - (n + len)) with (Zlength rest - len) by lia.
  rewrite (sublist_app1 _ 0 n (map vi (z_out z))) by (rewrite ?Zlength_map; unfold n; lia).
  rewrite (sublist_same 0 n (map vi (z_out z))) by (rewrite ?Zlength_map; unfold n; lia).
  rewrite (sublist_app2 n (n + len) (map vi (z_out z))) by (rewrite ?Zlength_map; unfold n; lia).
  rewrite (sublist_app2 (n + len) (n + Zlength rest) (map vi (z_out z))) by (rewrite ?Zlength_map; unfold n; lia).
  rewrite !Zlength_map. fold n.
  replace (n + len - n) with len by lia. replace (n - n) with 0 by lia.
  replace (n + Zlength rest - n) with (Zlength rest) by lia.
  rewrite (sublist_app1 _ 0 len (map vi data)) by (rewrite ?Zlength_map; lia).
  rewrite (sublist_same 0 len (map vi data)) by (rewrite ?Zlength_map; lia).
  rewrite (sublist_app2 len (Zlength rest) (map vi data)) by (rewrite ?Zlength_map; lia).
  rewrite Zlength_map, Hd, Z.sub_diag.
  rewrite (sublist_same 0 (Zlength rest - len)) by (rewrite ?Zlength_sublist by lia; lia).
  cancel.
Qed.

Lemma strm_in_at_res z1 o a t sp strmp pin msgv gv :
  strm_in_at (in_res z1 o a t) sp strmp pin msgv gv = strm_in_at z1 sp strmp pin msgv gv.
Proof. reflexivity. Qed.

Lemma in_obj_res z1 o a t ish pin : in_obj ish (in_res z1 o a t) pin = in_obj ish z1 pin.
Proof. reflexivity. Qed.

Lemma next_out_add (pout : val) n len : isptr pout -> 0 <= len <= Int.max_unsigned ->
  force_val (sem_add_ptr_int tuchar Unsigned (offset_val n pout) (vi len)) = offset_val (n + len) pout.
Proof.
  intros Hp Hl. destruct pout; try contradiction. unfold vi. simpl. f_equal. rewrite Ptrofs.add_assoc. f_equal.
  unfold Ptrofs.of_intu, Ptrofs.of_int. rewrite Int.unsigned_repr by lia.
  rewrite ptrofs_mul_repr, Z.mul_1_l, ptrofs_add_repr. reflexivity.
Qed.

Lemma avail_out_sub a len : Vint (Int.sub (Int.repr a) (Int.repr len)) = vi (a - len).
Proof. unfold vi. rewrite sub_repr. reflexivity. Qed.

Lemma total_out_add t len : 0 <= len <= Int.max_unsigned ->
  Vlong (Int64.add (Int64.repr t) (Int64.repr (Int.unsigned (Int.repr len)))) = vl (u64 (t + len)).
Proof.
  intros Hl. rewrite Int.unsigned_repr by lia. rewrite add64_repr. unfold vl, u64. f_equal.
  change 18446744073709551616 with Int64.modulus.
  rewrite <- Int64.unsigned_repr_eq, Int64.repr_unsigned. reflexivity.
Qed.
