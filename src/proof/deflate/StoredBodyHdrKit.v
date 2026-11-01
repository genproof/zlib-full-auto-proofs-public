(** * Helpers for sb_hdr_frag (StoredBodyHdr.v): the four length-byte stores into pending_buf and the shape of
    flush_pending's result. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.proof.deflate.StoredKit.
Require Import Zlib.proof.deflate.StoredFacts.
Require Import Zlib.proof.deflate.StoredBodyKit.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

Lemma out_ok_wr buf p bb bv bu m i v :
  out_ok (mkOut buf p bb bv bu) m -> 0 <= i < Zlength buf -> 0 <= v < 256 ->
  out_ok (mkOut (upd_Znth i buf v) p bb bv bu) (upd_Znth i m true).
Proof.
  intros [[Hm Hd] [Hb [Hp [Hbb [Hbv Hbu]]]]] Hi Hv. cbn in *.
  split; [split|]; cbn.
  - rewrite !Zlength_upd_Znth. auto.
  - intros j Hj Hdj. rewrite Zlength_upd_Znth in Hj.
    destruct (Z.eq_dec j i) as [->|ne].
    + rewrite upd_Znth_same by lia. auto.
    + rewrite upd_Znth_diff in Hdj by lia. rewrite upd_Znth_diff by lia. auto.
  - rewrite Zlength_upd_Znth. rep_lia.
Qed.

Lemma c_pb_wr_out s buf p bb bv bu m i v s' :
  c_pb_wr (set_d_out s (mkOut buf p bb bv bu, m)) i v = Some s' ->
  0 <= i < Zlength buf /\ s' = set_d_out s (mkOut (upd_Znth i buf v) p bb bv bu, upd_Znth i m true).
Proof.
  unfold c_pb_wr, mb_wr, d_pb, set_d_pb, in_range. simpl.
  destruct (andb (0 <=? i) (i <? Zlength buf)) eqn:E; [|discriminate].
  intros H; inversion H; subst; clear H.
  apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  split; [lia | reflexivity].
Qed.

Lemma mb_read_bytes b lo n l : mb_read b lo n = Some l -> mb_ok b -> Forall (fun x => 0 <= x < 256) l.
Proof.
  unfold mb_read, mb_definedb. intros H [Hm Hd].
  destruct (andb (0 <=? n) (andb (andb (0 <=? lo) (lo + n <=? Zlength (mb_val b))) _)) eqn:E; [|discriminate].
  inversion H; subst; clear H.
  apply andb_prop in E as [E1 E2]. apply andb_prop in E2 as [E2 E4].
  apply andb_prop in E2 as [E2 E3]. apply Z.leb_le in E1, E2, E3.
  rewrite forallb_forall in E4.
  apply Forall_Znth. intros i Hi. rewrite Zlength_sublist in Hi by lia.
  rewrite Znth_sublist by lia. apply Hd; [lia|].
  apply E4. apply in_map_iff. exists (Z.to_nat i). split; [lia|]. apply in_seq. lia.
Qed.

Lemma u32_nonneg x : 0 <= u32 x.
Proof. unfold u32. apply Z.mod_pos_bound. lia. Qed.

Lemma fp_shape s z r : 0 <= d_po s -> 0 <= z_avail_out z ->
  c_flush_pending s z = Some r ->
  fst r = set_d_po (set_d_out s (d_out (fst r))) (d_po (fst r)) /\ 0 <= d_po (fst r).
Proof.
  intros Hpo Ha H. unfold c_flush_pending in H. inv_bind H. destruct x as [o m].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:E0 end.
  - inversion H; subst; clear H. split; [reflexivity | exact Hpo].
  - inv_bind H. inv_bind H.
    match type of H with Some (if ?c then _ else _, _) = _ => destruct c end;
      inversion H; subst; clear H; (split; [reflexivity|]);
      cbn; try match goal with |- context [if ?c then _ else _] => destruct c end;
        try lia; pose proof (u32_nonneg (d_pending (set_d_out s (o, m)))); lia.
Qed.

Lemma u64_bound x : 0 <= u64 x <= Int64.max_unsigned.
Proof. unfold u64. pose proof (Z.mod_pos_bound x 18446744073709551616 ltac:(lia)). rep_lia. Qed.

Lemma fp_strm s z r : strm_ranges z -> c_flush_pending s z = Some r ->
  mb_ok (mkMB (o_buf (tr_out (d_tr (fst r)))) (d_pbm (fst r))) ->
  strm_ranges (snd r) /\ z_in (snd r) = z_in z /\ z_msg (snd r) = z_msg z.
Proof.
  intros Hr H Hm. unfold c_flush_pending in H. inv_bind H. destruct x as [o m].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:E0 end.
  - inversion H; subst; clear H. cbn. auto.
  - inv_bind H. rename Ha0 into Hrd. inv_bind H. rename Ha0 into Hop.
    pose proof (mb_read_len _ _ _ _ Hrd) as Hl.
    assert (Hb : Forall (fun b => 0 <= b < 256) x).
    { apply (mb_read_bytes _ _ _ _ Hrd).
      match type of H with Some (if ?c then _ else _, _) = _ => destruct c end;
        inversion H; subst; exact Hm. }
    unfold out_put in Hop. destruct (Zlength x <=? z_avail_out z) eqn:El; [|discriminate].
    apply Z.leb_le in El. inversion Hop; subst; clear Hop.
    inversion H; subst; clear H. cbn [snd]. rewrite <- Hl in *.
    unfold strm_ranges in *. cbn [z_in z_next_in z_avail_in z_total_in z_out z_avail_out z_total_out z_adler z_msg
      set_z_out set_z_avail_out set_z_total_out].
    pose proof (Zlength_nonneg x). pose proof (u64_bound (z_total_out z + Zlength x)).
    unfold u32_ok, u64_ok in *. rewrite Zlength_app.
    split; [|split; reflexivity].
    destruct Hr as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?).
    repeat split; try lia; first [assumption | apply Forall_app; split; assumption].
Qed.

Lemma dstate_ranges_out_po s o x : dstate_ranges s -> 0 <= x -> dstate_ranges (set_d_po (set_d_out s o) x).
Proof. intros H Hx. destruct s. unfold dstate_ranges in *. cbn in *. intuition. Qed.

(** The groups of [s] untouched by S_hdr, the new out_at and pending_out of [s'], fold into the state
    [set_d_po (set_d_out s (d_out s')) (d_po s')]. *)
Lemma dstate_at_fold s s' p gv :
  dstate_ranges s -> 0 <= d_po s' -> Int.min_signed <= tr_data_type (fst (d_trm s)) <= Int.max_signed ->
  sb_trees_frame (d_trm s) (p_s p) gv * out_at (tr_out (d_tr s')) (d_pbm s') (p_s p) (p_pbuf p) *
  sym_at (fst (d_trm s)) (p_s p) (p_pbuf p) *
  @field_at DCS.CS Ews t_ds (DOT _strm) (p_strm p) (p_s p) *
  @field_at DCS.CS Ews t_strm (DOT _data_type) (vi (tr_data_type (fst (d_trm s)))) (p_strm p) *
  win_at s p * hash_at s p * match_at s p * cfg_at s p *
  @field_at DCS.CS Ews t_ds (DOT _status) (vi (d_status s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _pending_buf_size) (vl (d_pending_buf_size s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _pending_out) (offset_val (d_po s') (p_pbuf p)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _wrap) (vi (d_wrap s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _gzhead) (p_gzhead p) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _gzindex) (vl (d_gzindex s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _method) (vi (d_method s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _last_flush) (vi (d_last_flush s)) (p_s p)
  |-- dstate_at (set_d_po (set_d_out s (d_out s')) (d_po s')) p gv.
Proof.
  intros Hr Hpo Hdt.
  unfold dstate_at. apply andp_right; [apply prop_right; apply dstate_ranges_out_po; auto|].
  rewrite sb_trees_at_split.
  set (S := set_d_po (set_d_out s (d_out s')) (d_po s')).
  change (sb_trees_frame (d_trm S) (p_s p) gv) with (sb_trees_frame (d_trm s) (p_s p) gv).
  change (sym_at (fst (d_trm S)) (p_s p) (p_pbuf p)) with (sym_at (fst (d_trm s)) (p_s p) (p_pbuf p)).
  change (dtype_at (fst (d_trm S)) (p_s p) (p_strm p)) with (dtype_at (fst (d_trm s)) (p_s p) (p_strm p)).
  change (win_at S p) with (win_at s p). change (hash_at S p) with (hash_at s p).
  change (match_at S p) with (match_at s p). change (cfg_at S p) with (cfg_at s p).
  change (out_at (tr_out (fst (d_trm S))) (snd (d_trm S)) (p_s p) (p_pbuf p))
    with (out_at (tr_out (d_tr s')) (d_pbm s') (p_s p) (p_pbuf p)).
  unfold stat_at, dtype_at. subst S. cbn [d_status d_pending_buf_size d_po d_wrap d_gzindex d_method d_last_flush
    set_d_po set_d_out set_d_pbm set_d_tr].
  rewrite prop_true_andp by exact Hdt. cancel.
Qed.

(** c_hdr unfolded: the header block, the four stores (indices in range), flush_pending. *)
Definition hdr_buf (buf : list Z) (p len : Z) : list Z :=
  upd_Znth (u64 (p - 1))
    (upd_Znth (u64 (p - 2))
      (upd_Znth (u64 (p - 3))
        (upd_Znth (u64 (p - 4)) buf (u8 len))
        (u8 (Z.shiftr len 8)))
      (u8 (u32 (Z.lnot len))))
    (u8 (Z.shiftr (u32 (Z.lnot len)) 8)).
Definition hdr_mask (m : list bool) (p : Z) : list bool :=
  upd_Znth (u64 (p - 1)) (upd_Znth (u64 (p - 2)) (upd_Znth (u64 (p - 3)) (upd_Znth (u64 (p - 4)) m true) true) true) true.

Lemma c_hdr_inv s z len last r : c_hdr s z len last = Some r ->
  exists buf p bb bv bu m,
    c_tr_stored_block (d_out s) [] 0 last = Some (mkOut buf p bb bv bu, m) /\
    0 <= u64 (p - 4) < Zlength buf /\ 0 <= u64 (p - 3) < Zlength buf /\
    0 <= u64 (p - 2) < Zlength buf /\ 0 <= u64 (p - 1) < Zlength buf /\
    c_flush_pending (set_d_out s (mkOut (hdr_buf buf p len) p bb bv bu, hdr_mask m p)) z = Some r.
Proof.
  unfold c_hdr. intros H. inv_bind H. destruct x as [[buf p bb bv bu] m].
  inv_bind H. apply c_pb_wr_out in Ha0. destruct Ha0 as [I1 ->].
  inv_bind H. apply c_pb_wr_out in Ha0. destruct Ha0 as [I2 ->].
  inv_bind H. apply c_pb_wr_out in Ha0. destruct Ha0 as [I3 ->].
  inv_bind H. apply c_pb_wr_out in Ha0. destruct Ha0 as [I4 ->].
  rewrite !Zlength_upd_Znth in *.
  exists buf, p, bb, bv, bu, m. exact (conj Ha (conj I1 (conj I2 (conj I3 (conj I4 H))))).
Qed.

(** ** The C side of the four stores *)
Lemma u64_sub_lt x k n : 0 <= x <= Int64.max_unsigned -> 0 < k <= 4 -> n <= Int.max_unsigned ->
  u64 (x - k) < n -> k <= x /\ u64 (x - k) = x - k.
Proof.
  intros Hx Hk Hn H. unfold u64 in *. destruct (Z_lt_le_dec x k) as [Hl|Hl].
  - exfalso. assert (E : (x - k) mod 18446744073709551616 = x - k + 18446744073709551616).
    { rewrite <- (Z_mod_plus_full (x - k) 1). apply Z.mod_small. lia. }
    rewrite E in H. rep_lia.
  - split; [lia|]. apply Z.mod_small. rep_lia.
Qed.

Lemma not_repr a : Int.not (Int.repr a) = Int.repr (Z.lnot a).
Proof.
  apply Int.same_bits_eq; intros i Hi. rewrite Int.bits_not by auto.
  rewrite !Int.testbit_repr by auto. rewrite Z.lnot_spec by lia. reflexivity.
Qed.

Lemma repr_u32 a : Int.repr (u32 a) = Int.repr a.
Proof.
  unfold u32. change 4294967296 with Int.modulus. rewrite <- Int.unsigned_repr_eq. apply Int.repr_unsigned.
Qed.

Lemma u32_bound a : 0 <= u32 a <= Int.max_unsigned.
Proof. unfold u32. pose proof (Z.mod_pos_bound a 4294967296 ltac:(lia)). rep_lia. Qed.

Lemma hdr_v1 len : Int.zero_ext 8 (Int.zero_ext 8 (Int.repr len)) = Int.repr (u8 len).
Proof. rewrite zext8_idem, zext8_repr. reflexivity. Qed.

Lemma hdr_v2 len : 0 <= len <= Int.max_unsigned ->
  Int.zero_ext 8 (Int.zero_ext 8 (Int.shru (Int.repr len) (Int.repr 8))) = Int.repr (u8 (Z.shiftr len 8)).
Proof.
  intros. rewrite zext8_idem, shru_repr by rep_lia. rewrite zext8_repr. unfold u8.
  rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma hdr_v3 len : Int.zero_ext 8 (Int.zero_ext 8 (Int.not (Int.repr len))) = Int.repr (u8 (u32 (Z.lnot len))).
Proof.
  rewrite zext8_idem, not_repr, <- repr_u32, zext8_repr. reflexivity.
Qed.

Lemma hdr_v4 len :
  Int.zero_ext 8 (Int.zero_ext 8 (Int.shru (Int.not (Int.repr len)) (Int.repr 8))) =
  Int.repr (u8 (Z.shiftr (u32 (Z.lnot len)) 8)).
Proof.
  rewrite zext8_idem, not_repr, <- repr_u32. pose proof (u32_bound (Z.lnot len)).
  rewrite shru_repr by rep_lia. rewrite zext8_repr. unfold u8.
  rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma hdr_vals buf m pnd len : Zlength m = Zlength buf -> 4 <= pnd <= Zlength buf ->
  0 <= len <= Int.max_unsigned -> Zlength buf <= Int.max_unsigned ->
  upd_Znth (pnd - 1)
    (upd_Znth (pnd - 2)
      (upd_Znth (pnd - 3)
        (upd_Znth (pnd - 4) (pb_vals buf m) (Vint (Int.zero_ext 8 (Int.zero_ext 8 (Int.repr len)))))
        (Vint (Int.zero_ext 8 (Int.zero_ext 8 (Int.shru (Int.repr len) (Int.repr 8))))))
      (Vint (Int.zero_ext 8 (Int.zero_ext 8 (Int.not (Int.repr len))))))
    (Vint (Int.zero_ext 8 (Int.zero_ext 8 (Int.shru (Int.not (Int.repr len)) (Int.repr 8)))))
  = pb_vals (hdr_buf buf pnd len) (hdr_mask m pnd).
Proof.
  intros Hm Hp Hl Hb.
  rewrite hdr_v1, hdr_v2, hdr_v3, hdr_v4 by auto.
  unfold hdr_buf, hdr_mask.
  assert (U : forall k, 1 <= k <= 4 -> u64 (pnd - k) = pnd - k) by (intros; unfold u64; apply Z.mod_small; rep_lia).
  rewrite !U by lia.
  rewrite !pb_vals_upd by (rewrite ?Zlength_upd_Znth; lia). reflexivity.
Qed.

Lemma hdr_out_ok buf pnd bb bv bu m len : out_ok (mkOut buf pnd bb bv bu) m -> 4 <= pnd <= Zlength buf ->
  out_ok (mkOut (hdr_buf buf pnd len) pnd bb bv bu) (hdr_mask m pnd).
Proof.
  intros Hok Hp. unfold hdr_buf, hdr_mask.
  assert (U : forall k, 1 <= k <= 4 -> u64 (pnd - k) = pnd - k).
  { intros; unfold u64; apply Z.mod_small. destruct Hok as [_ [_ [Hq _]]]. cbn in Hq. rep_lia. }
  rewrite !U by lia.
  repeat apply out_ok_wr; rewrite ?Zlength_upd_Znth; try lia; try apply u8_range; auto.
Qed.

(** The six fields after the four stores are out_at of the model's buffer. *)
Lemma hdr_out_at buf pnd bb bv bu m len sp pbp :
  out_ok (mkOut buf pnd bb bv bu) m -> 4 <= pnd <= Zlength buf -> 0 <= len <= Int.max_unsigned ->
  @field_at DCS.CS Ews t_ds (DOT _pending) (vl pnd) sp *
  @field_at DCS.CS Ews t_ds (DOT _pending_buf) pbp sp *
  @field_at DCS.CS Ews t_ds (DOT _bi_buf) (vi bb) sp *
  @field_at DCS.CS Ews t_ds (DOT _bi_valid) (vi bv) sp *
  @field_at DCS.CS Ews t_ds (DOT _bi_used) (vi bu) sp *
  @data_at DCS.CS Ews (tarray tuchar (Zlength buf))
    (upd_Znth (pnd - 1)
      (upd_Znth (pnd - 2)
        (upd_Znth (pnd - 3)
          (upd_Znth (pnd - 4) (pb_vals buf m) (Vint (Int.zero_ext 8 (Int.zero_ext 8 (Int.repr len)))))
          (Vint (Int.zero_ext 8 (Int.zero_ext 8 (Int.shru (Int.repr len) (Int.repr 8))))))
        (Vint (Int.zero_ext 8 (Int.zero_ext 8 (Int.not (Int.repr len))))))
      (Vint (Int.zero_ext 8 (Int.zero_ext 8 (Int.shru (Int.not (Int.repr len)) (Int.repr 8)))))) pbp
  |-- out_at (mkOut (hdr_buf buf pnd len) pnd bb bv bu) (hdr_mask m pnd) sp pbp.
Proof.
  intros Hok Hp Hl. pose proof (hdr_out_ok _ _ _ _ _ _ len Hok Hp) as Hok'.
  destruct Hok as [[Hm _] [Hb _]]. cbn in Hm, Hb.
  rewrite hdr_vals by (first [assumption | rep_lia]).
  unfold out_at. apply andp_right; [apply prop_right; exact Hok'|]. cbn [o_buf o_pending o_bi_buf o_bi_valid o_bi_used].
  unfold hdr_buf. rewrite !Zlength_upd_Znth. cancel.
Qed.

Lemma out_at_okp o m sp pbp : out_at o m sp pbp = (!! out_ok o m && out_at o m sp pbp)%logic.
Proof.
  unfold out_at. apply pred_ext; [|apply andp_left2; apply derives_refl].
  apply andp_right; [apply andp_left1; apply derives_refl | apply derives_refl].
Qed.

(** The final fold into dfull. *)
Lemma hdr_final s s' z z' p pin pout ish R msgv gv :
  s' = set_d_po (set_d_out s (d_out s')) (d_po s') -> 0 <= d_po s' ->
  dstate_ranges s -> Int.min_signed <= tr_data_type (fst (d_trm s)) <= Int.max_signed ->
  strm_ranges z' -> z_in z' = z_in z -> msg_ok (z_msg z') msgv -> readable_share ish ->
  sb_trees_frame (d_trm s) (p_s p) gv * out_at (tr_out (d_tr s')) (d_pbm s') (p_s p) (p_pbuf p) *
  sym_at (fst (d_trm s)) (p_s p) (p_pbuf p) *
  @field_at DCS.CS Ews t_ds (DOT _strm) (p_strm p) (p_s p) *
  @field_at DCS.CS Ews t_strm (DOT _data_type) (vi (tr_data_type (fst (d_trm s)))) (p_strm p) *
  win_at s p * hash_at s p * match_at s p * cfg_at s p *
  @field_at DCS.CS Ews t_ds (DOT _status) (vi (d_status s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _pending_buf_size) (vl (d_pending_buf_size s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _pending_out) (offset_val (d_po s') (p_pbuf p)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _wrap) (vi (d_wrap s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _gzhead) (p_gzhead p) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _gzindex) (vl (d_gzindex s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _method) (vi (d_method s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _last_flush) (vi (d_last_flush s)) (p_s p) *
  strm_at z' (p_s p) (p_strm p) pin pout msgv gv * in_obj ish z pin * out_space z' pout R
  |-- dfull s' z' p pin pout ish R msgv gv.
Proof.
  intros E Hpo Hr Hdt Hz Hin Hmsg Hsh.
  unfold dfull. apply andp_right; [apply prop_right; auto|].
  unfold in_obj at 1. rewrite <- Hin. fold (in_obj ish z' pin).
  sep_apply (dstate_at_fold s s' p gv Hr Hpo Hdt). rewrite <- E. cancel.
Qed.
