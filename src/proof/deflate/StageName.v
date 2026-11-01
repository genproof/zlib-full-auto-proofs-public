(** * deflate(): the gzip file name (e12, [if (s->status == NAME_STATE) { ... }]) against its model (DeflateKit.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.DeflateKit.
Require Import Zlib.proof.crc32.Combine.
#[export] Existing Instance DCS.CS.
Open Scope cmodel_scope.

(** ** The pieces of the statement *)
Definition SN_inner : statement := ltac:(let x := eval cbv [S_name nth_stmt df_body f_deflate fn_body] in S_name in
  match x with Ssequence _ (Sifthenelse _ (Ssequence (Ssequence _ (Ssequence _ (Sifthenelse _ ?a _))) _) _) => exact a end).
Definition SN_body : statement := ltac:(let x := eval cbv [SN_inner] in SN_inner in
  match x with Ssequence _ (Ssequence (Sloop ?b _) _) => exact b end).
Definition SN_hc2 : statement := ltac:(let x := eval cbv [SN_inner] in SN_inner in
  match x with Ssequence _ (Ssequence _ (Ssequence ?c _)) => exact c end).
Definition SN_incr : statement := ltac:(let x := eval cbv [SN_inner] in SN_inner in
  match x with Ssequence _ (Ssequence (Sloop _ ?i) _) => exact i end).
Definition SN_part1 : statement := ltac:(let x := eval cbv [SN_body] in SN_body in
  match x with Ssequence ?a _ => exact a end).
Definition SN_part2 : statement := ltac:(let x := eval cbv [SN_body] in SN_body in
  match x with Ssequence _ ?a => exact a end).
Definition SN_hc1 : statement := ltac:(let x := eval cbv [SN_part1] in SN_part1 in
  match x with Ssequence _ (Ssequence _ (Sifthenelse _ (Ssequence ?c _) _)) => exact c end).

(** The locals of the loop *)
Definition sn_locals (p : dptrs) (flush beg : Z) (gv : globals) : list localdef :=
  [temp _beg__1 (vl beg); temp _strm (p_strm p); temp _s (p_s p); temp _flush (vi flush); gvars gv].

(** ** Opening [dfull] / [gzh_at] at the few fields HCRC_UPDATE reads *)
Definition fr_nogz (s : dstate) (z : strm) (p : dptrs) (pin : val) (ish : share) (gv : globals) : mpred :=
  (ltree_at (tr_ltree (d_tr s)) (p_s p) * dtree_at (tr_dtree (d_tr s)) (p_s p) *
   sym_at (d_tr s) (p_s p) (p_pbuf p) * dtype_at (d_tr s) (p_s p) (p_strm p) * lvl_at (d_tr s) (p_s p) *
   trees_rest (d_tr s) (p_s p) (p_strm p) gv *
   win_at s p * hash_at s p * match_at s p * cfg_at s p *
   @field_at DCS.CS Ews t_ds (DOT _status) (vi (d_status s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _pending_buf_size) (vl (d_pending_buf_size s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _wrap) (vi (d_wrap s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _gzindex) (vl (d_gzindex s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _method) (vi (d_method s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _last_flush) (vi (d_last_flush s)) (p_s p) *
   in_obj ish z pin)%logic.

Lemma dfull_gz_open s z p pin pout ish R msgv gv :
  dfull s z p pin pout ish R msgv gv |--
  (!! (strm_ranges z /\ msg_ok (z_msg z) msgv /\ dstate_ranges s /\ readable_share ish) &&
   (strm_at z (p_s p) (p_strm p) pin pout msgv gv * out_space z pout R *
    @field_at DCS.CS Ews t_ds (DOT _pending_out) (offset_val (d_po s) (p_pbuf p)) (p_s p) *
    out_at (tr_out (d_tr s)) (d_pbm s) (p_s p) (p_pbuf p) *
    @field_at DCS.CS Ews t_ds (DOT _gzhead) (p_gzhead p) (p_s p) * fr_nogz s z p pin ish gv))%logic.
Proof.
  sep_apply (dfull_flush_open s z p pin pout ish R msgv gv). unfold flush_frame, fr_nogz. Intros.
  apply andp_right; [apply prop_right; tauto|]. cancel.
Qed.

Lemma dfull_gz_close s z z0 p pin pout ish R msgv gv :
  strm_ranges z -> msg_ok (z_msg z) msgv -> dstate_ranges s -> readable_share ish -> z_in z = z_in z0 ->
  strm_at z (p_s p) (p_strm p) pin pout msgv gv * out_space z pout R *
  @field_at DCS.CS Ews t_ds (DOT _pending_out) (offset_val (d_po s) (p_pbuf p)) (p_s p) *
  out_at (tr_out (d_tr s)) (d_pbm s) (p_s p) (p_pbuf p) *
  @field_at DCS.CS Ews t_ds (DOT _gzhead) (p_gzhead p) (p_s p) * fr_nogz s z0 p pin ish gv
  |-- dfull s z p pin pout ish R msgv gv.
Proof.
  intros Hz Hm Hd Hi Ein.
  eapply derives_trans; [| apply (dfull_flush_back s z p pin pout ish R msgv gv); auto].
  unfold flush_frame, fr_nogz. unfold in_obj. rewrite Ein. entailer!.
Qed.

Definition gzh_nohc (sh : share) (h : gzh) (hp xp np cp : val) : mpred :=
  (@field_at DCS.CS sh t_gzh (DOT _text) (vi (gz_text h)) hp *
  @field_at DCS.CS sh t_gzh (DOT _time) (vl (gz_time h)) hp *
  @field_at DCS.CS sh t_gzh (DOT _os) (vi (gz_os h)) hp *
  @field_at DCS.CS sh t_gzh (DOT _extra) xp hp *
  @field_at DCS.CS sh t_gzh (DOT _extra_len) (vi (gz_extra_len h)) hp *
  @field_at DCS.CS sh t_gzh (DOT _name) np hp *
  @field_at DCS.CS sh t_gzh (DOT _comment) cp hp *
  (EX v : val, @field_at DCS.CS sh t_gzh (DOT _xflags) v hp) *
  (EX v : val, @field_at DCS.CS sh t_gzh (DOT _extra_max) v hp) *
  (EX v : val, @field_at DCS.CS sh t_gzh (DOT _name_max) v hp) *
  (EX v : val, @field_at DCS.CS sh t_gzh (DOT _comm_max) v hp) *
  (EX v : val, @field_at DCS.CS sh t_gzh (DOT _done) v hp) *
  opt_obj sh (gz_extra h) xp * opt_obj sh (gz_name h) np * opt_obj sh (gz_comment h) cp)%logic.

Lemma gzh_hc_open sh h hp xp np cp :
  gzh_at sh h hp xp np cp =
  (!! (readable_share sh /\ gzh_ok h) &&
   (@field_at DCS.CS sh t_gzh (DOT _hcrc) (vi (gz_hcrc h)) hp * gzh_nohc sh h hp xp np cp))%logic.
Proof. unfold gzh_at, gzh_nohc. apply pred_ext; Intros; entailer!. Qed.

Lemma gzh_hc_unfold sh h hp xp np cp :
  gzh_at sh h hp xp np cp |--
  (!! (readable_share sh /\ gzh_ok h) &&
   (@field_at DCS.CS sh t_gzh (DOT _hcrc) (vi (gz_hcrc h)) hp * gzh_nohc sh h hp xp np cp))%logic.
Proof. rewrite gzh_hc_open. apply derives_refl. Qed.

Lemma gzh_hc_fold sh h hp xp np cp : readable_share sh -> gzh_ok h ->
  @field_at DCS.CS sh t_gzh (DOT _hcrc) (vi (gz_hcrc h)) hp * gzh_nohc sh h hp xp np cp |-- gzh_at sh h hp xp np cp.
Proof. intros. rewrite gzh_hc_open. entailer!. Qed.

Lemma out_at_fold o m sp pbp : out_ok o m ->
  @field_at DCS.CS Ews t_ds (DOT Zlib.trees.code._pending) (vl (o_pending o)) sp *
  @field_at DCS.CS Ews t_ds (DOT Zlib.trees.code._pending_buf) pbp sp *
  @field_at DCS.CS Ews t_ds (DOT Zlib.trees.code._bi_buf) (vi (o_bi_buf o)) sp *
  @field_at DCS.CS Ews t_ds (DOT Zlib.trees.code._bi_valid) (vi (o_bi_valid o)) sp *
  @field_at DCS.CS Ews t_ds (DOT Zlib.trees.code._bi_used) (vi (o_bi_used o)) sp *
  @data_at DCS.CS Ews (tarray tuchar (Zlength (o_buf o))) (pb_vals (o_buf o) m) pbp
  |-- out_at o m sp pbp.
Proof. intros. unfold out_at. entailer!. Qed.

(** ** Reads of pending_buf (from StageExtra) *)
Lemma pb_vals_sublist lo hi b m : Zlength m = Zlength b ->
  pb_vals (sublist lo hi b) (sublist lo hi m) = sublist lo hi (pb_vals b m).
Proof. intros H. unfold pb_vals. rewrite sublist_map, sublist_combine. reflexivity. Qed.

Lemma mb_definedb_spec b lo hi : lo <= hi -> mb_definedb b lo hi = true ->
  0 <= lo /\ hi <= Zlength (mb_val b) /\ forall i, lo <= i < hi -> Znth i (mb_def b) = true.
Proof.
  unfold mb_definedb. intros Hle H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1, H2. split; [lia|split; [lia|]].
  intros i Hi. rewrite forallb_forall in H3. apply (H3 i).
  replace i with (lo + Z.of_nat (Z.to_nat (i - lo))) at 1 by lia.
  apply (in_map (fun k : nat => lo + Z.of_nat k)). apply in_seq. lia.
Qed.

Lemma mb_read_vals b lo n bytes : mb_ok b -> mb_read b lo n = Some bytes ->
  bytes = sublist lo (lo + n) (mb_val b) /\ Zlength bytes = n /\ 0 <= lo /\ 0 <= n /\
  lo + n <= Zlength (mb_val b) /\
  sublist lo (lo + n) (mb_vals b) = map vi bytes /\ Forall (fun x => 0 <= x < 256) bytes.
Proof.
  intros [Hl Hd] H. unfold mb_read in H.
  destruct (0 <=? n) eqn:E0; [|discriminate]. apply Z.leb_le in E0.
  destruct (mb_definedb b lo (lo + n)) eqn:E; [|discriminate]. cbn in H. inversion H; subst; clear H.
  apply mb_definedb_spec in E as (E1 & E2 & E3); [|lia].
  rewrite Zlength_sublist by lia.
  split; [reflexivity|split; [lia|split; [lia|split; [lia|split; [lia|]]]]].
  split.
  - unfold mb_vals. rewrite <- pb_vals_sublist by auto.
    apply Znth_eq_ext.
    + rewrite Zlength_pb_vals, Zlength_map by (rewrite !Zlength_sublist; lia). reflexivity.
    + intros i Hi. rewrite Zlength_pb_vals in Hi by (rewrite !Zlength_sublist; lia).
      rewrite Zlength_sublist in Hi by lia.
      rewrite Znth_pb_vals by (rewrite ?Zlength_sublist; lia).
      rewrite Znth_map by (rewrite Zlength_sublist; lia).
      rewrite (Znth_sublist _ _ _ (mb_def b)) by lia. rewrite E3 by lia. reflexivity.
  - apply Forall_forall. intros x Hx. apply In_Znth in Hx. destruct Hx as [i [Hi Hx]]. subst x.
    rewrite Zlength_sublist in Hi by lia. rewrite Znth_sublist by lia.
    apply Hd; [lia|]. apply E3. lia.
Qed.

Lemma add_ptr_long_tuchar pbp beg : isptr pbp -> force_val (sem_add_ptr_long tuchar pbp (vl beg)) = offset_val beg pbp.
Proof.
  destruct pbp; try contradiction. intros _. unfold vl. simpl.
  f_equal. rewrite Ptrofs.mul_commut, Ptrofs.mul_one. f_equal.
  unfold Ptrofs.of_int64. apply Ptrofs.eqm_samerepr. apply Ptrofs.eqm_sym.
  unfold Ptrofs.eqm. rewrite Int64.unsigned_repr_eq.
  change Ptrofs.modulus with Int64.modulus. apply Zbits.eqmod_mod. reflexivity.
Qed.

(** ** HCRC_UPDATE(beg) *)
Lemma cmpu_gt64 a b : 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.cmpu Cgt (Int64.repr a) (Int64.repr b) = (a >? b).
Proof.
  intros Ha Hb. unfold Int64.cmpu. rewrite Int64.ltu_not. unfold Int64.ltu, Int64.eq.
  rewrite !Int64.unsigned_repr by auto. zfin.
Qed.

Definition hc_cond (h : gzh) (s : dstate) (beg : Z) : bool := (negb (gz_hcrc h =? 0) && (d_pending s >? beg))%bool.

Lemma hc1_ok {Espec : OracleKind} p pin pout ish R msgv gv flush s z beg h hsh xp np cp W z' :
  c_hcrc_update h s z beg = Some z' -> 0 <= beg <= Int64.max_unsigned ->
  @semax DCS.CS Espec Delta_df
    (PROPx [] (LOCALx (sn_locals p flush beg gv)
     (SEPx [dfull s z p pin pout ish R msgv gv; deflate_globals gv; gzh_at hsh h (p_gzhead p) xp np cp; W])))
    SN_hc1
    (normal_ret_assert (PROPx [] (LOCALx (sn_locals p flush beg gv)
     (SEPx [dfull s z' p pin pout ish R msgv gv; deflate_globals gv; gzh_at hsh h (p_gzhead p) xp np cp; W])))).
Proof.
  intros Hc Hbeg. unfold sn_locals. cbv [SN_hc1].
  sep_apply (dfull_gz_open s z p pin pout ish R msgv gv). Intros.
  apply semax_loop_nocontinue.
  sep_apply (gzh_hc_unfold hsh h (p_gzhead p) xp np cp). Intros.
  forward. forward.
  unfold out_at. Intros.
  forward_if_temp _t'57 (Vint (Int.repr (if hc_cond h s beg then 1 else 0))).
  { forward. forward. entailer!.
    unfold hc_cond. rewrite (proj2 (Z.eqb_neq _ _) H6'). cbn [negb andb].
    rewrite cmpu_gt64 by (open_dranges H1; unfold d_pending; destruct H5 as (_ & _ & ? & _); lia).
    unfold d_pending. destruct (_ >? _); reflexivity. }
  { forward. entailer!. unfold hc_cond.
    replace (gz_hcrc h) with 0 by (destruct H4 as (_ & _ & _ & _ & ?); symmetry; apply repr_inj_signed; auto; rep_lia).
    reflexivity. }
  forward_if (PROPx [] (LOCALx [temp _beg__1 (vl beg); temp _strm (p_strm p); temp _s (p_s p);
     temp _flush (vi flush); gvars gv]
     (SEPx [dfull s z' p pin pout ish R msgv gv; deflate_globals gv; gzh_at hsh h (p_gzhead p) xp np cp; W]))).
  { assert (Hcd : hc_cond h s beg = true) by (destruct (hc_cond h s beg); [reflexivity | contradiction]).
    unfold c_hcrc_update in Hc. fold (hc_cond h s beg) in Hc. rewrite Hcd in Hc.
    inv_bind Hc. rename x into bytes, Ha into Hrd. inversion Hc; subst z'; clear Hc.
    rewrite strm_at_open. Intros.
    forward. forward. forward.
    unfold deflate_globals. Intros.
    rewrite (QuickProof.Assembly.data_at_tuchar_cs DCS.CS Zlib.units.Crc32.CS Ews).
    forward_call (z_adler z, offset_val beg (p_pbuf p), d_pending s - beg, false, Ews, p_pbuf p, beg,
      Zlength (o_buf (tr_out (d_tr s))), pb_vals (o_buf (tr_out (d_tr s))) (d_pbm s), bytes, false, Ews, gv, Ers).
    1: (match goal with Hf : field_compatible (Tarray tuchar _ _) _ (p_pbuf p) |- _ =>
          apply field_compatible_isptr in Hf; exact Hf end).
    1: (entailer!; simpl; rewrite add_ptr_long_tuchar; [reflexivity|];
        match goal with Hf : field_compatible (Tarray tuchar _ _) _ (p_pbuf p) |- _ =>
          apply field_compatible_isptr in Hf; exact Hf end).
    1: (unfold Frame; rewrite emp_sepcon; match goal with |- ?P |-- fold_right_sepcon ?F => unify F [P] end;
        simpl; rewrite sepcon_emp; apply derives_refl).
    { assert (Hgt : beg < d_pending s)
        by (unfold hc_cond in Hcd; apply andb_prop in Hcd as [_ Hg]; apply Z.gtb_lt in Hg; lia).
      pose proof H5 as (Hmb & _ & Hpr & _). destruct (mb_read_vals _ _ _ _ Hmb Hrd) as (Eb & Lb & Hb0 & Hn0 & Hle & Hsub & Hby).
      cbn [mb_val mb_vals mb_def] in *. unfold mb_vals in Hsub; cbn [mb_val mb_def] in Hsub.
      split; [open_zranges H; lia|]. split; [unfold d_pending in *; pose proof (Zlength_nonneg bytes); lia|].
      split; [|apply Zlib.proof.adler32.Bytes.cbuf_valid_pos; unfold d_pending in *; lia].
      unfold Bytes.cbuf_ok. split; [reflexivity|]. split; [auto|]. split; [lia|]. split; [unfold d_pending in *; lia|].
      split; [auto|]. split.
      - unfold Bytes.is_bytes. eapply Forall_impl; [|exact Hby]. intros; rep_lia.
      - unfold Bytes.bytes_rep. rewrite Hsub. reflexivity. }
    Intros.
    rewrite (QuickProof.Assembly.data_at_tuchar_cs Zlib.units.Crc32.CS DCS.CS Ews).
    forward.
    assert (Hcr : 0 <= Model.ref_crc32 (z_adler z) bytes <= Int64.max_unsigned).
    { pose proof H5 as (Hmb & _). destruct (mb_read_vals _ _ _ _ Hmb Hrd) as (_ & _ & _ & _ & _ & _ & Hby).
      assert (Hib : Bytes.is_bytes bytes) by (unfold Bytes.is_bytes; eapply Forall_impl; [|exact Hby]; intros; rep_lia).
      pose proof (ref_crc32_range (z_adler z) bytes Hib) as Hr. unfold is32 in Hr. rep_lia. }
    sep_apply (strm_at_set_adler z (Model.ref_crc32 (z_adler z) bytes) (p_s p) (p_strm p) pin pout msgv gv).
    sep_apply (out_at_fold (tr_out (d_tr s)) (d_pbm s) (p_s p) (p_pbuf p)); auto.
    change (out_space z pout R) with (out_space (set_z_adler z (Model.ref_crc32 (z_adler z) bytes)) pout R).
    sep_apply (dfull_gz_close s (set_z_adler z (Model.ref_crc32 (z_adler z) bytes)) z p pin pout ish R msgv gv); auto.
    { apply strm_ranges_set_adler; auto. }
    sep_apply (gzh_hc_fold hsh h (p_gzhead p) xp np cp); auto.
    unfold deflate_globals. entailer!. }
  { assert (Hcd : hc_cond h s beg = false)
      by (destruct (hc_cond h s beg); [apply repr_inj_unsigned in H6; rep_lia | reflexivity]).
    unfold c_hcrc_update in Hc. fold (hc_cond h s beg) in Hc. rewrite Hcd in Hc.
    inversion Hc; subst z'; clear Hc.
    forward.
    sep_apply (out_at_fold (tr_out (d_tr s)) (d_pbm s) (p_s p) (p_pbuf p)); auto.
    sep_apply (dfull_gz_close s z z p pin pout ish R msgv gv); auto.
    sep_apply (gzh_hc_fold hsh h (p_gzhead p) xp np cp); auto.
    entailer!. }
  forward. entailer!.
Qed.

(** The same after the loop. *)
Lemma hc2_ok {Espec : OracleKind} p pin pout ish R msgv gv flush s z beg h hsh xp np cp W z' :
  c_hcrc_update h s z beg = Some z' -> 0 <= beg <= Int64.max_unsigned ->
  @semax DCS.CS Espec Delta_df
    (PROPx [] (LOCALx (sn_locals p flush beg gv)
     (SEPx [dfull s z p pin pout ish R msgv gv; deflate_globals gv; gzh_at hsh h (p_gzhead p) xp np cp; W])))
    SN_hc2
    (normal_ret_assert (PROPx [] (LOCALx (sn_locals p flush beg gv)
     (SEPx [dfull s z' p pin pout ish R msgv gv; deflate_globals gv; gzh_at hsh h (p_gzhead p) xp np cp; W])))).
Proof.
  intros Hc Hbeg. unfold sn_locals. cbv [SN_hc2].
  sep_apply (dfull_gz_open s z p pin pout ish R msgv gv). Intros.
  apply semax_loop_nocontinue.
  sep_apply (gzh_hc_unfold hsh h (p_gzhead p) xp np cp). Intros.
  forward. forward.
  unfold out_at. Intros.
  forward_if_temp _t'61 (Vint (Int.repr (if hc_cond h s beg then 1 else 0))).
  { forward. forward. entailer!.
    unfold hc_cond. rewrite (proj2 (Z.eqb_neq _ _) H6'). cbn [negb andb].
    rewrite cmpu_gt64 by (open_dranges H1; unfold d_pending; destruct H5 as (_ & _ & ? & _); lia).
    unfold d_pending. destruct (_ >? _); reflexivity. }
  { forward. entailer!. unfold hc_cond.
    replace (gz_hcrc h) with 0 by (destruct H4 as (_ & _ & _ & _ & ?); symmetry; apply repr_inj_signed; auto; rep_lia).
    reflexivity. }
  forward_if (PROPx [] (LOCALx [temp _beg__1 (vl beg); temp _strm (p_strm p); temp _s (p_s p);
     temp _flush (vi flush); gvars gv]
     (SEPx [dfull s z' p pin pout ish R msgv gv; deflate_globals gv; gzh_at hsh h (p_gzhead p) xp np cp; W]))).
  { assert (Hcd : hc_cond h s beg = true) by (destruct (hc_cond h s beg); [reflexivity | contradiction]).
    unfold c_hcrc_update in Hc. fold (hc_cond h s beg) in Hc. rewrite Hcd in Hc.
    inv_bind Hc. rename x into bytes, Ha into Hrd. inversion Hc; subst z'; clear Hc.
    rewrite strm_at_open. Intros.
    forward. forward. forward.
    unfold deflate_globals. Intros.
    rewrite (QuickProof.Assembly.data_at_tuchar_cs DCS.CS Zlib.units.Crc32.CS Ews).
    forward_call (z_adler z, offset_val beg (p_pbuf p), d_pending s - beg, false, Ews, p_pbuf p, beg,
      Zlength (o_buf (tr_out (d_tr s))), pb_vals (o_buf (tr_out (d_tr s))) (d_pbm s), bytes, false, Ews, gv, Ers).
    1: (match goal with Hf : field_compatible (Tarray tuchar _ _) _ (p_pbuf p) |- _ =>
          apply field_compatible_isptr in Hf; exact Hf end).
    1: (entailer!; simpl; rewrite add_ptr_long_tuchar; [reflexivity|];
        match goal with Hf : field_compatible (Tarray tuchar _ _) _ (p_pbuf p) |- _ =>
          apply field_compatible_isptr in Hf; exact Hf end).
    1: (unfold Frame; rewrite emp_sepcon; match goal with |- ?P |-- fold_right_sepcon ?F => unify F [P] end;
        simpl; rewrite sepcon_emp; apply derives_refl).
    { assert (Hgt : beg < d_pending s)
        by (unfold hc_cond in Hcd; apply andb_prop in Hcd as [_ Hg]; apply Z.gtb_lt in Hg; lia).
      pose proof H5 as (Hmb & _ & Hpr & _). destruct (mb_read_vals _ _ _ _ Hmb Hrd) as (Eb & Lb & Hb0 & Hn0 & Hle & Hsub & Hby).
      cbn [mb_val mb_vals mb_def] in *. unfold mb_vals in Hsub; cbn [mb_val mb_def] in Hsub.
      split; [open_zranges H; lia|]. split; [unfold d_pending in *; pose proof (Zlength_nonneg bytes); lia|].
      split; [|apply Zlib.proof.adler32.Bytes.cbuf_valid_pos; unfold d_pending in *; lia].
      unfold Bytes.cbuf_ok. split; [reflexivity|]. split; [auto|]. split; [lia|]. split; [unfold d_pending in *; lia|].
      split; [auto|]. split.
      - unfold Bytes.is_bytes. eapply Forall_impl; [|exact Hby]. intros; rep_lia.
      - unfold Bytes.bytes_rep. rewrite Hsub. reflexivity. }
    Intros.
    rewrite (QuickProof.Assembly.data_at_tuchar_cs Zlib.units.Crc32.CS DCS.CS Ews).
    forward.
    assert (Hcr : 0 <= Model.ref_crc32 (z_adler z) bytes <= Int64.max_unsigned).
    { pose proof H5 as (Hmb & _). destruct (mb_read_vals _ _ _ _ Hmb Hrd) as (_ & _ & _ & _ & _ & _ & Hby).
      assert (Hib : Bytes.is_bytes bytes) by (unfold Bytes.is_bytes; eapply Forall_impl; [|exact Hby]; intros; rep_lia).
      pose proof (ref_crc32_range (z_adler z) bytes Hib) as Hr. unfold is32 in Hr. rep_lia. }
    sep_apply (strm_at_set_adler z (Model.ref_crc32 (z_adler z) bytes) (p_s p) (p_strm p) pin pout msgv gv).
    sep_apply (out_at_fold (tr_out (d_tr s)) (d_pbm s) (p_s p) (p_pbuf p)); auto.
    change (out_space z pout R) with (out_space (set_z_adler z (Model.ref_crc32 (z_adler z) bytes)) pout R).
    sep_apply (dfull_gz_close s (set_z_adler z (Model.ref_crc32 (z_adler z) bytes)) z p pin pout ish R msgv gv); auto.
    { apply strm_ranges_set_adler; auto. }
    sep_apply (gzh_hc_fold hsh h (p_gzhead p) xp np cp); auto.
    unfold deflate_globals. entailer!. }
  { assert (Hcd : hc_cond h s beg = false)
      by (destruct (hc_cond h s beg); [apply repr_inj_unsigned in H6; rep_lia | reflexivity]).
    unfold c_hcrc_update in Hc. fold (hc_cond h s beg) in Hc. rewrite Hcd in Hc.
    inversion Hc; subst z'; clear Hc.
    forward.
    sep_apply (out_at_fold (tr_out (d_tr s)) (d_pbm s) (p_s p) (p_pbuf p)); auto.
    sep_apply (dfull_gz_close s z z p pin pout ish R msgv gv); auto.
    sep_apply (gzh_hc_fold hsh h (p_gzhead p) xp np cp); auto.
    entailer!. }
  forward. entailer!.
Qed.

(** ** The head of one iteration: [if (s->pending == s->pending_buf_size) { HCRC_UPDATE(beg); flush_pending(strm);
    if (s->pending != 0) { s->last_flush = -1; return Z_OK; } beg = 0; }] *)
Definition str_head (h : gzh) (s : dstate) (z : strm) (beg : Z) : option ((dstate * strm * Z) + (dstate * strm)) :=
  if d_pending s =? d_pending_buf_size s then
    (let* z := c_hcrc_update h s z beg in
     let* (s, z) := c_flush_pending s z in
     if negb (d_pending s =? 0) then Some (inr (set_d_last_flush s (-1), z)) else Some (inl (s, z, 0)))
  else Some (inl (s, z, beg)).

Lemma str_body_head h str s z beg : str_body h str (s, z, beg) =
  let* r := str_head h s z beg in
  match r with
  | inr e => Some (inr (inr e))
  | inl (s, z, beg) =>
    let* v := rd str (d_gzindex s) in
    let s := set_d_gzindex s (u64 (d_gzindex s + 1)) in
    let* s := c_dput_byte s v in
    if v =? 0 then Some (inr (inl (s, z, beg))) else Some (inl (s, z, beg))
  end.
Proof. reflexivity. Qed.

Lemma fr_nogz_fold s z p pin ish gv :
  ltree_at (tr_ltree (d_tr s)) (p_s p) * dtree_at (tr_dtree (d_tr s)) (p_s p) *
  sym_at (d_tr s) (p_s p) (p_pbuf p) * dtype_at (d_tr s) (p_s p) (p_strm p) * lvl_at (d_tr s) (p_s p) *
  trees_rest (d_tr s) (p_s p) (p_strm p) gv *
  win_at s p * hash_at s p * match_at s p * cfg_at s p *
  @field_at DCS.CS Ews t_ds (DOT _status) (vi (d_status s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _pending_buf_size) (vl (d_pending_buf_size s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _wrap) (vi (d_wrap s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _gzindex) (vl (d_gzindex s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _method) (vi (d_method s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _last_flush) (vi (d_last_flush s)) (p_s p) *
  in_obj ish z pin |-- fr_nogz s z p pin ish gv.
Proof. unfold fr_nogz. cancel. Qed.

(** flush_frame with a new last_flush. *)
Lemma flush_frame_lf s z p pin ish gv lf : dstate_ranges s -> readable_share ish -> s32_ok lf ->
  ltree_at (tr_ltree (d_tr s)) (p_s p) * dtree_at (tr_dtree (d_tr s)) (p_s p) *
  sym_at (d_tr s) (p_s p) (p_pbuf p) * dtype_at (d_tr s) (p_s p) (p_strm p) * lvl_at (d_tr s) (p_s p) *
  trees_rest (d_tr s) (p_s p) (p_strm p) gv *
  win_at s p * hash_at s p * match_at s p * cfg_at s p *
  @field_at DCS.CS Ews t_ds (DOT _status) (vi (d_status s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _pending_buf_size) (vl (d_pending_buf_size s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _wrap) (vi (d_wrap s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _gzhead) (p_gzhead p) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _gzindex) (vl (d_gzindex s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _method) (vi (d_method s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _last_flush) (vi lf) (p_s p) *
  in_obj ish z pin
  |-- flush_frame (set_d_last_flush s lf) z p pin ish gv.
Proof.
  intros Hs Hi Hlf.
  assert (Hd : dstate_ranges (set_d_last_flush s lf)) by (destruct s; unfold dstate_ranges in *; cbn in *; tauto).
  unfold flush_frame.
  set (s1 := set_d_last_flush s lf).
  change (win_at s1 p) with (win_at s p). change (hash_at s1 p) with (hash_at s p).
  change (match_at s1 p) with (match_at s p). change (cfg_at s1 p) with (cfg_at s p).
  change (d_tr s1) with (d_tr s).
  change (d_status s1) with (d_status s). change (d_pending_buf_size s1) with (d_pending_buf_size s).
  change (d_wrap s1) with (d_wrap s). change (d_gzindex s1) with (d_gzindex s).
  change (d_method s1) with (d_method s). change (d_last_flush s1) with lf.
  entailer!.
Qed.

Lemma hcrc_same h s z beg z' : c_hcrc_update h s z beg = Some z' ->
  z_out z' = z_out z /\ z_avail_out z' = z_avail_out z /\ z_in z' = z_in z /\ z_msg z' = z_msg z /\
  (strm_ranges z -> mb_ok (d_pb s) -> strm_ranges z').
Proof.
  unfold c_hcrc_update. intros H. destruct (_ && _)%bool.
  - inv_bind H. inversion H; subst z'. cbn.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    intros Hz Hmb. apply strm_ranges_set_adler; auto.
    assert (Hib : Bytes.is_bytes x).
    { unfold Bytes.is_bytes. eapply Forall_impl; [|exact (mb_read_bytes _ _ _ _ Hmb Ha)]. intros; rep_lia. }
    pose proof (ref_crc32_range (z_adler z) x Hib) as Hr. unfold is32 in Hr. rep_lia.
  - inversion H; subst z'. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. auto.
Qed.

Lemma lf_comm s o po x : set_d_last_flush (set_d_po (set_d_out s o) po) x = set_d_po (set_d_out (set_d_last_flush s x) o) po.
Proof. reflexivity. Qed.

Ltac forward_if_prop P :=
  match goal with |- semax _ (PROPx ?Ps (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx (P :: Ps) (LOCALx Q (SEPx R)))
  end.

Lemma part1_ok {Espec : OracleKind} p pin pout ish R msgv1 gv flush z s1 z1 beg h hsh xp np cp W r res :
  str_head h s1 z1 beg = Some r -> out_grow z z1 -> Zlength R = z_avail_out z -> 0 <= beg <= Int64.max_unsigned ->
  (forall s2 z2, r = inr (s2, z2) -> res = (s2, z2, Some Z_OK)) ->
  @semax DCS.CS Espec Delta_df
    (PROPx [] (LOCALx (sn_locals p flush beg gv)
     (SEPx [dfull s1 z1 p pin pout ish (rest_after z z1 R) msgv1 gv; deflate_globals gv;
            gzh_at hsh h (p_gzhead p) xp np cp; W])))
    SN_part1
    {| RA_normal :=
         match r with
         | inl (s2, z2, beg2) =>
           EX msgv2 : val, PROPx [out_grow z z2] (LOCALx (sn_locals p flush beg2 gv)
           (SEPx [dfull s2 z2 p pin pout ish (rest_after z z2 R) msgv2 gv; deflate_globals gv;
                  gzh_at hsh h (p_gzhead p) xp np cp; W]))
         | inr _ => FF
         end;
       RA_break := FF; RA_continue := FF;
       RA_return := RA_return (stage_post p pin pout ish R gv flush z
                                 (hdr_res (Some h) (p_gzhead p) (hsh, xp, np, cp) * W)%logic res) |}.
Proof.
  intros Hh Hg Hrl Hbeg Hres. unfold sn_locals. cbv [SN_part1].
  sep_apply (dfull_gz_open s1 z1 p pin pout ish (rest_after z z1 R) msgv1 gv). Intros.
  unfold fr_nogz, out_at. Intros.
  forward. forward.
  sep_apply (out_at_fold (tr_out (d_tr s1)) (d_pbm s1) (p_s p) (p_pbuf p)); auto.
  sep_apply (fr_nogz_fold s1 z1 p pin ish gv).
  sep_apply (dfull_gz_close s1 z1 z1 p pin pout ish (rest_after z z1 R) msgv1 gv); auto.
  forward_if.
  - assert (Ep : d_pending s1 = d_pending_buf_size s1).
    { apply Int64.same_if_eq in H4. destruct H3 as (_ & _ & Hp & _). open_dranges H1.
      apply repr_inj_unsigned64 in H4; auto. }
    unfold str_head in Hh. rewrite Ep, Z.eqb_refl in Hh.
    inv_bind Hh. rename x into z1', Ha into Hhc.
    inv_bind Hh. destruct x as [s2 z2]. rename Ha into Hfp.
    destruct (hcrc_same _ _ _ _ _ Hhc) as (Eo1 & Ea1 & Ei1 & Em1 & Hr1).
    eapply semax_seq'.
    { eapply semax_pre; [| apply (hc1_ok p pin pout ish (rest_after z z1 R) msgv1 gv flush s1 z1 beg h hsh xp np cp W z1' Hhc Hbeg)].
      unfold sn_locals. entailer!. }
    unfold sn_locals, MORE_COMMANDS, abbreviate. abbreviate_semax.
    sep_apply (dfull_flush_open s1 z1' p pin pout ish (rest_after z z1 R) msgv1 gv). Intros.
    forward_call (p_strm p, p_s p, p_pbuf p, pin, pout, msgv1, rest_after z z1 R, s1, z1', (s2, z2), gv).
    cbn [fst snd].
    destruct (c_flush_pending_same _ _ _ _ Hfp) as (Ein2 & Emsg2 & _).
    pose proof (c_flush_pending_grow _ _ _ Hfp) as Hgr2. cbn [snd] in Hgr2.
    destruct (c_flush_pending_inv _ _ _ _ H5 Hfp) as ([ob m] & po & Es2 & Hpo & Hr2). subst s2.
    change (tr_out (d_tr (set_d_po (set_d_out s1 (ob, m)) po))) with ob.
    change (d_pbm (set_d_po (set_d_out s1 (ob, m)) po)) with m.
    change (d_po (set_d_po (set_d_out s1 (ob, m)) po)) with po.
    change (d_pending (set_d_po (set_d_out s1 (ob, m)) po)) with (o_pending ob) in Hh.
    assert (Hpo2 : 0 <= po) by (apply Hpo; open_dranges H1; auto).
    assert (Hg1 : out_grow z z1') by (eapply out_grow_trans; [exact Hg | apply out_grow_same; auto]).
    assert (Hg2 : out_grow z z2) by (eapply out_grow_trans; [exact Hg1 | exact Hgr2]).
    unfold out_at. Intros.
    destruct (Hr2 H7) as [Hz2 _].
    assert (Era : rest_after z1' z2 (rest_after z z1 R) = rest_after z z2 R).
    { replace (rest_after z z1 R) with (rest_after z z1' R) by (unfold rest_after; rewrite Eo1; reflexivity).
      apply rest_after_trans; auto. open_zranges Hz2; lia. }
    rewrite Era.
    forward.
    sep_apply (out_at_fold ob m (p_s p) (p_pbuf p)); auto.
    forward_if_prop (o_pending ob = 0).
    + (* return Z_OK *)
      assert (Ep2 : (o_pending ob =? 0) = false).
      { apply Z.eqb_neq. intro E. rewrite E in *. contradiction. }
      rewrite Ep2 in Hh. cbn [negb] in Hh. inversion Hh; subst r; clear Hh.
      specialize (Hres _ _ eq_refl). subst res.
      unfold flush_frame. Intros.
      forward.
      unfold POSTCONDITION, abbreviate.
      eapply semax_pre; [| apply semax_return].
      apply andp_right; [entailer!|].
      go_lowerx. cbn [RA_return stage_post].
      Exists msgv1. rewrite lf_comm.
      change (Vint (Int.neg (Int.repr 1))) with (vi (-1)).
      sep_apply (flush_frame_lf s1 z1' p pin ish gv (-1)); auto. { unfold s32_ok; rep_lia. }
      sep_apply (dfull_out_close (set_d_last_flush s1 (-1)) z1' z2 ob m po p pin pout ish (rest_after z z2 R) msgv1 gv); auto.
      { rewrite Emsg2, Em1; auto. }
      entailer!.
      unfold PROPx, LOCALx, SEPx, local, lift1; simpl; entailer!.
    + forward. entailer!.
      destruct H7 as (_ & _ & Hp & _). apply repr_inj_unsigned64; auto. rep_lia.
    + Intros. rename H8 into Hp0.
      rewrite Hp0 in Hh. cbn in Hh. inversion Hh; subst r; clear Hh.
      forward.
      Exists msgv1.
      sep_apply (dfull_out_close s1 z1' z2 ob m po p pin pout ish (rest_after z z2 R) msgv1 gv); auto.
      { rewrite Emsg2, Em1; auto. }
      entailer!.
  - assert (Ep : (d_pending s1 =? d_pending_buf_size s1) = false).
    { apply Z.eqb_neq. intro E. unfold d_pending in E. rewrite E in H4. contradiction. }
    unfold str_head in Hh. rewrite Ep in Hh. inversion Hh; subst r; clear Hh.
    forward.
    Exists msgv1. entailer!.
Qed.

(** ** The gz_header, opened at the fields the stage reads (name, hcrc) (as in StageComment.v) *)
Definition gzh_restn (sh : share) (h : gzh) (hp xp cp : val) : mpred :=
  (@field_at DCS.CS sh t_gzh (DOT _text) (vi (gz_text h)) hp *
  @field_at DCS.CS sh t_gzh (DOT _time) (vl (gz_time h)) hp *
  @field_at DCS.CS sh t_gzh (DOT _os) (vi (gz_os h)) hp *
  @field_at DCS.CS sh t_gzh (DOT _extra) xp hp *
  @field_at DCS.CS sh t_gzh (DOT _extra_len) (vi (gz_extra_len h)) hp *
  @field_at DCS.CS sh t_gzh (DOT _comment) cp hp *
  (EX v : val, @field_at DCS.CS sh t_gzh (DOT _xflags) v hp) *
  (EX v : val, @field_at DCS.CS sh t_gzh (DOT _extra_max) v hp) *
  (EX v : val, @field_at DCS.CS sh t_gzh (DOT _name_max) v hp) *
  (EX v : val, @field_at DCS.CS sh t_gzh (DOT _comm_max) v hp) *
  (EX v : val, @field_at DCS.CS sh t_gzh (DOT _done) v hp) *
  opt_obj sh (gz_extra h) xp * opt_obj sh (gz_comment h) cp)%logic.

Lemma gzh_at_openn sh h hp xp np cp :
  gzh_at sh h hp xp np cp =
  (!! (readable_share sh /\ gzh_ok h) &&
   (@field_at DCS.CS sh t_gzh (DOT _name) np hp *
    @field_at DCS.CS sh t_gzh (DOT _hcrc) (vi (gz_hcrc h)) hp *
    opt_obj sh (gz_name h) np * gzh_restn sh h hp xp cp))%logic.
Proof. unfold gzh_at, gzh_restn. apply pred_ext; Intros; entailer!. Qed.

Lemma gzh_at_foldn sh h hp xp np cp : readable_share sh -> gzh_ok h ->
  @field_at DCS.CS sh t_gzh (DOT _name) np hp *
  @field_at DCS.CS sh t_gzh (DOT _hcrc) (vi (gz_hcrc h)) hp *
  opt_obj sh (gz_name h) np * gzh_restn sh h hp xp cp |-- gzh_at sh h hp xp np cp.
Proof. intros. rewrite gzh_at_openn. entailer!. Qed.


Lemma ff_close s z0 z3 st g lf ob m po p pin pout ish R msgv gv :
  dstate_ranges s -> readable_share ish -> s32_ok st -> u64_ok g -> s32_ok lf -> strm_ranges z3 ->
  msg_ok (z_msg z3) msgv -> z_in z3 = z_in z0 -> 0 <= po ->
  strm_at z3 (p_s p) (p_strm p) pin pout msgv gv * out_space z3 pout R *
  @field_at DCS.CS Ews t_ds (DOT _pending_out) (offset_val po (p_pbuf p)) (p_s p) *
  out_at ob m (p_s p) (p_pbuf p) *
  ltree_at (tr_ltree (d_tr s)) (p_s p) * dtree_at (tr_dtree (d_tr s)) (p_s p) *
  sym_at (d_tr s) (p_s p) (p_pbuf p) * dtype_at (d_tr s) (p_s p) (p_strm p) * lvl_at (d_tr s) (p_s p) *
  trees_rest (d_tr s) (p_s p) (p_strm p) gv *
  win_at s p * hash_at s p * match_at s p * cfg_at s p *
  @field_at DCS.CS Ews t_ds (DOT _status) (vi st) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _pending_buf_size) (vl (d_pending_buf_size s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _wrap) (vi (d_wrap s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _gzhead) (p_gzhead p) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _gzindex) (vl g) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _method) (vi (d_method s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _last_flush) (vi lf) (p_s p) *
  in_obj ish z0 pin
  |-- dfull (set_d_po (set_d_out (set_d_last_flush (set_d_gzindex (set_d_status s st) g) lf) (ob, m)) po)
        z3 p pin pout ish R msgv gv.
Proof.
  intros Hd Hsh Hst Hg Hlf Hz3 Hm3 Ein Hpo.
  set (s1 := set_d_last_flush (set_d_gzindex (set_d_status s st) g) lf).
  assert (Hd1 : dstate_ranges s1).
  { unfold s1, dstate_ranges in *. dsimpl. tauto. }
  eapply derives_trans; [| apply (dfull_out_close s1 z0 z3 ob m po p pin pout ish R msgv gv); auto].
  unfold flush_frame.
  change (win_at s1 p) with (win_at s p). change (hash_at s1 p) with (hash_at s p).
  change (match_at s1 p) with (match_at s p). change (cfg_at s1 p) with (cfg_at s p).
  change (tr_ltree (d_tr s1)) with (tr_ltree (d_tr s)). change (tr_dtree (d_tr s1)) with (tr_dtree (d_tr s)).
  change (sym_at (d_tr s1)) with (sym_at (d_tr s)). change (dtype_at (d_tr s1)) with (dtype_at (d_tr s)).
  change (lvl_at (d_tr s1)) with (lvl_at (d_tr s)). change (trees_rest (d_tr s1)) with (trees_rest (d_tr s)).
  change (d_status s1) with st. change (d_pending_buf_size s1) with (d_pending_buf_size s).
  change (d_wrap s1) with (d_wrap s). change (d_gzindex s1) with g.
  change (d_method s1) with (d_method s). change (d_last_flush s1) with lf.
  entailer!.
Qed.

Lemma gzi_eq s g o :
  set_d_out (set_d_gzindex s g) o =
  set_d_po (set_d_out (set_d_last_flush (set_d_gzindex (set_d_status s (d_status s)) g) (d_last_flush s)) o) (d_po s).
Proof. destruct s as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? t ?]; destruct t; reflexivity. Qed.


Lemma opt_obj_fold sh b p : Forall (fun x => 0 <= x < 256) b ->
  @data_at DCS.CS sh (tarray tuchar (Zlength b)) (map vi b) p *
  (if Zlength b =? 0 then @malloc_token DCS.CS Ews (tarray tuchar 0) p else emp) |-- opt_obj sh (Some b) p.
Proof. intros. unfold opt_obj. entailer!. Qed.

Lemma opt_obj_some sh b p : opt_obj sh (Some b) p =
  (!! Forall (fun x => 0 <= x < 256) b && (@data_at DCS.CS sh (tarray tuchar (Zlength b)) (map vi b) p *
   (if Zlength b =? 0 then @malloc_token DCS.CS Ews (tarray tuchar 0) p else emp)))%logic.
Proof. reflexivity. Qed.

(** Part 2 of the loop body: [val = s->gzhead->comment[s->gzindex++]; put_byte(s, val);] *)
Lemma part2_ok {Espec : OracleKind} p pin pout ish R msgv gv flush s z beg hsh h xp np cp W str v s' :
  gz_name h = Some str -> Forall (fun b => 0 <= b < 256) str ->
  rd str (d_gzindex s) = Some v ->
  c_dput_byte (set_d_gzindex s (u64 (d_gzindex s + 1))) v = Some s' ->
  @semax DCS.CS Espec Delta_df
    (PROPx [] (LOCALx (sn_locals p flush beg gv)
     (SEPx [dfull s z p pin pout ish R msgv gv; deflate_globals gv; gzh_at hsh h (p_gzhead p) xp np cp; W])))
    SN_part2
    (normal_ret_assert (PROPx [] (LOCALx (temp _val (vi v) :: sn_locals p flush beg gv)
     (SEPx [dfull s' z p pin pout ish R msgv gv; deflate_globals gv; gzh_at hsh h (p_gzhead p) xp np cp; W])))).
Proof.
  intros Hc Hby Hrd Hput. unfold sn_locals, df_locals. cbv [SN_part2].
  sep_apply (dfull_flush_open s z p pin pout ish R msgv gv). Intros.
  unfold flush_frame. Intros.
  forward. forward.
  rewrite gzh_at_openn. Intros.
  forward.
  rewrite Hc, opt_obj_some. Intros.
  forward.
  assert (Hg : 0 <= d_gzindex s < Zlength str /\ v = Znth (d_gzindex s) str).
  { unfold rd, in_range in Hrd. destruct (_ && _)%bool eqn:E; [|discriminate]. inversion Hrd.
    apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. split; [lia|reflexivity]. }
  destruct Hg as [Hg ->].
  assert (Hv : 0 <= Znth (d_gzindex s) str < 256) by (rewrite Forall_Znth in Hby; apply Hby; exact Hg).
  unfold vl. forward.
  { entailer!. rep_lia. }
  unfold c_dput_byte in Hput. inv_bind Hput. rename x into om, Ha into Hpb. inversion Hput; subst s'; clear Hput.
  change (d_out (set_d_gzindex s (u64 (d_gzindex s + 1)))) with (tr_out (d_tr s), d_pbm s) in Hpb.
  apply c_put_byte_inv in Hpb. destruct Hpb as [Hpi ->].
  open_out_at.
  forward. forward. forward. forward.
  change (Int.signed (Int.repr 1)) with 1. rewrite !add64_repr. norm_byte_val.
  sep_apply (out_at_put_byte (tr_out (d_tr s)) (d_pbm s) (Znth (d_gzindex s) str) (p_s p) (p_pbuf p) H5 Hpi).
  sep_apply (opt_obj_fold hsh str np Hby). rewrite <- Hc.
  sep_apply (gzh_at_foldn hsh h (p_gzhead p) xp np cp); auto.
  rewrite <- (repr_u64 (d_gzindex s + 1)).
  destruct (put_byte_c (tr_out (d_tr s)) (d_pbm s) (Znth (d_gzindex s) str)) as [ob m] eqn:Epb.
  cbn [fst snd].
  rewrite gzi_eq.
  open_dranges H1.
  sep_apply (ff_close s z z (d_status s) (u64 (d_gzindex s + 1)) (d_last_flush s) ob m (d_po s) p pin pout ish R msgv gv);
    auto; try (unfold s32_ok; lia); try apply u64_range.
  entailer!.
Qed.


Lemma str_head_beg h s z beg s2 z2 beg2 : str_head h s z beg = Some (inl (s2, z2, beg2)) -> beg2 = 0 \/ beg2 = beg.
Proof.
  unfold str_head. intros H. destruct (_ =? _).
  - inv_bind H. inv_bind H. destruct x0. destruct (negb _); inversion H; auto.
  - inversion H; auto.
Qed.


(** ** The loop *)
Definition sn_inv (p : dptrs) (pin pout : val) (ish : share) (R : list val) (gv : globals) (flush : Z) (z : strm)
    (hsh : share) (h : gzh) (xp np cp : val) (W : mpred) (str : list Z) (e : (dstate * strm * Z) + (dstate * strm))
    : environ -> mpred :=
  EX s1 : dstate, EX z1 : strm, EX beg : Z, EX msgv1 : val,
  PROPx [runs (str_body h str) (s1, z1, beg) e; out_grow z z1; 0 <= beg <= Int64.max_unsigned]
  (LOCALx (sn_locals p flush beg gv)
  (SEPx [dfull s1 z1 p pin pout ish (rest_after z z1 R) msgv1 gv; deflate_globals gv;
         gzh_at hsh h (p_gzhead p) xp np cp; W])).

Definition sn_cont (p : dptrs) (pin pout : val) (ish : share) (R : list val) (gv : globals) (flush : Z) (z : strm)
    (hsh : share) (h : gzh) (xp np cp : val) (W : mpred) (str : list Z) (e : (dstate * strm * Z) + (dstate * strm))
    : environ -> mpred :=
  EX s1 : dstate, EX z1 : strm, EX beg : Z, EX v : Z, EX msgv1 : val,
  PROPx [if v =? 0 then e = inl (s1, z1, beg) else runs (str_body h str) (s1, z1, beg) e;
         out_grow z z1; 0 <= beg <= Int64.max_unsigned; 0 <= v < 256]
  (LOCALx (temp _val (vi v) :: sn_locals p flush beg gv)
  (SEPx [dfull s1 z1 p pin pout ish (rest_after z z1 R) msgv1 gv; deflate_globals gv;
         gzh_at hsh h (p_gzhead p) xp np cp; W])).

Definition sn_brk (p : dptrs) (pin pout : val) (ish : share) (R : list val) (gv : globals) (flush : Z) (z : strm)
    (hsh : share) (h : gzh) (xp np cp : val) (W : mpred) (e : (dstate * strm * Z) + (dstate * strm))
    : environ -> mpred :=
  EX s1 : dstate, EX z1 : strm, EX beg : Z, EX msgv1 : val,
  PROPx [e = inl (s1, z1, beg); out_grow z z1; 0 <= beg <= Int64.max_unsigned]
  (LOCALx (sn_locals p flush beg gv)
  (SEPx [dfull s1 z1 p pin pout ish (rest_after z z1 R) msgv1 gv; deflate_globals gv;
         gzh_at hsh h (p_gzhead p) xp np cp; W])).

Lemma incr_ok {Espec : OracleKind} p pin pout ish R gv flush z hsh h xp np cp W str e Post :
  @semax DCS.CS Espec Delta_df (sn_cont p pin pout ish R gv flush z hsh h xp np cp W str e) SN_incr
    (loop2_ret_assert (sn_inv p pin pout ish R gv flush z hsh h xp np cp W str e)
       (overridePost (sn_brk p pin pout ish R gv flush z hsh h xp np cp W e) Post)).
Proof.
  unfold sn_cont. Intros s1 z1 beg v msgv1. cbv [SN_incr].
  forward_if.
  - forward. unfold sn_inv. Exists s1 z1 beg msgv1.
    rewrite (proj2 (Z.eqb_neq _ _) H3) in H. unfold sn_locals, df_locals. entailer!.
  - forward. destruct Post; unfold loop2_ret_assert; cbv beta iota. Exists s1 z1 beg msgv1.
    subst v. rewrite Z.eqb_refl in H. unfold sn_locals, df_locals. entailer!.
Qed.

Lemma rd_byte str i v : Forall (fun b => 0 <= b < 256) str -> rd str i = Some v -> 0 <= v < 256.
Proof.
  intros Hb H. unfold rd, in_range in H. destruct (_ && _)%bool eqn:E; [|discriminate]. inversion H; subst.
  apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  rewrite Forall_Znth in Hb. apply Hb. lia.
Qed.

Lemma body_ok {Espec : OracleKind} p pin pout ish R gv flush z hsh h xp np cp W str e res :
  gz_name h = Some str -> Forall (fun b => 0 <= b < 256) str -> Zlength R = z_avail_out z ->
  (forall s2 z2, e = inr (s2, z2) -> res = (s2, z2, Some Z_OK)) ->
  @semax DCS.CS Espec Delta_df (sn_inv p pin pout ish R gv flush z hsh h xp np cp W str e) SN_body
    (loop1_ret_assert (sn_cont p pin pout ish R gv flush z hsh h xp np cp W str e)
       (overridePost (sn_brk p pin pout ish R gv flush z hsh h xp np cp W e)
          (stage_post p pin pout ish R gv flush z (hdr_res (Some h) (p_gzhead p) (hsh, xp, np, cp) * W)%logic res))).
Proof.
  intros Hc Hby HR Hres.
  unfold sn_inv. Intros s1 z1 beg msgv1. rename H into Hrun, H0 into Hg1, H1 into Hbeg.
  assert (Hx : exists r0, str_head h s1 z1 beg = Some r0 /\
    (forall s2 z2, r0 = inr (s2, z2) -> e = inr (s2, z2)) /\
    (forall s2 z2 beg2, r0 = inl (s2, z2, beg2) -> exists v s3,
       rd str (d_gzindex s2) = Some v /\ c_dput_byte (set_d_gzindex s2 (u64 (d_gzindex s2 + 1))) v = Some s3 /\
       (if v =? 0 then e = inl (s3, z2, beg2) else runs (str_body h str) (s3, z2, beg2) e))).
  { destruct (runs_inv _ _ _ Hrun) as [Hb | (a' & Hb & Hr)]; rewrite str_body_head in Hb;
      inv_bind Hb; rename x into r0, Ha into Hh; exists r0; (split; [exact Hh|]).
    - split.
      + intros s2 z2 ->. inversion Hb. reflexivity.
      + intros s2 z2 beg2 ->. inv_bind Hb. inv_bind Hb. exists x, x0. split; [auto|split; [auto|]].
        destruct (x =? 0); inversion Hb; auto.
    - split.
      + intros s2 z2 ->. discriminate.
      + intros s2 z2 beg2 ->. inv_bind Hb. inv_bind Hb. exists x, x0. split; [auto|split; [auto|]].
        destruct (x =? 0); inversion Hb; subst; auto. }
  destruct Hx as (r0 & Hh & Hinr & Hinl).
  destruct res as [[s' z'] o].
  apply semax_seq with (Q := match r0 with
                    | inl (s2, z2, beg2) =>
                      EX msgv2 : val, PROPx [out_grow z z2] (LOCALx (sn_locals p flush beg2 gv)
                      (SEPx [dfull s2 z2 p pin pout ish (rest_after z z2 R) msgv2 gv; deflate_globals gv;
                             gzh_at hsh h (p_gzhead p) xp np cp; W]))
                    | inr _ => FF
                    end).
  { eapply semax_post; [| | | | apply (part1_ok p pin pout ish R msgv1 gv flush z s1 z1 beg h hsh xp np cp W r0 (s', z', o) Hh Hg1 HR Hbeg)].
    - intros. apply ENTAIL_refl.
    - intros. apply andp_left2. apply FF_left.
    - intros. apply andp_left2. apply FF_left.
    - intros. apply ENTAIL_refl.
    - intros s2 z2 E. apply Hres. apply Hinr. exact E. }
  destruct r0 as [[[s2 z2] beg2] | [s2 z2]].
  2: { apply semax_ff. }
  Intros msgv2.
  destruct (Hinl s2 z2 beg2 eq_refl) as (v & s3 & Hrd & Hput & Hif).
  pose proof (rd_byte _ _ _ Hby Hrd) as Hv.
  assert (Hbeg2 : 0 <= beg2 <= Int64.max_unsigned) by (destruct (str_head_beg _ _ _ _ _ _ _ Hh); subst; lia).
  eapply semax_post; [| | | | apply (part2_ok p pin pout ish (rest_after z z2 R) msgv2 gv flush s2 z2 beg2 hsh h xp np cp W str v s3 Hc Hby Hrd Hput)].
  - intros. unfold loop1_ret_assert, overridePost, normal_ret_assert. cbv beta iota.
    unfold sn_cont. Exists s3 z2 beg2 v msgv2. unfold sn_locals, df_locals. simpl RA_normal. entailer!.
  - intros. unfold normal_ret_assert. cbv beta iota. apply andp_left2. apply FF_left.
  - intros. unfold normal_ret_assert. cbv beta iota. apply andp_left2. apply FF_left.
  - intros. unfold normal_ret_assert. cbv beta iota. apply andp_left2. apply FF_left.
Qed.

Lemma loop_ok {Espec : OracleKind} p pin pout ish R gv flush z hsh h xp np cp W str e res :
  gz_name h = Some str -> Forall (fun b => 0 <= b < 256) str -> Zlength R = z_avail_out z ->
  (forall s2 z2, e = inr (s2, z2) -> res = (s2, z2, Some Z_OK)) ->
  @semax DCS.CS Espec Delta_df (sn_inv p pin pout ish R gv flush z hsh h xp np cp W str e) (Sloop SN_body SN_incr)
    (overridePost (sn_brk p pin pout ish R gv flush z hsh h xp np cp W e)
       (stage_post p pin pout ish R gv flush z (hdr_res (Some h) (p_gzhead p) (hsh, xp, np, cp) * W)%logic res)).
Proof.
  intros. apply semax_loop with (Q' := sn_cont p pin pout ish R gv flush z hsh h xp np cp W str e).
  - apply body_ok; auto.
  - apply incr_ok.
Qed.


Definition SN_beg : statement := ltac:(let x := eval cbv [SN_inner] in SN_inner in
  match x with Ssequence ?a _ => exact a end).

Definition SN_gz0 : statement := ltac:(let x := eval cbv [SN_inner] in SN_inner in
  match x with Ssequence _ (Ssequence _ (Ssequence _ ?c)) => exact c end).

Lemma SN_inner_eq : SN_inner = Ssequence SN_beg (Ssequence (Sloop SN_body SN_incr) (Ssequence SN_hc2 SN_gz0)).
Proof. reflexivity. Qed.

Lemma gzi0_eq s : set_d_gzindex s 0 =
  set_d_po (set_d_out (set_d_last_flush (set_d_gzindex (set_d_status s (d_status s)) 0) (d_last_flush s))
    (tr_out (d_tr s), d_pbm s)) (d_po s).
Proof. destruct s as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? t ?]; destruct t; reflexivity. Qed.

(** [s->gzindex = 0;] *)
Lemma gz0_ok {Espec : OracleKind} p pin pout ish R msgv gv flush s z beg hsh h xp np cp W :
  @semax DCS.CS Espec Delta_df
    (PROPx [] (LOCALx (sn_locals p flush beg gv)
     (SEPx [dfull s z p pin pout ish R msgv gv; deflate_globals gv; gzh_at hsh h (p_gzhead p) xp np cp; W])))
    SN_gz0
    (normal_ret_assert (PROPx [] (LOCALx (sn_locals p flush beg gv)
     (SEPx [dfull (set_d_gzindex s 0) z p pin pout ish R msgv gv; deflate_globals gv;
            gzh_at hsh h (p_gzhead p) xp np cp; W])))).
Proof.
  unfold sn_locals. cbv [SN_gz0].
  sep_apply (dfull_flush_open s z p pin pout ish R msgv gv). Intros.
  unfold flush_frame. Intros.
  forward.
  rewrite gzi0_eq.
  open_dranges H1.
  sep_apply (ff_close s z z (d_status s) 0 (d_last_flush s) (tr_out (d_tr s)) (d_pbm s) (d_po s) p pin pout ish R msgv gv);
    auto; try (unfold s32_ok, u64_ok; rep_lia).
Qed.

Lemma hcrc_adler h s z beg z' : c_hcrc_update h s z beg = Some z' -> z_out z' = z_out z /\ z_in z' = z_in z.
Proof.
  unfold c_hcrc_update. intros H. destruct (_ && _)%bool.
  - inv_bind H. inversion H; subst. split; reflexivity.
  - inversion H; subst. split; reflexivity.
Qed.

Definition sn_join (p : dptrs) (pin pout : val) (ish : share) (R : list val) (gv : globals) (flush : Z) (z : strm)
    (hsh : share) (h : gzh) (xp np cp : val) (W : mpred) (s2 : dstate) (z2 : strm) (o : option Z) : environ -> mpred :=
  EX msgv' : val, PROPx [o = None] (LOCALx (df_locals p flush gv)
  (SEPx [dfull s2 z2 p pin pout ish (rest_after z z2 R) msgv' gv; deflate_globals gv;
         gzh_at hsh h (p_gzhead p) xp np cp; W])).

Lemma beg_ok {Espec : OracleKind} p pin pout ish R msgv gv flush s z hsh h xp np cp W :
  @semax DCS.CS Espec Delta_df
    (PROPx [] (LOCALx (df_locals p flush gv)
     (SEPx [dfull s z p pin pout ish R msgv gv; deflate_globals gv; gzh_at hsh h (p_gzhead p) xp np cp; W])))
    SN_beg
    (normal_ret_assert (PROPx [0 <= d_pending s <= Int64.max_unsigned] (LOCALx (sn_locals p flush (d_pending s) gv)
     (SEPx [dfull s z p pin pout ish R msgv gv; deflate_globals gv; gzh_at hsh h (p_gzhead p) xp np cp; W])))).
Proof.
  unfold sn_locals, df_locals. cbv [SN_beg].
  sep_apply (dfull_gz_open s z p pin pout ish R msgv gv). Intros.
  unfold out_at. Intros.
  forward.
  sep_apply (out_at_fold (tr_out (d_tr s)) (d_pbm s) (p_s p) (p_pbuf p)); auto.
  sep_apply (dfull_gz_close s z z p pin pout ish R msgv gv); auto.
  unfold d_pending. destruct H3 as (_ & _ & ? & _). entailer!.
Qed.

Lemma tail_ok {Espec : OracleKind} p pin pout ish R msgv1 gv flush z s1 z1 z3 beg1 hsh h xp np cp W :
  c_hcrc_update h s1 z1 beg1 = Some z3 -> 0 <= beg1 <= Int64.max_unsigned ->
  @semax DCS.CS Espec Delta_df
    (PROPx [] (LOCALx (sn_locals p flush beg1 gv)
     (SEPx [dfull s1 z1 p pin pout ish (rest_after z z1 R) msgv1 gv; deflate_globals gv;
            gzh_at hsh h (p_gzhead p) xp np cp; W])))
    (Ssequence SN_hc2 SN_gz0)
    (normal_ret_assert (sn_join p pin pout ish R gv flush z hsh h xp np cp W (set_d_gzindex s1 0) z3 None)).
Proof.
  intros Hh Hbeg.
  destruct (hcrc_adler _ _ _ _ _ Hh) as [Eo _].
  eapply semax_seq'; [apply (hc2_ok p pin pout ish (rest_after z z1 R) msgv1 gv flush s1 z1 beg1 h hsh xp np cp W z3 Hh Hbeg)|].
  eapply semax_post; [| | | | apply (gz0_ok p pin pout ish (rest_after z z1 R) msgv1 gv flush s1 z3 beg1 hsh h xp np cp W)].
  - intros. unfold normal_ret_assert. cbv beta iota. simpl RA_normal.
    unfold sn_join. Exists msgv1.
    replace (rest_after z z3 R) with (rest_after z z1 R) by (unfold rest_after; rewrite Eo; reflexivity).
    set (s4 := set_d_gzindex s1 0). clearbody s4.
    unfold sn_locals, df_locals. entailer!.
  - intros. unfold normal_ret_assert. cbv beta iota. apply andp_left2. apply FF_left.
  - intros. unfold normal_ret_assert. cbv beta iota. apply andp_left2. apply FF_left.
  - intros. unfold normal_ret_assert. cbv beta iota. apply andp_left2. apply FF_left.
Qed.

Lemma loopseg_ok {Espec : OracleKind} p pin pout ish R msgv gv flush s z hsh h xp np cp W str e res :
  gz_name h = Some str -> Forall (fun b => 0 <= b < 256) str -> Zlength R = z_avail_out z ->
  runs (str_body h str) (s, z, d_pending s) e ->
  (forall s2 z2, e = inr (s2, z2) -> res = (s2, z2, Some Z_OK)) ->
  @semax DCS.CS Espec Delta_df
    (PROPx [0 <= d_pending s <= Int64.max_unsigned] (LOCALx (sn_locals p flush (d_pending s) gv)
     (SEPx [dfull s z p pin pout ish R msgv gv; deflate_globals gv; gzh_at hsh h (p_gzhead p) xp np cp; W])))
    (Sloop SN_body SN_incr)
    (overridePost (sn_brk p pin pout ish R gv flush z hsh h xp np cp W e)
       (stage_post p pin pout ish R gv flush z (hdr_res (Some h) (p_gzhead p) (hsh, xp, np, cp) * W)%logic res)).
Proof.
  intros Hc Hby HR Hl Hres.
  eapply semax_pre; [| apply loop_ok; eauto].
  unfold sn_inv. Exists s z (d_pending s) msgv. rewrite rest_after_refl.
  Intros. pose proof (out_grow_refl z). unfold sn_locals, df_locals. entailer!.
Qed.

Lemma str_inv h str s z s2 z2 o : c_deflate_str h (Some str) true s z = Some (s2, z2, o) ->
  exists e, runs (str_body h str) (s, z, d_pending s) e /\
  (forall s1 z1, e = inr (s1, z1) -> s2 = s1 /\ z2 = z1 /\ o = Some Z_OK) /\
  (forall s1 z1 beg1, e = inl (s1, z1, beg1) -> c_hcrc_update h s1 z1 beg1 = Some z2 /\ s2 = set_d_gzindex s1 0 /\ o = None).
Proof.
  unfold c_deflate_str. intros Hm.
  destruct (loop FUEL (str_body h str) (s, z, d_pending s)) as [e|] eqn:Hl; [|discriminate].
  exists e. split; [exact (loop_runs _ _ _ _ Hl)|]. cbn [bind] in Hm. split.
  - intros s1 z1 ->. inversion Hm; subst. auto.
  - intros s1 z1 beg1 ->. destruct (c_hcrc_update h s1 z1 beg1) as [z3|] eqn:Hh; [|discriminate].
    cbn [bind] in Hm. inversion Hm; subst. auto.
Qed.

Lemma inner_ok {Espec : OracleKind} p pin pout ish R msgv gv flush s z hsh h xp np cp W str s2 z2 o res :
  gz_name h = Some str -> Forall (fun b => 0 <= b < 256) str -> Zlength R = z_avail_out z ->
  c_deflate_str h (Some str) true s z = Some (s2, z2, o) ->
  (forall c, o = Some c -> res = (s2, z2, o)) ->
  @semax DCS.CS Espec Delta_df
    (PROPx [] (LOCALx (df_locals p flush gv)
     (SEPx [dfull s z p pin pout ish R msgv gv; deflate_globals gv; gzh_at hsh h (p_gzhead p) xp np cp; W])))
    SN_inner
    (overridePost (sn_join p pin pout ish R gv flush z hsh h xp np cp W s2 z2 o)
       (stage_post p pin pout ish R gv flush z (hdr_res (Some h) (p_gzhead p) (hsh, xp, np, cp) * W)%logic res)).
Proof.
  intros Hc Hby HR Hm Hres.
  destruct (str_inv _ _ _ _ _ _ _ Hm) as (e & Hl & Hinr & Hinl). clear Hm.
  rewrite SN_inner_eq.
  eapply semax_seq'; [apply beg_ok|].
  apply semax_seq with (Q := sn_brk p pin pout ish R gv flush z hsh h xp np cp W e).
  { rewrite overridePost_overridePost.
    apply (loopseg_ok p pin pout ish R msgv gv flush s z hsh h xp np cp W str e); auto.
    intros s1 z1 E. destruct (Hinr _ _ E) as (-> & -> & ->). apply Hres with Z_OK. reflexivity. }
  unfold sn_brk. Intros s1 z1 beg1 msgv1. rename H0 into Hg1, H1 into Hbeg.
  destruct (Hinl _ _ _ H) as (Hh & -> & ->). clear Hinl Hinr H Hl.
  eapply semax_post; [| | | | apply (tail_ok p pin pout ish R msgv1 gv flush z s1 z1 z2 beg1 hsh h xp np cp W Hh Hbeg)].
  - intros. rewrite overridePost_normal'. unfold normal_ret_assert. cbv beta iota. simpl RA_normal.
    apply andp_left2. apply derives_refl.
  - intros. unfold normal_ret_assert. cbv beta iota. apply andp_left2. apply FF_left.
  - intros. unfold normal_ret_assert. cbv beta iota. apply andp_left2. apply FF_left.
  - intros. unfold normal_ret_assert. cbv beta iota. apply andp_left2. apply FF_left.
Qed.


(** ** The stage *)
Definition gzh_nonm (sh : share) (h : gzh) (hp xp np cp : val) : mpred :=
  (@field_at DCS.CS sh t_gzh (DOT _text) (vi (gz_text h)) hp *
  @field_at DCS.CS sh t_gzh (DOT _time) (vl (gz_time h)) hp *
  @field_at DCS.CS sh t_gzh (DOT _os) (vi (gz_os h)) hp *
  @field_at DCS.CS sh t_gzh (DOT _extra) xp hp *
  @field_at DCS.CS sh t_gzh (DOT _extra_len) (vi (gz_extra_len h)) hp *
  @field_at DCS.CS sh t_gzh (DOT _comment) cp hp *
  @field_at DCS.CS sh t_gzh (DOT _hcrc) (vi (gz_hcrc h)) hp *
  (EX v : val, @field_at DCS.CS sh t_gzh (DOT _xflags) v hp) *
  (EX v : val, @field_at DCS.CS sh t_gzh (DOT _extra_max) v hp) *
  (EX v : val, @field_at DCS.CS sh t_gzh (DOT _name_max) v hp) *
  (EX v : val, @field_at DCS.CS sh t_gzh (DOT _comm_max) v hp) *
  (EX v : val, @field_at DCS.CS sh t_gzh (DOT _done) v hp) *
  opt_obj sh (gz_extra h) xp * opt_obj sh (gz_name h) np * opt_obj sh (gz_comment h) cp)%logic.

Lemma gzh_nm_unfold sh h hp xp np cp :
  gzh_at sh h hp xp np cp |--
  (!! (readable_share sh /\ gzh_ok h) &&
   (@field_at DCS.CS sh t_gzh (DOT _name) np hp * gzh_nonm sh h hp xp np cp))%logic.
Proof. unfold gzh_at, gzh_nonm. Intros. entailer!. Qed.

Lemma gzh_nm_fold sh h hp xp np cp : readable_share sh -> gzh_ok h ->
  @field_at DCS.CS sh t_gzh (DOT _name) np hp * gzh_nonm sh h hp xp np cp |-- gzh_at sh h hp xp np cp.
Proof. intros. unfold gzh_at, gzh_nonm. entailer!. Qed.

Lemma gzh_name_null sh h hp xp np cp : gz_name h = None ->
  gzh_at sh h hp xp np cp |-- !! (np = nullval).
Proof. intros E. unfold gzh_at. rewrite E. unfold opt_obj at 2. Intros. entailer!. Qed.

Lemma gzh_hp_ptr sh h hp xp np cp : gzh_at sh h hp xp np cp |-- !! isptr hp.
Proof. unfold gzh_at. Intros. entailer!. Qed.

Lemma gzh_name_ptr sh h hp xp np cp str : gz_name h = Some str ->
  gzh_at sh h hp xp np cp |-- !! isptr np.
Proof. intros E. unfold gzh_at. rewrite E. unfold opt_obj at 2. Intros. entailer!. Qed.

(** The name's bytes are bytes: a premise of [stage_name_fix], derived from the header's resource in
    [hdr_res_name_bytes] below. *)
Definition name_bytes (s : dstate) : Prop :=
  forall h str, d_gzhead s = Some h -> gz_name h = Some str -> Forall (fun x => 0 <= x < 256) str.

Lemma st_eq s st : set_d_status s st =
  set_d_po (set_d_out (set_d_last_flush (set_d_gzindex (set_d_status s st) (d_gzindex s)) (d_last_flush s))
    (tr_out (d_tr s), d_pbm s)) (d_po s).
Proof. destruct s as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? t ?]; destruct t; reflexivity. Qed.

Local Transparent denote_tc_test_eq.

Lemma stage_name_fix : forall (Espec : OracleKind) p pin pout ish R msgv gv flush s z hx W res,
  0 <= flush <= 5 -> c_deflate_name s z = Some res -> gz_ok (d_gzhead s) (p_gzhead p) hx W -> name_bytes s ->
  @semax DCS.CS Espec Delta_df
    (stage_pre p pin pout ish R msgv gv flush s z (hdr_res (d_gzhead s) (p_gzhead p) hx * W))%logic S_name
    (stage_post p pin pout ish R gv flush z (hdr_res (d_gzhead s) (p_gzhead p) hx * W)%logic res).
Proof.
  intros Espec p pin pout ish R msgv gv flush s z hx W res Hfl Hc Hgz Hnb.
  unfold stage_pre, stage_post, df_locals.
  cbv [S_name nth_stmt df_body f_deflate fn_body].
  sep_apply (dfull_gz_open s z p pin pout ish R msgv gv). Intros.
  unfold fr_nogz. Intros.
  forward.
  sep_apply (fr_nogz_fold s z p pin ish gv).
  sep_apply (dfull_gz_close s z z p pin pout ish R msgv gv); auto.
  destruct res as [[s' z'] o].
  forward_if (EX msgv' : val, PROP (o = None)
    LOCAL (temp _strm (p_strm p); temp _s (p_s p); temp _flush (vi flush); gvars gv)
    SEP (dfull s' z' p pin pout ish (rest_after z z' R) msgv' gv; deflate_globals gv;
         (hdr_res (d_gzhead s) (p_gzhead p) hx * W)%logic)).
  - (* NAME_STATE *)
    assert (Est : d_status s = NAME_STATE).
    { unfold NAME_STATE. open_dranges H1. apply repr_inj_signed; auto; rep_lia. }
    assert_PROP (Zlength R = z_avail_out z) as HR.
    { sep_apply (dfull_gz_open s z p pin pout ish R msgv gv). unfold out_space. entailer!. }
    unfold c_deflate_name in Hc. rewrite Est, Z.eqb_refl in Hc. unfold c_gzhead in Hc.
    destruct (d_gzhead s) as [h|] eqn:Egz; [|discriminate]. cbn [bind] in Hc.
    destruct hx as [[[hsh xp] np] cp]. destruct Hgz as (Hrs & _ & Hvn & _).
    unfold then_stage in Hc. destruct (c_deflate_str h (gz_name h) true s z) as [[[s2 z2] o2]|] eqn:Hstr;
      [|discriminate]. cbn [bind] in Hc.
    change (hdr_res (Some h) (p_gzhead p) (hsh, xp, np, cp)) with (gzh_at hsh h (p_gzhead p) xp np cp).
    Intros.
    assert_PROP (match gz_name h with None => np = nullval | Some _ => isptr np end) as Hnn.
    { destruct (gz_name h) as [str|] eqn:Enm.
      - sep_apply (gzh_name_ptr hsh h (p_gzhead p) xp np cp str Enm). entailer!.
      - sep_apply (gzh_name_null hsh h (p_gzhead p) xp np cp Enm). entailer!. }
    assert_PROP (isptr (p_gzhead p)) as Hgp.
    { sep_apply (gzh_hp_ptr hsh h (p_gzhead p) xp np cp). entailer!. }
    sep_apply (dfull_gz_open s z p pin pout ish R msgv gv). Intros.
    forward.
    sep_apply (gzh_nm_unfold hsh h (p_gzhead p) xp np cp). Intros.
    forward.
    { entailer!. destruct (gz_name h); [destruct np; try contradiction; simpl; auto | subst; simpl; auto]. }
    sep_apply (gzh_nm_fold hsh h (p_gzhead p) xp np cp); auto.
    sep_apply (dfull_gz_close s z z p pin pout ish R msgv gv); auto.
    forward_if (EX msgv' : val, PROP (o2 = None)
      LOCAL (temp _strm (p_strm p); temp _s (p_s p); temp _flush (vi flush); gvars gv)
      SEP (dfull s2 z2 p pin pout ish (rest_after z z2 R) msgv' gv; deflate_globals gv;
           gzh_at hsh h (p_gzhead p) xp np cp; W)).
    + destruct (gz_name h) as [str|] eqn:Enm;
        [destruct np; try contradiction; unfold denote_tc_test_eq; simpl; apply andp_right; [apply prop_right; reflexivity|];
         apply derives_trans with ((gzh_at hsh h (p_gzhead p) xp (Vptr b i) cp * W) * TT)%logic; [cancel|];
         apply sepcon_weak_valid_pointer1; apply Hvn; congruence
        | subst np; simpl; entailer!].
    + (* name != Z_NULL *)
      assert (Hres : forall c, o2 = Some c -> (s', z', o) = (s2, z2, o2))
        by (intros c E; subst o2; inversion Hc; reflexivity).
      destruct (gz_name h) as [str|] eqn:Enm.
      2: { subst np. exfalso. auto. }
      unfold POSTCONDITION, abbreviate.
      eapply semax_pre; [| apply (inner_ok p pin pout ish R msgv gv flush s z hsh h xp np cp W str s2 z2 o2 (s', z', o)
                                Enm (Hnb h str Egz Enm) HR Hstr Hres)].
      unfold df_locals. entailer!.
    + (* name == Z_NULL *)
      forward.
      destruct (gz_name h) as [str|] eqn:Enm.
      { destruct np; try contradiction. discriminate. }
      unfold c_deflate_str in Hstr. inversion Hstr; subst s2 z2 o2.
      Exists msgv. rewrite rest_after_refl. entailer!.
    + (* s->status = COMMENT_STATE *)
      Intros msgv2. subst o2.
      inversion Hc; subst s' z' o; clear Hc.
      sep_apply (dfull_flush_open s2 z2 p pin pout ish (rest_after z z2 R) msgv2 gv). Intros.
      unfold flush_frame. Intros.
      forward.
      rewrite (st_eq s2 DState.COMMENT_STATE).
      open_dranges H7.
      sep_apply (ff_close s2 z2 z2 91 (d_gzindex s2) (d_last_flush s2) (tr_out (d_tr s2)) (d_pbm s2) (d_po s2)
                   p pin pout ish (rest_after z z2 R) msgv2 gv); auto; try (unfold s32_ok, u64_ok; rep_lia).
      Exists msgv2. entailer!. apply derives_refl.
  - (* not NAME_STATE *)
    forward.
    unfold c_deflate_name in Hc.
    rewrite (proj2 (Z.eqb_neq _ _)) in Hc by (unfold NAME_STATE; intro E; rewrite E in *; contradiction).
    inversion Hc; subst s' z' o; clear Hc.
    Exists msgv. rewrite rest_after_refl. entailer!.
  - Intros msgv'. subst o. Exists msgv'. entailer!.
Qed.

(** With the fix of DRep.opt_obj (bytes are bytes), [name_bytes s] follows from [gzh_at] and
    [stage_name : stage_ok_gz S_name c_deflate_name] is [stage_name_fix] with that fact. *)

Lemma hdr_res_name_bytes s ghp hx : hdr_res (d_gzhead s) ghp hx |-- !! name_bytes s.
Proof.
  unfold name_bytes. destruct (d_gzhead s) as [h|] eqn:E.
  - destruct hx as [[[hsh xp] np] cp]. simpl. unfold gzh_at.
    destruct (gz_name h) as [str|] eqn:En.
    + unfold opt_obj at 2. Intros. apply prop_right. intros h' str' E1 E2.
      inversion E1; subst h'. rewrite En in E2. inversion E2; subst str'. assumption.
    + apply prop_right. intros h' str' E1 E2. inversion E1; subst h'. congruence.
  - apply prop_right. intros h' str' E1. discriminate.
Qed.

Lemma stage_name : stage_ok_gz S_name c_deflate_name.
Proof.
  intros Espec p pin pout ish R msgv gv flush s z hx W res Hfl Hc Hgz.
  unfold stage_pre.
  assert_PROP (name_bytes s) as Hnb.
  { go_lowerx. sep_apply (hdr_res_name_bytes s (p_gzhead p) hx). Intros. apply prop_right; assumption. }
  apply (stage_name_fix Espec p pin pout ish R msgv gv flush s z hx W res Hfl Hc Hgz Hnb).
Qed.
