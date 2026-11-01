(** * deflate(): the gzip comment (e13, [if (s->status == COMMENT_STATE) { ... }]) against its model (DeflateKit.v).
    Ported from the v4 proof: [stage_comment_fix] under [comment_bytes s], which follows from the
    byte range in DRep.opt_obj (v6). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.DeflateKit.
Require Import Zlib.proof.crc32.Combine.
#[export] Existing Instance DCS.CS.
Open Scope cmodel_scope.

Definition SC_inner : statement := ltac:(let x := eval cbv [S_comment nth_stmt df_body f_deflate fn_body] in S_comment in
  match x with Ssequence _ (Sifthenelse _ (Ssequence (Ssequence _ (Ssequence _ (Sifthenelse _ ?a _))) _) _) => exact a end).
Definition SC_body : statement := ltac:(let x := eval cbv [SC_inner] in SC_inner in
  match x with Ssequence _ (Ssequence (Sloop ?b _) _) => exact b end).
Definition SC_incr : statement := ltac:(let x := eval cbv [SC_inner] in SC_inner in
  match x with Ssequence _ (Ssequence (Sloop _ ?b) _) => exact b end).
Definition SC_hc2 : statement := ltac:(let x := eval cbv [SC_inner] in SC_inner in
  match x with Ssequence _ (Ssequence _ ?c) => exact c end).
Definition SC_part1 : statement := ltac:(let x := eval cbv [SC_body] in SC_body in
  match x with Ssequence ?a _ => exact a end).
Definition SC_part2 : statement := ltac:(let x := eval cbv [SC_body] in SC_body in
  match x with Ssequence _ ?a => exact a end).

Definition SC_hc1 : statement := ltac:(let x := eval cbv [SC_part1] in SC_part1 in
  match x with Ssequence _ (Ssequence _ (Sifthenelse _ (Ssequence ?c _) _)) => exact c end).

Definition sc_locals (p : dptrs) (flush beg : Z) (gv : globals) : list localdef :=
  temp _beg__2 (vl beg) :: df_locals p flush gv.

Lemma out_at_fold o m sp pbp : out_ok o m ->
  @field_at DCS.CS Ews t_ds (DOT Zlib.trees.code._pending) (vl (o_pending o)) sp *
  @field_at DCS.CS Ews t_ds (DOT Zlib.trees.code._pending_buf) pbp sp *
  @field_at DCS.CS Ews t_ds (DOT Zlib.trees.code._bi_buf) (vi (o_bi_buf o)) sp *
  @field_at DCS.CS Ews t_ds (DOT Zlib.trees.code._bi_valid) (vi (o_bi_valid o)) sp *
  @field_at DCS.CS Ews t_ds (DOT Zlib.trees.code._bi_used) (vi (o_bi_used o)) sp *
  @data_at DCS.CS Ews (tarray tuchar (Zlength (o_buf o))) (pb_vals (o_buf o) m) pbp
  |-- out_at o m sp pbp.
Proof. intros. unfold out_at. entailer!. Qed.

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

(** ** The gz_header, opened at the fields the stage reads (comment, hcrc) *)
Definition gzh_restc (sh : share) (h : gzh) (hp xp np : val) : mpred :=
  (@field_at DCS.CS sh t_gzh (DOT _text) (vi (gz_text h)) hp *
  @field_at DCS.CS sh t_gzh (DOT _time) (vl (gz_time h)) hp *
  @field_at DCS.CS sh t_gzh (DOT _os) (vi (gz_os h)) hp *
  @field_at DCS.CS sh t_gzh (DOT _extra) xp hp *
  @field_at DCS.CS sh t_gzh (DOT _extra_len) (vi (gz_extra_len h)) hp *
  @field_at DCS.CS sh t_gzh (DOT _name) np hp *
  (EX v : val, @field_at DCS.CS sh t_gzh (DOT _xflags) v hp) *
  (EX v : val, @field_at DCS.CS sh t_gzh (DOT _extra_max) v hp) *
  (EX v : val, @field_at DCS.CS sh t_gzh (DOT _name_max) v hp) *
  (EX v : val, @field_at DCS.CS sh t_gzh (DOT _comm_max) v hp) *
  (EX v : val, @field_at DCS.CS sh t_gzh (DOT _done) v hp) *
  opt_obj sh (gz_extra h) xp * opt_obj sh (gz_name h) np)%logic.

Lemma gzh_at_openc sh h hp xp np cp :
  gzh_at sh h hp xp np cp =
  (!! (readable_share sh /\ gzh_ok h) &&
   (@field_at DCS.CS sh t_gzh (DOT _comment) cp hp *
    @field_at DCS.CS sh t_gzh (DOT _hcrc) (vi (gz_hcrc h)) hp *
    opt_obj sh (gz_comment h) cp * gzh_restc sh h hp xp np))%logic.
Proof. unfold gzh_at, gzh_restc. apply pred_ext; Intros; entailer!. Qed.

Lemma opt_obj_fold sh b p : Forall (fun x => 0 <= x < 256) b ->
  @data_at DCS.CS sh (tarray tuchar (Zlength b)) (map vi b) p *
  (if Zlength b =? 0 then @malloc_token DCS.CS Ews (tarray tuchar 0) p else emp) |-- opt_obj sh (Some b) p.
Proof. intros. unfold opt_obj. entailer!. Qed.

Lemma gzh_at_foldc sh h hp xp np cp : readable_share sh -> gzh_ok h ->
  @field_at DCS.CS sh t_gzh (DOT _comment) cp hp *
  @field_at DCS.CS sh t_gzh (DOT _hcrc) (vi (gz_hcrc h)) hp *
  opt_obj sh (gz_comment h) cp * gzh_restc sh h hp xp np |-- gzh_at sh h hp xp np cp.
Proof. intros. rewrite gzh_at_openc. entailer!. Qed.

Lemma opt_obj_some sh b p : opt_obj sh (Some b) p =
  (!! Forall (fun x => 0 <= x < 256) b &&
   (@data_at DCS.CS sh (tarray tuchar (Zlength b)) (map vi b) p *
   (if Zlength b =? 0 then @malloc_token DCS.CS Ews (tarray tuchar 0) p else emp)))%logic.
Proof. reflexivity. Qed.

Lemma opt_obj_some_b sh b p : Forall (fun x => 0 <= x < 256) b -> opt_obj sh (Some b) p =
  (@data_at DCS.CS sh (tarray tuchar (Zlength b)) (map vi b) p *
   (if Zlength b =? 0 then @malloc_token DCS.CS Ews (tarray tuchar 0) p else emp))%logic.
Proof. intros. unfold opt_obj. apply pred_ext; entailer!. Qed.

(** Part 2 of the loop body: [val = s->gzhead->comment[s->gzindex++]; put_byte(s, val);] *)
Lemma part2_ok {Espec : OracleKind} p pin pout ish R msgv gv flush s z beg hsh h xp np cp W str v s' :
  gz_comment h = Some str -> Forall (fun b => 0 <= b < 256) str ->
  rd str (d_gzindex s) = Some v ->
  c_dput_byte (set_d_gzindex s (u64 (d_gzindex s + 1))) v = Some s' ->
  @semax DCS.CS Espec Delta_df
    (PROPx [] (LOCALx (sc_locals p flush beg gv)
     (SEPx [dfull s z p pin pout ish R msgv gv; deflate_globals gv; gzh_at hsh h (p_gzhead p) xp np cp; W])))
    SC_part2
    (normal_ret_assert (PROPx [] (LOCALx (temp _val__1 (vi v) :: sc_locals p flush beg gv)
     (SEPx [dfull s' z p pin pout ish R msgv gv; deflate_globals gv; gzh_at hsh h (p_gzhead p) xp np cp; W])))).
Proof.
  intros Hc Hby Hrd Hput. unfold sc_locals, df_locals. cbv [SC_part2].
  sep_apply (dfull_flush_open s z p pin pout ish R msgv gv). Intros.
  unfold flush_frame. Intros.
  forward. forward.
  rewrite gzh_at_openc. Intros.
  forward.
  rewrite Hc, (opt_obj_some_b hsh str cp Hby). Intros.
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
  sep_apply (opt_obj_fold hsh str cp Hby). rewrite <- Hc.
  sep_apply (gzh_at_foldc hsh h (p_gzhead p) xp np cp); auto.
  rewrite <- (repr_u64 (d_gzindex s + 1)).
  destruct (put_byte_c (tr_out (d_tr s)) (d_pbm s) (Znth (d_gzindex s) str)) as [ob m] eqn:Epb.
  cbn [fst snd].
  rewrite gzi_eq.
  open_dranges H1.
  sep_apply (ff_close s z z (d_status s) (u64 (d_gzindex s + 1)) (d_last_flush s) ob m (d_po s) p pin pout ish R msgv gv);
    auto; try (unfold s32_ok; lia); try apply u64_range.
  entailer!.
Qed.

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
    (PROPx [] (LOCALx (sc_locals p flush beg gv)
     (SEPx [dfull s z p pin pout ish R msgv gv; deflate_globals gv; gzh_at hsh h (p_gzhead p) xp np cp; W])))
    SC_hc1
    (normal_ret_assert (PROPx [] (LOCALx (sc_locals p flush beg gv)
     (SEPx [dfull s z' p pin pout ish R msgv gv; deflate_globals gv; gzh_at hsh h (p_gzhead p) xp np cp; W])))).
Proof.
  intros Hc Hbeg. unfold sc_locals, df_locals. cbv [SC_hc1].
  sep_apply (dfull_gz_open s z p pin pout ish R msgv gv). Intros.
  apply semax_loop_nocontinue.
  sep_apply (gzh_hc_unfold hsh h (p_gzhead p) xp np cp). Intros.
  forward. forward.
  unfold out_at. Intros.
  forward_if_temp _t'63 (Vint (Int.repr (if hc_cond h s beg then 1 else 0))).
  { forward. forward. entailer!.
    unfold hc_cond. rewrite (proj2 (Z.eqb_neq _ _) H6'). cbn [negb andb].
    rewrite cmpu_gt64 by (open_dranges H1; unfold d_pending; destruct H5 as (_ & _ & ? & _); lia).
    unfold d_pending. destruct (_ >? _); reflexivity. }
  { forward. entailer!. unfold hc_cond.
    replace (gz_hcrc h) with 0 by (destruct H4 as (_ & _ & _ & _ & ?); symmetry; apply repr_inj_signed; auto; rep_lia).
    reflexivity. }
  forward_if (PROPx [] (LOCALx [temp _beg__2 (vl beg); temp _strm (p_strm p); temp _s (p_s p);
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
    (PROPx [] (LOCALx (sc_locals p flush beg gv)
     (SEPx [dfull s z p pin pout ish R msgv gv; deflate_globals gv; gzh_at hsh h (p_gzhead p) xp np cp; W])))
    SC_hc2
    (normal_ret_assert (PROPx [] (LOCALx (sc_locals p flush beg gv)
     (SEPx [dfull s z' p pin pout ish R msgv gv; deflate_globals gv; gzh_at hsh h (p_gzhead p) xp np cp; W])))).
Proof.
  intros Hc Hbeg. unfold sc_locals, df_locals. cbv [SC_hc2].
  sep_apply (dfull_gz_open s z p pin pout ish R msgv gv). Intros.
  apply semax_loop_nocontinue.
  sep_apply (gzh_hc_unfold hsh h (p_gzhead p) xp np cp). Intros.
  forward. forward.
  unfold out_at. Intros.
  forward_if_temp _t'67 (Vint (Int.repr (if hc_cond h s beg then 1 else 0))).
  { forward. forward. entailer!.
    unfold hc_cond. rewrite (proj2 (Z.eqb_neq _ _) H6'). cbn [negb andb].
    rewrite cmpu_gt64 by (open_dranges H1; unfold d_pending; destruct H5 as (_ & _ & ? & _); lia).
    unfold d_pending. destruct (_ >? _); reflexivity. }
  { forward. entailer!. unfold hc_cond.
    replace (gz_hcrc h) with 0 by (destruct H4 as (_ & _ & _ & _ & ?); symmetry; apply repr_inj_signed; auto; rep_lia).
    reflexivity. }
  forward_if (PROPx [] (LOCALx [temp _beg__2 (vl beg); temp _strm (p_strm p); temp _s (p_s p);
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

(** ** The model of one iteration, split like the body *)
Definition str_head (h : gzh) (s : dstate) (z : strm) (beg : Z) : option ((dstate * strm * Z) + (dstate * strm)) :=
  if d_pending s =? d_pending_buf_size s then
    let* z := c_hcrc_update h s z beg in
    let* (s, z) := c_flush_pending s z in
    if negb (d_pending s =? 0) then Some (inr (set_d_last_flush s (-1), z)) else Some (inl (s, z, 0))
  else Some (inl (s, z, beg)).

Lemma str_body_eq h str s z beg : str_body h str (s, z, beg) =
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

Lemma str_head_beg h s z beg s2 z2 beg2 : str_head h s z beg = Some (inl (s2, z2, beg2)) -> beg2 = 0 \/ beg2 = beg.
Proof.
  unfold str_head. intros H. destruct (_ =? _).
  - inv_bind H. inv_bind H. destruct x0. destruct (negb _); inversion H; auto.
  - inversion H; auto.
Qed.

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

(** Part 1: [if (s->pending == s->pending_buf_size) { HCRC_UPDATE(beg);
    flush_pending(strm); if (s->pending != 0) { s->last_flush = -1; return Z_OK; } beg = 0; }] *)
Lemma part1_ok {Espec : OracleKind} p pin pout ish R msgv1 gv flush z s1 z1 beg h hsh xp np cp W r res :
  str_head h s1 z1 beg = Some r -> out_grow z z1 -> Zlength R = z_avail_out z -> 0 <= beg <= Int64.max_unsigned ->
  (forall s2 z2, r = inr (s2, z2) -> res = (s2, z2, Some Z_OK)) ->
  @semax DCS.CS Espec Delta_df
    (PROPx [] (LOCALx (sc_locals p flush beg gv)
     (SEPx [dfull s1 z1 p pin pout ish (rest_after z z1 R) msgv1 gv; deflate_globals gv;
            gzh_at hsh h (p_gzhead p) xp np cp; W])))
    SC_part1
    {| RA_normal := match r with
                    | inl (s2, z2, beg2) =>
                      EX msgv2 : val, PROPx [out_grow z z2] (LOCALx (sc_locals p flush beg2 gv)
                      (SEPx [dfull s2 z2 p pin pout ish (rest_after z z2 R) msgv2 gv; deflate_globals gv;
                             gzh_at hsh h (p_gzhead p) xp np cp; W]))
                    | inr _ => FF
                    end;
       RA_break := FF; RA_continue := FF;
       RA_return := RA_return (stage_post p pin pout ish R gv flush z
                                 (hdr_res (Some h) (p_gzhead p) (hsh, xp, np, cp) * W)%logic res) |}.
Proof.
  intros Hh Hg Hrl Hbeg Hres. unfold sc_locals, df_locals. cbv [SC_part1].
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
      unfold sc_locals, df_locals. entailer!. }
    unfold sc_locals, df_locals, MORE_COMMANDS, abbreviate. abbreviate_semax.
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

(** ** The loop *)
Definition sc_inv (p : dptrs) (pin pout : val) (ish : share) (R : list val) (gv : globals) (flush : Z) (z : strm)
    (hsh : share) (h : gzh) (xp np cp : val) (W : mpred) (str : list Z) (e : (dstate * strm * Z) + (dstate * strm))
    : environ -> mpred :=
  EX s1 : dstate, EX z1 : strm, EX beg : Z, EX msgv1 : val,
  PROPx [runs (str_body h str) (s1, z1, beg) e; out_grow z z1; 0 <= beg <= Int64.max_unsigned]
  (LOCALx (sc_locals p flush beg gv)
  (SEPx [dfull s1 z1 p pin pout ish (rest_after z z1 R) msgv1 gv; deflate_globals gv;
         gzh_at hsh h (p_gzhead p) xp np cp; W])).

Definition sc_cont (p : dptrs) (pin pout : val) (ish : share) (R : list val) (gv : globals) (flush : Z) (z : strm)
    (hsh : share) (h : gzh) (xp np cp : val) (W : mpred) (str : list Z) (e : (dstate * strm * Z) + (dstate * strm))
    : environ -> mpred :=
  EX s1 : dstate, EX z1 : strm, EX beg : Z, EX v : Z, EX msgv1 : val,
  PROPx [if v =? 0 then e = inl (s1, z1, beg) else runs (str_body h str) (s1, z1, beg) e;
         out_grow z z1; 0 <= beg <= Int64.max_unsigned; 0 <= v < 256]
  (LOCALx (temp _val__1 (vi v) :: sc_locals p flush beg gv)
  (SEPx [dfull s1 z1 p pin pout ish (rest_after z z1 R) msgv1 gv; deflate_globals gv;
         gzh_at hsh h (p_gzhead p) xp np cp; W])).

Definition sc_brk (p : dptrs) (pin pout : val) (ish : share) (R : list val) (gv : globals) (flush : Z) (z : strm)
    (hsh : share) (h : gzh) (xp np cp : val) (W : mpred) (e : (dstate * strm * Z) + (dstate * strm))
    : environ -> mpred :=
  EX s1 : dstate, EX z1 : strm, EX beg : Z, EX msgv1 : val,
  PROPx [e = inl (s1, z1, beg); out_grow z z1; 0 <= beg <= Int64.max_unsigned]
  (LOCALx (sc_locals p flush beg gv)
  (SEPx [dfull s1 z1 p pin pout ish (rest_after z z1 R) msgv1 gv; deflate_globals gv;
         gzh_at hsh h (p_gzhead p) xp np cp; W])).

Lemma incr_ok {Espec : OracleKind} p pin pout ish R gv flush z hsh h xp np cp W str e Post :
  @semax DCS.CS Espec Delta_df (sc_cont p pin pout ish R gv flush z hsh h xp np cp W str e) SC_incr
    (loop2_ret_assert (sc_inv p pin pout ish R gv flush z hsh h xp np cp W str e)
       (overridePost (sc_brk p pin pout ish R gv flush z hsh h xp np cp W e) Post)).
Proof.
  unfold sc_cont. Intros s1 z1 beg v msgv1. cbv [SC_incr].
  forward_if.
  - forward. unfold sc_inv. Exists s1 z1 beg msgv1.
    rewrite (proj2 (Z.eqb_neq _ _) H3) in H. unfold sc_locals, df_locals. entailer!.
  - forward. destruct Post; unfold loop2_ret_assert; cbv beta iota. Exists s1 z1 beg msgv1.
    subst v. rewrite Z.eqb_refl in H. unfold sc_locals, df_locals. entailer!.
Qed.

Lemma rd_byte str i v : Forall (fun b => 0 <= b < 256) str -> rd str i = Some v -> 0 <= v < 256.
Proof.
  intros Hb H. unfold rd, in_range in H. destruct (_ && _)%bool eqn:E; [|discriminate]. inversion H; subst.
  apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  rewrite Forall_Znth in Hb. apply Hb. lia.
Qed.

Lemma body_ok {Espec : OracleKind} p pin pout ish R gv flush z hsh h xp np cp W str e res :
  gz_comment h = Some str -> Forall (fun b => 0 <= b < 256) str -> Zlength R = z_avail_out z ->
  (forall s2 z2, e = inr (s2, z2) -> res = (s2, z2, Some Z_OK)) ->
  @semax DCS.CS Espec Delta_df (sc_inv p pin pout ish R gv flush z hsh h xp np cp W str e) SC_body
    (loop1_ret_assert (sc_cont p pin pout ish R gv flush z hsh h xp np cp W str e)
       (overridePost (sc_brk p pin pout ish R gv flush z hsh h xp np cp W e)
          (stage_post p pin pout ish R gv flush z (hdr_res (Some h) (p_gzhead p) (hsh, xp, np, cp) * W)%logic res))).
Proof.
  intros Hc Hby HR Hres.
  unfold sc_inv. Intros s1 z1 beg msgv1. rename H into Hrun, H0 into Hg1, H1 into Hbeg.
  assert (Hx : exists r0, str_head h s1 z1 beg = Some r0 /\
    (forall s2 z2, r0 = inr (s2, z2) -> e = inr (s2, z2)) /\
    (forall s2 z2 beg2, r0 = inl (s2, z2, beg2) -> exists v s3,
       rd str (d_gzindex s2) = Some v /\ c_dput_byte (set_d_gzindex s2 (u64 (d_gzindex s2 + 1))) v = Some s3 /\
       (if v =? 0 then e = inl (s3, z2, beg2) else runs (str_body h str) (s3, z2, beg2) e))).
  { destruct (runs_inv _ _ _ Hrun) as [Hb | (a' & Hb & Hr)]; rewrite str_body_eq in Hb;
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
                      EX msgv2 : val, PROPx [out_grow z z2] (LOCALx (sc_locals p flush beg2 gv)
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
    unfold sc_cont. Exists s3 z2 beg2 v msgv2. unfold sc_locals, df_locals. simpl RA_normal. entailer!.
  - intros. unfold normal_ret_assert. cbv beta iota. apply andp_left2. apply FF_left.
  - intros. unfold normal_ret_assert. cbv beta iota. apply andp_left2. apply FF_left.
  - intros. unfold normal_ret_assert. cbv beta iota. apply andp_left2. apply FF_left.
Qed.

Lemma loop_ok {Espec : OracleKind} p pin pout ish R gv flush z hsh h xp np cp W str e res :
  gz_comment h = Some str -> Forall (fun b => 0 <= b < 256) str -> Zlength R = z_avail_out z ->
  (forall s2 z2, e = inr (s2, z2) -> res = (s2, z2, Some Z_OK)) ->
  @semax DCS.CS Espec Delta_df (sc_inv p pin pout ish R gv flush z hsh h xp np cp W str e) (Sloop SC_body SC_incr)
    (overridePost (sc_brk p pin pout ish R gv flush z hsh h xp np cp W e)
       (stage_post p pin pout ish R gv flush z (hdr_res (Some h) (p_gzhead p) (hsh, xp, np, cp) * W)%logic res)).
Proof.
  intros. apply semax_loop with (Q' := sc_cont p pin pout ish R gv flush z hsh h xp np cp W str e).
  - apply body_ok; auto.
  - apply incr_ok.
Qed.

(** ** The branch [if (s->gzhead->comment != Z_NULL) { ... }] *)
Definition SC_beg : statement := ltac:(let x := eval cbv [SC_inner] in SC_inner in
  match x with Ssequence ?a _ => exact a end).

Lemma SC_inner_eq : SC_inner = Ssequence SC_beg (Ssequence (Sloop SC_body SC_incr) SC_hc2).
Proof. reflexivity. Qed.

Lemma hcrc_adler h s z beg z' : c_hcrc_update h s z beg = Some z' -> z_out z' = z_out z /\ z_in z' = z_in z.
Proof.
  unfold c_hcrc_update. intros H. destruct (_ && _)%bool.
  - inv_bind H. inversion H; subst. split; reflexivity.
  - inversion H; subst. split; reflexivity.
Qed.

Definition sc_join (p : dptrs) (pin pout : val) (ish : share) (R : list val) (gv : globals) (flush : Z) (z : strm)
    (hsh : share) (h : gzh) (xp np cp : val) (W : mpred) (s2 : dstate) (z2 : strm) (o : option Z) : environ -> mpred :=
  EX msgv' : val, PROPx [o = None] (LOCALx (df_locals p flush gv)
  (SEPx [dfull s2 z2 p pin pout ish (rest_after z z2 R) msgv' gv; deflate_globals gv;
         gzh_at hsh h (p_gzhead p) xp np cp; W])).

Lemma inner_beg {Espec : OracleKind} p pin pout ish R msgv gv flush s z hsh h xp np cp W :
  @semax DCS.CS Espec Delta_df
    (PROPx [] (LOCALx (df_locals p flush gv)
     (SEPx [dfull s z p pin pout ish R msgv gv; deflate_globals gv; gzh_at hsh h (p_gzhead p) xp np cp; W])))
    SC_beg
    (normal_ret_assert (PROPx [0 <= d_pending s <= Int64.max_unsigned] (LOCALx (sc_locals p flush (d_pending s) gv)
     (SEPx [dfull s z p pin pout ish R msgv gv; deflate_globals gv; gzh_at hsh h (p_gzhead p) xp np cp; W])))).
Proof.
  unfold sc_locals, df_locals. cbv [SC_beg].
  sep_apply (dfull_gz_open s z p pin pout ish R msgv gv). Intros.
  unfold out_at. Intros.
  forward.
  sep_apply (out_at_fold (tr_out (d_tr s)) (d_pbm s) (p_s p) (p_pbuf p)); auto.
  sep_apply (dfull_gz_close s z z p pin pout ish R msgv gv); auto.
  unfold d_pending. destruct H3 as (_ & _ & ? & _). entailer!.
Qed.

Lemma inner_tail {Espec : OracleKind} p pin pout ish R gv flush z hsh h xp np cp W s1 z1 beg1 msgv1 z3 Post :
  c_hcrc_update h s1 z1 beg1 = Some z3 -> 0 <= beg1 <= Int64.max_unsigned ->
  @semax DCS.CS Espec Delta_df
    (PROPx [] (LOCALx (sc_locals p flush beg1 gv)
     (SEPx [dfull s1 z1 p pin pout ish (rest_after z z1 R) msgv1 gv; deflate_globals gv;
            gzh_at hsh h (p_gzhead p) xp np cp; W])))
    SC_hc2
    (overridePost (sc_join p pin pout ish R gv flush z hsh h xp np cp W s1 z3 None) Post).
Proof.
  intros Hh Hbeg.
  destruct (hcrc_adler _ _ _ _ _ Hh) as [Eo _].
  eapply semax_post; [| | | | apply (hc2_ok p pin pout ish (rest_after z z1 R) msgv1 gv flush s1 z1 beg1 h hsh xp np cp W z3 Hh Hbeg)].
  - intros. rewrite overridePost_normal'. simpl RA_normal.
    unfold sc_join. Exists msgv1.
    replace (rest_after z z3 R) with (rest_after z z1 R) by (unfold rest_after; rewrite Eo; reflexivity).
    unfold sc_locals, df_locals. entailer!.
  - intros. unfold normal_ret_assert. cbv beta iota. apply andp_left2. apply FF_left.
  - intros. unfold normal_ret_assert. cbv beta iota. apply andp_left2. apply FF_left.
  - intros. unfold normal_ret_assert. cbv beta iota. apply andp_left2. apply FF_left.
Qed.

Lemma inner_loop {Espec : OracleKind} p pin pout ish R msgv gv flush s z hsh h xp np cp W str e res :
  gz_comment h = Some str -> Forall (fun b => 0 <= b < 256) str -> Zlength R = z_avail_out z ->
  runs (str_body h str) (s, z, d_pending s) e ->
  (forall s2 z2, e = inr (s2, z2) -> res = (s2, z2, Some Z_OK)) ->
  @semax DCS.CS Espec Delta_df
    (PROPx [0 <= d_pending s <= Int64.max_unsigned] (LOCALx (sc_locals p flush (d_pending s) gv)
     (SEPx [dfull s z p pin pout ish R msgv gv; deflate_globals gv; gzh_at hsh h (p_gzhead p) xp np cp; W])))
    (Sloop SC_body SC_incr)
    (overridePost (sc_brk p pin pout ish R gv flush z hsh h xp np cp W e)
       (stage_post p pin pout ish R gv flush z (hdr_res (Some h) (p_gzhead p) (hsh, xp, np, cp) * W)%logic res)).
Proof.
  intros Hc Hby HR Hl Hres.
  eapply semax_pre; [| apply (loop_ok p pin pout ish R gv flush z hsh h xp np cp W str e res Hc Hby HR Hres)].
  unfold sc_inv. Exists s z (d_pending s) msgv. rewrite rest_after_refl.
  apply andp_right.
  - apply andp_left2. unfold PROPx. apply andp_left1. apply prop_derives. intros [Hp _].
    split; [exact Hl | split; [apply out_grow_refl | split; [exact Hp | exact I]]].
  - apply andp_left2. unfold PROPx. apply andp_left2. apply derives_refl.
Qed.

Lemma c_deflate_str_some h str r s z : c_deflate_str h (Some str) r s z =
  let* e := loop FUEL (str_body h str) (s, z, d_pending s) in
  match e with
  | inr (s, z) => Some (s, z, Some Z_OK)
  | inl (s, z, beg) => let* z := c_hcrc_update h s z beg in Some (if r then set_d_gzindex s 0 else s, z, None)
  end.
Proof. reflexivity. Qed.

Lemma str_model h str s z s2 z2 o : c_deflate_str h (Some str) false s z = Some (s2, z2, o) ->
  exists e, runs (str_body h str) (s, z, d_pending s) e /\
  ((forall s1 z1, e = inr (s1, z1) -> s2 = s1 /\ z2 = z1 /\ o = Some Z_OK) /\
   (forall s1 z1 beg1, e = inl (s1, z1, beg1) -> c_hcrc_update h s1 z1 beg1 = Some z2 /\ s2 = s1 /\ o = None)).
Proof.
  rewrite c_deflate_str_some. intros H.
  destruct (loop FUEL (str_body h str) (s, z, d_pending s)) as [e|] eqn:E; [|discriminate].
  exists e. split; [apply (loop_runs _ _ _ _ E)|].
  cbn [bind] in H. split.
  - intros s1 z1 ->. inversion H. auto.
  - intros s1 z1 beg1 ->. destruct (c_hcrc_update h s1 z1 beg1) as [z3|]; [|discriminate].
    inversion H. auto.
Qed.

Lemma inner_ok {Espec : OracleKind} p pin pout ish R msgv gv flush s z hsh h xp np cp W str s2 z2 o res :
  gz_comment h = Some str -> Forall (fun b => 0 <= b < 256) str -> Zlength R = z_avail_out z ->
  c_deflate_str h (Some str) false s z = Some (s2, z2, o) ->
  (forall c, o = Some c -> res = (s2, z2, o)) ->
  @semax DCS.CS Espec Delta_df
    (PROPx [] (LOCALx (df_locals p flush gv)
     (SEPx [dfull s z p pin pout ish R msgv gv; deflate_globals gv; gzh_at hsh h (p_gzhead p) xp np cp; W])))
    SC_inner
    (overridePost (sc_join p pin pout ish R gv flush z hsh h xp np cp W s2 z2 o)
       (stage_post p pin pout ish R gv flush z (hdr_res (Some h) (p_gzhead p) (hsh, xp, np, cp) * W)%logic res)).
Proof.
  intros Hc Hby HR Hm Hres.
  destruct (str_model _ _ _ _ _ _ _ Hm) as (e & Hl & Hinr & Hinl). clear Hm.
  rewrite SC_inner_eq.
  eapply semax_seq'; [apply inner_beg|].
  apply semax_seq with (Q := sc_brk p pin pout ish R gv flush z hsh h xp np cp W e).
  { rewrite overridePost_overridePost. apply inner_loop with (str := str); auto.
    intros s1 z1 E. destruct (Hinr s1 z1 E) as (-> & -> & ->). apply Hres with Z_OK. reflexivity. }
  unfold sc_brk. Intros s1 z1 beg1 msgv1. rename H into Ee, H0 into Hg1, H1 into Hbeg.
  destruct (Hinl s1 z1 beg1 Ee) as (Hh & -> & ->).
  apply inner_tail; auto.
Qed.

(** ** The stage *)
Lemma st_status_eq s st :
  set_d_status s st =
  set_d_po (set_d_out (set_d_last_flush (set_d_gzindex (set_d_status s st) (d_gzindex s)) (d_last_flush s))
    (d_out s)) (d_po s).
Proof. destruct s as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? t ?]; destruct t; reflexivity. Qed.

Lemma S_comment_eq : S_comment = ltac:(let x := eval cbv [S_comment nth_stmt df_body f_deflate fn_body] in S_comment in
  match x with Ssequence ?a (Sifthenelse ?b (Ssequence (Ssequence ?c (Ssequence ?d (Sifthenelse ?f _ ?g))) ?i) ?j) =>
    exact (Ssequence a (Sifthenelse b (Ssequence (Ssequence c (Ssequence d (Sifthenelse f SC_inner g))) i) j)) end).
Proof. reflexivity. Qed.

Lemma out_space_len z p R : out_space z p R |-- !! (Zlength R = z_avail_out z) && out_space z p R.
Proof. unfold out_space. entailer!. Qed.

Lemma gzh_comment_null sh h hp xp np cp : gz_comment h = None -> gzh_at sh h hp xp np cp |-- !! (cp = nullval).
Proof. intros E. rewrite gzh_at_openc, E. unfold opt_obj. Intros. entailer!. Qed.

Lemma gzh_comment_ptr sh h hp xp np cp str : gz_comment h = Some str -> gzh_at sh h hp xp np cp |-- !! isptr cp.
Proof. intros E. rewrite gzh_at_openc, E, opt_obj_some. Intros. entailer!. Qed.

Lemma gzh_comment_pon sh h hp xp np cp : gzh_at sh h hp xp np cp |-- !! is_pointer_or_null cp.
Proof.
  destruct (gz_comment h) as [str|] eqn:E.
  - sep_apply (gzh_comment_ptr sh h hp xp np cp str E). entailer!.
  - sep_apply (gzh_comment_null sh h hp xp np cp E). entailer!.
Qed.

Lemma comment_test_eq sh h hp xp np cp str R : readable_share sh -> gz_comment h = Some str ->
  R * gzh_at sh h hp xp np cp |-- denote_tc_test_eq cp (Vlong (Int64.repr 0)).
Proof.
  intros Hsh E. rewrite gzh_at_openc, E, opt_obj_some. Intros.
  assert_PROP (isptr cp) by entailer!.
  replace (denote_tc_test_eq cp (Vlong (Int64.repr 0))) with (denote_tc_test_eq (offset_val 0 cp) (Vlong (Int64.repr 0)))
    by (rewrite isptr_offset_val_zero; auto).
  eapply derives_trans; [| apply (Zlib.proof.adler32.Bytes.cbuf_test_eq_frame
    (R * @field_at DCS.CS sh t_gzh (DOT _comment) cp hp * @field_at DCS.CS sh t_gzh (DOT _hcrc) (vi (gz_hcrc h)) hp *
     gzh_restc sh h hp xp np)%logic
    (Zlength str =? 0) Ews sh cp 0 (Zlength str) (map vi str))]; auto.
  - destruct (Zlength str =? 0) eqn:Ez; [|cancel].
    apply Z.eqb_eq in Ez. rewrite Ez. cancel.
  - pose proof (Zlength_nonneg str). lia.
  - destruct (Zlength str =? 0) eqn:Ez; [left; auto | right]. apply Z.eqb_neq in Ez. pose proof (Zlength_nonneg str). lia.
Qed.

(** The comment's bytes are bytes: a premise of [stage_comment_fix], derived from the header's resource in
    [hdr_res_comment_bytes] below. *)
Definition comment_bytes (s : dstate) : Prop :=
  forall h str, d_gzhead s = Some h -> gz_comment h = Some str -> Forall (fun x => 0 <= x < 256) str.

Lemma stage_comment_fix : forall (Espec : OracleKind) p pin pout ish R msgv gv flush s z hx W res,
  0 <= flush <= 5 -> c_deflate_comment s z = Some res -> gz_ok (d_gzhead s) (p_gzhead p) hx W -> comment_bytes s ->
  @semax DCS.CS Espec Delta_df
    (stage_pre p pin pout ish R msgv gv flush s z (hdr_res (d_gzhead s) (p_gzhead p) hx * W))%logic S_comment
    (stage_post p pin pout ish R gv flush z (hdr_res (d_gzhead s) (p_gzhead p) hx * W)%logic res).
Proof.
  intros Espec p pin pout ish R msgv gv flush s z hx W res Hfl Hc Hgz Hcb.
  unfold stage_pre, stage_post, df_locals.
  rewrite S_comment_eq.
  sep_apply (dfull_gz_open s z p pin pout ish R msgv gv). Intros.
  sep_apply (out_space_len z pout R). Intros. rename H3 into HR.
  unfold fr_nogz. Intros.
  forward.
  sep_apply (fr_nogz_fold s z p pin ish gv).
  sep_apply (dfull_gz_close s z z p pin pout ish R msgv gv); auto.
  destruct res as [[s' z'] o].
  forward_if (EX msgv' : val, PROP (o = None)
    LOCAL (temp _strm (p_strm p); temp _s (p_s p); temp _flush (vi flush); gvars gv)
    SEP (dfull s' z' p pin pout ish (rest_after z z' R) msgv' gv; deflate_globals gv;
         (hdr_res (d_gzhead s) (p_gzhead p) hx * W)%logic)).
  - (* COMMENT_STATE *)
    assert (Est : d_status s = DState.COMMENT_STATE).
    { unfold DState.COMMENT_STATE. open_dranges H1. apply repr_inj_signed; auto; unfold s32_ok in *; rep_lia. }
    unfold c_deflate_comment in Hc. rewrite Est, Z.eqb_refl in Hc. unfold c_gzhead in Hc.
    destruct (d_gzhead s) as [h|] eqn:Hgh; [|discriminate].
    destruct hx as [[[hsh xp] np] cp]. destruct Hgz as (Hrs & _ & _ & Hwc).
    cbn [bind] in Hc. unfold then_stage in Hc. inv_bind Hc. destruct x as [[s2 z2] o1]. rename Ha into Hstr.
    change (hdr_res (Some h) (p_gzhead p) (hsh, xp, np, cp)) with (gzh_at hsh h (p_gzhead p) xp np cp).
    Intros.
    rewrite gzh_at_openc. Intros.
    sep_apply (dfull_gz_open s z p pin pout ish R msgv gv). Intros.
    forward.
    forward.
    { sep_apply (gzh_at_foldc hsh h (p_gzhead p) xp np cp); auto. sep_apply (gzh_comment_pon hsh h (p_gzhead p) xp np cp). entailer!. }
    sep_apply (dfull_gz_close s z z p pin pout ish R msgv gv); auto.
    sep_apply (gzh_at_foldc hsh h (p_gzhead p) xp np cp); auto.
    forward_if (sc_join p pin pout ish R gv flush z hsh h xp np cp W s2 z2 o1).
    { destruct (gz_comment h) as [str|] eqn:Ecm.
      - eapply derives_trans; [| apply (comment_test_eq hsh h (p_gzhead p) xp np cp str
          (dfull s z p pin pout ish R msgv gv * deflate_globals gv * W)%logic Hrs Ecm)]. cancel.
      - sep_apply (gzh_comment_null hsh h (p_gzhead p) xp np cp Ecm). Intros. subst cp.
        apply denote_tc_test_eq_split; apply valid_pointer_null. }
    { destruct (gz_comment h) as [str|] eqn:Ecm.
      2: { assert_PROP (cp = nullval) by (sep_apply (gzh_comment_null hsh h (p_gzhead p) xp np cp Ecm); entailer!).
           contradiction. }
      unfold POSTCONDITION, abbreviate. rewrite overridePost_overridePost.
      eapply semax_pre; [| apply (inner_ok p pin pout ish R msgv gv flush s z hsh h xp np cp W str s2 z2 o1 (s', z', o)); auto].
      { unfold df_locals. entailer!. }
      { eapply Hcb; eauto. }
      { intros c ->. inversion Hc. reflexivity. } }
    { destruct (gz_comment h) as [str|] eqn:Ecm.
      { assert_PROP (isptr cp) by (sep_apply (gzh_comment_ptr hsh h (p_gzhead p) xp np cp str Ecm); entailer!).
        subst cp. contradiction. }
      cbn in Hstr. inversion Hstr; subst s2 z2 o1; clear Hstr.
      forward. unfold sc_join, df_locals. Exists msgv. rewrite rest_after_refl. entailer!. }
    unfold sc_join, df_locals. Intros msgv'. subst o1. inversion Hc; subst s' z' o; clear Hc.
    sep_apply (dfull_gz_open s2 z2 p pin pout ish (rest_after z z2 R) msgv' gv). Intros.
    unfold fr_nogz. Intros.
    forward.
    rewrite (st_status_eq s2 DState.HCRC_STATE).
    change (d_out s2) with (tr_out (d_tr s2), d_pbm s2).
    change (Vint (Int.repr 103)) with (vi DState.HCRC_STATE).
    Exists msgv'.
    pose proof H7 as Hd2. open_dranges H7.
    sep_apply (ff_close s2 z2 z2 DState.HCRC_STATE (d_gzindex s2) (d_last_flush s2) (tr_out (d_tr s2)) (d_pbm s2)
      (d_po s2) p pin pout ish (rest_after z z2 R) msgv' gv).
    all: try (unfold s32_ok, DState.HCRC_STATE; rep_lia); try (unfold u64_ok; lia); auto.
    change (hdr_res (Some h) (p_gzhead p) (hsh, xp, np, cp)) with (gzh_at hsh h (p_gzhead p) xp np cp).
    entailer!.
  - (* not COMMENT_STATE *)
    forward.
    unfold c_deflate_comment in Hc.
    rewrite (proj2 (Z.eqb_neq _ _)) in Hc by (unfold DState.COMMENT_STATE; intro E; rewrite E in *; contradiction).
    inversion Hc; subst s' z' o; clear Hc.
    Exists msgv. rewrite rest_after_refl. entailer!.
  - Intros msgv'. subst o. Exists msgv'. entailer!.
Qed.

Lemma hdr_res_comment_bytes s ghp hx : hdr_res (d_gzhead s) ghp hx |-- !! comment_bytes s.
Proof.
  unfold comment_bytes. destruct (d_gzhead s) as [h|] eqn:E.
  - destruct hx as [[[hsh xp] np] cp]. simpl. unfold gzh_at.
    destruct (gz_comment h) as [str|] eqn:En.
    + unfold opt_obj at 3. Intros. apply prop_right. intros h' str' E1 E2.
      inversion E1; subst h'. rewrite En in E2. inversion E2; subst str'. assumption.
    + apply prop_right. intros h' str' E1 E2. inversion E1; subst h'. congruence.
  - apply prop_right. intros h' str' E1. discriminate.
Qed.

Lemma stage_comment : stage_ok_gz S_comment c_deflate_comment.
Proof.
  intros Espec p pin pout ish R msgv gv flush s z hx W res Hfl Hc Hgz.
  unfold stage_pre.
  assert_PROP (comment_bytes s) as Hcb.
  { go_lowerx. sep_apply (hdr_res_comment_bytes s (p_gzhead p) hx). entailer!. }
  apply (stage_comment_fix Espec p pin pout ish R msgv gv flush s z hx W res Hfl Hc Hgz Hcb).
Qed.
