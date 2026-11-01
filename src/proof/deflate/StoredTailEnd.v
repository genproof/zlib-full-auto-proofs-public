(** * deflate_stored, second phase, part 3 (StoredTailKit.S_p2_tail): from [have = ((unsigned)s->bi_valid + 42)
    >> 3;] to [return last ? finish_started : need_more;]: a stored block from the window into pending
    (_tr_stored_block) and flush_pending, against StoredTailKit.ds_tail. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.proof.deflate.StoredTailKit.
Require Import Zlib.proof.deflate.StoredFacts.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

(** ** The end: [if (last) s->bi_used = 8; return last ? finish_started : need_more;] *)
Definition S_end : statement := sub S_p2_tail [1;1;1;1;1]%nat.

Lemma ste_ranges_bi_used s x : dstate_ranges s -> dstate_ranges (set_d_bi_used s x).
Proof. unfold dstate_ranges. destruct s; cbn. intuition. Qed.

Lemma st_end_frag {Espec : OracleKind} (p : dptrs) (pin pout : val) (ish : share) (rest : list val)
    (msgv : val) (gv : globals) (s : dstate) (z z0 : strm) (flush lst : Z) :
  lst = 0 \/ lst = 1 ->
  semax Delta_ds
    (PROP () LOCAL (temp _last (vi lst); gvars gv; temp _s (p_s p); temp _flush (vi flush))
     SEP (dfull s z p pin pout ish (rest_after z0 z rest) msgv gv; deflate_globals gv))
    S_end
    (ds_fun_post p pin pout ish rest gv z0
       (if lst =? 0 then (s, z, need_more) else (set_d_bi_used s 8, z, finish_started))).
Proof.
  intros Hl.
  cbv [S_end S_p2_tail S_phase2 sub f_deflate_stored fn_body].
  unfold ds_fun_post.
  destruct Hl as [-> | ->]; cbn [Z.eqb fst snd bstate_num].
  - forward_if True. { contradiction. } { forward. entailer!. }
    forward_if (temp _t'23 (vi 0)). { contradiction. } { forward. entailer!. }
    forward. unfold dfull_post. Exists msgv. cbn [fst snd]. entailer!.
  - forward_if (PROP () LOCAL (temp _last (vi 1); gvars gv; temp _s (p_s p); temp _flush (vi flush))
      SEP (dfull (set_d_bi_used s 8) z p pin pout ish (rest_after z0 z rest) msgv gv; deflate_globals gv)).
    { unfold dfull at 1. Intros. unfold dstate_at at 1. rewrite st_trees_at_split. unfold out_at at 1. Intros.
      forward.
      unfold dfull, dstate_at. rewrite st_trees_at_split. unfold out_at.
      match goal with HR : out_ok _ _ |- _ => rename HR into Hoo end.
      assert (Hoo' : out_ok (tr_out (fst (d_trm (set_d_bi_used s 8)))) (snd (d_trm (set_d_bi_used s 8)))).
      { destruct (tr_out (fst (d_trm s))) as [ob op obb obv obu] eqn:Eo.
        change (tr_out (fst (d_trm (set_d_bi_used s 8)))) with
          (mkOut (o_buf (tr_out (d_tr s))) (o_pending (tr_out (d_tr s))) (o_bi_buf (tr_out (d_tr s)))
                 (o_bi_valid (tr_out (d_tr s))) 8).
        change (fst (d_trm s)) with (d_tr s) in Eo. rewrite Eo. cbn [o_buf o_pending o_bi_buf o_bi_valid].
        apply (out_ok_set_bits ob op obb obv obu _ obb obv 8 Hoo);
          destruct Hoo as [_ [_ [_ [Hb [Hv _]]]]]; cbn in *; rep_lia. }
      assert (Hr3 : dstate_ranges (set_d_bi_used s 8)) by (apply ste_ranges_bi_used; assumption).
      entailer!.
      apply derives_refl. }
    { discriminate. }
    forward_if (temp _t'23 (vi 2)). { forward. entailer!. } { discriminate. }
    forward. unfold dfull_post. Exists msgv. cbn [fst snd]. entailer!.
Qed.

(** ** The model, split like the statement *)
Section TModel.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

Definition st_have (s : dstate) : Z :=
  u32 (let a := u64 (d_pending_buf_size s - stored_hdr s) in if a >? MAX_STORED then MAX_STORED else a).
Definition st_mb (s : dstate) : Z := if st_have s >? d_w_size s then d_w_size s else st_have s.
Definition st_left (s : dstate) : Z := u32 (d_strstart s - d_block_start s).
Definition st_cond (s : dstate) (z : strm) (flush : Z) : bool :=
  (st_left s >=? st_mb s) ||
  ((negb (st_left s =? 0) || (flush =? Z_FINISH)) && negb (flush =? Z_NO_FLUSH) &&
   (z_avail_in z =? 0) && (st_left s <=? st_have s)).
Definition st_len (have left : Z) : Z := if left >? have then have else left.
Definition st_last (z : strm) (flush len left : Z) : Z :=
  if (flush =? Z_FINISH) && (z_avail_in z =? 0) && (len =? left) then 1 else 0.
Definition st_buf (s : dstate) (len : Z) : option (list Z) :=
  if len =? 0 then Some [] else mb_read (d_window s) (d_block_start s) len.
Definition st_branch (s : dstate) (z : strm) (flush have left : Z) : option (dstate * strm * Z) :=
  let len := st_len have left in
  let last := st_last z flush len left in
  let* buf := st_buf s len in
  let* o := c_tr_stored_block (d_out s) buf len last in
  let s := set_d_out s o in
  let* _ := guard (in_long (d_block_start s + len)) in
  let s := set_d_block_start s (d_block_start s + len) in
  let* (s, z) := c_flush_pending s z in
  Some (s, z, last).

Lemma ds_tail_eq s z flush :
  ds_tail s z flush =
  (let* _ := guard (in_long (d_strstart s - d_block_start s)) in
   let* (s, z, last) := (if st_cond s z flush then st_branch s z flush (st_have s) (st_left s) else Some (s, z, 0)) in
   if last =? 0 then Some (s, z, need_more) else Some (set_d_bi_used s 8, z, finish_started)).
Proof. reflexivity. Qed.

Lemma st_branch_inv s z flush have left r :
  st_branch s z flush have left = Some r ->
  exists buf o, st_buf s (st_len have left) = Some buf /\
    c_tr_stored_block (d_out s) buf (st_len have left) (st_last z flush (st_len have left) left) = Some o /\
    in_long (d_block_start s + st_len have left) = true /\
    c_flush_pending (set_d_block_start (set_d_out s o) (d_block_start s + st_len have left)) z = Some (fst r) /\
    snd r = st_last z flush (st_len have left) left.
Proof.
  unfold st_branch. intros H.
  apply bind_inv in H; destruct H as [buf [Hb H]].
  apply bind_inv in H; destruct H as [o [Ho H]].
  apply bind_inv in H; destruct H as [[] [Hg H]]. apply guard_inv in Hg.
  apply bind_inv in H; destruct H as [[s1 z1] [Hf H]]. inversion H; subst; clear H.
  exists buf, o. cbn. auto.
Qed.
End TModel.

(** strm_at with the allocator fields folded. *)
Lemma strm_at_split z sp strmp pin pout msgv gv :
  strm_at z sp strmp pin pout msgv gv =
  (@field_at DCS.CS Ews t_strm (DOT _next_in) (offset_val (z_next_in z) pin) strmp *
   @field_at DCS.CS Ews t_strm (DOT _avail_in) (vi (z_avail_in z)) strmp *
   @field_at DCS.CS Ews t_strm (DOT _total_in) (vl (z_total_in z)) strmp *
   @field_at DCS.CS Ews t_strm (DOT _next_out) (offset_val (Zlength (z_out z)) pout) strmp *
   @field_at DCS.CS Ews t_strm (DOT _avail_out) (vi (z_avail_out z)) strmp *
   @field_at DCS.CS Ews t_strm (DOT _total_out) (vl (z_total_out z)) strmp *
   @field_at DCS.CS Ews t_strm (DOT _msg) msgv strmp *
   @field_at DCS.CS Ews t_strm (DOT _state) sp strmp *
   st_zfuncs strmp gv *
   @field_at DCS.CS Ews t_strm (DOT _opaque) nullval strmp *
   @field_at DCS.CS Ews t_strm (DOT _adler) (vl (z_adler z)) strmp *
   @field_at_ DCS.CS Ews t_strm (DOT _reserved) strmp)%logic.
Proof. unfold strm_at, st_zfuncs. apply pred_ext; cancel. Qed.

Lemma int_eq_repr_s a b : Int.min_signed <= a <= Int.max_signed -> Int.min_signed <= b <= Int.max_signed ->
  Int.eq (Int.repr a) (Int.repr b) = (a =? b).
Proof.
  intros. destruct (Z.eqb_spec a b); [subst; apply Int.eq_true|].
  apply Int.eq_false. intro E. apply repr_inj_signed in E; auto.
Qed.

Lemma int_eq_repr_u a b : 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  Int.eq (Int.repr a) (Int.repr b) = (a =? b).
Proof.
  intros. destruct (Z.eqb_spec a b); [subst; apply Int.eq_true|].
  apply Int.eq_false. intro E. apply repr_inj_unsigned in E; auto.
Qed.

(** ** The window slice given to _tr_stored_block *)
Lemma ste_tuchar_offset0 n j p:
  field_compatible (tarray tuchar n) [] p -> 0 <= j <= n ->
  @field_address0 DCS.CS (Tarray tuchar n noattr) [ArraySubsc j] p = offset_val j p.
Proof.
  intros. rewrite field_address0_offset.
  - simpl. f_equal. lia.
  - eapply field_compatible0_cons_Tarray; [reflexivity | auto | lia].
Qed.

Lemma ste_split3 sh n a b (v: list val) p:
  field_compatible (tarray tuchar n) [] p -> 0 <= a <= b -> b <= n -> Zlength v = n ->
  @data_at DCS.CS sh (tarray tuchar n) v p =
  (@data_at DCS.CS sh (tarray tuchar a) (sublist 0 a v) p *
   @data_at DCS.CS sh (tarray tuchar (b - a)) (sublist a b v) (offset_val a p) *
   @data_at DCS.CS sh (tarray tuchar (n - b)) (sublist b n v) (offset_val b p))%logic.
Proof.
  intros FC A B L.
  unfold tarray. rewrite (split3_data_at_Tarray_tuchar sh n a b v p) by (first [exact L | lia]).
  rewrite !ste_tuchar_offset0 by (auto; lia). reflexivity.
Qed.

(** The window without the slice [bs, bs + len) (the whole window when len = 0). *)
Definition win_rest (n bs len : Z) (vals : list val) (wp : val) : mpred :=
  if len =? 0 then @data_at DCS.CS Ews (tarray tuchar n) vals wp
  else (@data_at DCS.CS Ews (tarray tuchar bs) (sublist 0 bs vals) wp *
        @data_at DCS.CS Ews (tarray tuchar (n - (bs + len))) (sublist (bs + len) n vals)
          (offset_val (bs + len) wp))%logic.

Lemma win_buf_split w bs len buf wp :
  mb_ok w -> (if len =? 0 then Some [] else mb_read w bs len) = Some buf ->
  field_compatible (tarray tuchar (Zlength (mb_val w))) [] wp ->
  @data_at DCS.CS Ews (tarray tuchar (Zlength (mb_val w))) (mb_vals w) wp =
  (buf_at Ews len buf (offset_val bs wp) * win_rest (Zlength (mb_val w)) bs len (mb_vals w) wp)%logic.
Proof.
  intros Hok Hb FC. unfold buf_at, win_rest. destruct (len =? 0) eqn:E.
  - rewrite emp_sepcon. reflexivity.
  - destruct (mb_read_vals _ _ _ _ Hok Hb) as (Hs & Hl & Hlo & Hlen & Hhi & Hby).
    rewrite (ste_split3 Ews (Zlength (mb_val w)) bs (bs + len) (mb_vals w) wp FC) by
      (try lia; apply Zlength_mb_vals; exact Hok).
    rewrite Hs, Hl. replace (bs + len - bs) with len by lia.
    rewrite prop_true_andp by (split; [auto | exact Hby]).
    apply pred_ext; cancel.
Qed.

Lemma ste_add_ptr_long q k : isptr q ->
  force_val (sem_add_ptr_long tschar q (vl k)) = offset_val k q.
Proof.
  intros P. destruct q; try contradiction. unfold vl. simpl. unfold sem_add_ptr_long. simpl.
  f_equal. f_equal. unfold Ptrofs.of_int64. rewrite ptrofs_mul_repr. rewrite Z.mul_1_l.
  apply Ptrofs.eqm_samerepr. apply Ptrofs.eqm_sym. 
  change Ptrofs.eqm with (Zbits.eqmod Ptrofs.modulus).
  rewrite Int64.unsigned_repr_eq. change Int64.modulus with Ptrofs.modulus.
  apply Zbits.eqmod_mod. reflexivity.
Qed.

Lemma win_buf_join w bs len buf wp :
  mb_ok w -> (if len =? 0 then Some [] else mb_read w bs len) = Some buf ->
  field_compatible (tarray tuchar (Zlength (mb_val w))) [] wp ->
  (buf_at Ews len buf (offset_val bs wp) * win_rest (Zlength (mb_val w)) bs len (mb_vals w) wp)%logic
  |-- @data_at DCS.CS Ews (tarray tuchar (Zlength (mb_val w))) (mb_vals w) wp.
Proof. intros. rewrite (win_buf_split w bs len buf wp) by auto. apply derives_refl. Qed.

Lemma in_long_range x : in_long x = true -> Int64.min_signed <= x <= Int64.max_signed.
Proof.
  unfold in_long. intros H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2. rep_lia.
Qed.

Lemma strm_at_fold z sp strmp pin pout msgv gv :
  (@field_at DCS.CS Ews t_strm (DOT _next_in) (offset_val (z_next_in z) pin) strmp *
   @field_at DCS.CS Ews t_strm (DOT _avail_in) (vi (z_avail_in z)) strmp *
   @field_at DCS.CS Ews t_strm (DOT _total_in) (vl (z_total_in z)) strmp *
   @field_at DCS.CS Ews t_strm (DOT _next_out) (offset_val (Zlength (z_out z)) pout) strmp *
   @field_at DCS.CS Ews t_strm (DOT _avail_out) (vi (z_avail_out z)) strmp *
   @field_at DCS.CS Ews t_strm (DOT _total_out) (vl (z_total_out z)) strmp *
   @field_at DCS.CS Ews t_strm (DOT _msg) msgv strmp *
   @field_at DCS.CS Ews t_strm (DOT _state) sp strmp *
   st_zfuncs strmp gv *
   @field_at DCS.CS Ews t_strm (DOT _opaque) nullval strmp *
   @field_at DCS.CS Ews t_strm (DOT _adler) (vl (z_adler z)) strmp *
   @field_at_ DCS.CS Ews t_strm (DOT _reserved) strmp)%logic
  |-- strm_at z sp strmp pin pout msgv gv.
Proof. rewrite strm_at_split. apply derives_refl. Qed.

(** ** flush_pending's result (from StoredBodyHdrKit) *)
Lemma ste_mb_read_bytes b lo n l : mb_read b lo n = Some l -> mb_ok b -> Forall (fun x => 0 <= x < 256) l.
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

Lemma ste_u32_nonneg x : 0 <= u32 x.
Proof. unfold u32. apply Z.mod_pos_bound. lia. Qed.

Lemma ste_u64_bound x : 0 <= u64 x <= Int64.max_unsigned.
Proof. unfold u64. pose proof (Z.mod_pos_bound x 18446744073709551616 ltac:(lia)). rep_lia. Qed.

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
        try lia; pose proof (ste_u32_nonneg (d_pending (set_d_out s (o, m)))); lia.
Qed.

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
    { apply (ste_mb_read_bytes _ _ _ _ Hrd).
      match type of H with Some (if ?c then _ else _, _) = _ => destruct c end;
        inversion H; subst; exact Hm. }
    unfold out_put in Hop. destruct (Zlength x <=? z_avail_out z) eqn:El; [|discriminate].
    apply Z.leb_le in El. inversion Hop; subst; clear Hop.
    inversion H; subst; clear H. cbn [snd]. rewrite <- Hl in *.
    unfold strm_ranges in *. cbn [z_in z_next_in z_avail_in z_total_in z_out z_avail_out z_total_out z_adler z_msg
      set_z_out set_z_avail_out set_z_total_out].
    pose proof (Zlength_nonneg x). pose proof (ste_u64_bound (z_total_out z + Zlength x)).
    unfold u32_ok, u64_ok in *. rewrite Zlength_app.
    split; [|split; reflexivity].
    destruct Hr as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?).
    repeat split; try lia; first [assumption | apply Forall_app; split; assumption].
Qed.

Lemma ste_ranges_final s o x o' po : dstate_ranges s -> s64_ok x -> 0 <= po ->
  dstate_ranges (set_d_po (set_d_out (set_d_block_start (set_d_out s o) x) o') po).
Proof. intros H Hx Hpo. destruct s. unfold dstate_ranges in *. cbn in *. intuition. Qed.

Lemma out_at_okp o m sp pbp : out_at o m sp pbp = (!! out_ok o m && out_at o m sp pbp)%logic.
Proof.
  unfold out_at. apply pred_ext; [|apply andp_left2; apply derives_refl].
  apply andp_right; [apply andp_left1; apply derives_refl | apply derives_refl].
Qed.

(** The final fold into dfull. *)
Lemma tail_fold s o x s' z0 z' p pin pout ish R msgv gv :
  s' = set_d_po (set_d_out (set_d_block_start (set_d_out s o) x) (d_out s')) (d_po s') -> 0 <= d_po s' ->
  dstate_ranges s -> s64_ok x -> Int.min_signed <= tr_data_type (fst (d_trm s)) <= Int.max_signed ->
  strm_ranges z' -> z_in z' = z_in z0 -> msg_ok (z_msg z') msgv -> readable_share ish ->
  st_trees_frame (d_trm s) (p_s p) gv * out_at (tr_out (d_tr s')) (d_pbm s') (p_s p) (p_pbuf p) *
  sym_at (fst (d_trm s)) (p_s p) (p_pbuf p) *
  @field_at DCS.CS Ews t_ds (DOT _strm) (p_strm p) (p_s p) *
  @field_at DCS.CS Ews t_strm (DOT _data_type) (vi (tr_data_type (fst (d_trm s)))) (p_strm p) *
  @field_at DCS.CS Ews t_ds (DOT _window) (p_window p) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _window_size) (vl (d_window_size s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _w_size) (vi (d_w_size s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _w_bits) (vi (d_w_bits s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _w_mask) (vi (d_w_mask s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _high_water) (vl (d_high_water s)) (p_s p) *
  @data_at DCS.CS Ews (tarray tuchar (Zlength (mb_val (d_window s)))) (mb_vals (d_window s)) (p_window p) *
  hash_at s p *
  @field_at DCS.CS Ews t_ds (DOT _block_start) (vl x) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _match_length) (vi (d_match_length s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _prev_match) (vi (d_prev_match s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _match_available) (vi (d_match_available s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _strstart) (vi (d_strstart s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _match_start) (vi (d_match_start s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _lookahead) (vi (d_lookahead s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _prev_length) (vi (d_prev_length s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _insert) (vi (d_insert s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _slid) (vi (d_slid s)) (p_s p) *
  cfg_at s p *
  @field_at DCS.CS Ews t_ds (DOT _status) (vi (d_status s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _pending_buf_size) (vl (d_pending_buf_size s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _pending_out) (offset_val (d_po s') (p_pbuf p)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _wrap) (vi (d_wrap s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _gzhead) (p_gzhead p) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _gzindex) (vl (d_gzindex s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _method) (vi (d_method s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _last_flush) (vi (d_last_flush s)) (p_s p) *
  strm_at z' (p_s p) (p_strm p) pin pout msgv gv * in_obj ish z0 pin * out_space z' pout R
  |-- dfull s' z' p pin pout ish R msgv gv.
Proof.
  intros E Hpo Hr Hx Hdt Hz Hin Hmsg Hsh.
  unfold dfull. apply andp_right; [apply prop_right; auto|].
  unfold in_obj at 1. rewrite <- Hin. fold (in_obj ish z' pin).
  rewrite E. set (S := set_d_po (set_d_out (set_d_block_start (set_d_out s o) x) (d_out s')) (d_po s')).
  unfold dstate_at. rewrite prop_true_andp by (apply ste_ranges_final; auto).
  rewrite st_trees_at_split.
  change (st_trees_frame (d_trm S) (p_s p) gv) with (st_trees_frame (d_trm s) (p_s p) gv).
  change (sym_at (fst (d_trm S)) (p_s p) (p_pbuf p)) with (sym_at (fst (d_trm s)) (p_s p) (p_pbuf p)).
  change (dtype_at (fst (d_trm S)) (p_s p) (p_strm p)) with (dtype_at (fst (d_trm s)) (p_s p) (p_strm p)).
  change (win_at S p) with (win_at s p). change (hash_at S p) with (hash_at s p).
  change (cfg_at S p) with (cfg_at s p).
  change (out_at (tr_out (fst (d_trm S))) (snd (d_trm S)) (p_s p) (p_pbuf p))
    with (out_at (tr_out (d_tr s')) (d_pbm s') (p_s p) (p_pbuf p)).
  change (match_at S p) with
   (@field_at DCS.CS Ews t_ds (DOT _block_start) (vl x) (p_s p) *
    @field_at DCS.CS Ews t_ds (DOT _match_length) (vi (d_match_length s)) (p_s p) *
    @field_at DCS.CS Ews t_ds (DOT _prev_match) (vi (d_prev_match s)) (p_s p) *
    @field_at DCS.CS Ews t_ds (DOT _match_available) (vi (d_match_available s)) (p_s p) *
    @field_at DCS.CS Ews t_ds (DOT _strstart) (vi (d_strstart s)) (p_s p) *
    @field_at DCS.CS Ews t_ds (DOT _match_start) (vi (d_match_start s)) (p_s p) *
    @field_at DCS.CS Ews t_ds (DOT _lookahead) (vi (d_lookahead s)) (p_s p) *
    @field_at DCS.CS Ews t_ds (DOT _prev_length) (vi (d_prev_length s)) (p_s p) *
    @field_at DCS.CS Ews t_ds (DOT _insert) (vi (d_insert s)) (p_s p) *
    @field_at DCS.CS Ews t_ds (DOT _slid) (vi (d_slid s)) (p_s p))%logic.
  change (stat_at S p) with
   (@field_at DCS.CS Ews t_ds (DOT _status) (vi (d_status s)) (p_s p) *
    @field_at DCS.CS Ews t_ds (DOT _pending_buf_size) (vl (d_pending_buf_size s)) (p_s p) *
    @field_at DCS.CS Ews t_ds (DOT _pending_out) (offset_val (d_po s') (p_pbuf p)) (p_s p) *
    @field_at DCS.CS Ews t_ds (DOT _wrap) (vi (d_wrap s)) (p_s p) *
    @field_at DCS.CS Ews t_ds (DOT _gzhead) (p_gzhead p) (p_s p) *
    @field_at DCS.CS Ews t_ds (DOT _gzindex) (vl (d_gzindex s)) (p_s p) *
    @field_at DCS.CS Ews t_ds (DOT _method) (vi (d_method s)) (p_s p) *
    @field_at DCS.CS Ews t_ds (DOT _last_flush) (vi (d_last_flush s)) (p_s p))%logic.
  unfold dtype_at, win_at. rewrite prop_true_andp by exact Hdt. cancel.
  all: apply derives_refl.
Qed.

(** ** The stored block and the flush *)
Definition S_branch : statement := sub S_p2_tail [1;1;1;1;0;1;1]%nat.

Lemma st_branch_core {Espec : OracleKind} (p : dptrs) (pin pout : val) (ish : share) (rest : list val)
    (msgv : val) (gv : globals) (s : dstate) (z : strm) (flush have left : Z)
    (buf : list Z) (o : cout) (len lst : Z) (r : dstate * strm) :
  Int.min_signed <= flush <= Int.max_signed -> 0 <= have <= Int.max_unsigned -> 0 <= left <= Int.max_unsigned ->
  (left > have -> len = have) -> (left <= have -> len = left) ->
  (((flush =? Z_FINISH) && (z_avail_in z =? 0) && (len =? left))%bool = true -> lst = 1) ->
  (((flush =? Z_FINISH) && (z_avail_in z =? 0) && (len =? left))%bool = false -> lst = 0) ->
  st_buf s len = Some buf ->
  c_tr_stored_block (d_out s) buf len lst = Some o ->
  in_long (d_block_start s + len) = true ->
  c_flush_pending (set_d_block_start (set_d_out s o) (d_block_start s + len)) z = Some r ->
  semax Delta_ds
    (PROP () LOCAL (temp _left (vi left); temp _have (vi have); temp _last (vi 0); gvars gv; temp _s (p_s p);
                    temp _flush (vi flush))
     SEP (dfull s z p pin pout ish rest msgv gv; deflate_globals gv))
    S_branch
    (normal_ret_assert
      (PROP () LOCAL (temp _last (vi lst); gvars gv; temp _s (p_s p); temp _flush (vi flush))
       SEP (dfull (fst r) (snd r) p pin pout ish (rest_after z (snd r) rest) msgv gv;
            deflate_globals gv))).
Proof.
  intros Hfl Hhv Hlf HL1 HL2 HS1 HS0 Hbuf Hsb Hlong Hfp.
  cbv [S_branch S_p2_tail S_phase2 sub f_deflate_stored fn_body].
  assert (Hlen : 0 <= len <= Int.max_unsigned)
    by (destruct (Z_gt_le_dec left have); [rewrite HL1 | rewrite HL2]; lia).
  assert (Hlst : 0 <= lst <= 1)
    by (destruct (((flush =? Z_FINISH) && (z_avail_in z =? 0) && (len =? left))%bool) eqn:Eb;
        [rewrite HS1 by reflexivity | rewrite HS0 by reflexivity]; lia).
  forward_if (temp _t'15 (vi len)).
  { forward. entailer!. rewrite HL1 by lia. reflexivity. }
  { forward. entailer!. rewrite HL2 by lia. reflexivity. }
  forward.
  unfold dfull at 1. Intros. unfold dstate_at at 1. rewrite st_trees_at_split, strm_at_split.
  unfold dtype_at at 1, win_at at 1, match_at at 1. Intros.
  assert (Hai : 0 <= z_avail_in z <= Int.max_unsigned) by (unfold strm_ranges, u32_ok in H; lia).
  forward_if (temp _t'16 (bool2val ((flush =? Z_FINISH) && (z_avail_in z =? 0))%bool)).
  { forward. forward. forward. entailer!.
    destruct (Z.eqb_spec (z_avail_in z) 0), (zeq (z_avail_in z) 0); try lia; reflexivity. }
  { forward. entailer!.
    change Z_FINISH with 4; rewrite (proj2 (Z.eqb_neq _ _) H4); reflexivity. }
  forward_if (temp _t'17 (bool2val ((flush =? Z_FINISH) && (z_avail_in z =? 0) && (len =? left))%bool)).
  { forward. entailer!. rewrite H4. cbn [andb].
    destruct (Z.eqb_spec len left), (zeq len left); try lia; reflexivity. }
  { forward. entailer!. rewrite H4. reflexivity. }
  forward_if (temp _t'18 (vi lst)).
  { forward. entailer!. rewrite HS1 by exact H4. reflexivity. }
  { forward. entailer!. rewrite HS0 by exact H4. reflexivity. }
  forward.
  forward. forward.
  assert_PROP (field_compatible (tarray tuchar (Zlength (mb_val (d_window s)))) [] (p_window p)) by entailer!.
  assert (Hwok : mb_ok (d_window s)) by (unfold dstate_ranges in H2; tauto).
  rewrite (win_buf_split (d_window s) (d_block_start s) len buf (p_window p) Hwok Hbuf H4).
  Intros.
  forward_call (p_s p, p_pbuf p, tr_out (fst (d_trm s)), snd (d_trm s), offset_val (d_block_start s) (p_window p),
                Ews, buf, len, lst, o).
  { apply prop_right. assert (Pw : isptr (p_window p)) by (destruct H4; auto). cbn. unfold vl in *.
    rewrite <- (ste_add_ptr_long _ (d_block_start s) Pw). destruct (p_window p); try contradiction. cbn.
    rewrite Int.unsigned_repr by rep_lia. reflexivity. }
  pose proof (in_long_range _ Hlong) as Hbsl.
  assert (Hbs : Int64.min_signed <= d_block_start s <= Int64.max_signed)
    by (unfold dstate_ranges, s64_ok in H2; tauto).
  forward. forward.
  assert (Ebs : Vlong (Int64.add (Int64.repr (d_block_start s)) (Int64.repr (Int.unsigned (Int.repr len))))
                = vl (d_block_start s + len))
    by (rewrite Int.unsigned_repr by rep_lia; unfold vl; rewrite add64_repr; reflexivity).
  rewrite Ebs.
  forward.
  sep_apply (win_buf_join (d_window s) (d_block_start s) len buf (p_window p) Hwok Hbuf H4).
  sep_apply (strm_at_fold z (p_s p) (p_strm p) pin pout msgv gv).
  change (out_at (fst o) (snd o) (p_s p) (p_pbuf p)) with
    (out_at (tr_out (d_tr (set_d_block_start (set_d_out s o) (d_block_start s + len))))
            (d_pbm (set_d_block_start (set_d_out s o) (d_block_start s + len))) (p_s p) (p_pbuf p)).
  unfold stat_at at 1. Intros.
  change (offset_val (d_po s) (p_pbuf p)) with
    (offset_val (d_po (set_d_block_start (set_d_out s o) (d_block_start s + len))) (p_pbuf p)).
  forward_call (p_strm p, p_s p, p_pbuf p, pin, pout, msgv, rest,
                set_d_block_start (set_d_out s o) (d_block_start s + len), z, r, gv).
  rewrite (out_at_okp (tr_out (d_tr (fst r)))). Intros.
  match goal with HH : out_ok (tr_out (d_tr (fst r))) _ |- _ => rename HH into Hoo end.
  assert (Hpo : 0 <= d_po (set_d_block_start (set_d_out s o) (d_block_start s + len)))
    by (change (d_po (set_d_block_start (set_d_out s o) (d_block_start s + len))) with (d_po s);
        unfold dstate_ranges in H2; tauto).
  assert (Haz : 0 <= z_avail_out z)
    by (destruct H as (_ & _ & _ & _ & _ & _ & Ha & _); unfold u32_ok in Ha; lia).
  destruct (fp_shape _ z r Hpo Haz Hfp) as [Es Hpo'].
  destruct (fp_strm _ _ _ H Hfp (proj1 Hoo)) as [Hz' [Hin Hmsg]].
  sep_apply (tail_fold s o (d_block_start s + len) (fst r) z (snd r) p pin pout ish
               (rest_after z (snd r) rest) msgv gv Es Hpo' H2 Hbsl H3 Hz' Hin
               ltac:(rewrite Hmsg; exact H0) H1).
  entailer!.
Qed.

Lemma st_branch_frag {Espec : OracleKind} (p : dptrs) (pin pout : val) (ish : share) (rest : list val)
    (msgv : val) (gv : globals) (s : dstate) (z : strm) (flush have left : Z) (r : dstate * strm * Z) :
  Int.min_signed <= flush <= Int.max_signed -> 0 <= have <= Int.max_unsigned -> 0 <= left <= Int.max_unsigned ->
  st_branch s z flush have left = Some r ->
  semax Delta_ds
    (PROP () LOCAL (temp _left (vi left); temp _have (vi have); temp _last (vi 0); gvars gv; temp _s (p_s p);
                    temp _flush (vi flush))
     SEP (dfull s z p pin pout ish rest msgv gv; deflate_globals gv))
    S_branch
    (normal_ret_assert
      (PROP () LOCAL (temp _last (vi (snd r)); gvars gv; temp _s (p_s p); temp _flush (vi flush))
       SEP (dfull (fst (fst r)) (snd (fst r)) p pin pout ish (rest_after z (snd (fst r)) rest) msgv gv;
            deflate_globals gv))).
Proof.
  intros Hfl Hhv Hlf H.
  apply st_branch_inv in H as (buf & o & Hbuf & Hsb & Hlong & Hfp & Hlst).
  rewrite Hlst.
  apply (st_branch_core p pin pout ish rest msgv gv s z flush have left buf o (st_len have left)
           (st_last z flush (st_len have left) left) (fst r) Hfl Hhv Hlf);
    try assumption.
  - intros. unfold st_len. destruct (Z.gtb_spec left have); lia.
  - intros. unfold st_len. destruct (Z.gtb_spec left have); lia.
  - intros E. unfold st_last. rewrite E. reflexivity.
  - intros E. unfold st_last. rewrite E. reflexivity.
Qed.

(** ** Arithmetic of the head: have, min_block, left *)
Lemma ste_u32_range x : 0 <= u32 x <= Int.max_unsigned.
Proof. unfold u32. pose proof (Z.mod_pos_bound x 4294967296 ltac:(lia)). rep_lia. Qed.

Lemma hdr_eq bv : Int.shru (Int.add (Int.repr bv) (Int.repr 42)) (Int.repr 3) = Int.repr (Z.shiftr (u32 (u32 bv + 42)) 3).
Proof.
  rewrite add_repr. unfold Int.shru. f_equal. change (Int.unsigned (Int.repr 3)) with 3. f_equal.
  rewrite Int.unsigned_repr_eq. unfold u32. change 4294967296 with Int.modulus.
  rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma hdr_range x : 0 <= Z.shiftr (u32 x) 3 <= Int.max_unsigned.
Proof.
  pose proof (ste_u32_range x). rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  split; [apply Z.div_pos; lia|]. pose proof (Z.div_le_upper_bound (u32 x) 8 (u32 x) ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma ste_u64_sub_unsigned a b :
  Int64.unsigned (Int64.sub (Int64.repr a) (Int64.repr b)) = u64 (a - b).
Proof. rewrite sub64_repr, Int64.unsigned_repr_eq. reflexivity. Qed.

Lemma ste_vl_u64 x : vl (u64 x) = vl x.
Proof.
  unfold vl, u64. f_equal. change 18446744073709551616 with Int64.modulus.
  rewrite <- Int64.unsigned_repr_eq. apply Int64.repr_unsigned.
Qed.

Lemma ste_vi_u32 x : vi (u32 x) = vi x.
Proof.
  unfold vi, u32. f_equal. change 4294967296 with Int.modulus.
  rewrite <- Int.unsigned_repr_eq. apply Int.repr_unsigned.
Qed.

Lemma ste_repr_u64 x : Int.repr (u64 x) = Int.repr x.
Proof.
  apply Int.eqm_samerepr. unfold u64. apply Int.eqm_sym.
  change Int.eqm with (Zbits.eqmod Int.modulus).
  apply (Zbits.eqmod_divides 18446744073709551616).
  - apply Zbits.eqmod_mod. lia.
  - exists 4294967296. reflexivity.
Qed.

(** ** [if (_t'19) { the stored block } ] *)
Definition S_if : statement := sub S_p2_tail [1;1;1;1;0;1]%nat.

Lemma st_if_frag {Espec : OracleKind} (p : dptrs) (pin pout : val) (ish : share) (rest : list val)
    (msgv : val) (gv : globals) (s : dstate) (z : strm) (flush have left : Z) (c : bool)
    (r : dstate * strm * Z) :
  Int.min_signed <= flush <= Int.max_signed -> 0 <= have <= Int.max_unsigned -> 0 <= left <= Int.max_unsigned ->
  (if c then st_branch s z flush have left else Some (s, z, 0)) = Some r ->
  semax Delta_ds
    (PROP () LOCAL (temp _t'19 (bool2val c); temp _left (vi left); temp _have (vi have); temp _last (vi 0);
                    gvars gv; temp _s (p_s p); temp _flush (vi flush))
     SEP (dfull s z p pin pout ish rest msgv gv; deflate_globals gv))
    S_if
    (normal_ret_assert
      (PROP () LOCAL (temp _last (vi (snd r)); gvars gv; temp _s (p_s p); temp _flush (vi flush))
       SEP (dfull (fst (fst r)) (snd (fst r)) p pin pout ish (rest_after z (snd (fst r)) rest) msgv gv;
            deflate_globals gv))).
Proof.
  intros Hfl Hhv Hlf H.
  cbv [S_if S_p2_tail S_phase2 sub f_deflate_stored fn_body].
  forward_if.
  - destruct c; [|discriminate].
    eapply semax_pre; [| apply (st_branch_frag p pin pout ish rest msgv gv s z flush have left r Hfl Hhv Hlf H)].
    entailer!.
  - destruct c; [discriminate|]. inversion H; subst r. forward. cbn [fst snd]. rewrite rest_after_same.
    entailer!.
Qed.

Lemma st_last_01 s z flush have left r : st_branch s z flush have left = Some r -> snd r = 0 \/ snd r = 1.
Proof.
  intros H. apply st_branch_inv in H as (_ & _ & _ & _ & _ & _ & ->). unfold st_last.
  destruct (_ && _)%bool; auto.
Qed.

(** Model facts kept out of Floyd's sight during the forward steps (an anomaly otherwise, in a field load). *)
Definition st_hide (P : Prop) : Prop := P.
Lemma st_hide_intro (P : Prop) : P -> st_hide P.
Proof. auto. Qed.

Lemma st_tail_frag {Espec : OracleKind} (p : dptrs) (pin pout : val) (ish : share) (rest : list val)
    (msgv : val) (gv : globals) (s : dstate) (z : strm) (flush : Z) (r : dstate * strm * bstate) :
  Int.min_signed <= flush <= Int.max_signed ->
  ds_tail s z flush = Some r ->
  semax Delta_ds
    (PROP () LOCAL (temp _last (vi 0); gvars gv; temp _s (p_s p); temp _flush (vi flush))
     SEP (dfull s z p pin pout ish rest msgv gv; deflate_globals gv))
    S_p2_tail (ds_fun_post p pin pout ish rest gv z r).
Proof.
  intros Hfl H.
  rewrite ds_tail_eq in H.
  apply bind_inv in H; destruct H as [[] [Hg H]]. apply guard_inv in Hg.
  apply bind_inv in H; destruct H as [[[s1 z1] lst] [Hb H]].
  pose proof (conj Hb H) as HBH. apply st_hide_intro in HBH. clear Hb H.
  cbv [S_p2_tail S_phase2 sub f_deflate_stored fn_body]. unfold ds_fun_post.
  unfold dfull at 1. Intros. unfold dstate_at at 1. rewrite st_trees_at_split, strm_at_split.
  unfold out_at at 1, stat_at at 1, win_at at 1, match_at at 1, dtype_at at 1. Intros.
  match goal with HR : dstate_ranges s |- _ => pose proof HR as HR' end.
  match goal with HR : strm_ranges z |- _ => pose proof HR as HZ' end.
  match goal with HR : out_ok _ _ |- _ => pose proof HR as HO' end.
  unfold dstate_ranges, u32_ok, u64_ok, s64_ok in HR'. unfold strm_ranges, u32_ok in HZ'.
  destruct HO' as (_ & _ & _ & _ & Hbv & _).
  assert (Hpbs : 0 <= d_pending_buf_size s <= Int64.max_unsigned) by lia.
  assert (Hws : 0 <= d_w_size s <= Int.max_unsigned) by lia.
  assert (Hss : 0 <= d_strstart s <= Int.max_unsigned) by lia.
  assert (Hbs : Int64.min_signed <= d_block_start s <= Int64.max_signed) by lia.
  assert (Hai : 0 <= z_avail_in z <= Int.max_unsigned) by lia.
  clear HR' HZ'.
  pose proof (hdr_range (u32 (o_bi_valid (tr_out (d_tr s))) + 42)) as Hhv.
  forward. forward.
  rewrite hdr_eq.
  change (Z.shiftr (u32 (u32 (o_bi_valid (tr_out (fst (d_trm s)))) + 42)) 3) with (stored_hdr s).
  change (Z.shiftr (u32 (u32 (o_bi_valid (tr_out (d_tr s))) + 42)) 3) with (stored_hdr s) in Hhv.
  forward.
  pose proof (ste_u64_bound (d_pending_buf_size s - stored_hdr s)) as Hu.
  forward_if (temp _t'13 (vl (if u64 (d_pending_buf_size s - stored_hdr s) >? MAX_STORED then MAX_STORED
                              else u64 (d_pending_buf_size s - stored_hdr s)))).
  { forward. entailer!.
    match goal with HH : Int64.unsigned _ < Int64.unsigned _ |- _ => rename HH into Hlt end.
    rewrite Int.unsigned_repr in Hlt by rep_lia. rewrite (Int64.unsigned_repr 65535) in Hlt by rep_lia.
    rewrite Int64.unsigned_repr_eq in Hlt. change Int64.modulus with 18446744073709551616 in Hlt.
    fold (u64 (d_pending_buf_size s - stored_hdr s)) in Hlt.
    destruct (Z.gtb_spec (u64 (d_pending_buf_size s - stored_hdr s)) MAX_STORED);
      [reflexivity | unfold MAX_STORED in *; lia]. }
  { forward. forward. entailer!.
    match goal with HH : Int64.unsigned _ >= Int64.unsigned _ |- _ => rename HH into Hge end.
    rewrite Int.unsigned_repr in * by rep_lia. rewrite (Int64.unsigned_repr 65535) in Hge by rep_lia.
    rewrite Int64.unsigned_repr_eq in Hge. change Int64.modulus with 18446744073709551616 in Hge.
    fold (u64 (d_pending_buf_size s - stored_hdr s)) in Hge.
    destruct (Z.gtb_spec (u64 (d_pending_buf_size s - stored_hdr s)) MAX_STORED);
      [unfold MAX_STORED in *; lia|]. rewrite ste_vl_u64. reflexivity. }
  forward.
  assert (Eh : Vint (Int.repr (Int64.unsigned (Int64.repr
                 (if u64 (d_pending_buf_size s - stored_hdr s) >? MAX_STORED then MAX_STORED
                  else u64 (d_pending_buf_size s - stored_hdr s))))) = vi (st_have s)).
  { unfold st_have. rewrite Int64.unsigned_repr; [rewrite ste_vi_u32; reflexivity|].
    destruct (_ >? _); unfold MAX_STORED; rep_lia. }
  rewrite Eh. clear Eh.
  assert (Hhave : 0 <= st_have s <= Int.max_unsigned) by apply ste_u32_range.
  forward.
  forward_if (temp _t'14 (vi (st_mb s))).
  { forward. forward. entailer!. unfold st_mb. destruct (Z.gtb_spec (st_have s) (d_w_size s)); [reflexivity | lia]. }
  { forward. entailer!. unfold st_mb. destruct (Z.gtb_spec (st_have s) (d_w_size s)); [lia | reflexivity]. }
  assert (Hmb : 0 <= st_mb s <= Int.max_unsigned) by (unfold st_mb; destruct (_ >? _); lia).
  forward.
  pose proof (in_long_range _ Hg) as Hlg.
  forward. forward. forward.
  assert (El : Vint (Int.repr (Int64.unsigned (Int64.sub (Int64.repr (Int.unsigned (Int.repr (d_strstart s))))
                 (Int64.repr (d_block_start s))))) = vi (st_left s)).
  { rewrite Int.unsigned_repr by rep_lia. rewrite ste_u64_sub_unsigned. unfold st_left. rewrite ste_vi_u32.
    unfold vi. apply f_equal. apply ste_repr_u64. }
  rewrite El. clear El.
  assert (Hleft : 0 <= st_left s <= Int.max_unsigned) by apply ste_u32_range.
  forward_if (temp _t'19 (bool2val (st_cond s z flush))).
  { forward. entailer!. unfold st_cond. rewrite (proj2 (Z.geb_ge _ _)) by lia. reflexivity. }
  { forward_if (temp _t'20 (bool2val (negb (st_left s =? 0) || (flush =? Z_FINISH))%bool)).
    { forward. entailer!. match goal with HH : st_left s <> 0 |- _ => rewrite (proj2 (Z.eqb_neq _ _) HH) end.
      reflexivity. }
    { forward. entailer!.
      match goal with HH : Int.repr (st_left s) = Int.zero |- _ => rename HH into Hl0 end.
      change Int.zero with (Int.repr 0) in Hl0. apply repr_inj_unsigned in Hl0; [|rep_lia|rep_lia].
      rewrite Hl0, int_eq_repr_s by rep_lia. reflexivity. }
    forward_if (temp _t'21 (bool2val ((negb (st_left s =? 0) || (flush =? Z_FINISH)) && negb (flush =? Z_NO_FLUSH))%bool)).
    { forward. entailer!.
      match goal with HH : (negb (st_left s =? 0) || (flush =? Z_FINISH))%bool = true |- _ => rewrite HH end.
      rewrite int_eq_repr_s by rep_lia. reflexivity. }
    { forward. entailer!.
      match goal with HH : (negb (st_left s =? 0) || (flush =? Z_FINISH))%bool = false |- _ => rewrite HH end.
      reflexivity. }
    forward_if (temp _t'22 (bool2val ((negb (st_left s =? 0) || (flush =? Z_FINISH)) && negb (flush =? Z_NO_FLUSH)
                                      && (z_avail_in z =? 0))%bool)).
    { forward. forward. forward. entailer!.
      match goal with HH : ((negb (st_left s =? 0) || (flush =? Z_FINISH)) && negb (flush =? Z_NO_FLUSH))%bool = true
        |- _ => rewrite HH end.
      cbn [andb]. destruct (Z.eqb_spec (z_avail_in z) 0), (zeq (z_avail_in z) 0); try lia; reflexivity. }
    { forward. entailer!.
      match goal with HH : ((negb (st_left s =? 0) || (flush =? Z_FINISH)) && negb (flush =? Z_NO_FLUSH))%bool = false
        |- _ => rewrite HH end.
      reflexivity. }
    forward_if.
    { forward. forward. entailer!.
      unfold st_cond. destruct (Z.geb_spec (st_left s) (st_mb s)); [lia|]. cbn [orb].
      match goal with HH : ((negb (st_left s =? 0) || (flush =? Z_FINISH)) && negb (flush =? Z_NO_FLUSH) &&
                            (z_avail_in z =? 0))%bool = true |- _ => rewrite HH end.
      cbn [andb]. destruct (Z.leb_spec (st_left s) (st_have s)), (zlt (st_have s) (st_left s)); try lia;
        reflexivity. }
    { forward. entailer!.
      unfold st_cond. destruct (Z.geb_spec (st_left s) (st_mb s)); [lia|]. cbn [orb].
      match goal with HH : ((negb (st_left s =? 0) || (flush =? Z_FINISH)) && negb (flush =? Z_NO_FLUSH) &&
                            (z_avail_in z =? 0))%bool = false |- _ => rewrite HH end.
      reflexivity. } }
  unfold st_hide in HBH. destruct HBH as [Hb Hr].
  eapply semax_seq'.
  { eapply semax_pre;
      [| apply (st_if_frag p pin pout ish rest msgv gv s z flush (st_have s) (st_left s) (st_cond s z flush)
                (s1, z1, lst) Hfl Hhave Hleft Hb)].
    unfold dfull, dstate_at. rewrite st_trees_at_split, strm_at_split.
    unfold out_at, stat_at, win_at, match_at, dtype_at. entailer!. }
  cbn [fst snd].
  assert (Hl01 : lst = 0 \/ lst = 1).
  { destruct (st_cond s z flush); [apply st_last_01 in Hb; exact Hb | inversion Hb; auto]. }
  unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
  replace r with (if lst =? 0 then (s1, z1, need_more) else (set_d_bi_used s1 8, z1, finish_started))
    by (destruct Hl01 as [-> | ->]; cbn [Z.eqb] in Hr |- *; congruence).
  apply (st_end_frag p pin pout ish rest msgv gv s1 z1 z flush lst Hl01).
Qed.
