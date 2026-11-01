(** * deflate(): the gzip extra field (e11, [if (s->status == EXTRA_STATE) { ... }]) against its model (DeflateKit.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.DeflateKit.
Require Import Zlib.proof.zutil.Libc.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.crc32.Combine.
#[export] Existing Instance DCS.CS.
Open Scope cmodel_scope.

(** ** Masked buffers (from StoredWinKit) *)

Lemma Zlength_mb_vals b : Zlength (mb_def b) = Zlength (mb_val b) -> Zlength (mb_vals b) = Zlength (mb_val b).
Proof. intros. unfold mb_vals. apply Zlength_pb_vals. auto. Qed.

Lemma pb_vals_app b1 b2 m1 m2 : Zlength m1 = Zlength b1 ->
  pb_vals (b1 ++ b2) (m1 ++ m2) = pb_vals b1 m1 ++ pb_vals b2 m2.
Proof. intros H. unfold pb_vals. rewrite combine_app' by lia. apply map_app. Qed.

Lemma pb_vals_sublist lo hi b m : Zlength m = Zlength b ->
  pb_vals (sublist lo hi b) (sublist lo hi m) = sublist lo hi (pb_vals b m).
Proof. intros H. unfold pb_vals. rewrite sublist_map, sublist_combine. reflexivity. Qed.

Lemma pb_vals_all_true b : pb_vals b (repeat true (Z.to_nat (Zlength b))) = map vi b.
Proof.
  unfold pb_vals. rewrite Zlength_correct, Nat2Z.id.
  induction b as [|x b IH]; [reflexivity|]. cbn. f_equal. exact IH.
Qed.

Lemma mb_vals_write b lo src b' :
  Zlength (mb_def b) = Zlength (mb_val b) ->
  mb_write b lo src = Some b' ->
  mb_vals b' = sublist 0 lo (mb_vals b) ++ map vi src ++
               sublist (lo + Zlength src) (Zlength (mb_val b)) (mb_vals b) /\
  Zlength (mb_val b') = Zlength (mb_val b) /\ Zlength (mb_def b') = Zlength (mb_val b') /\
  0 <= lo /\ lo + Zlength src <= Zlength (mb_val b).
Proof.
  intros Hl H. unfold mb_write in H.
  destruct (andb (0 <=? lo) (lo + Zlength src <=? Zlength (mb_val b))) eqn:E; [|discriminate].
  apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
  inversion H; subst; clear H. pose proof (Zlength_nonneg src).
  unfold mb_vals; cbn [mb_val mb_def].
  assert (Hlen : Zlength (sublist 0 lo (mb_val b) ++ src ++
                  sublist (lo + Zlength src) (Zlength (mb_val b)) (mb_val b)) = Zlength (mb_val b)).
  { rewrite !Zlength_app, !Zlength_sublist by lia. lia. }
  assert (Hlen' : Zlength (sublist 0 lo (mb_def b) ++ repeat true (Z.to_nat (Zlength src)) ++
                  sublist (lo + Zlength src) (Zlength (mb_def b)) (mb_def b)) = Zlength (mb_val b)).
  { rewrite !Zlength_app, Zlength_repeat, !Zlength_sublist by lia. lia. }
  split; [|split; [exact Hlen|split; [lia|split; lia]]].
  rewrite !pb_vals_app.
  2: { rewrite Zlength_repeat; lia. }
  2: { rewrite !Zlength_sublist by lia. lia. }
  rewrite pb_vals_all_true. rewrite Hl.
  rewrite !pb_vals_sublist by auto. reflexivity.
Qed.

Lemma mb_ok_write b lo src b' :
  mb_ok b -> Forall (fun x => 0 <= x < 256) src -> mb_write b lo src = Some b' -> mb_ok b'.
Proof.
  intros [Hl Hd] Hs H. unfold mb_write in H.
  destruct (andb (0 <=? lo) (lo + Zlength src <=? Zlength (mb_val b))) eqn:E; [|discriminate].
  apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
  inversion H; subst; clear H. pose proof (Zlength_nonneg src).
  split; cbn [mb_val mb_def].
  - rewrite !Zlength_app, Zlength_repeat, !Zlength_sublist by lia. lia.
  - intros i Hi Hdi. rewrite !Zlength_app, !Zlength_sublist in Hi by lia.
    destruct (Z_lt_dec i lo).
    + rewrite app_Znth1 in Hdi by (rewrite Zlength_sublist; lia).
      rewrite app_Znth1 by (rewrite Zlength_sublist; lia).
      rewrite Znth_sublist in Hdi by lia. rewrite Znth_sublist by lia.
      apply Hd; [lia|]. rewrite Z.add_0_r in *. auto.
    + rewrite app_Znth2 in Hdi by (rewrite Zlength_sublist; lia).
      rewrite app_Znth2 by (rewrite Zlength_sublist; lia).
      rewrite Zlength_sublist in Hdi by lia. rewrite Zlength_sublist by lia.
      destruct (Z_lt_dec (i - (lo - 0)) (Zlength src)).
      * rewrite app_Znth1 by lia. rewrite Forall_forall in Hs. apply Hs. apply Znth_In. lia.
      * rewrite app_Znth2 in Hdi by (rewrite ?Zlength_repeat; lia).
        rewrite app_Znth2 by (rewrite ?Zlength_repeat; lia).
        rewrite Zlength_repeat in Hdi by lia.
        rewrite Znth_sublist in Hdi by lia. rewrite Znth_sublist by lia. apply Hd; [lia|]. auto.
Qed.

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

(** ** Byte arrays: slices *)

Lemma tuchar_offset0 n j p:
  field_compatible (tarray tuchar n) [] p -> 0 <= j <= n ->
  field_address0 (Tarray tuchar n noattr) [ArraySubsc j] p = offset_val j p.
Proof.
  intros. rewrite field_address0_offset.
  - simpl. f_equal. lia.
  - eapply field_compatible0_cons_Tarray; [reflexivity | auto | lia].
Qed.

Lemma data_at_tuchar_split3 sh n a b (v: list val) p:
  field_compatible (tarray tuchar n) [] p -> 0 <= a <= b -> b <= n -> Zlength v = n ->
  @data_at DCS.CS sh (tarray tuchar n) v p =
  (@data_at DCS.CS sh (tarray tuchar a) (sublist 0 a v) p *
   @data_at DCS.CS sh (tarray tuchar (b - a)) (sublist a b v) (offset_val a p) *
   @data_at DCS.CS sh (tarray tuchar (n - b)) (sublist b n v) (offset_val b p))%logic.
Proof.
  intros FC A B L.
  unfold tarray. rewrite (split3_data_at_Tarray_tuchar sh n a b v p) by (first [exact L | lia]).
  rewrite !tuchar_offset0 by (auto; lia). reflexivity.
Qed.

(** memcpy from a separate object into [lo, lo + n) of a masked buffer. *)
Lemma mb_split_in sh b wp lo n :
  Zlength (mb_def b) = Zlength (mb_val b) -> 0 <= lo -> 0 <= n -> lo + n <= Zlength (mb_val b) ->
  @data_at DCS.CS sh (tarray tuchar (Zlength (mb_val b))) (mb_vals b) wp |--
  (!! field_compatible (tarray tuchar (Zlength (mb_val b))) [] wp &&
  (@data_at DCS.CS sh (tarray tuchar lo) (sublist 0 lo (mb_vals b)) wp *
   @data_at_ DCS.CS sh (tarray tuchar n) (offset_val lo wp) *
   @data_at DCS.CS sh (tarray tuchar (Zlength (mb_val b) - (lo + n)))
     (sublist (lo + n) (Zlength (mb_val b)) (mb_vals b)) (offset_val (lo + n) wp)))%logic.
Proof.
  intros Hl H1 H2 H3. assert_PROP (field_compatible (tarray tuchar (Zlength (mb_val b))) [] wp) by entailer!.
  apply andp_right; [apply prop_right; auto|].
  rewrite (data_at_tuchar_split3 sh _ lo (lo + n)) by (rewrite ?Zlength_mb_vals; auto; lia).
  replace (lo + n - lo) with n by lia. cancel.
Qed.

Lemma mb_join_in sh b wp lo src b' :
  Zlength (mb_def b) = Zlength (mb_val b) -> mb_write b lo src = Some b' ->
  field_compatible (tarray tuchar (Zlength (mb_val b))) [] wp ->
  (@data_at DCS.CS sh (tarray tuchar lo) (sublist 0 lo (mb_vals b)) wp *
   @data_at DCS.CS sh (tarray tuchar (Zlength src)) (map vi src) (offset_val lo wp) *
   @data_at DCS.CS sh (tarray tuchar (Zlength (mb_val b) - (lo + Zlength src)))
     (sublist (lo + Zlength src) (Zlength (mb_val b)) (mb_vals b)) (offset_val (lo + Zlength src) wp))%logic |--
  @data_at DCS.CS sh (tarray tuchar (Zlength (mb_val b'))) (mb_vals b') wp.
Proof.
  intros Hl Hw FC. destruct (mb_vals_write _ _ _ _ Hl Hw) as (E & L1 & L2 & H1 & H2).
  pose proof (Zlength_nonneg src). pose proof (Zlength_mb_vals b Hl).
  rewrite L1, (data_at_tuchar_split3 sh _ lo (lo + Zlength src) (mb_vals b') wp)
    by (rewrite ?L1 in *; rewrite ?Zlength_mb_vals; auto; lia).
  rewrite E.
  set (V := mb_vals b) in *. set (L := Zlength (mb_val b)) in *. set (n := Zlength src) in *.
  assert (A1 : sublist 0 lo (sublist 0 lo V ++ map vi src ++ sublist (lo + n) L V) = sublist 0 lo V) by list_solve.
  assert (A2 : sublist lo (lo + n) (sublist 0 lo V ++ map vi src ++ sublist (lo + n) L V) = map vi src) by list_solve.
  assert (A3 : sublist (lo + n) L (sublist 0 lo V ++ map vi src ++ sublist (lo + n) L V) = sublist (lo + n) L V)
    by list_solve.
  rewrite A1, A2, A3. replace (lo + n - lo) with n by lia. cancel.
Qed.

(** The extra field in three slices; the middle one is a memcpy source. *)
Lemma obj_split sh x xp lo n :
  field_compatible (tarray tuchar (Zlength x)) [] xp -> 0 <= lo -> 0 <= n -> lo + n <= Zlength x ->
  @data_at DCS.CS sh (tarray tuchar (Zlength x)) (map vi x) xp =
  (@data_at DCS.CS sh (tarray tuchar lo) (sublist 0 lo (map vi x)) xp *
   @data_at DCS.CS sh (tarray tuchar n) (byte_vals (sublist lo (lo + n) x)) (offset_val lo xp) *
   @data_at DCS.CS sh (tarray tuchar (Zlength x - (lo + n))) (sublist (lo + n) (Zlength x) (map vi x))
     (offset_val (lo + n) xp))%logic.
Proof.
  intros FC H1 H2 H3.
  rewrite (data_at_tuchar_split3 sh _ lo (lo + n)) by (rewrite ?Zlength_map; auto; lia).
  replace (lo + n - lo) with n by lia. unfold byte_vals. rewrite <- sublist_map. reflexivity.
Qed.

(** ** The gz_header, opened at the fields the stage reads *)
Definition gzh_rest (sh : share) (h : gzh) (hp np cp : val) : mpred :=
  (@field_at DCS.CS sh t_gzh (DOT _text) (vi (gz_text h)) hp *
  @field_at DCS.CS sh t_gzh (DOT _time) (vl (gz_time h)) hp *
  @field_at DCS.CS sh t_gzh (DOT _os) (vi (gz_os h)) hp *
  @field_at DCS.CS sh t_gzh (DOT _name) np hp *
  @field_at DCS.CS sh t_gzh (DOT _comment) cp hp *
  (EX v : val, @field_at DCS.CS sh t_gzh (DOT _xflags) v hp) *
  (EX v : val, @field_at DCS.CS sh t_gzh (DOT _extra_max) v hp) *
  (EX v : val, @field_at DCS.CS sh t_gzh (DOT _name_max) v hp) *
  (EX v : val, @field_at DCS.CS sh t_gzh (DOT _comm_max) v hp) *
  (EX v : val, @field_at DCS.CS sh t_gzh (DOT _done) v hp) *
  opt_obj sh (gz_name h) np * opt_obj sh (gz_comment h) cp)%logic.

Lemma gzh_at_open sh h hp xp np cp :
  gzh_at sh h hp xp np cp =
  (!! (readable_share sh /\ gzh_ok h) &&
   (@field_at DCS.CS sh t_gzh (DOT _extra) xp hp *
    @field_at DCS.CS sh t_gzh (DOT _extra_len) (vi (gz_extra_len h)) hp *
    @field_at DCS.CS sh t_gzh (DOT _hcrc) (vi (gz_hcrc h)) hp *
    opt_obj sh (gz_extra h) xp * gzh_rest sh h hp np cp))%logic.
Proof.
  unfold gzh_at, gzh_rest. apply pred_ext; Intros; entailer!.
Qed.

Lemma gzh_at_fold sh h hp xp np cp : readable_share sh -> gzh_ok h ->
  @field_at DCS.CS sh t_gzh (DOT _extra) xp hp *
  @field_at DCS.CS sh t_gzh (DOT _extra_len) (vi (gz_extra_len h)) hp *
  @field_at DCS.CS sh t_gzh (DOT _hcrc) (vi (gz_hcrc h)) hp *
  opt_obj sh (gz_extra h) xp * gzh_rest sh h hp np cp |-- gzh_at sh h hp xp np cp.
Proof. intros. rewrite gzh_at_open. entailer!. Qed.

(** [(extra_len & 0xffff) - gzindex] as the C computes it (uInt operand converted to ulg). *)
Lemma overridePost_twice Q J R : overridePost Q (overridePost J R) = overridePost Q R.
Proof. destruct R; reflexivity. Qed.

(** [q == Z_NULL] is defined for the extra pointer (as in StageGzip.v). *)
Lemma opt_obj_tc sh o q Q : readable_share sh ->
  opt_obj sh o q * Q |-- denote_tc_test_eq q (Vlong (Int64.repr 0)).
Proof.
  intros Hsh. apply denote_tc_test_eq_split; [|apply valid_pointer_null].
  apply sepcon_valid_pointer1.
  destruct o as [b|]; unfold opt_obj.
  - apply andp_left2. destruct (Zlength b =? 0) eqn:E.
    + apply sepcon_valid_pointer2. apply malloc_token_valid_pointer. simpl. lia.
    + rewrite sepcon_emp. apply data_at_valid_ptr; [apply readable_nonidentity; auto|].
      apply Z.eqb_neq in E. pose proof (Zlength_nonneg b). simpl. rewrite Z.max_r by lia. lia.
  - Intros. subst. apply valid_pointer_null.
Qed.

Lemma out_space_len z p R : out_space z p R |-- !! (Zlength R = z_avail_out z) && out_space z p R.
Proof. unfold out_space. entailer!. Qed.

Lemma RA_normal_override Q R : RA_normal (overridePost Q R) = Q.
Proof. destruct R; reflexivity. Qed.

Lemma left_val el gi : 0 <= el <= Int.max_unsigned ->
  Int64.sub (Int64.repr (Int.unsigned (Int.and (Int.repr el) (Int.repr 65535)))) (Int64.repr gi) =
  Int64.repr (u64 (Z.land el 65535 - gi)).
Proof.
  intros Hel. rewrite repr_u64. unfold Int.and. rewrite (Int.unsigned_repr el) by rep_lia.
  change (Int.unsigned (Int.repr 65535)) with 65535.
  assert (0 <= Z.land el 65535 < 65536).
  { change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. reflexivity. }
  rewrite Int.unsigned_repr by rep_lia. apply sub64_repr.
Qed.

(** ** Back to [dfull] after changes of status, gzindex, last_flush, the bit output and pending_out *)
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

(** The states of the stage in the form of [ff_close]. *)
Lemma st_iter_eq s pb n g o po lf :
  set_d_last_flush (set_d_po (set_d_out (set_d_gzindex (set_d_pending (set_d_pb s pb) n) g) o) po) lf =
  set_d_po (set_d_out (set_d_last_flush (set_d_gzindex (set_d_status s (d_status s)) g) lf) o) po.
Proof. destruct s as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? t ?]; destruct t; reflexivity. Qed.

Lemma st_iter_eq' s pb n g o po :
  set_d_po (set_d_out (set_d_gzindex (set_d_pending (set_d_pb s pb) n) g) o) po =
  set_d_po (set_d_out (set_d_last_flush (set_d_gzindex (set_d_status s (d_status s)) g) (d_last_flush s)) o) po.
Proof. destruct s as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? t ?]; destruct t; reflexivity. Qed.

Lemma st_tail_eq s pb n :
  set_d_gzindex (set_d_pending (set_d_pb s pb) n) 0 =
  set_d_po (set_d_out (set_d_last_flush (set_d_gzindex (set_d_status s (d_status s)) 0) (d_last_flush s))
    (mkOut (mb_val pb) n (o_bi_buf (tr_out (d_tr s))) (o_bi_valid (tr_out (d_tr s))) (o_bi_used (tr_out (d_tr s))),
     mb_def pb)) (d_po s).
Proof. destruct s as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? t ?]; destruct t; reflexivity. Qed.

Lemma st_status_eq s st :
  set_d_status s st =
  set_d_po (set_d_out (set_d_last_flush (set_d_gzindex (set_d_status s st) (d_gzindex s)) (d_last_flush s))
    (d_out s)) (d_po s).
Proof. destruct s as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? t ?]; destruct t; reflexivity. Qed.

(** ** HCRC_UPDATE(beg) *)
Lemma hcrc_shape h s z beg z' : strm_ranges z -> mb_ok (d_pb s) -> c_hcrc_update h s z beg = Some z' ->
  z' = set_z_adler z (z_adler z') /\ strm_ranges z'.
Proof.
  intros Hz Hok H. unfold c_hcrc_update in H.
  destruct (_ && _)%bool.
  - destruct (mb_read (d_pb s) beg (d_pending s - beg)) as [bytes|] eqn:Hr; [|discriminate].
    cbn in H. inversion H; subst; clear H.
    destruct (mb_read_vals _ _ _ _ Hok Hr) as (_ & _ & _ & _ & _ & _ & Fb).
    assert (Hb : is_bytes bytes).
    { unfold is_bytes. eapply Forall_impl; [|exact Fb]. intros a Ha. simpl in Ha. rep_lia. }
    pose proof (ref_crc32_range (z_adler z) bytes Hb) as Hc. unfold is32 in Hc.
    split; [destruct z; reflexivity|]. apply strm_ranges_set_adler; auto. rep_lia.
  - inversion H; subst. split; [destruct z'; reflexivity | auto].
Qed.

(** ** The parts of the stage *)
Definition S_eloop : statement :=
  ltac:(let t := eval cbv [S_extra nth_stmt df_body f_deflate fn_body] in S_extra in
        lazymatch t with context [Ssequence (Sloop ?a ?b) ?c] => exact (Sloop a b) end).
Definition S_etail : statement :=
  ltac:(let t := eval cbv [S_extra nth_stmt df_body f_deflate fn_body] in S_extra in
        lazymatch t with context [Ssequence (Sloop ?a ?b) ?c] => exact c end).

Definition ext_locals (p : dptrs) (flush : Z) (gv : globals) (beg lft : Z) : list localdef :=
  temp _beg (Vlong (Int64.repr beg)) :: temp _left (Vlong (Int64.repr lft)) :: df_locals p flush gv.

(** The loop invariant: the state [(s1, z1, beg, left)] of the model loop, which runs to its result [e]. *)
Definition ext_inv (p : dptrs) (pin pout : val) (ish : share) (R : list val) (msgv : val) (gv : globals)
    (flush : Z) (z : strm) (X : mpred) (h : gzh) (x : list Z)
    (e : (dstate * strm * Z * Z) + (dstate * strm)) : environ -> mpred :=
  EX s1 : dstate, EX z1 : strm, EX beg : Z, EX lft : Z,
  PROPx [runs (extra_body h x) (s1, z1, beg, lft) e; out_grow z z1; u64_ok beg; u64_ok lft]
  (LOCALx (ext_locals p flush gv beg lft)
  (SEPx [dfull s1 z1 p pin pout ish (rest_after z z1 R) msgv gv; deflate_globals gv; X])).

(** The loop left by its test ([e = inl ..]). *)
Definition ext_exit (p : dptrs) (pin pout : val) (ish : share) (R : list val) (msgv : val) (gv : globals)
    (flush : Z) (z : strm) (X : mpred) (e : (dstate * strm * Z * Z) + (dstate * strm)) : environ -> mpred :=
  EX s1 : dstate, EX z1 : strm, EX beg : Z, EX lft : Z,
  PROPx [e = inl (s1, z1, beg, lft); out_grow z z1; u64_ok beg; u64_ok lft]
  (LOCALx (ext_locals p flush gv beg lft)
  (SEPx [dfull s1 z1 p pin pout ish (rest_after z z1 R) msgv gv; deflate_globals gv; X])).

(** ** The pieces of the loop body *)
Definition EL_body : statement := ltac:(let t := eval cbv [S_eloop] in S_eloop in
  lazymatch t with Sloop ?b _ => exact b end).
Definition EL_hc : statement := ltac:(let t := eval cbv [EL_body] in EL_body in
  lazymatch t with context [Sloop ?c Sbreak] => exact c end).

Definition el_locals (p : dptrs) (flush : Z) (gv : globals) (beg lft copy : Z) : list localdef :=
  temp _copy (vl copy) :: ext_locals p flush gv beg lft.

Lemma add_ptr_long_tuchar pbp beg : isptr pbp -> force_val (sem_add_ptr_long tuchar pbp (vl beg)) = offset_val beg pbp.
Proof.
  destruct pbp; try contradiction. intros _. unfold vl. simpl.
  f_equal. rewrite Ptrofs.mul_commut, Ptrofs.mul_one. f_equal.
  unfold Ptrofs.of_int64. apply Ptrofs.eqm_samerepr. apply Ptrofs.eqm_sym.
  unfold Ptrofs.eqm. rewrite Int64.unsigned_repr_eq.
  change Ptrofs.modulus with Int64.modulus. apply Zbits.eqmod_mod. reflexivity.
Qed.

Lemma cmpu_gt64 a b : 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.cmpu Cgt (Int64.repr a) (Int64.repr b) = (a >? b).
Proof.
  intros Ha Hb. unfold Int64.cmpu. rewrite Int64.ltu_not. unfold Int64.ltu, Int64.eq.
  rewrite !Int64.unsigned_repr by auto. zfin.
Qed.

Definition hc_cond (h : gzh) (s : dstate) (beg : Z) : bool := (negb (gz_hcrc h =? 0) && (d_pending s >? beg))%bool.

(** The gz_header opened at hcrc. *)
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

Lemma gzh_hc_unfold sh h hp xp np cp :
  gzh_at sh h hp xp np cp |--
  (!! (readable_share sh /\ gzh_ok h) &&
   (@field_at DCS.CS sh t_gzh (DOT _hcrc) (vi (gz_hcrc h)) hp * gzh_nohc sh h hp xp np cp))%logic.
Proof. unfold gzh_at, gzh_nohc. Intros. entailer!. Qed.

Lemma gzh_hc_fold sh h hp xp np cp : readable_share sh -> gzh_ok h ->
  @field_at DCS.CS sh t_gzh (DOT _hcrc) (vi (gz_hcrc h)) hp * gzh_nohc sh h hp xp np cp |-- gzh_at sh h hp xp np cp.
Proof. intros. unfold gzh_at, gzh_nohc. entailer!. Qed.

(** [dfull] opened at the fields HCRC_UPDATE reads. *)
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

(** HCRC_UPDATE(beg) in the loop (port of StageName.hc1_ok). *)
Lemma el_hc_ok {Espec : OracleKind} p pin pout ish R msgv gv flush s z beg lft copy h hsh xp np cp W z' :
  c_hcrc_update h s z beg = Some z' -> 0 <= beg <= Int64.max_unsigned ->
  @semax DCS.CS Espec Delta_df
    (PROPx [] (LOCALx (el_locals p flush gv beg lft copy)
     (SEPx [dfull s z p pin pout ish R msgv gv; deflate_globals gv; gzh_at hsh h (p_gzhead p) xp np cp; W])))
    (Sloop EL_hc Sbreak)
    (normal_ret_assert (PROPx [] (LOCALx (el_locals p flush gv beg lft copy)
     (SEPx [dfull s z' p pin pout ish R msgv gv; deflate_globals gv; gzh_at hsh h (p_gzhead p) xp np cp; W])))).
Proof.
  intros Hc Hbeg. unfold el_locals, ext_locals, df_locals. cbv [EL_hc].
  sep_apply (dfull_gz_open s z p pin pout ish R msgv gv). Intros.
  apply semax_loop_nocontinue.
  sep_apply (gzh_hc_unfold hsh h (p_gzhead p) xp np cp). Intros.
  forward. forward.
  unfold out_at. Intros.
  forward_if_temp _t'53 (Vint (Int.repr (if hc_cond h s beg then 1 else 0))).
  { forward. forward. entailer!.
    unfold hc_cond. rewrite (proj2 (Z.eqb_neq _ _) H6'). cbn [negb andb].
    rewrite cmpu_gt64 by (open_dranges H1; unfold d_pending; destruct H5 as (_ & _ & ? & _); lia).
    unfold d_pending. destruct (_ >? _); reflexivity. }
  { forward. entailer!. unfold hc_cond.
    replace (gz_hcrc h) with 0 by (destruct H4 as (_ & _ & _ & _ & ?); symmetry; apply repr_inj_signed; auto; rep_lia).
    reflexivity. }
  forward_if (PROPx [] (LOCALx [temp _copy (vl copy); temp _beg (Vlong (Int64.repr beg));
     temp _left (Vlong (Int64.repr lft)); temp _strm (p_strm p); temp _s (p_s p);
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
    1: (entailer!; simpl; change (Vlong (Int64.repr beg)) with (vl beg); rewrite add_ptr_long_tuchar; [reflexivity|];
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

(** ** One iteration of the model loop *)
Lemma eb_exit h x s z beg lft e : runs (extra_body h x) (s, z, beg, lft) e ->
  (u64 (d_pending s + lft) >? d_pending_buf_size s) = false -> e = inl (s, z, beg, lft).
Proof.
  intros Hr Ht. destruct (runs_inv _ _ _ Hr) as [Hb | (a' & Hb & _)]; unfold extra_body in Hb; rewrite Ht in Hb;
    inversion Hb; auto.
Qed.

Lemma eb_step h x s z beg lft e : runs (extra_body h x) (s, z, beg, lft) e ->
  (u64 (d_pending s + lft) >? d_pending_buf_size s) = true ->
  exists bytes pb z2 s3 z3,
  rds x (d_gzindex s) (u64 (d_pending_buf_size s - d_pending s)) = Some bytes /\
  mb_write (d_pb s) (d_pending s) bytes = Some pb /\
  c_hcrc_update h (set_d_pending (set_d_pb s pb) (d_pending_buf_size s)) z beg = Some z2 /\
  c_flush_pending (set_d_gzindex (set_d_pending (set_d_pb s pb) (d_pending_buf_size s))
                     (u64 (d_gzindex s + u64 (d_pending_buf_size s - d_pending s)))) z2 = Some (s3, z3) /\
  (if d_pending s3 =? 0 then runs (extra_body h x) (s3, z3, 0, u64 (lft - u64 (d_pending_buf_size s - d_pending s))) e
   else e = inr (set_d_last_flush s3 (-1), z3)).
Proof.
  intros Hr Ht.
  destruct (runs_inv _ _ _ Hr) as [Hb | (a' & Hb & Hr')]; unfold extra_body in Hb; rewrite Ht in Hb;
    inv_bind Hb; rename x0 into bytes, Ha into Hby; inv_bind Hb; rename x0 into pb, Ha into Hpb;
    inv_bind Hb; rename x0 into z2, Ha into Hz2; inv_bind Hb; destruct x0 as [s3 z3]; rename Ha into Hf;
    exists bytes, pb, z2, s3, z3; (split; [auto|split; [auto|split; [auto|split; [auto|]]]]).
  - destruct (d_pending s3 =? 0); cbn in Hb; inversion Hb; auto.
  - destruct (d_pending s3 =? 0); cbn in Hb; inversion Hb; subst; auto.
Qed.

Lemma ltu_test a b c : 0 <= c <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr c) (Int64.add (Int64.repr a) (Int64.repr b)) = (u64 (a + b) >? c).
Proof.
  intros Hc. unfold Int64.ltu. rewrite add64_repr, (Int64.unsigned_repr c) by auto.
  rewrite Int64.unsigned_repr_eq. unfold u64.
  change Int64.modulus with 18446744073709551616.
  rewrite Z.gtb_ltb. destruct (zlt c ((a + b) mod 18446744073709551616)); symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

Lemma obj_join sh x xp lo n bytes :
  field_compatible (tarray tuchar (Zlength x)) [] xp -> 0 <= lo -> 0 <= n -> lo + n <= Zlength x ->
  bytes = sublist lo (lo + n) x -> Zlength bytes = n ->
  @data_at DCS.CS sh (tarray tuchar lo) (sublist 0 lo (map vi x)) xp *
  @data_at DCS.CS sh (tarray tuchar (Zlength bytes)) (map vi bytes) (offset_val lo xp) *
  @data_at DCS.CS sh (tarray tuchar (Zlength x - (lo + Zlength bytes)))
    (sublist (lo + Zlength bytes) (Zlength x) (map vi x)) (offset_val (lo + Zlength bytes) xp)
  |-- @data_at DCS.CS sh (tarray tuchar (Zlength x)) (map vi x) xp.
Proof.
  intros FC H1 H2 H3 Eb Lb. rewrite Lb. rewrite (obj_split sh x xp lo n) by auto. subst bytes.
  apply derives_refl.
Qed.

Lemma opt_obj_fold sh b p : Forall (fun x => 0 <= x < 256) b ->
  @data_at DCS.CS sh (tarray tuchar (Zlength b)) (map vi b) p *
  (if Zlength b =? 0 then @malloc_token DCS.CS Ews (tarray tuchar 0) p else emp) |-- opt_obj sh (Some b) p.
Proof. intros Hb. unfold opt_obj. apply andp_right; [apply prop_right; exact Hb | apply derives_refl]. Qed.

Lemma pend_eq s pb n :
  set_d_pending (set_d_pb s pb) n =
  set_d_po (set_d_out s (mkOut (mb_val pb) n (o_bi_buf (tr_out (d_tr s))) (o_bi_valid (tr_out (d_tr s)))
                          (o_bi_used (tr_out (d_tr s))), mb_def pb)) (d_po s).
Proof. destruct s as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? t ?]; destruct t; reflexivity. Qed.

Lemma gzi_eq' s g : set_d_gzindex s g =
  set_d_po (set_d_out (set_d_last_flush (set_d_gzindex (set_d_status s (d_status s)) g) (d_last_flush s))
    (tr_out (d_tr s), d_pbm s)) (d_po s).
Proof. destruct s as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? t ?]; destruct t; reflexivity. Qed.

Lemma hcrc_same h s z beg z' : c_hcrc_update h s z beg = Some z' ->
  z_out z' = z_out z /\ z_avail_out z' = z_avail_out z /\ z_in z' = z_in z /\ z_msg z' = z_msg z.
Proof.
  unfold c_hcrc_update. intros H. destruct (_ && _)%bool.
  - inv_bind H. inversion H; subst z'. cbn. auto.
  - inversion H; subst z'. auto.
Qed.

Lemma lf_comm s o po v : set_d_last_flush (set_d_po (set_d_out s o) po) v = set_d_po (set_d_out (set_d_last_flush s v) o) po.
Proof. reflexivity. Qed.

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

Ltac forward_if_prop P :=
  match goal with |- semax _ (PROPx ?Ps (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx (P :: Ps) (LOCALx Q (SEPx R)))
  end.

Lemma el_body_ok {Espec : OracleKind} p pin pout ish R msgv gv flush z hsh xp np cp W h x e res :
  0 <= flush <= 5 -> gz_extra h = Some x -> Forall (fun b => 0 <= b < 256) x -> Zlength R = z_avail_out z ->
  (forall s' z', e = inr (s', z') -> res = (s', z', Some Z_OK)) ->
  @semax DCS.CS Espec Delta_df
    (ext_inv p pin pout ish R msgv gv flush z (gzh_at hsh h (p_gzhead p) xp np cp * W)%logic h x e)
    EL_body
    (loop1_ret_assert (ext_inv p pin pout ish R msgv gv flush z (gzh_at hsh h (p_gzhead p) xp np cp * W)%logic h x e)
      (overridePost (ext_exit p pin pout ish R msgv gv flush z (gzh_at hsh h (p_gzhead p) xp np cp * W)%logic e)
       (stage_post p pin pout ish R gv flush z (gzh_at hsh h (p_gzhead p) xp np cp * W)%logic res))).
Proof.
  intros Hfl Hx Hxb HR Hres. destruct res as [[sr zr] orr].
  unfold loop1_ret_assert, overridePost, stage_post. cbv beta iota zeta.
  unfold ext_inv. Intros s1 z1 beg lft. rename H into Hrun, H0 into Hg1, H1 into Hbeg, H2 into Hlft.
  unfold ext_locals, df_locals. cbv [EL_body].
  sep_apply (dfull_flush_open s1 z1 p pin pout ish (rest_after z z1 R) msgv gv). Intros.
  unfold flush_frame, out_at. Intros.
  forward. forward.
  sep_apply (out_at_fold (tr_out (d_tr s1)) (d_pbm s1) (p_s p) (p_pbuf p)); auto.
  sep_apply (flush_frame_fold s1 z1 p pin ish gv); auto.
  sep_apply (dfull_flush_back s1 z1 p pin pout ish (rest_after z z1 R) msgv gv); auto.
  forward_if.
  2: { assert (Ht : (u64 (d_pending s1 + lft) >? d_pending_buf_size s1) = false).
       { rewrite <- ltu_test by (open_dranges H1; auto). exact H4. }
       pose proof (eb_exit _ _ _ _ _ _ _ Hrun Ht). subst e.
       forward.
       unfold ext_exit, ext_locals, df_locals. Exists s1 z1 beg lft. entailer!. }
  assert (Ht : (u64 (d_pending s1 + lft) >? d_pending_buf_size s1) = true).
  { rewrite <- ltu_test by (open_dranges H1; auto). exact H4. }
  destruct (eb_step _ _ _ _ _ _ _ Hrun Ht) as (bytes & pb & z2 & s3 & z3 & Hrd & Hpb & Hz2 & Hfp & Hif).
  clear Hrun H4.
  set (copy := u64 (d_pending_buf_size s1 - d_pending s1)) in *.
  set (gi := d_gzindex s1) in *.
  assert (Hrds : 0 <= gi /\ 0 <= copy /\ gi + copy <= Zlength x /\ bytes = sublist gi (gi + copy) x).
  { unfold rds in Hrd. destruct (_ && _)%bool eqn:Er; [|discriminate]. inversion Hrd; subst bytes.
    rewrite !andb_true_iff in Er. destruct Er as [[E1 E2] E3]. apply Z.leb_le in E1, E2, E3. auto. }
  destruct Hrds as (Hgi & Hcp & Hgx & Eb).
  assert (Lb : Zlength bytes = copy) by (rewrite Eb, Zlength_sublist by lia; lia).
  assert (Hbb : Forall (fun b => 0 <= b < 256) bytes) by (rewrite Eb; apply Forall_sublist; auto).
  pose proof H2 as (Hmb1 & _ & _ & _ & _ & _).
  destruct (mb_vals_write _ _ _ _ (proj1 Hmb1) Hpb) as (Ewv & Lpb & Ldpb & Hpe0 & Hpe1).
  sep_apply (dfull_flush_open s1 z1 p pin pout ish (rest_after z z1 R) msgv gv). Intros.
  unfold flush_frame, out_at. Intros.
  forward. forward. forward.
  replace (Int64.sub (Int64.repr (d_pending_buf_size s1)) (Int64.repr (o_pending (tr_out (d_tr s1)))))
    with (Int64.repr copy) by (unfold copy; rewrite repr_u64, sub64_repr; reflexivity).
  rewrite gzh_at_open. Intros.
  rewrite Hx. unfold opt_obj. Intros.
  assert_PROP (field_compatible (tarray tuchar (Zlength x)) [] xp) as FCx by entailer!.
  forward. forward. forward. forward. forward.
  rewrite (obj_split hsh x xp gi copy) by auto.
  rewrite <- Eb.
  change (@data_at DCS.CS Ews (tarray tuchar (Zlength (o_buf (tr_out (d_tr s1))))) (pb_vals (o_buf (tr_out (d_tr s1))) (d_pbm s1)) (p_pbuf p))
    with (@data_at DCS.CS Ews (tarray tuchar (Zlength (mb_val (d_pb s1)))) (mb_vals (d_pb s1)) (p_pbuf p)).
  assert (Hl1 : Zlength (mb_def (d_pb s1)) = Zlength (mb_val (d_pb s1))) by exact (proj1 Hmb1).
  assert (Hl2 : d_pending s1 + copy <= Zlength (mb_val (d_pb s1))) by (rewrite <- Lb; exact Hpe1).
  sep_apply (mb_split_in Ews (d_pb s1) (p_pbuf p) (d_pending s1) copy Hl1 Hpe0 Hcp Hl2).
  Intros.
  replace copy with (Zlength bytes) by auto.
  forward_call (Ews, offset_val (d_pending s1) (p_pbuf p), hsh, offset_val gi xp, bytes).
  { entailer!. simpl. pose proof (field_compatible_isptr _ _ _ FCx). pose proof (field_compatible_isptr _ _ _ H6).
    rewrite !add_ptr_long_tuchar by auto. reflexivity. }
  { split; [unfold bytes_ok; eapply Forall_impl; [|exact Hbb]; intros; simpl in *; rep_lia | rewrite Lb; apply u64_range]. }
  change (byte_vals bytes) with (map vi bytes).
  sep_apply (obj_join hsh x xp gi copy bytes FCx Hgi Hcp Hgx Eb Lb).
  sep_apply (mb_join_in Ews (d_pb s1) (p_pbuf p) (d_pending s1) bytes pb Hl1 Hpb H6).
  forward. forward.
  assert (Hok2 : out_ok (mkOut (mb_val pb) (d_pending_buf_size s1) (o_bi_buf (tr_out (d_tr s1)))
                           (o_bi_valid (tr_out (d_tr s1))) (o_bi_used (tr_out (d_tr s1)))) (mb_def pb)).
  { pose proof (mb_ok_write _ _ _ _ Hmb1 Hbb Hpb) as Hm. destruct H2 as (_ & Hb2 & _ & Hb4 & Hb5 & Hb6).
    open_dranges H1. cbn [mb_val] in Lpb.
    split; [destruct pb; exact Hm|]. cbn [o_buf o_pending o_bi_buf o_bi_valid o_bi_used].
    rewrite Lpb. repeat split; auto; lia. }
  sep_apply (opt_obj_fold hsh x xp Hxb). rewrite <- Hx.
  sep_apply (gzh_at_fold hsh h (p_gzhead p) xp np cp); auto.
  set (ob2 := mkOut (mb_val pb) (d_pending_buf_size s1) (o_bi_buf (tr_out (d_tr s1)))
                           (o_bi_valid (tr_out (d_tr s1))) (o_bi_used (tr_out (d_tr s1)))) in *.
  sep_apply (out_at_fold ob2 (mb_def pb) (p_s p) (p_pbuf p) Hok2).
  sep_apply (flush_frame_fold s1 z1 p pin ish gv); auto.
  sep_apply (dfull_out_close s1 z1 z1 ob2 (mb_def pb) (d_po s1) p pin pout ish (rest_after z z1 R) msgv gv); auto.
  { open_dranges H1. auto. }
  unfold ob2. rewrite <- pend_eq.
  set (s2 := set_d_pending (set_d_pb s1 pb) (d_pending_buf_size s1)) in *.
  rewrite Lb.
  eapply semax_seq'.
  { eapply semax_pre; [| apply (el_hc_ok p pin pout ish (rest_after z z1 R) msgv gv flush s2 z1 beg lft copy h hsh xp np cp W z2 Hz2 Hbeg)].
    unfold el_locals, ext_locals, df_locals. entailer!. }
  clear Ewv Lpb Ldpb Hpe1 Hl1 Hl2 H6 FCx Hok2 Hmb1 Hrd Eb Hbb.
  destruct (hcrc_same _ _ _ _ _ Hz2) as (Eo1 & Ea1 & Ei1 & Em1).
  unfold el_locals, ext_locals, df_locals, MORE_COMMANDS, abbreviate.
  (* s->gzindex += copy *)
  sep_apply (dfull_flush_open s2 z2 p pin pout ish (rest_after z z1 R) msgv gv). Intros.
  unfold flush_frame. Intros.
  forward. forward.
  change (d_gzindex s2) with gi.
  rewrite add64_repr. change (Int64.repr (d_gzindex s1 + copy)) with (Int64.repr (gi + copy)).
  rewrite <- (repr_u64 (gi + copy)). change (Vlong (Int64.repr (u64 (gi + copy)))) with (vl (u64 (gi + copy))).
  rewrite (gzi_eq' s2 (u64 (gi + copy))) in Hfp.
  sep_apply (ff_close s2 z2 z2 (d_status s2) (u64 (gi + copy)) (d_last_flush s2) (tr_out (d_tr s2)) (d_pbm s2) (d_po s2)
               p pin pout ish (rest_after z z1 R) msgv gv); auto.
  1-4: (open_dranges H8; unfold s32_ok, u64_ok in *; auto; try apply u64_range).
  set (s2' := set_d_po _ _) in Hfp |- *. clearbody s2'.
  (* flush_pending(strm) *)
  sep_apply (dfull_flush_open s2' z2 p pin pout ish (rest_after z z1 R) msgv gv). Intros.
  forward_call (p_strm p, p_s p, p_pbuf p, pin, pout, msgv, rest_after z z1 R, s2', z2, (s3, z3), gv).
  cbn [fst snd].
  destruct (c_flush_pending_same _ _ _ _ Hfp) as (Ein2 & Emsg2 & _).
  pose proof (c_flush_pending_grow _ _ _ Hfp) as Hgr2. cbn [snd] in Hgr2.
  destruct (c_flush_pending_inv _ _ _ _ H6 Hfp) as ([ob m] & po & Es3 & Hpo & Hr3). subst s3.
  change (tr_out (d_tr (set_d_po (set_d_out s2' (ob, m)) po))) with ob.
  change (d_pbm (set_d_po (set_d_out s2' (ob, m)) po)) with m.
  change (d_po (set_d_po (set_d_out s2' (ob, m)) po)) with po.
  change (d_pending (set_d_po (set_d_out s2' (ob, m)) po)) with (o_pending ob) in Hif.
  assert (Hpo2 : 0 <= po) by (apply Hpo; open_dranges H9; auto).
  assert (Hg2a : out_grow z z2) by (eapply out_grow_trans; [exact Hg1 | apply out_grow_same; auto]).
  assert (Hg3 : out_grow z z3) by (eapply out_grow_trans; [exact Hg2a | exact Hgr2]).
  unfold out_at. Intros. rename H10 into Hob.
  destruct (Hr3 Hob) as [Hz3 _].
  assert (Era : rest_after z2 z3 (rest_after z z1 R) = rest_after z z3 R).
  { replace (rest_after z z1 R) with (rest_after z z2 R) by (unfold rest_after; rewrite Eo1; reflexivity).
    apply rest_after_trans; auto. open_zranges Hz3; lia. }
  rewrite Era.
  forward.
  sep_apply (out_at_fold ob m (p_s p) (p_pbuf p)); auto.
  forward_if_prop (o_pending ob = 0).
  - assert (Ep2 : (o_pending ob =? 0) = false).
    { apply Z.eqb_neq. intro E. rewrite E in *. contradiction. }
    rewrite Ep2 in Hif. specialize (Hres _ _ Hif). inversion Hres; subst sr zr orr; clear Hres.
    unfold flush_frame. Intros.
    forward.
    unfold POSTCONDITION, abbreviate.
    eapply semax_pre; [| apply semax_return].
    apply andp_right; [entailer!|].
    go_lowerx. cbn [RA_return loop1_ret_assert overridePost stage_post].
    Exists msgv. rewrite lf_comm.
    change (Vint (Int.neg (Int.repr 1))) with (vi (-1)).
    sep_apply (flush_frame_lf s2' z2 p pin ish gv (-1)); auto. { unfold s32_ok; rep_lia. }
    sep_apply (dfull_out_close (set_d_last_flush s2' (-1)) z2 z3 ob m po p pin pout ish (rest_after z z3 R) msgv gv); auto.
    { rewrite Emsg2; auto. }
    unfold PROPx, LOCALx, SEPx, local, lift1; simpl; entailer!.
  - forward. entailer!. destruct Hob as (_ & _ & Hp & _). apply repr_inj_unsigned64; auto. rep_lia.
  - Intros. rename H10 into Hp0. rewrite Hp0 in Hif. cbn in Hif.
    forward. forward.
    Exists (set_d_po (set_d_out s2' (ob, m)) po) z3 0 (u64 (lft - copy)).
    rewrite sub64_repr, <- (repr_u64 (lft - copy)).
    change (Int.signed (Int.repr 0)) with 0.
    sep_apply (dfull_out_close s2' z2 z3 ob m po p pin pout ish (rest_after z z3 R) msgv gv); auto.
    { rewrite Emsg2; auto. }
    entailer!. split; [unfold u64_ok; rep_lia | apply u64_range].
Qed.

(** Part 1: the while loop.  Its return ([s->pending != 0] after flush_pending) is the stage's return. *)
Lemma extra_loop : forall (Espec : OracleKind) p pin pout ish R msgv gv flush z hsh xp np cp W h x e res,
  0 <= flush <= 5 -> gz_extra h = Some x -> Forall (fun b => 0 <= b < 256) x -> Zlength R = z_avail_out z ->
  (forall s' z', e = inr (s', z') -> res = (s', z', Some Z_OK)) ->
  @semax DCS.CS Espec Delta_df
    (ext_inv p pin pout ish R msgv gv flush z (gzh_at hsh h (p_gzhead p) xp np cp * W)%logic h x e)
    S_eloop
    (overridePost (ext_exit p pin pout ish R msgv gv flush z (gzh_at hsh h (p_gzhead p) xp np cp * W)%logic e)
       (stage_post p pin pout ish R gv flush z (gzh_at hsh h (p_gzhead p) xp np cp * W)%logic res)).
Proof.
  intros Espec p pin pout ish R msgv gv flush z hsh xp np cp W h x e res Hfl Hx Hxb HR Hres.
  cbv [S_eloop].
  apply semax_loop with (Q' := ext_inv p pin pout ish R msgv gv flush z (gzh_at hsh h (p_gzhead p) xp np cp * W)%logic h x e).
  - apply el_body_ok; auto.
  - unfold ext_inv. Intros s1 z1 beg lft.
    destruct res as [[? ?] ?]. unfold loop2_ret_assert, overridePost, stage_post. cbv beta iota zeta.
    forward. Exists s1 z1 beg lft. unfold ext_locals, df_locals. entailer!.
Qed.

(** The model after the loop. *)
Definition extra_tail_m (h : gzh) (x : list Z) (s : dstate) (z : strm) (beg lft : Z) : option dres :=
  let* bytes := rds x (d_gzindex s) lft in
  let* pb := mb_write (d_pb s) (d_pending s) bytes in
  let s := set_d_pb s pb in
  let s := set_d_pending s (u64 (d_pending s + lft)) in
  let* z := c_hcrc_update h s z beg in
  Some (set_d_gzindex s 0, z, None).

Lemma extra_tail_m_none h x s z beg lft a b o : extra_tail_m h x s z beg lft = Some (a, b, o) -> o = None.
Proof. unfold extra_tail_m. intros H. inv_bind H. inv_bind H. inv_bind H. inversion H; auto. Qed.

(** ** The pieces of the tail *)
Definition S_ecopy : statement :=
  ltac:(let t := eval cbv [S_etail] in S_etail in
        lazymatch t with Ssequence ?a (Ssequence ?b _) => exact (Ssequence a b) end).
Definition S_ehc : statement :=
  ltac:(let t := eval cbv [S_etail] in S_etail in
        lazymatch t with Ssequence _ (Ssequence _ (Ssequence ?c _)) => exact c end).
Definition S_egz : statement :=
  ltac:(let t := eval cbv [S_etail] in S_etail in
        lazymatch t with Ssequence _ (Ssequence _ (Ssequence _ ?d)) => exact d end).

Definition et_mid (s : dstate) (pb : mbuf) (lft : Z) : dstate :=
  set_d_pending (set_d_pb s pb) (u64 (d_pending s + lft)).


Lemma st_mid_eq s pb n :
  et_mid s pb n =
  set_d_po (set_d_out (set_d_last_flush (set_d_gzindex (set_d_status s (d_status s)) (d_gzindex s)) (d_last_flush s))
    (mkOut (mb_val pb) (u64 (d_pending s + n)) (o_bi_buf (tr_out (d_tr s))) (o_bi_valid (tr_out (d_tr s)))
       (o_bi_used (tr_out (d_tr s))), mb_def pb)) (d_po s).
Proof. destruct s as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? t ?]; destruct t; reflexivity. Qed.

Lemma obj_join_t sh x xp lo bytes :
  field_compatible (tarray tuchar (Zlength x)) [] xp -> 0 <= lo -> lo + Zlength bytes <= Zlength x ->
  sublist lo (lo + Zlength bytes) x = bytes ->
  (@data_at DCS.CS sh (tarray tuchar lo) (sublist 0 lo (map vi x)) xp *
   @data_at DCS.CS sh (tarray tuchar (Zlength bytes)) (byte_vals bytes) (offset_val lo xp) *
   @data_at DCS.CS sh (tarray tuchar (Zlength x - (lo + Zlength bytes)))
     (sublist (lo + Zlength bytes) (Zlength x) (map vi x)) (offset_val (lo + Zlength bytes) xp))%logic
  |-- @data_at DCS.CS sh (tarray tuchar (Zlength x)) (map vi x) xp.
Proof.
  intros FC H1 H2 H3. pose proof (Zlength_nonneg bytes).
  rewrite (obj_split sh x xp lo (Zlength bytes)) by (auto; lia). rewrite H3. cancel.
Qed.


Lemma opt_obj_some_open sh o b q : o = Some b ->
  opt_obj sh o q |-- (@data_at DCS.CS sh (tarray tuchar (Zlength b)) (map vi b) q *
   (if Zlength b =? 0 then @malloc_token DCS.CS Ews (tarray tuchar 0) q else emp))%logic.
Proof. intros ->. unfold opt_obj. apply andp_left2. apply derives_refl. Qed.

Lemma gzh_at_unfold sh h hp xp np cp :
  gzh_at sh h hp xp np cp |--
  (!! (readable_share sh /\ gzh_ok h) &&
   (@field_at DCS.CS sh t_gzh (DOT _extra) xp hp *
    @field_at DCS.CS sh t_gzh (DOT _extra_len) (vi (gz_extra_len h)) hp *
    @field_at DCS.CS sh t_gzh (DOT _hcrc) (vi (gz_hcrc h)) hp *
    opt_obj sh (gz_extra h) xp * gzh_rest sh h hp np cp))%logic.
Proof. rewrite gzh_at_open. apply derives_refl. Qed.

Lemma et_copy {Espec : OracleKind} p pin pout ish R msgv gv flush z1 s1 hsh h xp np cp W x beg lft bytes pb :
  gz_extra h = Some x -> Forall (fun b => 0 <= b < 256) x -> u64_ok lft ->
  rds x (d_gzindex s1) lft = Some bytes -> mb_write (d_pb s1) (d_pending s1) bytes = Some pb ->
  @semax DCS.CS Espec Delta_df
    (PROPx [] (LOCALx (ext_locals p flush gv beg lft)
     (SEPx [dfull s1 z1 p pin pout ish R msgv gv; deflate_globals gv;
            (gzh_at hsh h (p_gzhead p) xp np cp * W)%logic])))
    S_ecopy
    (normal_ret_assert (PROPx [] (LOCALx (ext_locals p flush gv beg lft)
     (SEPx [dfull (et_mid s1 pb lft) z1 p pin pout ish R msgv gv; deflate_globals gv;
            (gzh_at hsh h (p_gzhead p) xp np cp * W)%logic])))).
Proof.
  intros Hx Hxb Hl Hr Hw. unfold ext_locals, df_locals. cbv [S_ecopy].
  assert (Hr' := Hr). unfold rds in Hr'.
  destruct ((0 <=? d_gzindex s1) && (0 <=? lft) && (d_gzindex s1 + lft <=? Zlength x))%bool eqn:E; [|discriminate].
  inversion Hr'; clear Hr'. rewrite !andb_true_iff, !Z.leb_le in E. destruct E as [[E1 E2] E3].
  assert (Lb : Zlength bytes = lft) by (subst bytes; rewrite Zlength_sublist; lia).
  subst lft.
  sep_apply (dfull_flush_open s1 z1 p pin pout ish R msgv gv). Intros.
  unfold flush_frame, out_at. Intros.
  sep_apply (gzh_at_unfold hsh h (p_gzhead p) xp np cp). Intros.
  sep_apply (opt_obj_some_open hsh (gz_extra h) x xp Hx). Intros.
  forward. forward. forward. forward. forward.
  pose proof H3 as (Hmb & Hbl & Hpr & _).
  assert (Hdl: Zlength (mb_def (d_pb s1)) = Zlength (mb_val (d_pb s1))) by (destruct Hmb; auto).
  pose proof (mb_vals_write _ _ _ _ Hdl Hw) as (Ew & L1 & L2 & G0 & G1).
  assert_PROP (field_compatible (tarray tuchar (Zlength x)) [] xp) as FCx by entailer!.
  rewrite (obj_split hsh x xp (d_gzindex s1) (Zlength bytes)) by (auto; lia).
  change (pb_vals (o_buf (tr_out (d_tr s1))) (d_pbm s1)) with (mb_vals (d_pb s1)).
  change (Zlength (o_buf (tr_out (d_tr s1)))) with (Zlength (mb_val (d_pb s1))).
  sep_apply (mb_split_in Ews (d_pb s1) (p_pbuf p) (d_pending s1) (Zlength bytes)); [auto; lia ..|].
  Intros. rewrite H0.
  assert_PROP (isptr (p_pbuf p)) as Hpp by entailer!.
  assert (Hxp : isptr xp) by (apply field_compatible_isptr in FCx; auto).
  forward_call (Ews, offset_val (d_pending s1) (p_pbuf p), hsh, offset_val (d_gzindex s1) xp, bytes).
  { entailer!. simpl. rewrite !add_ptr_long_tuchar by auto. reflexivity. }
  { split; [|unfold u64_ok in Hl; lia]. unfold bytes_ok. rewrite <- H0. apply Forall_sublist.
    eapply Forall_impl; [|exact Hxb]. intros; simpl in *; rep_lia. }
  forward. forward.
  rewrite add64_repr.
  assert (Hsub : sublist (d_gzindex s1) (d_gzindex s1 + Zlength bytes) x = bytes) by exact H0.
  sep_apply (obj_join_t hsh x xp (d_gzindex s1) bytes); auto.
  change (byte_vals bytes) with (map vi bytes).
  sep_apply (mb_join_in Ews (d_pb s1) (p_pbuf p) (d_pending s1) bytes pb); auto.
  sep_apply (opt_obj_fold hsh x xp Hxb).
  rewrite <- Hx. sep_apply (gzh_at_fold hsh h (p_gzhead p) xp np cp); auto.
  change (o_pending (tr_out (d_tr s1))) with (d_pending s1).
  replace (Vlong (Int64.repr (d_pending s1 + Zlength bytes))) with (vl (u64 (d_pending s1 + Zlength bytes)))
    by (unfold vl; rewrite repr_u64; reflexivity).
  change (mb_vals pb) with (pb_vals (mb_val pb) (mb_def pb)).
  sep_apply (out_at_fold (mkOut (mb_val pb) (u64 (d_pending s1 + Zlength bytes)) (o_bi_buf (tr_out (d_tr s1)))
     (o_bi_valid (tr_out (d_tr s1))) (o_bi_used (tr_out (d_tr s1)))) (mb_def pb) (p_s p) (p_pbuf p)).
  { assert (Hby : Forall (fun b => 0 <= b < 256) bytes) by (rewrite <- Hsub; apply Forall_sublist; auto).
    pose proof (mb_ok_write _ _ _ _ Hmb Hby Hw) as Hok.
    destruct H3 as (_ & _ & _ & Hb1 & Hb2 & Hb3).
    split; [destruct pb; exact Hok|]. cbn [o_buf o_pending o_bi_buf o_bi_valid o_bi_used].
    split; [cbn in L1; lia|]. split; [apply u64_range|]. auto. }
  rewrite st_mid_eq.
  open_dranges H2.
  sep_apply (ff_close s1 z1 z1 (d_status s1) (d_gzindex s1) (d_last_flush s1)
    (mkOut (mb_val pb) (u64 (d_pending s1 + Zlength bytes)) (o_bi_buf (tr_out (d_tr s1)))
     (o_bi_valid (tr_out (d_tr s1))) (o_bi_used (tr_out (d_tr s1)))) (mb_def pb) (d_po s1) p pin pout ish R msgv gv);
    auto; try (unfold s32_ok, u64_ok; lia).
  entailer!.
Qed.

(** ** HCRC_UPDATE(beg) after the last copy (from StageName) *)
(** ** Opening [dfull] / [gzh_at] at the few fields HCRC_UPDATE reads *)




Lemma gzh_hc_open sh h hp xp np cp :
  gzh_at sh h hp xp np cp =
  (!! (readable_share sh /\ gzh_ok h) &&
   (@field_at DCS.CS sh t_gzh (DOT _hcrc) (vi (gz_hcrc h)) hp * gzh_nohc sh h hp xp np cp))%logic.
Proof. unfold gzh_at, gzh_nohc. apply pred_ext; Intros; entailer!. Qed.





Lemma et_hc {Espec : OracleKind} p pin pout ish R msgv gv flush s z beg lft h hsh xp np cp W z' :
  c_hcrc_update h s z beg = Some z' -> u64_ok beg ->
  @semax DCS.CS Espec Delta_df
    (PROPx [] (LOCALx (ext_locals p flush gv beg lft)
     (SEPx [dfull s z p pin pout ish R msgv gv; deflate_globals gv; (gzh_at hsh h (p_gzhead p) xp np cp * W)%logic])))
    S_ehc
    (normal_ret_assert (PROPx [] (LOCALx (ext_locals p flush gv beg lft)
     (SEPx [dfull s z' p pin pout ish R msgv gv; deflate_globals gv; (gzh_at hsh h (p_gzhead p) xp np cp * W)%logic])))).
Proof.
  intros Hc Hbeg. unfold ext_locals, df_locals, u64_ok in *. cbv [S_ehc]. Intros.
  change (Vlong (Int64.repr beg)) with (vl beg). change (Vlong (Int64.repr lft)) with (vl lft).
  sep_apply (dfull_gz_open s z p pin pout ish R msgv gv). Intros.
  apply semax_loop_nocontinue.
  sep_apply (gzh_hc_unfold hsh h (p_gzhead p) xp np cp). Intros.
  forward. forward.
  unfold out_at. Intros.
  forward_if_temp _t'55 (Vint (Int.repr (if hc_cond h s beg then 1 else 0))).
  { forward. forward. entailer!.
    unfold hc_cond. rewrite (proj2 (Z.eqb_neq _ _) H6'). cbn [negb andb].
    rewrite cmpu_gt64 by (open_dranges H1; unfold d_pending; destruct H5 as (_ & _ & ? & _); lia).
    unfold d_pending. destruct (_ >? _); reflexivity. }
  { forward. entailer!. unfold hc_cond.
    replace (gz_hcrc h) with 0 by (destruct H4 as (_ & _ & _ & _ & ?); symmetry; apply repr_inj_signed; auto; rep_lia).
    reflexivity. }
  forward_if (PROPx [] (LOCALx [temp _beg (vl beg); temp _left (vl lft); temp _strm (p_strm p); temp _s (p_s p);
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

Lemma hcrc_adler_only h s z beg z' : c_hcrc_update h s z beg = Some z' -> z' = set_z_adler z (z_adler z').
Proof.
  unfold c_hcrc_update. intros H. destruct (_ && _)%bool.
  - destruct (mb_read (d_pb s) beg (d_pending s - beg)) as [bytes|]; [|discriminate].
    cbn in H. inversion H; subst; clear H. destruct z; reflexivity.
  - inversion H; subst. destruct z'; reflexivity.
Qed.

Lemma st_gz0_eq s :
  set_d_gzindex s 0 =
  set_d_po (set_d_out (set_d_last_flush (set_d_gzindex (set_d_status s (d_status s)) 0) (d_last_flush s))
    (d_out s)) (d_po s).
Proof. destruct s as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? t ?]; destruct t; reflexivity. Qed.

(** Part 2: after the loop: the last memcpy, [s->pending += left], HCRC_UPDATE(beg), [s->gzindex = 0]. *)
Lemma extra_tail : forall (Espec : OracleKind) p pin pout ish R msgv gv flush z hsh xp np cp W h x s1 z1 beg lft
    s2 z2,
  0 <= flush <= 5 -> gz_extra h = Some x -> Forall (fun b => 0 <= b < 256) x -> Zlength R = z_avail_out z ->
  out_grow z z1 -> u64_ok beg -> u64_ok lft ->
  extra_tail_m h x s1 z1 beg lft = Some (s2, z2, None) ->
  @semax DCS.CS Espec Delta_df
    (PROPx [] (LOCALx (ext_locals p flush gv beg lft)
     (SEPx [dfull s1 z1 p pin pout ish (rest_after z z1 R) msgv gv; deflate_globals gv;
            (gzh_at hsh h (p_gzhead p) xp np cp * W)%logic])))
    S_etail
    (normal_ret_assert
     (PROPx [out_grow z z2] (LOCALx (df_locals p flush gv)
     (SEPx [dfull s2 z2 p pin pout ish (rest_after z z2 R) msgv gv; deflate_globals gv;
            (gzh_at hsh h (p_gzhead p) xp np cp * W)%logic])))).
Proof.
  intros Espec p pin pout ish R msgv gv flush z hsh xp np cp W h x s1 z1 beg lft s2 z2 Hfl Hx Hxb HR Hg Hbeg Hlft Ht.
  unfold extra_tail_m in Ht.
  apply bind_inv in Ht; destruct Ht as [bytes [Hr Ht]].
  apply bind_inv in Ht; destruct Ht as [pb [Hw Ht]].
  apply bind_inv in Ht; destruct Ht as [z3 [Hh Ht]].
  inversion Ht; subst s2 z2; clear Ht.
  change (set_d_pending (set_d_pb s1 pb) (u64 (d_pending (set_d_pb s1 pb) + lft))) with (et_mid s1 pb lft) in *.
  cbv [S_etail]. apply <- seq_assoc.
  eapply semax_seq'.
  { apply (et_copy p pin pout ish (rest_after z z1 R) msgv gv flush z1 s1 hsh h xp np cp W x beg lft bytes pb); auto. }
  eapply semax_seq'.
  { apply (et_hc p pin pout ish (rest_after z z1 R) msgv gv flush (et_mid s1 pb lft) z1 beg lft h hsh xp np cp W z3);
      auto. }
  pose proof (hcrc_adler_only _ _ _ _ _ Hh) as E3.
  assert (Eo : z_out z3 = z_out z1) by (rewrite E3; destruct z1; reflexivity).
  assert (Ea : z_avail_out z3 = z_avail_out z1) by (rewrite E3; destruct z1; reflexivity).
  assert (Ei : z_in z3 = z_in z1) by (rewrite E3; destruct z1; reflexivity).
  replace (rest_after z z3 R) with (rest_after z z1 R) by (unfold rest_after; rewrite Eo; reflexivity).
  assert (Hg3 : out_grow z z3) by (destruct Hg as [d [G1 G2]]; exists d; rewrite Eo, Ea; auto).
  unfold ext_locals, df_locals.
  set (s := et_mid s1 pb lft) in *.
  sep_apply (dfull_flush_open s z3 p pin pout ish (rest_after z z1 R) msgv gv). Intros.
  unfold flush_frame. Intros.
  forward.
  rewrite (st_gz0_eq s). change (d_out s) with (tr_out (d_tr s), d_pbm s).
  sep_apply (ff_close s z3 z3 (d_status s) 0 (d_last_flush s) (tr_out (d_tr s)) (d_pbm s) (d_po s) p pin pout ish
               (rest_after z z1 R) msgv gv); auto.
  1-4: (open_dranges H1; unfold s32_ok, u64_ok in *; rep_lia).
  entailer!.
Qed.

(** Not in EXTRA_STATE: nothing happens. *)
Lemma extra_skip : forall (Espec : OracleKind) p pin pout ish R msgv gv flush s z X,
  d_status s <> DState.EXTRA_STATE ->
  @semax DCS.CS Espec Delta_df (stage_pre p pin pout ish R msgv gv flush s z X) S_extra
    (stage_post p pin pout ish R gv flush z X (s, z, None)).
Proof.
  intros Espec p pin pout ish R msgv gv flush s z X Hst.
  unfold stage_pre, stage_post, df_locals.
  cbv [S_extra nth_stmt df_body f_deflate fn_body].
  sep_apply (dfull_flush_open s z p pin pout ish R msgv gv). Intros.
  unfold flush_frame. Intros.
  forward.
  forward_if.
  - exfalso. apply Hst. unfold DState.EXTRA_STATE. open_dranges H1. apply repr_inj_signed; auto; unfold s32_ok in *; rep_lia.
  - forward. Exists msgv. rewrite rest_after_refl.
    sep_apply (flush_frame_fold s z p pin ish gv); auto.
    sep_apply (dfull_flush_back s z p pin pout ish R msgv gv); auto.
    entailer!.
Qed.
(** The stage. *)
Lemma stage_extra : stage_ok_gz S_extra c_deflate_extra.
Proof.
  intros Espec p pin pout ish R msgv gv flush s z hx W res Hfl Hc Hgz.
  destruct (Z.eq_dec (d_status s) DState.EXTRA_STATE) as [Est|Est].
  2: { unfold c_deflate_extra in Hc. rewrite (proj2 (Z.eqb_neq _ _) Est) in Hc. inversion Hc; subst.
       apply extra_skip; auto. }
  unfold c_deflate_extra in Hc. rewrite Est, Z.eqb_refl in Hc. unfold c_gzhead in Hc.
  destruct (d_gzhead s) as [h|] eqn:Hgh; [|discriminate].
  try rewrite Hgh in Hgz. destruct hx as [[[hsh xp] np] cp]. cbn [gz_ok] in Hgz. destruct Hgz as (Hrs & Hwx & _ & _).
  change (hdr_res (Some h) (p_gzhead p) (hsh, xp, np, cp)) with (gzh_at hsh h (p_gzhead p) xp np cp).
  inv_bind Hc. inversion Ha; subst x; clear Ha.
  inv_bind Hc. rename x into r, Ha into Hr. destruct r as [[s2 z2] o].
  destruct res as [[s3 z3] o3].
  unfold stage_pre, stage_post, df_locals.
  cbv [S_extra nth_stmt df_body f_deflate fn_body].
  sep_apply (dfull_flush_open s z p pin pout ish R msgv gv). Intros.
  unfold flush_frame. Intros.
  sep_apply (out_space_len z pout R). Intros. rename H3 into HRl.
  forward.
  forward_if.
  2: { exfalso. apply H3. rewrite Est. reflexivity. }
  rewrite gzh_at_open. Intros.
  forward. forward.
  { destruct (gz_extra h); unfold opt_obj; Intros; entailer!. }
  forward_if (PROP (o = None)
    LOCAL (temp _strm (p_strm p); temp _s (p_s p); temp _flush (vi flush); gvars gv)
    SEP (dfull s2 z2 p pin pout ish (rest_after z z2 R) msgv gv; deflate_globals gv;
         (gzh_at hsh h (p_gzhead p) xp np cp * W)%logic)).
  { eapply derives_trans; [| apply (opt_obj_tc hsh (gz_extra h) xp TT Hrs)]. cancel. }
  - (* extra != Z_NULL *)
    destruct (gz_extra h) as [x|] eqn:Hx.
    2: { unfold opt_obj. Intros. contradiction. }
    assert_PROP (Forall (fun b => 0 <= b < 256) x) as Hbx by (unfold opt_obj; entailer!).
    unfold out_at. Intros.
    forward. forward. forward. forward. forward.
    rewrite (left_val (gz_extra_len h) (d_gzindex s)) by (destruct H4 as (_ & _ & _ & ? & _); auto).
    sep_apply (out_at_fold (tr_out (d_tr s)) (d_pbm s) (p_s p) (p_pbuf p)); auto.
    sep_apply (flush_frame_fold s z p pin ish gv); auto.
    sep_apply (dfull_flush_back s z p pin pout ish R msgv gv); auto.
    rewrite <- Hx. sep_apply (gzh_at_fold hsh h (p_gzhead p) xp np cp); auto.
    inv_bind Hr. rename x0 into e, Ha into He. apply loop_runs in He.
    eapply semax_seq.
    { unfold POSTCONDITION, abbreviate. rewrite overridePost_twice.
      eapply semax_pre; [| apply (extra_loop Espec p pin pout ish R msgv gv flush z hsh xp np cp W h x e (s3, z3, o3)); auto].
      - unfold ext_inv, ext_locals, df_locals.
        Exists s z (d_pending s) (u64 (Z.land (gz_extra_len h) 65535 - d_gzindex s)).
        rewrite rest_after_refl. entailer!.
        split; [apply out_grow_refl|]. split; [destruct H6 as (_ & _ & Hp & _); exact Hp | apply u64_range].
      - intros s' z' ->. cbn in Hr. inversion Hr; subst. cbn in Hc. inversion Hc. reflexivity. }
    unfold ext_exit, ext_locals. Intros s1 z1 beg lft. subst e.
    assert (Ht : extra_tail_m h x s1 z1 beg lft = Some (s2, z2, o)) by exact Hr.
    pose proof (extra_tail_m_none _ _ _ _ _ _ _ _ _ Ht); subst o.
    unfold MORE_COMMANDS, abbreviate.
    eapply semax_post; [| | | | eapply semax_pre;
      [| apply (extra_tail Espec p pin pout ish R msgv gv flush z hsh xp np cp W h x s1 z1 beg lft s2 z2); auto]].
    + unfold POSTCONDITION, abbreviate. rewrite RA_normal_override. unfold df_locals, normal_ret_assert.
      simpl RA_normal. entailer!.
    + unfold normal_ret_assert. simpl RA_break. normalize.
    + unfold normal_ret_assert. simpl RA_continue. normalize.
    + intros vl. unfold normal_ret_assert. simpl RA_return. normalize.
    + unfold ext_locals, df_locals. entailer!.
  - (* extra == Z_NULL *)
    assert_PROP (gz_extra h = None) as Hx.
    { destruct (gz_extra h) as [x|] eqn:Hx; [|entailer!]. unfold opt_obj. subst xp.
      Intros. entailer!. }
    rewrite Hx in Hr. inversion Hr; subst s2 z2 o; clear Hr.
    forward.
    rewrite rest_after_refl.
    sep_apply (flush_frame_fold s z p pin ish gv); auto.
    sep_apply (dfull_flush_back s z p pin pout ish R msgv gv); auto.
    sep_apply (gzh_at_fold hsh h (p_gzhead p) xp np cp); auto.
    entailer!.
  - (* s->status = NAME_STATE *)
    Intros. subst o. cbn in Hc. inversion Hc; subst s3 z3 o3; clear Hc.
    sep_apply (dfull_flush_open s2 z2 p pin pout ish (rest_after z z2 R) msgv gv). Intros.
    unfold flush_frame. Intros.
    forward.
    Exists msgv. rewrite (st_status_eq s2 DState.NAME_STATE).
    change (d_out s2) with (tr_out (d_tr s2), d_pbm s2).
    change (Vint (Int.repr 73)) with (vi DState.NAME_STATE).
    sep_apply (ff_close s2 z2 z2 DState.NAME_STATE (d_gzindex s2) (d_last_flush s2) (tr_out (d_tr s2)) (d_pbm s2)
                 (d_po s2) p pin pout ish (rest_after z z2 R) msgv gv); auto.
    1-4: (open_dranges H7; unfold s32_ok, u64_ok, DState.NAME_STATE in *; rep_lia).
    entailer!.
Qed.

