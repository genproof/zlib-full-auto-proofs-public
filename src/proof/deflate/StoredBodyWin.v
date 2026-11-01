(** * deflate_stored's loop body, part (c): the copy from the window to next_out,
    [if (left) { if (left > len) left = len; zmemcpy(...); next_out/avail_out/total_out/block_start; len -= left; }]
    (StoredBodyKit.S_win, model c_win). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.proof.deflate.StoredKit.
Require Import Zlib.proof.deflate.StoredFacts.
Require Import Zlib.proof.deflate.StoredBodyKit.

#[export] Existing Instance DCS.CS.

Require Import Zlib.proof.zutil.Libc.
Require Zlib.trees.code.

(** ** Byte arrays: slices *)
Lemma sbw_tuchar_offset0 n j p:
  field_compatible (tarray tuchar n) [] p -> 0 <= j <= n ->
  @field_address0 DCS.CS (Tarray tuchar n noattr) [ArraySubsc j] p = offset_val j p.
Proof.
  intros. rewrite field_address0_offset.
  - simpl. f_equal. lia.
  - eapply field_compatible0_cons_Tarray; [reflexivity | auto | lia].
Qed.

Lemma sbw_split3 sh n a b (v: list val) p:
  field_compatible (tarray tuchar n) [] p -> 0 <= a <= b -> b <= n -> Zlength v = n ->
  @data_at DCS.CS sh (tarray tuchar n) v p =
  (@data_at DCS.CS sh (tarray tuchar a) (sublist 0 a v) p *
   @data_at DCS.CS sh (tarray tuchar (b - a)) (sublist a b v) (offset_val a p) *
   @data_at DCS.CS sh (tarray tuchar (n - b)) (sublist b n v) (offset_val b p))%logic.
Proof.
  intros FC A B L.
  unfold tarray. rewrite (split3_data_at_Tarray_tuchar sh n a b v p) by (first [exact L | lia]).
  rewrite !sbw_tuchar_offset0 by (auto; lia). reflexivity.
Qed.

Lemma sbw_definedb_spec b lo hi : mb_definedb b lo hi = true ->
  0 <= lo /\ hi <= Zlength (mb_val b) /\ forall i, lo <= i < hi -> Znth i (mb_def b) = true.
Proof.
  unfold mb_definedb. intros H. apply andb_prop in H. destruct H as [H H2].
  apply andb_prop in H. destruct H as [H0 H1]. apply Z.leb_le in H0. apply Z.leb_le in H1.
  split; [lia | split; [lia |]]. intros i Hi.
  rewrite forallb_forall in H2. apply H2. apply in_map_iff.
  exists (Z.to_nat (i - lo)). split; [lia |]. apply in_seq. lia.
Qed.

(** The defined slice of a masked buffer: its values are the bytes read. *)
Lemma sbw_mb_read b lo n bytes : mb_ok b -> mb_read b lo n = Some bytes ->
  0 <= lo /\ 0 <= n /\ lo + n <= Zlength (mb_val b) /\ bytes = sublist lo (lo + n) (mb_val b) /\
  sublist lo (lo + n) (mb_vals b) = byte_vals bytes /\ bytes_ok bytes /\ Zlength bytes = n.
Proof.
  intros [L K] H. unfold mb_read in H.
  destruct ((0 <=? n) && mb_definedb b lo (lo + n))%bool eqn:D; [|discriminate].
  injection H as <-. apply andb_prop in D. destruct D as [D0 D]. apply Z.leb_le in D0.
  apply sbw_definedb_spec in D. destruct D as (D1 & D2 & D3).
  split; [lia|]. split; [lia|]. split; [lia|]. split; [reflexivity|].
  split; [|split].
  - apply Znth_eq_ext.
    + unfold mb_vals. rewrite Zlength_sublist, Zlength_byte_vals, Zlength_sublist by (rewrite ?Zlength_pb_vals; lia). lia.
    + intros i Hi. unfold mb_vals in *. rewrite Zlength_sublist in Hi by (rewrite ?Zlength_pb_vals; lia).
      rewrite Znth_sublist by lia. rewrite Znth_byte_vals by (rewrite Zlength_sublist; lia).
      rewrite Znth_sublist by lia. rewrite Znth_pb_vals by lia. rewrite D3 by lia. reflexivity.
  - unfold bytes_ok. apply Forall_Znth. intros i Hi.
    rewrite Zlength_sublist in Hi by lia. rewrite Znth_sublist by lia.
    specialize (K (i + lo) ltac:(lia) (D3 (i + lo) ltac:(lia))). rep_lia.
  - rewrite Zlength_sublist by lia. lia.
Qed.

Lemma sbw_ranges_win s : dstate_ranges s ->
  mb_ok (d_window s) /\ Zlength (mb_val (d_window s)) <= Int.max_unsigned /\ s64_ok (d_block_start s).
Proof. unfold dstate_ranges. tauto. Qed.

Lemma sbw_add_ptr_long q k : isptr q -> 0 <= k <= Int64.max_unsigned ->
  force_val (sem_add_ptr_long tuchar q (vl k)) = offset_val k q.
Proof.
  intros P K. destruct q; try contradiction. unfold vl. simpl. unfold sem_add_ptr_long. simpl.
  f_equal. f_equal. unfold Ptrofs.of_int64. rewrite Int64.unsigned_repr by lia.
  rewrite ptrofs_mul_repr. f_equal. lia.
Qed.

Lemma sbw_add_ptr_int p k n : isptr p -> 0 <= n <= Int.max_unsigned ->
  force_val (sem_add_ptr_int tuchar Unsigned (offset_val k p) (vi n)) = offset_val (k + n) p.
Proof.
  intros P N. destruct p; try contradiction. simpl. unfold sem_add_ptr_int. simpl.
  f_equal. rewrite Ptrofs.add_assoc. f_equal.
  unfold Ptrofs.of_intu, Ptrofs.of_int. rewrite Int.unsigned_repr by rep_lia.
  rewrite ptrofs_mul_repr, ptrofs_add_repr. f_equal. lia.
Qed.

(** The representation after the step. *)
Lemma sbw_dstate_at_bs s x p gv :
  dstate_at (set_d_block_start s x) p gv =
  (!! dstate_ranges (set_d_block_start s x) &&
   (trees_at (d_trm s) (p_s p) (p_pbuf p) (p_strm p) gv * win_at s p * hash_at s p *
    match_at (set_d_block_start s x) p * cfg_at s p * stat_at s p))%logic.
Proof. reflexivity. Qed.

Lemma sbw_match_at_bs s x p :
  match_at (set_d_block_start s x) p =
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
Proof. reflexivity. Qed.

Definition sbw_z (z : strm) (bytes : list Z) (a t : Z) : strm :=
  set_z_total_out (set_z_avail_out (set_z_out z (z_out z ++ bytes)) a) t.

Lemma sbw_strm_at z bytes a t sp strmp pin pout msgv gv :
  strm_at (sbw_z z bytes a t) sp strmp pin pout msgv gv =
  (@field_at DCS.CS Ews t_strm (DOT _next_in) (offset_val (z_next_in z) pin) strmp *
   @field_at DCS.CS Ews t_strm (DOT _avail_in) (vi (z_avail_in z)) strmp *
   @field_at DCS.CS Ews t_strm (DOT _total_in) (vl (z_total_in z)) strmp *
   @field_at DCS.CS Ews t_strm (DOT _next_out) (offset_val (Zlength (z_out z ++ bytes)) pout) strmp *
   @field_at DCS.CS Ews t_strm (DOT _avail_out) (vi a) strmp *
   @field_at DCS.CS Ews t_strm (DOT _total_out) (vl t) strmp *
   @field_at DCS.CS Ews t_strm (DOT _msg) msgv strmp *
   @field_at DCS.CS Ews t_strm (DOT _state) sp strmp *
   sb_strm_zfuncs strmp gv *
   @field_at DCS.CS Ews t_strm (DOT _opaque) nullval strmp *
   @field_at DCS.CS Ews t_strm (DOT _adler) (vl (z_adler z)) strmp *
   @field_at_ DCS.CS Ews t_strm (DOT _reserved) strmp)%logic.
Proof. rewrite sb_strm_at_split. reflexivity. Qed.

Lemma sbw_in_obj ish z bytes a t pin : in_obj ish (sbw_z z bytes a t) pin = in_obj ish z pin.
Proof. reflexivity. Qed.

Lemma sbw_out_space z bytes a t pout rest :
  out_space (sbw_z z bytes a t) pout rest =
  (!! (Zlength rest = a) &&
   @data_at DCS.CS Ews (tarray tuchar (Zlength (z_out z ++ bytes) + a)) (map vi (z_out z ++ bytes) ++ rest) pout)%logic.
Proof. reflexivity. Qed.

Lemma sbw_rest_after z bytes a t rest :
  rest_after z (sbw_z z bytes a t) rest = sublist (Zlength bytes) (Zlength rest) rest.
Proof. unfold rest_after. cbn. rewrite Zlength_app. f_equal. lia. Qed.

Lemma sbw_msg z bytes a t : z_msg (sbw_z z bytes a t) = z_msg z.
Proof. reflexivity. Qed.

Lemma sbw_strm_ranges z bytes : strm_ranges z -> Zlength bytes <= z_avail_out z -> bytes_ok bytes ->
  strm_ranges (sbw_z z bytes (z_avail_out z - Zlength bytes) (u64 (z_total_out z + Zlength bytes))).
Proof.
  unfold strm_ranges, sbw_z, u32_ok, u64_ok, bytes_ok. cbn. intros (A1&A2&A3&A4&A5&A6&A7&A8&A9&A10&A11&A12) L B.
  pose proof (Zlength_nonneg bytes).
  assert (0 <= u64 (z_total_out z + Zlength bytes) < 18446744073709551616) by (unfold u64; apply Z.mod_pos_bound; lia).
  rewrite Zlength_app. repeat split; try rep_lia; try assumption.
  apply Forall_app. split; auto. eapply Forall_impl; [|exact B]. cbn. intros. rep_lia.
Qed.

Lemma sbw_dstate_ranges s x : dstate_ranges s -> s64_ok x -> dstate_ranges (set_d_block_start s x).
Proof. unfold dstate_ranges. destruct s; cbn. intuition. Qed.

Lemma sbw_vl_u64 x : vl (u64 x) = vl x.
Proof.
  unfold vl, u64. f_equal. change 18446744073709551616 with Int64.modulus.
  rewrite <- Int64.unsigned_repr_eq. apply Int64.repr_unsigned.
Qed.

(** c_win, explicitly. *)
Lemma c_win_inv s z len left r : c_win s z len left = Some r -> left <> 0 ->
  let l := if left >? len then len else left in
  exists bytes, mb_read (d_window s) (d_block_start s) l = Some bytes /\ Zlength bytes <= z_avail_out z /\
  in_long (d_block_start s + l) = true /\
  r = (set_d_block_start s (d_block_start s + l),
       set_z_total_out (set_z_avail_out (set_z_out z (z_out z ++ bytes)) (u32 (z_avail_out z - l)))
                       (u64 (z_total_out z + l)),
       u32 (len - l)).
Proof.
  unfold c_win. intros H N. apply Z.eqb_neq in N. rewrite N in H. cbv zeta in *.
  apply bind_some in H. destruct H as [bytes [E1 H]].
  apply bind_some in H. destruct H as [z1 [E2 H]].
  apply bind_some in H. destruct H as [u [E3 H]].
  unfold guard in E3. destruct (in_long _) eqn:El; [|discriminate].
  exists bytes. unfold out_put in E2. destruct (Zlength bytes <=? z_avail_out z) eqn:Lz; [|discriminate].
  apply Z.leb_le in Lz. injection E2 as <-. injection H as <-.
  split; [exact E1|]. split; [exact Lz|]. split; [reflexivity|]. reflexivity.
Qed.


Open Scope cmodel_scope.

Lemma sb_win_frag {Espec : OracleKind} (p : dptrs) (pin pout : val) (ish : share) (rest : list val)
    (msgv : val) (gv : globals) (s : dstate) (z : strm) (flush min_block used len left last : Z)
    (r : dstate * strm * Z) :
  Int.min_signed <= flush <= Int.max_signed -> 0 <= min_block <= Int.max_unsigned ->
  0 <= used <= Int.max_unsigned -> 0 <= len <= Int.max_unsigned -> 0 <= left <= Int.max_unsigned ->
  0 <= last <= 1 ->
  c_win s z len left = Some r ->
  semax Delta_ds
    (PROP () LOCAL (temp _len (vi len); temp _left (vi left); temp _last (vi last); temp _min_block (vi min_block);
                    temp _used (vi used); gvars gv; temp _s (p_s p); temp _flush (vi flush))
     SEP (dfull s z p pin pout ish rest msgv gv; deflate_globals gv))
    S_win
    (normal_ret_assert
      (PROP () LOCAL (temp _len (vi (snd r)); temp _last (vi last); temp _min_block (vi min_block);
                      temp _used (vi used); gvars gv; temp _s (p_s p); temp _flush (vi flush))
       SEP (dfull (fst (fst r)) (snd (fst r)) p pin pout ish (rest_after z (snd (fst r)) rest) msgv gv;
            deflate_globals gv))).
Proof.
  intros.
  unfold S_win, S_el, ones. show_stmt. simpl.
  destruct (Z.eqb_spec left 0) as [L0|L0].
  { subst left. unfold c_win in H5. cbn in H5. injection H5 as <-. cbn [fst snd].
    forward_if; [contradiction H5; reflexivity|].
    forward. rewrite rest_after_same. entailer!. }
  destruct (c_win_inv _ _ _ _ _ H5 L0) as (bytes & Er & Lb & Il & ->). cbn [fst snd].
  set (l := if left >? len then len else left) in *.
  forward_if; [| exfalso; apply L0; apply repr_inj_unsigned in H6; rep_lia].
  assert (Hl : 0 <= l <= len /\ l <= left) by (unfold l; destruct (Z.gtb_spec left len); lia).
  match goal with |- semax _ (PROPx _ (LOCALx (_ :: temp _left _ :: ?L) (SEPx ?S))) _ _ =>
    forward_if (PROPx [] (LOCALx (temp _len (vi len) :: temp _left (vi l) :: L) (SEPx S))) end.
  { forward. entailer!. unfold l. try rewrite Int.unsigned_repr in * by rep_lia.
    destruct (Z.gtb_spec left len); [reflexivity | lia]. }
  { forward. entailer!. unfold l. try rewrite Int.unsigned_repr in * by rep_lia.
    destruct (Z.gtb_spec left len); [lia | reflexivity]. }
  unfold dfull. Intros. unfold dstate_at. rewrite sb_trees_at_split, sb_strm_at_split.
  unfold dtype_at, win_at, match_at, out_space. Intros.
  forward. forward. forward. forward.
  destruct (sbw_ranges_win _ H10) as (Wok & WL & Bs).
  destruct (sbw_mb_read _ _ _ _ Wok Er) as (B0 & _ & Bhi & Ebytes & Evals & Bok & Lbytes).
  set (bs := d_block_start s) in *.
  set (Lz := Zlength (z_out z)) in *.
  set (av := z_avail_out z) in *.
  set (win := d_window s) in *.
  assert (HLz: 0 <= Lz) by (unfold Lz; apply Zlength_nonneg).
  assert (Hz := H7). destruct Hz as (_ & _ & _ & _ & _ & _ & Hav & HLout & Htot & _ & _ & Hout).
  unfold u32_ok, u64_ok in Hav, Htot. unfold s64_ok in Bs.
  assert_PROP (field_compatible (tarray tuchar (Lz + av)) [] pout) as FCo by entailer!.
  assert_PROP (field_compatible (tarray tuchar (Zlength (mb_val win))) [] (p_window p)) as FCw by entailer!.
  assert (Pout: isptr pout) by (destruct FCo; auto).
  assert (Pw: isptr (p_window p)) by (destruct FCw; auto).
  rewrite (sbw_split3 Ews (Lz + av) Lz (Lz + l) (map vi (z_out z) ++ rest) pout)
    by (auto; try lia; rewrite ?Zlength_app, ?Zlength_map; unfold Lz, av in *; lia).
  rewrite (sbw_split3 Ews (Zlength (mb_val win)) bs (bs + l) (mb_vals win) (p_window p))
    by (auto; try lia; unfold mb_vals; rewrite ?Zlength_pb_vals; destruct Wok; lia).
  rewrite Evals.
  assert (E1: sublist 0 Lz (map vi (z_out z) ++ rest) = map vi (z_out z)) by list_solve.
  assert (E2: sublist Lz (Lz + l) (map vi (z_out z) ++ rest) = sublist 0 l rest) by list_solve.
  assert (E3: sublist (Lz + l) (Lz + av) (map vi (z_out z) ++ rest) = sublist l av rest) by list_solve.
  rewrite E1, E2, E3. replace (Lz + l - Lz) with l by lia. replace (bs + l - bs) with l by lia.
  Intros.
  forward_call (Ews, offset_val Lz pout, Ews, offset_val bs (p_window p), bytes).
  { entailer!. rewrite Lbytes. simpl. rewrite sbw_add_ptr_long by (auto; rep_lia).
    rewrite Int.unsigned_repr by rep_lia.
    reflexivity. }
  { rewrite Lbytes. sep_apply (data_at_data_at_ Ews (tarray tuchar l) (sublist 0 l rest) (offset_val Lz pout)).
    cancel. }
  forward. forward. forward. forward.
  forward. forward. forward. forward.
  forward. forward. forward. forward.
  forward. forward.
  forward.
  assert (El : l = Zlength bytes) by lia.
  assert (Ea : u32 (av - l) = av - Zlength bytes) by (unfold u32; rewrite Z.mod_small; rep_lia).
  assert (Elen : u32 (len - l) = len - l) by (unfold u32; rewrite Z.mod_small; rep_lia).
  assert (Ibs : s64_ok (bs + l)).
  { unfold in_long in Il. apply andb_prop in Il. destruct Il as [I1 I2].
    apply Z.leb_le in I1, I2. unfold s64_ok. rep_lia. }
  clearbody l. subst l.
  rewrite Ea, Elen.
  fold (sbw_z z bytes (av - Zlength bytes) (u64 (z_total_out z + Zlength bytes))).
  unfold dfull. rewrite sbw_dstate_at_bs, sbw_strm_at, sbw_in_obj, sbw_out_space, sbw_rest_after, sbw_msg.
  rewrite sbw_match_at_bs, sb_trees_at_split. unfold dtype_at, win_at.
  set (n := Zlength bytes) in *.
  rewrite sbw_add_ptr_int by (auto; rep_lia).
  change (d_window s) with win.
  rewrite (sbw_split3 Ews (Zlength (mb_val win)) bs (bs + n) (mb_vals win) (p_window p))
    by (auto; try lia; unfold mb_vals; rewrite ?Zlength_pb_vals; destruct Wok; lia).
  rewrite Evals.
  rewrite Zlength_app. fold n. fold Lz. rewrite H11.
  replace (Lz + n + (av - n)) with (Lz + av) by lia.
  assert (Hn : 0 <= n) by (unfold n; apply Zlength_nonneg).
  rewrite (sbw_split3 Ews (Lz + av) Lz (Lz + n) (map vi (z_out z ++ bytes) ++ sublist n av rest) pout)
    by (auto; try lia; rewrite ?Zlength_app, ?Zlength_map, ?Zlength_sublist by lia; unfold Lz, n; rewrite ?Zlength_app; lia).
  assert (F1: sublist 0 Lz (map vi (z_out z ++ bytes) ++ sublist n av rest) = map vi (z_out z)) by list_solve.
  assert (F2: sublist Lz (Lz + n) (map vi (z_out z ++ bytes) ++ sublist n av rest) = map vi bytes) by list_solve.
  assert (F3: sublist (Lz + n) (Lz + av) (map vi (z_out z ++ bytes) ++ sublist n av rest) = sublist n av rest)
    by list_solve.
  rewrite F1, F2, F3. change (map vi bytes) with (byte_vals bytes).
  replace (Lz + n - Lz) with n by lia. replace (bs + n - bs) with n by lia.
  assert (Rz : strm_ranges (sbw_z z bytes (av - n) (u64 (z_total_out z + n))))
    by (apply sbw_strm_ranges; auto; lia).
  assert (Rs : dstate_ranges (set_d_block_start s (bs + n))) by (apply sbw_dstate_ranges; auto).
  rewrite Int.unsigned_repr by rep_lia. rewrite !sub_repr, !add64_repr, sbw_vl_u64.
  change (Vint (Int.repr (len - n))) with (vi (len - n)).
  change (Vint (Int.repr (av - n))) with (vi (av - n)).
  change (Vlong (Int64.repr (bs + n))) with (vl (bs + n)).
  change (Vlong (Int64.repr (z_total_out z + n))) with (vl (z_total_out z + n)).
  entailer!.
  rewrite Zlength_sublist by lia. lia.
Qed.
