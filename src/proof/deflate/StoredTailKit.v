(** * Kit for the second phase of deflate_stored (StoredTail.v, [ds_phase2_frag]): the statement [S_phase2] and
    the model [ds_phase2] split into four pieces, the shapes of the fragment triples, and helper lemmas.

    S_phase2 = S_p2_slide; S_p2_read; S_p2_hw; S_p2_tail   (seq_assoc)
    - [S_p2_slide]: [have = (unsigned)(s->window_size - s->strstart); if (avail_in > have && block_start >= w_size)
      { slide ... }]                                   model [ds_slide s z = Some (s1, have)]
    - [S_p2_read]: [if (have > avail_in) have = avail_in; if (have) { read_buf ...; strstart += have; insert += ... }]
                                                       model [ds_read s z have = Some (s2, z2)]
    - [S_p2_hw]: [if (s->high_water < s->strstart) s->high_water = s->strstart;]   model [upd_high_water]
    - [S_p2_tail]: from [have = ((unsigned)s->bi_valid + 42) >> 3;] to the return   model [ds_tail s z flush]. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.trees.TLemmas.
Require Export Zlib.proof.deflate.StoredKit.
Require Zlib.trees.code.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

(** ** Statements *)
Definition S_p2_slide : statement := Ssequence (sub S_phase2 [0]%nat) (sub S_phase2 [1;0]%nat).
Definition S_p2_read : statement := Ssequence (sub S_phase2 [1;1;0]%nat) (sub S_phase2 [1;1;1;0]%nat).
Definition S_p2_hw : statement := sub S_phase2 [1;1;1;1;0]%nat.
Definition S_p2_tail : statement := sub S_phase2 [1;1;1;1;1]%nat.

Lemma S_phase2_eq :
  S_phase2 = Ssequence (sub S_phase2 [0]%nat) (Ssequence (sub S_phase2 [1;0]%nat)
               (Ssequence (sub S_phase2 [1;1;0]%nat) (Ssequence (sub S_phase2 [1;1;1;0]%nat)
                 (Ssequence S_p2_hw S_p2_tail)))).
Proof. reflexivity. Qed.

(** Show the statements concretely. *)
Ltac show_tail_stmt :=
  cbv [S_p2_slide S_p2_read S_p2_hw S_p2_tail S_phase2 sub f_deflate_stored fn_body].

(** ** The model, split like the statement *)
Section Model.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

Definition ds_slide (s : dstate) (z : strm) : option (dstate * Z) :=
  let have := u32 (u64 (d_window_size s - d_strstart s)) in
  if (z_avail_in z >? have) && (d_block_start s >=? d_w_size s) then
    let s := set_d_block_start s (d_block_start s - d_w_size s) in
    let s := set_d_strstart s (u32 (d_strstart s - d_w_size s)) in
    let* win := mb_move (d_window s) 0 (d_w_size s) (d_strstart s) in
    let s := set_d_window s win in
    let s := incr_matches s in
    let have := u32 (have + d_w_size s) in
    Some (clamp_insert s, have)
  else Some (s, have).

Definition ds_read (s : dstate) (z : strm) (have : Z) : option (dstate * strm) :=
  let have := if have >? z_avail_in z then z_avail_in z else have in
  if have =? 0 then Some (s, z) else
  let* (z, data) := c_read_buf s z have in
  let* win := mb_write (d_window s) (d_strstart s) data in
  let s := set_d_window s win in
  let s := set_d_strstart s (u32 (d_strstart s + have)) in
  Some (add_insert s have, z).

Definition ds_tail (s : dstate) (z : strm) (flush : Z) : option (dstate * strm * bstate) :=
  let have := stored_hdr s in
  let have := u32 (let a := u64 (d_pending_buf_size s - have) in if a >? MAX_STORED then MAX_STORED else a) in
  let min_block := if have >? d_w_size s then d_w_size s else have in
  let* _ := guard (in_long (d_strstart s - d_block_start s)) in
  let left := u32 (d_strstart s - d_block_start s) in
  let* (s, z, last) :=
    (if (left >=? min_block) ||
        ((negb (left =? 0) || (flush =? Z_FINISH)) && negb (flush =? Z_NO_FLUSH) &&
         (z_avail_in z =? 0) && (left <=? have)) then
       let len := if left >? have then have else left in
       let last := if (flush =? Z_FINISH) && (z_avail_in z =? 0) && (len =? left) then 1 else 0 in
       let* buf := (if len =? 0 then Some [] else mb_read (d_window s) (d_block_start s) len) in
       let* o := c_tr_stored_block (d_out s) buf len last in
       let s := set_d_out s o in
       let* _ := guard (in_long (d_block_start s + len)) in
       let s := set_d_block_start s (d_block_start s + len) in
       let* (s, z) := c_flush_pending s z in
       Some (s, z, last)
     else Some (s, z, 0)) in
  if last =? 0 then Some (s, z, need_more) else Some (set_d_bi_used s 8, z, finish_started).

Lemma ds_phase2_split s z flush :
  ds_phase2 s z flush =
  let* (s1, h) := ds_slide s z in
  let* (s2, z2) := ds_read s1 z h in
  ds_tail (upd_high_water s2) z2 flush.
Proof. reflexivity. Qed.

Lemma ds_slide_have s z s1 h : ds_slide s z = Some (s1, h) -> 0 <= h <= Int.max_unsigned.
Proof.
  unfold ds_slide. intros H.
  assert (U : forall x, 0 <= u32 x <= Int.max_unsigned)
    by (intros x; unfold u32; pose proof (Z.mod_pos_bound x 4294967296 ltac:(lia)); rep_lia).
  destruct (_ && _).
  - destruct (mb_move _ _ _ _); cbn in H; [|discriminate]. inversion H; subst. apply U.
  - inversion H; subst. apply U.
Qed.

(** read_buf does not touch the output. *)
Lemma ds_read_out s z h s2 z2 : ds_read s z h = Some (s2, z2) ->
  z_out z2 = z_out z /\ z_avail_out z2 = z_avail_out z /\ z_total_out z2 = z_total_out z.
Proof.
  unfold ds_read. intros H.
  destruct (_ =? 0); [inversion H; subst; auto|].
  apply bind_inv in H; destruct H as [[z1 d] [Hr H]].
  apply bind_inv in H; destruct H as [w [_ H]]. inversion H; subst.
  unfold c_read_buf in Hr. destruct (_ =? 0); [inversion Hr; subst; auto|].
  apply bind_inv in Hr; destruct Hr as [d' [_ Hr]]. inversion Hr; subst. cbn.
  destruct (d_wrap s =? 1); [cbn; auto|]. destruct (d_wrap s =? 2); cbn; auto.
Qed.
End Model.

(** ** Folded groups *)

(** trees.c's part of the state without out_at, sym_at, dtype_at (mentions trees.c's globals: keep folded). *)
Definition st_trees_frame (cs : tstate * list bool) (sp : val) (gv : globals) : mpred :=
  (ltree_at (tr_ltree (fst cs)) sp * dtree_at (tr_dtree (fst cs)) sp * bltree_at (tr_bltree (fst cs)) sp *
   ldesc_at (field_address t_ds (DOT Zlib.trees.code._dyn_ltree) sp) (tr_lmax (fst cs)) (gv Zlib.trees.code._static_l_desc) sp *
   ddesc_at (field_address t_ds (DOT Zlib.trees.code._dyn_dtree) sp) (tr_dmax (fst cs)) (gv Zlib.trees.code._static_d_desc) sp *
   bldesc_at (field_address t_ds (DOT Zlib.trees.code._bl_tree) sp) (tr_blmax (fst cs)) (gv Zlib.trees.code._static_bl_desc) sp *
   work_at (tr_wk (fst cs)) sp * lvl_at (fst cs) sp)%logic.

Lemma st_trees_at_split cs sp pbp strmp gv :
  trees_at cs sp pbp strmp gv =
  (st_trees_frame cs sp gv * out_at (tr_out (fst cs)) (snd cs) sp pbp * sym_at (fst cs) sp pbp *
   dtype_at (fst cs) sp strmp)%logic.
Proof. unfold trees_at, st_trees_frame. apply pred_ext; cancel. Qed.

(** The allocator fields of the z_stream (zutil.c's globals: keep folded). *)
Definition st_zfuncs (strmp : val) (gv : globals) : mpred :=
  (@field_at DCS.CS Ews t_strm (DOT _zalloc) (gv _zcalloc) strmp *
   @field_at DCS.CS Ews t_strm (DOT _zfree) (gv _zcfree) strmp)%logic.

(** strm_in_at with the allocator fields folded. *)
Lemma st_strm_in_split z sp strmp pin msgv gv :
  strm_in_at z sp strmp pin msgv gv =
  (@field_at DCS.CS Ews t_strm (DOT _next_in) (offset_val (z_next_in z) pin) strmp *
   @field_at DCS.CS Ews t_strm (DOT _avail_in) (vi (z_avail_in z)) strmp *
   @field_at DCS.CS Ews t_strm (DOT _total_in) (vl (z_total_in z)) strmp *
   @field_at DCS.CS Ews t_strm (DOT _msg) msgv strmp *
   @field_at DCS.CS Ews t_strm (DOT _state) sp strmp *
   st_zfuncs strmp gv *
   @field_at DCS.CS Ews t_strm (DOT _opaque) nullval strmp *
   @field_at DCS.CS Ews t_strm (DOT _adler) (vl (z_adler z)) strmp *
   @field_at_ DCS.CS Ews t_strm (DOT _reserved) strmp)%logic.
Proof. unfold strm_in_at, st_zfuncs. apply pred_ext; cancel. Qed.

(** ** Masked buffers (the window) as VST contents *)

Lemma Zlength_mb_vals b : mb_ok b -> Zlength (mb_vals b) = Zlength (mb_val b).
Proof. intros [H _]. unfold mb_vals. apply Zlength_pb_vals. auto. Qed.

Lemma firstn_combine {A B} n (l1 : list A) (l2 : list B) :
  firstn n (combine l1 l2) = combine (firstn n l1) (firstn n l2).
Proof.
  revert l1 l2; induction n; intros [|a l1] [|b l2]; simpl; auto.
  rewrite IHn. reflexivity.
Qed.

Lemma skipn_combine {A B} n (l1 : list A) (l2 : list B) :
  skipn n (combine l1 l2) = combine (skipn n l1) (skipn n l2).
Proof.
  revert l1 l2; induction n; intros [|a l1] [|b l2]; simpl; auto.
  destruct (skipn n l1); auto.
Qed.

Lemma sublist_pb_vals lo hi b m :
  sublist lo hi (pb_vals b m) = pb_vals (sublist lo hi b) (sublist lo hi m).
Proof.
  unfold pb_vals. rewrite sublist_map. f_equal.
  unfold sublist. rewrite firstn_combine, skipn_combine. reflexivity.
Qed.

Lemma combine_app2 {A B} (a1 a2 : list A) (b1 b2 : list B) :
  length a1 = length b1 -> combine (a1 ++ a2) (b1 ++ b2) = combine a1 b1 ++ combine a2 b2.
Proof.
  revert b1; induction a1; intros [|b b1]; simpl; try discriminate; auto.
  intros E. f_equal. apply IHa1. lia.
Qed.

Lemma pb_vals_app a1 a2 b1 b2 : Zlength a1 = Zlength b1 ->
  pb_vals (a1 ++ a2) (b1 ++ b2) = pb_vals a1 b1 ++ pb_vals a2 b2.
Proof.
  intros E. unfold pb_vals. rewrite combine_app2, map_app; auto.
  rewrite !Zlength_correct in E. lia.
Qed.

Lemma pb_vals_true l n : n = Zlength l -> pb_vals l (repeat true (Z.to_nat n)) = map vi l.
Proof.
  intros ->. rewrite Zlength_correct, Nat2Z.id. unfold pb_vals.
  induction l; simpl; auto. f_equal. apply IHl.
Qed.

Lemma mb_definedb_spec b lo hi : mb_definedb b lo hi = true ->
  0 <= lo /\ hi <= Zlength (mb_val b) /\ forall i, lo <= i < hi -> Znth i (mb_def b) = true.
Proof.
  unfold mb_definedb. intros H. apply andb_prop in H as [H1 H2]. apply andb_prop in H1 as [H0 H1].
  apply Z.leb_le in H0, H1. split; [lia | split; [lia|]].
  intros i Hi. rewrite forallb_forall in H2. specialize (H2 (lo + Z.of_nat (Z.to_nat (i - lo)))).
  rewrite Z2Nat.id in H2 by lia. replace (lo + (i - lo)) with i in H2 by lia. apply H2.
  apply in_map_iff. exists (Z.to_nat (i - lo)). split; [rewrite Z2Nat.id by lia; lia|].
  apply in_seq. lia.
Qed.

(** The defined bytes [mb_read] returns are the VST contents of their slice. *)
Lemma mb_read_vals b lo len l : mb_ok b -> mb_read b lo len = Some l ->
  sublist lo (lo + len) (mb_vals b) = map vi l /\ Zlength l = len /\ 0 <= lo /\ 0 <= len /\
  lo + len <= Zlength (mb_val b) /\ Forall (fun x => 0 <= x < 256) l.
Proof.
  intros [Hl Hok] H. unfold mb_read in H.
  destruct (0 <=? len) eqn:E0; [|discriminate]. cbn [andb] in H.
  destruct (mb_definedb b lo (lo + len)) eqn:E1; [|discriminate]. inversion H; subst l; clear H.
  apply Z.leb_le in E0. apply mb_definedb_spec in E1 as [Hlo [Hhi Hd]].
  assert (Ln : Zlength (sublist lo (lo + len) (mb_val b)) = len) by (rewrite Zlength_sublist; lia).
  split; [|split; [exact Ln | split; [lia | split; [lia | split; [lia|]]]]].
  - unfold mb_vals. rewrite sublist_pb_vals.
    apply Znth_eq_ext.
    + rewrite Zlength_pb_vals, Zlength_map; [lia|]. rewrite !Zlength_sublist; lia.
    + intros i Hi. rewrite Zlength_pb_vals in Hi by (rewrite !Zlength_sublist; lia). rewrite Ln in Hi.
      rewrite Znth_pb_vals by (rewrite ?Zlength_sublist; lia).
      rewrite Znth_map by lia. rewrite !Znth_sublist by lia. rewrite Hd by lia. reflexivity.
  - apply Forall_Znth. intros i Hi. rewrite Ln in Hi. rewrite Znth_sublist by lia.
    apply Hok; [lia|]. apply Hd. lia.
Qed.

(** The VST contents after [mb_write]. *)
Lemma mb_write_vals b lo src b' : mb_ok b -> mb_write b lo src = Some b' ->
  Forall (fun x => 0 <= x < 256) src ->
  mb_ok b' /\ Zlength (mb_val b') = Zlength (mb_val b) /\ 0 <= lo /\ lo + Zlength src <= Zlength (mb_val b) /\
  mb_vals b' = sublist 0 lo (mb_vals b) ++ map vi src ++ sublist (lo + Zlength src) (Zlength (mb_val b)) (mb_vals b).
Proof.
  intros [Hl Hok] H Hsrc. unfold mb_write in H.
  destruct ((0 <=? lo) && (lo + Zlength src <=? Zlength (mb_val b)))%bool eqn:E; [|discriminate].
  apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1, E2. inversion H; subst b'; clear H.
  pose proof (Zlength_nonneg src).
  assert (Lr : Zlength (repeat true (Z.to_nat (Zlength src))) = Zlength src)
    by (rewrite Zlength_repeat; lia).
  assert (Lv : Zlength (sublist 0 lo (mb_val b) ++ src ++ sublist (lo + Zlength src) (Zlength (mb_val b)) (mb_val b))
               = Zlength (mb_val b)) by (rewrite !Zlength_app, !Zlength_sublist; lia).
  assert (Ld : Zlength (sublist 0 lo (mb_def b) ++ repeat true (Z.to_nat (Zlength src)) ++
                        sublist (lo + Zlength src) (Zlength (mb_def b)) (mb_def b)) = Zlength (mb_val b))
    by (rewrite !Zlength_app, !Zlength_sublist; lia).
  split; [|split; [exact Lv | split; [lia | split; [lia|]]]].
  - split; cbn [mb_val mb_def]; [lia|]. intros i Hi Hd. rewrite Lv in Hi.
    destruct (Z_lt_dec i lo).
    + rewrite app_Znth1 in Hd by (rewrite Zlength_sublist; lia).
      rewrite app_Znth1 by (rewrite Zlength_sublist; lia).
      rewrite Znth_sublist in Hd by lia. rewrite Znth_sublist by lia.
      replace (i + 0) with i in * by lia. apply Hok; [lia | exact Hd].
    + rewrite app_Znth2 in Hd by (rewrite Zlength_sublist; lia).
      rewrite app_Znth2 by (rewrite Zlength_sublist; lia).
      rewrite (Zlength_sublist 0 lo (mb_def b)) in Hd by lia.
      rewrite (Zlength_sublist 0 lo (mb_val b)) by lia.
      destruct (Z_lt_dec (i - (lo - 0)) (Zlength src)).
      * rewrite app_Znth1 by lia. eapply Forall_Znth in Hsrc; [exact Hsrc | lia].
      * rewrite app_Znth2 in Hd by lia. rewrite app_Znth2 by lia. rewrite Lr in Hd.
        rewrite Znth_sublist in Hd by lia. rewrite Znth_sublist by lia.
        apply Hok; [lia | exact Hd].
  - unfold mb_vals; cbn [mb_val mb_def].
    rewrite !sublist_pb_vals. rewrite <- Hl.
    rewrite !pb_vals_app by (rewrite ?Zlength_correct_nat, ?Zlength_sublist, ?Zlength_repeat; lia).
    rewrite pb_vals_true; reflexivity.
Qed.
