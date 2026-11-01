(** * Body proof of deflateEnd.  ZFREE(strm, strm->state) needs data_at_ Ews t_ds (the whole
    5968 bytes, padding included: VST's spacers): dend_at's 61 per-field field_at's and [DRep.ds_pad] (v7). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.deflate.DModel3 Zlib.proof.deflate.DSpec Zlib.proof.deflate.DCS.
Require Import Zlib.deflate.code.
Require Import Zlib.proof.deflate.ApiKit.

(** The fields of deflate_state deflateEnd does not read. *)
Definition dend_rest (sp : val) : mpred :=
  (   @field_at_ DCS.CS Ews t_ds (DOT _pending_buf_size) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _pending_out) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _pending) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _wrap) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _gzhead) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _gzindex) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _method) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _last_flush) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _w_size) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _w_bits) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _w_mask) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _window_size) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _ins_h) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _hash_size) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _hash_bits) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _hash_mask) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _hash_shift) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _block_start) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _match_length) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _prev_match) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _match_available) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _strstart) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _match_start) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _lookahead) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _prev_length) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _max_chain_length) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _max_lazy_match) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _level) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _strategy) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _good_match) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _nice_match) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _dyn_ltree) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _dyn_dtree) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _bl_tree) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _l_desc) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _d_desc) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _bl_desc) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _bl_count) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _heap) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _heap_len) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _heap_max) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _depth) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _sym_buf) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _lit_bufsize) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _sym_next) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _sym_end) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _opt_len) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _static_len) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _matches) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _insert) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _bi_buf) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _bi_valid) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _bi_used) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _high_water) sp *
   @field_at_ DCS.CS Ews t_ds (DOT _slid) sp)%logic.

Lemma dend_at_split s p :
  dend_at s p =
  (@field_at DCS.CS Ews t_ds (DOT _strm) (p_strm p) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _status) (vi (d_status s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _pending_buf) (p_pbuf p) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _head) (p_head p) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _prev) (p_prev p) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _window) (p_window p) (p_s p) *
   @malloc_token DCS.CS Ews t_ds (p_s p) *
   opt_alloc (tarray tuchar (4 * tr_lit_bufsize (d_tr s))) (p_pbuf p) *
   opt_alloc (tarray tushort (d_hash_size s)) (p_head p) *
   opt_alloc (tarray tushort (d_w_size s)) (p_prev p) *
   opt_alloc (tarray tuchar (2 * d_w_size s)) (p_window p) *
   dend_rest (p_s p))%logic.
Proof.
  unfold dend_at, dend_rest. apply pred_ext; cancel.
Qed.

Lemma mb_fact sh n b z : memory_block sh n (Vptr b z) |-- !! (Ptrofs.unsigned z + n < Ptrofs.modulus).
Proof.
  eapply derives_trans; [apply memory_block_local_facts|]. apply prop_derives. intros [_ H]. exact H.
Qed.

Lemma offset_val_repr b z o : offset_val o (Vptr b (Ptrofs.repr z)) = Vptr b (Ptrofs.repr (z + o)).
Proof.
  simpl. f_equal. unfold Ptrofs.add. apply Ptrofs.eqm_samerepr. apply Ptrofs.eqm_add;
  apply Ptrofs.eqm_sym, Ptrofs.eqm_unsigned_repr.
Qed.

(** Two adjacent blocks at [z + o] and [z + o'] (o' = o + n) form one of size N = n + m. *)
Lemma mb_join sh b z o o' n m N :
  n + m = N -> o + n = o' -> 0 <= n -> 0 <= m -> 0 <= z + o < Ptrofs.modulus ->
  memory_block sh n (Vptr b (Ptrofs.repr (z + o))) * memory_block sh m (Vptr b (Ptrofs.repr (z + o')))
  |-- memory_block sh N (Vptr b (Ptrofs.repr (z + o))).
Proof.
  intros HN Ho Hn Hm Hz.
  rewrite (add_andp _ _ (sepcon_derives _ _ _ _ (mb_fact sh n b _) (mb_fact sh m b _))).
  rewrite sepcon_prop_prop. normalize.
  rewrite Ptrofs.unsigned_repr in H by rep_lia.
  rewrite Ptrofs.unsigned_repr in H0 by rep_lia.
  subst. replace (z + (o + n)) with ((z + o) + n) by lia.
  rewrite <- memory_block_split by rep_lia. apply derives_refl.
Qed.

Ltac mb_step :=
  match goal with
  | |- ?R |-- memory_block ?sh ?N (Vptr ?b (Ptrofs.repr (?z + ?o))) =>
    match R with context [memory_block sh ?n (Vptr b (Ptrofs.repr (z + o)))] =>
      tryif (assert_succeeds (assert (n = N) by reflexivity)) then cancel else
      (let m := eval compute in (N - n) in let o' := eval compute in (o + n) in
       eapply derives_trans; [ | apply (mb_join sh b z o o' n m N);
                                 [reflexivity | reflexivity | lia | lia | lia] ];
       cancel)
    end
  end.

Lemma ds_data_at_ (sp a b c d e f : val) :
  (@field_at DCS.CS Ews t_ds (DOT _strm) a sp *
   @field_at DCS.CS Ews t_ds (DOT _status) b sp *
   @field_at DCS.CS Ews t_ds (DOT _pending_buf) c sp *
   @field_at DCS.CS Ews t_ds (DOT _head) d sp *
   @field_at DCS.CS Ews t_ds (DOT _prev) e sp *
   @field_at DCS.CS Ews t_ds (DOT _window) f sp *
   dend_rest sp * ds_pad sp)%logic
  |-- @data_at_ DCS.CS Ews t_ds sp.
Proof.
  match goal with |- ?L |-- _ => assert (HF : L |-- !! field_compatible t_ds (DOT _strm) sp) end.
  { apply derives_trans with (@field_at DCS.CS Ews t_ds (DOT _strm) a sp * TT)%logic; [cancel|].
    rewrite field_at_compatible'. normalize. }
  rewrite (add_andp _ _ HF). normalize. clear HF.
  rename H into Hfc. apply field_compatible_cons in Hfc. destruct Hfc as [_ Hfc].
  rewrite <- memory_block_data_at_ by auto.
  sep_apply (field_at_field_at_ Ews t_ds (DOT _strm) a sp).
  sep_apply (field_at_field_at_ Ews t_ds (DOT _status) b sp).
  sep_apply (field_at_field_at_ Ews t_ds (DOT _pending_buf) c sp).
  sep_apply (field_at_field_at_ Ews t_ds (DOT _head) d sp).
  sep_apply (field_at_field_at_ Ews t_ds (DOT _prev) e sp).
  sep_apply (field_at_field_at_ Ews t_ds (DOT _window) f sp).
  unfold dend_rest, ds_pad. rewrite !field_at__memory_block.
  rewrite !field_compatible_field_address by (apply field_compatible_cons; split; [apply id_in_list_true; vm_compute; reflexivity | exact Hfc]).
  unfold spacer, at_offset. simpl.
  destruct Hfc as (Hp & _ & Hsz & _). destruct sp as [| | | | | bb i]; try contradiction. simpl in Hsz.
  rewrite <- (Ptrofs.repr_unsigned i). pose proof (Ptrofs.unsigned_range i). forget (Ptrofs.unsigned i) as z.
  rewrite !offset_val_repr.
  replace (Vptr bb (Ptrofs.repr z)) with (Vptr bb (Ptrofs.repr (z + 0))) by (rewrite Z.add_0_r; auto).
  repeat mb_step.
Qed.

Lemma dstream_end_check_some s strmp gv :
  dstream_end (Some s) strmp gv |--
  EX p : dptrs, !! (p_strm p = strmp) &&
  (dcheck_at (Some s) strmp (p_s p) (gv _zcalloc) (gv _zcfree) gv *
   (dcheck_at (Some s) strmp (p_s p) (gv _zcalloc) (gv _zcfree) gv -* dstream_end (Some s) strmp gv)).
Proof.
  unfold dstream_end at 1. Intros p dt. Exists p.
  unfold dcheck_at, dend_at. entailer!.
  rewrite <- wand_sepcon_adjoint. unfold dstream_end, dend_at. Exists p dt. entailer!.
Qed.

Lemma dstream_end_check_none strmp gv :
  dstream_end None strmp gv |--
  EX za : val, EX zf : val,
  (dcheck_at None strmp nullval za zf gv * (dcheck_at None strmp nullval za zf gv -* dstream 2 None strmp nullval gv)).
Proof.
  unfold dstream_end at 1. Intros za zf op dt. Exists za zf.
  unfold dcheck_at. entailer!. rewrite <- wand_sepcon_adjoint. unfold dstream. Exists za zf op dt. entailer!.
Qed.

Lemma opt_alloc_null t : opt_alloc t nullval = emp.
Proof. unfold opt_alloc. rewrite if_true by auto. reflexivity. Qed.
Lemma opt_alloc_nn t q : q <> nullval -> opt_alloc t q = (@malloc_token DCS.CS Ews t q * @data_at_ DCS.CS Ews t q)%logic.
Proof. intros. unfold opt_alloc. rewrite if_false by auto. reflexivity. Qed.

Lemma opt_alloc_ptr t q : opt_alloc t q |-- !! is_pointer_or_null q.
Proof.
  unfold opt_alloc. destruct (eq_dec q nullval).
  - subst. entailer!.
  - entailer!.
Qed.

(** TRY_FREE(strm, s->f): the join point is the precondition with [opt_alloc T Q] replaced by emp. *)
Ltac sep_drop X S :=
  let F := eval pattern X in S in
  lazymatch F with ?G _ => eval cbv beta in (G emp) end.

Ltac try_free_if X1 X2 :=
  match goal with |- semax _ (PROPx ?P (LOCALx (_ :: _ :: ?L) (SEPx ?S))) _ _ =>
    let S1 := sep_drop X1 S in
    let S2 := sep_drop X2 S1 in
    forward_if (PROPx P (LOCALx L (SEPx S2)))
  end.

Ltac try_free gv T Q :=
  assert_PROP (is_pointer_or_null Q) by (sep_apply (opt_alloc_ptr T Q); entailer!);
  forward; forward;
  try_free_if (opt_alloc T Q) (opt_alloc T Q);
  [ unfold opt_alloc at 1; let E := fresh "E" in destruct (eq_dec Q nullval) as [E|E]; [rewrite E; entailer! | entailer!]
  | let E := fresh "E" in
    assert (E : isptr Q) by (match goal with H : _ |- _ => exact H end);
    rewrite (opt_alloc_nn T Q) by (let E2 := fresh "E2" in intro E2; rewrite E2 in E; contradiction); Intros;
    forward; forward; forward; forward;
    forward_call (T, Q, gv, nullval);
    [ rewrite if_false by (let E2 := fresh "E2" in intro E2; rewrite E2 in E; contradiction); cancel | entailer! ]
  | let E := fresh "E" in
    assert (E : Q = nullval) by (match goal with H : _ |- _ => exact H end);
    forward; rewrite E, opt_alloc_null; entailer!
  | idtac ].

(** Closing the ended stream (strm->state = Z_NULL, the default allocator's functions). *)
Lemma close_none strmp gv za zf dt :
  za = gv _zcalloc -> zf = gv _zcfree ->
  (func_ptr' (snd (@Zlib.proof.zutil.Spec.zcalloc_spec DCS.CS)) za * func_ptr' (snd (@Zlib.proof.zutil.Spec.zcfree_spec DCS.CS)) zf *
   @field_at_ DCS.CS Ews t_strm (DOT _reserved) strmp *
   @field_at DCS.CS Ews t_strm (DOT _state) nullval strmp *
   @field_at DCS.CS Ews t_strm (DOT _zalloc) za strmp *
   @field_at DCS.CS Ews t_strm (DOT _zfree) zf strmp *
   @field_at DCS.CS Ews t_strm (DOT _opaque) nullval strmp *
   @field_at DCS.CS Ews t_strm (DOT _data_type) dt strmp)%logic
  |-- dstream 2 None strmp nullval gv.
Proof.
  intros -> ->. unfold dstream, zfuncs. Exists (gv _zcalloc) (gv _zcfree) nullval dt. entailer!.
Qed.

Lemma body_deflateEnd : ob_deflateEnd.
Proof.
  unfold ob_deflateEnd. start_function.
  destruct os as [s|].
  2:{ subst r. sep_apply dstream_end_check_none. Intros za zf.
      forward_call (@None dstate, strmp, nullval, za, zf, ni, gv).
      sep_apply mp_wand.
      forward_if; [forward; entailer! | discriminate]. }
  sep_apply dstream_end_check_some. Intros pc.
  forget (gv _zcalloc) as za; forget (gv _zcfree) as zf.
  forward_call (Some s, strmp, p_s pc, za, zf, ni, gv).
  sep_apply mp_wand. clear dependent pc. clear dependent za. clear dependent zf.
  unfold c_deflateEnd, bad_state, c_deflateStateCheck in H |- *.
  destruct (status_ok (d_status s)) eqn:Hst; cbn in H.
  2:{ inv H. forward_if; [forward; entailer! | discriminate]. }
  inv H. forward_if; [contradiction|].
  unfold dstream_end. Intros p dt. rewrite dend_at_split. unfold zfuncs. Intros.
  freeze FR := (dend_rest _) (field_at_ _ _ (DOT _reserved) _) (field_at _ _ (DOT _data_type) _ _) (ds_pad _).
  remember (gv _zcalloc) as za eqn:Eza. remember (gv _zcfree) as zf eqn:Ezf.
  forward. forward.
  try_free gv (tarray tuchar (4 * tr_lit_bufsize (d_tr s))) (p_pbuf p).
  try_free gv (tarray tushort (d_hash_size s)) (p_head p).
  try_free gv (tarray tushort (d_w_size s)) (p_prev p).
  try_free gv (tarray tuchar (2 * d_w_size s)) (p_window p).
  forward. forward. forward.
  thaw FR.
  sep_apply (ds_data_at_ (p_s p) (p_strm p) (vi (d_status s)) (p_pbuf p) (p_head p) (p_prev p) (p_window p)).
  assert_PROP (isptr (p_s p)) as Hsp by entailer!.
  forward_call (t_ds, p_s p, gv, nullval).
  { rewrite if_false by (intro E; rewrite E in Hsp; contradiction). cancel. }
  forward.
  sep_apply (close_none strmp gv za zf dt Eza Ezf). clear Eza Ezf.
  forward_if (PROP () LOCAL (temp _t'2 (vi (if d_status s =? BUSY_STATE then Z_DATA_ERROR else Z_OK)))
    SEP (dstream 2 None strmp nullval gv; mem_mgr gv; @field_at DCS.CS Ews t_strm (DOT _next_in) ni strmp)).
  all: try (forward; entailer!).
  all: destruct (Z.eqb_spec (d_status s) BUSY_STATE); unfold BUSY_STATE in *; try lia; reflexivity.
Qed.
