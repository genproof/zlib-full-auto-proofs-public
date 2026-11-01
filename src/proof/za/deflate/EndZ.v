(* deflateEnd with a caller-supplied allocator: a live stream gives what deflateEnd needs ([za_dstream_end]),
   the field groups of the state converted to deflateEnd's view by the lemmas of src/proof/deflate/Api_toend.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.deflate.code.
Require Import Zlib.proof.za.deflate.Stmt.
Require Import Zlib.proof.deflate.Api_toend Zlib.proof.deflate.ApiKit.

Section ZA.
Context {ZA : zallocator}.

Lemma opt_alloc_za_intro (t : type) (q : val) :
  (za_tok t q * @data_at_ DCS.CS Ews t q)%logic |-- opt_alloc_za t q.
Proof.
  unfold opt_alloc_za. destruct (eq_dec q nullval).
  - subst. assert_PROP False by (entailer!; match goal with H : field_compatible _ _ nullval |- _ => destruct H; contradiction end). contradiction.
  - cancel.
Qed.

End ZA.

Local Opaque field_at field_at_ data_at data_at_ za_tok opt_alloc_za zfuncs_za.

Lemma data_at__nonnull {cs : compspecs} sh t q : @data_at_ cs sh t q |-- !! (q <> nullval).
Proof.
  Transparent data_at_ data_at. rewrite data_at__isptr. Opaque data_at_ data_at. normalize.
  apply prop_right. intro E. subst. contradiction.
Qed.

(* A live stream (any allocator) is one deflateEnd can end: its four buffers are allocated, none is Z_NULL. *)
Lemma za_dstream_end_proof : za_dstream_end_stmt.
Proof.
  unfold za_dstream_end_stmt; intros ZA0 s strmp ghp gv Pw Ph Pl. unfold dstream_za, dend_stream.
  Intros p. rewrite dstate_at'_2. unfold dstate_at, dtokens_za, trees_at. Intros.
  destruct H as [? [? [? ?]]]. destruct H1 as [Hw [Hp [Hh Hb]]].
  sep_apply win_end. sep_apply hash_end. sep_apply match_end. sep_apply cfg_end. sep_apply stat_end.
  sep_apply tr3_end. sep_apply desc_end. sep_apply work_end. sep_apply out_end. sep_apply sym_end.
  sep_apply lvl_end. sep_apply dtype_end. Intros dt.
  unfold d_trm; cbn [fst snd].
  rewrite Hw, Hp, Hh, Hb.
  assert_PROP (p_pbuf p <> nullval /\ p_head p <> nullval /\ p_prev p <> nullval /\ p_window p <> nullval)
    as HN.
  { sep_apply (data_at__nonnull Ews (tarray tuchar (4 * tr_lit_bufsize (d_tr s))) (p_pbuf p)).
    sep_apply (data_at__nonnull Ews (tarray tuchar (2 * d_w_size s)) (p_window p)).
    sep_apply (data_at__nonnull Ews (tarray tushort (d_w_size s)) (p_prev p)).
    sep_apply (data_at__nonnull Ews (tarray tushort (d_hash_size s)) (p_head p)).
    entailer!. }
  destruct HN as (N1 & N2 & N3 & N4).
  unfold dend_at_za.
  sep_apply (opt_alloc_za_intro (tarray tuchar (4 * tr_lit_bufsize (d_tr s))) (p_pbuf p)).
  sep_apply (opt_alloc_za_intro (tarray tuchar (2 * d_w_size s)) (p_window p)).
  sep_apply (opt_alloc_za_intro (tarray tushort (d_w_size s)) (p_prev p)).
  sep_apply (opt_alloc_za_intro (tarray tushort (d_hash_size s)) (p_head p)).
  Exists p.
  rewrite (prop_true_andp (p_strm p = p_strm p /\ _)) by auto.
  rewrite (prop_true_andp (p_strm p = p_strm p /\ _))
    by (split; [reflexivity | unfold dstate_ranges, s32_ok in H2; repeat split; tauto]).
  Exists dt. cancel.
Qed.

(** * The body of deflateEnd with a caller-supplied allocator *)
Require Import Zlib.proof.deflate.Api_end.
Require Import Zlib.proof.deflate.DModel3.
Local Transparent field_at field_at_ data_at data_at_ za_tok opt_alloc_za zfuncs_za.

Section ZB.
Context {ZA : zallocator}.

Lemma dend_at_za_split s p :
  dend_at_za s p =
  (@field_at DCS.CS Ews t_ds (DOT _strm) (p_strm p) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _status) (vi (d_status s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _pending_buf) (p_pbuf p) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _head) (p_head p) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _prev) (p_prev p) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _window) (p_window p) (p_s p) *
   @za_tok ZA DCS.CS t_ds (p_s p) *
   opt_alloc_za (tarray tuchar (4 * tr_lit_bufsize (d_tr s))) (p_pbuf p) *
   opt_alloc_za (tarray tushort (d_hash_size s)) (p_head p) *
   opt_alloc_za (tarray tushort (d_w_size s)) (p_prev p) *
   opt_alloc_za (tarray tuchar (2 * d_w_size s)) (p_window p) *
   dend_rest (p_s p))%logic.
Proof.
  unfold dend_at_za, dend_rest. apply pred_ext; cancel.
Qed.

Lemma dend_stream_check_some s p strmp gv :
  dend_stream (Some s) p strmp gv |--
  !! (p_strm p = strmp) &&
  (dcheck_at_za (Some s) strmp (p_s p) za_alloc za_free gv *
   (dcheck_at_za (Some s) strmp (p_s p) za_alloc za_free gv -* dend_stream (Some s) p strmp gv)).
Proof.
  unfold dend_stream at 1. Intros dt.
  unfold dcheck_at_za, dend_at_za. entailer!.
  rewrite <- wand_sepcon_adjoint. unfold dend_stream, dend_at_za. Intros. Exists dt. entailer!.
Qed.

Lemma dend_stream_check_none p strmp gv :
  dend_stream None p strmp gv |--
  EX za : val, EX zf : val,
  (dcheck_at_za None strmp nullval za zf gv *
   (dcheck_at_za None strmp nullval za zf gv -* dstream_za 2 None strmp nullval gv)).
Proof.
  unfold dend_stream, dstream_end_za at 1. Intros za zf op dt. Exists za zf.
  unfold dcheck_at_za. entailer!. rewrite <- wand_sepcon_adjoint. unfold dstream_za. Exists za zf op dt. entailer!.
Qed.

Lemma opt_alloc_za_null t : opt_alloc_za t nullval = emp.
Proof. unfold opt_alloc_za. rewrite if_true by auto. reflexivity. Qed.
Lemma opt_alloc_za_nn t q : q <> nullval -> opt_alloc_za t q = (za_tok t q * @data_at_ DCS.CS Ews t q)%logic.
Proof. intros. unfold opt_alloc_za. rewrite if_false by auto. reflexivity. Qed.

Lemma opt_alloc_za_ptr t q : opt_alloc_za t q |-- !! is_pointer_or_null q.
Proof.
  unfold opt_alloc_za. destruct (eq_dec q nullval).
  - subst. entailer!.
  - entailer!.
Qed.

Lemma za_buf_valid t q : 0 < sizeof t ->
  (za_tok t q * @data_at_ DCS.CS Ews t q * TT)%logic |-- valid_pointer q.
Proof.
  intros. apply sepcon_valid_pointer1. apply sepcon_valid_pointer2.
  apply data_at__valid_ptr; [auto | lia].
Qed.

Lemma dend_free_null n : dend_free nullval n = [].
Proof. unfold dend_free. rewrite if_true by auto. reflexivity. Qed.
Lemma dend_free_nn q n : q <> nullval -> dend_free q n = [ZFree n].
Proof. intros. unfold dend_free. rewrite if_false by auto. reflexivity. Qed.

(** Closing the ended stream: strm->state = Z_NULL, the allocator's functions kept. *)
Lemma close_none_za strmp gv dt :
  (func_ptr' zalloc_spec za_alloc * func_ptr' zfree_spec za_free *
   @field_at_ DCS.CS Ews t_strm (DOT _reserved) strmp *
   @field_at DCS.CS Ews t_strm (DOT _state) nullval strmp *
   @field_at DCS.CS Ews t_strm (DOT _zalloc) za_alloc strmp *
   @field_at DCS.CS Ews t_strm (DOT _zfree) za_free strmp *
   @field_at DCS.CS Ews t_strm (DOT _opaque) za_opaque strmp *
   @field_at DCS.CS Ews t_strm (DOT _data_type) dt strmp)%logic
  |-- dclosed strmp gv.
Proof.
  unfold dclosed, zfuncs_za, za_funcs. Exists dt. entailer!.
Qed.

End ZB.

Lemma sizeof_tarray_eq {cs : compspecs} t n : sizeof (tarray t n) = sizeof t * Z.max 0 n.
Proof. reflexivity. Qed.

Ltac sz_tac := rewrite sizeof_tarray_eq; simpl sizeof; rewrite Z.max_r by lia; lia.

(** Replace X by Y in the list of separating conjuncts S. *)
Ltac sep_repl X Y S :=
  let F := eval pattern X in S in
  lazymatch F with ?G _ => eval cbv beta in (G Y) end.

(** TRY_FREE(strm, s->f) for the buffer Q of type T and N bytes: the join point is the precondition without
    [opt_alloc_za T Q] and with the allocator's events extended by [dend_free Q N]. *)
Ltac try_free_za gv T Q N :=
  assert_PROP (is_pointer_or_null Q) by (sep_apply (opt_alloc_za_ptr T Q); entailer!);
  forward; forward;
  lazymatch goal with |- semax _ (PROPx ?P (LOCALx (_ :: _ :: ?L) (SEPx ?S))) _ _ =>
    lazymatch S with context [za_res gv ?TR] =>
      let S1 := sep_repl (opt_alloc_za T Q) (@emp mpred Nveric Sveric) S in
      let S2 := sep_repl (za_res gv TR) (za_res gv (TR ++ dend_free Q N)) S1 in
      forward_if (PROPx P (LOCALx L (SEPx S2)));
      [ unfold opt_alloc_za at 1; let E := fresh "E" in destruct (eq_dec Q nullval) as [E|E];
        [ rewrite E; entailer!
        | apply denote_tc_test_eq_split; [ | apply valid_pointer_null];
          eapply derives_trans; [ | apply (za_buf_valid T Q); sz_tac ]; cancel ]
      | let E := fresh "E" in
        assert (E : isptr Q) by (match goal with H : _ |- _ => exact H end);
        assert (EQ : Q <> nullval) by (let E2 := fresh "E2" in intro E2; rewrite E2 in E; contradiction);
        rewrite (opt_alloc_za_nn T Q EQ); Intros;
        forward; forward; forward; forward;
        forward_call (T, Q, gv, TR);
        rewrite (dend_free_nn Q N EQ);
        replace (sizeof T) with N by sz_tac; entailer!
      | let E := fresh "E" in
        assert (E : Q = nullval) by (match goal with H : _ |- _ => exact H end);
        forward; rewrite E, opt_alloc_za_null, dend_free_null, app_nil_r; entailer!
      | idtac ]
    end
  end.

Section ZC.
Context {ZA : zallocator}.

Lemma body_za_deflateEnd :
  @semax_body DSpec.Vprog (@Gprog_za_deflateEnd ZA) DCS.CS f_deflateEnd (@za_deflateEnd_spec ZA).
Proof.
  start_function.
  destruct os as [s|].
  2:{ subst r. sep_apply dend_stream_check_none. Intros za zf.
      forward_call (@None dstate, strmp, nullval, za, zf, ni, gv).
      sep_apply mp_wand.
      forward_if; [forward; Exists tr; entailer! | discriminate]. }
  sep_apply dend_stream_check_some. Intros.
  forward_call (Some s, strmp, p_s p, za_alloc, za_free, ni, gv).
  sep_apply mp_wand.
  unfold c_deflateEnd, bad_state, c_deflateStateCheck in H |- *.
  destruct (status_ok (d_status s)) eqn:Hst; cbn in H.
  2:{ inv H. forward_if; [forward | discriminate]. Exists tr. entailer!. }
  inv H. forward_if; [contradiction|].
  unfold dend_stream. Intros dt. rewrite dend_at_za_split. unfold zfuncs_za, za_funcs. Intros.
  assert (HS : 0 < d_w_size s /\ 0 < d_hash_size s /\ 0 < tr_lit_bufsize (d_tr s)) by (repeat split; lia).
  destruct HS as (HS1 & HS2 & HS3).
  freeze FR := (dend_rest _) (field_at_ _ _ (DOT _reserved) _) (field_at _ _ (DOT _data_type) _ _) (ds_pad _).
  forward. forward.
  try_free_za gv (tarray tuchar (4 * tr_lit_bufsize (d_tr s))) (p_pbuf p) (4 * tr_lit_bufsize (d_tr s)).
  try_free_za gv (tarray tushort (d_hash_size s)) (p_head p) (2 * d_hash_size s).
  try_free_za gv (tarray tushort (d_w_size s)) (p_prev p) (2 * d_w_size s).
  try_free_za gv (tarray tuchar (2 * d_w_size s)) (p_window p) (2 * d_w_size s).
  forward. forward. forward.
  thaw FR.
  sep_apply (ds_data_at_ (p_s p) (p_strm p) (vi (d_status s)) (p_pbuf p) (p_head p) (p_prev p) (p_window p)).
  assert_PROP (isptr (p_s p)) as Hsp by entailer!.
  match goal with |- context [za_res gv ?TR] => forward_call (t_ds, p_s p, gv, TR) end.
  forward.
  sep_apply (close_none_za (p_strm p) gv dt).
  forward_if (PROP () LOCAL (temp _t'2 (vi (if d_status s =? BUSY_STATE then Z_DATA_ERROR else Z_OK)))
    SEP (dclosed (p_strm p) gv; za_res gv (tr ++ dend_events s p);
         @field_at DCS.CS Ews t_strm (DOT _next_in) ni (p_strm p))).
  1,2: forward; unfold dend_events; rewrite !app_assoc; entailer!;
       destruct (Z.eqb_spec (d_status s) BUSY_STATE); unfold BUSY_STATE in *; try lia; reflexivity.
  forward. Exists (tr ++ dend_events s p). entailer!.
Qed.

End ZC.
