(** * FLUSH_BLOCK_ONLY / FLUSH_BLOCK (fix F5) of deflate.c's compressors, as tactics on [dfull]

    - [fbo_tac p pin pout ish gv z rest Hfbo]: the statements of FLUSH_BLOCK_ONLY(s, last) (both cases of
      block_start), from SEP [dfull s4 z2 ...; deflate_globals gv] to SEP [dfull s6 z6 ...; deflate_globals gv]
      for [Hfbo : c_flush_block_only s4 z2 last = Some (s6, z6)].
    - [f5_tac]: F5's test [s->strm->avail_out == 0 && (!last || s->pending != 0 || s->wrap != 0)] up to the
      temp holding its value ([Vint (Int.repr (Z.b2z B))], B the model's test in [c_flush_block]); the stream is
      opened with [dfull_f5_open] (only the four fields read) and closed with [dfull_f5_close]. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.proof.deflate.CompressKit.
Require Import Zlib.deflate.code.
#[export] Existing Instance DCS.CS.
Open Scope cmodel_scope.

(** ** dfull with the four fields read by F5's test apart *)
Definition f5_rest (s : dstate) (z : strm) (p : dptrs) (pin pout : val) (ish : share) (rest : list val)
    (msgv : val) (gv : globals) : mpred :=
  (ltree_at (tr_ltree (d_tr s)) (p_s p) * dtree_at (tr_dtree (d_tr s)) (p_s p) *
   sym_at (d_tr s) (p_s p) (p_pbuf p) * trees_rest (d_tr s) (p_s p) (p_strm p) gv *
   @field_at DCS.CS Ews t_strm (DOT _data_type) (vi (tr_data_type (d_tr s))) (p_strm p) *
   @field_at DCS.CS Ews t_ds (DOT _pending_buf) (p_pbuf p) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _bi_buf) (vi (o_bi_buf (tr_out (d_tr s)))) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _bi_valid) (vi (o_bi_valid (tr_out (d_tr s)))) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _bi_used) (vi (o_bi_used (tr_out (d_tr s)))) (p_s p) *
   @data_at DCS.CS Ews (tarray tuchar (Zlength (o_buf (tr_out (d_tr s))))) (pb_vals (o_buf (tr_out (d_tr s))) (d_pbm s))
     (p_pbuf p) *
   win_at s p * hash_at s p * match_at s p * cfg_at s p *
   @field_at DCS.CS Ews t_ds (DOT _status) (vi (d_status s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _pending_buf_size) (vl (d_pending_buf_size s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _pending_out) (offset_val (d_po s) (p_pbuf p)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _gzhead) (p_gzhead p) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _gzindex) (vl (d_gzindex s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _method) (vi (d_method s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _last_flush) (vi (d_last_flush s)) (p_s p) *
   @field_at DCS.CS Ews t_strm (DOT _next_in) (offset_val (z_next_in z) pin) (p_strm p) *
   @field_at DCS.CS Ews t_strm (DOT _avail_in) (vi (z_avail_in z)) (p_strm p) *
   @field_at DCS.CS Ews t_strm (DOT _total_in) (vl (z_total_in z)) (p_strm p) *
   @field_at DCS.CS Ews t_strm (DOT _next_out) (offset_val (Zlength (z_out z)) pout) (p_strm p) *
   @field_at DCS.CS Ews t_strm (DOT _total_out) (vl (z_total_out z)) (p_strm p) *
   @field_at DCS.CS Ews t_strm (DOT _msg) msgv (p_strm p) *
   @field_at DCS.CS Ews t_strm (DOT _state) (p_s p) (p_strm p) *
   ck_strm_zfuncs (p_strm p) gv *
   @field_at DCS.CS Ews t_strm (DOT _opaque) nullval (p_strm p) *
   @field_at DCS.CS Ews t_strm (DOT _adler) (vl (z_adler z)) (p_strm p) *
   @field_at_ DCS.CS Ews t_strm (DOT _reserved) (p_strm p) *
   in_obj ish z pin * out_space z pout rest)%logic.

Lemma dfull_f5_open s z p pin pout ish rest msgv gv :
  dfull s z p pin pout ish rest msgv gv |--
  !! (strm_ranges z /\ msg_ok (z_msg z) msgv /\ readable_share ish /\ dstate_ranges s /\
      out_ok (tr_out (d_tr s)) (d_pbm s) /\ Int.min_signed <= tr_data_type (d_tr s) <= Int.max_signed) &&
  (@field_at DCS.CS Ews t_ds (DOT _strm) (p_strm p) (p_s p) *
   @field_at DCS.CS Ews t_strm (DOT _avail_out) (vi (z_avail_out z)) (p_strm p) *
   @field_at DCS.CS Ews t_ds (DOT _pending) (vl (d_pending s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _wrap) (vi (d_wrap s)) (p_s p) *
   f5_rest s z p pin pout ish rest msgv gv).
Proof.
  unfold dfull, dstate_at, f5_rest, d_pending. rewrite trees_at_open, ck_strm_at_open.
  unfold d_trm, out_at, dtype_at, stat_at. cbn [fst snd]. Intros. entailer!.
Qed.

Lemma dfull_f5_close s z p pin pout ish rest msgv gv :
  strm_ranges z -> msg_ok (z_msg z) msgv -> readable_share ish -> dstate_ranges s ->
  out_ok (tr_out (d_tr s)) (d_pbm s) -> Int.min_signed <= tr_data_type (d_tr s) <= Int.max_signed ->
  @field_at DCS.CS Ews t_ds (DOT _strm) (p_strm p) (p_s p) *
  @field_at DCS.CS Ews t_strm (DOT _avail_out) (vi (z_avail_out z)) (p_strm p) *
  @field_at DCS.CS Ews t_ds (DOT _pending) (vl (d_pending s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _wrap) (vi (d_wrap s)) (p_s p) *
  f5_rest s z p pin pout ish rest msgv gv
  |-- dfull s z p pin pout ish rest msgv gv.
Proof.
  intros. unfold dfull, dstate_at, f5_rest, d_pending. rewrite trees_at_open, ck_strm_at_open.
  unfold d_trm, out_at, dtype_at, stat_at. cbn [fst snd]. entailer!.
Qed.


(** ** Closing FLUSH_BLOCK_ONLY: the pieces after flush_pending back into [dfull] (proved once: an in-place
    unfold + entailer! per use made the kernel check of the compressors' Qed far too slow). *)
Lemma out_space_prop z pout R : out_space z pout R = (!! (Zlength R = z_avail_out z) && out_space z pout R)%logic.
Proof. unfold out_space. apply pred_ext; entailer!. Qed.

Lemma out_at_prop o m sp pbp : out_at o m sp pbp = (!! out_ok o m && out_at o m sp pbp)%logic.
Proof. unfold out_at. apply pred_ext; entailer!. Qed.

Lemma fbo_close s4 tt5 s6 z2 z6 o6 po6 p pin pout ish R msgv gv :
  s6 = set_d_po (set_d_out (set_d_block_start (set_d_trm s4 tt5) (d_strstart s4)) o6) po6 ->
  z_in z6 = z_in z2 -> msg_ok (z_msg z6) msgv -> strm_ranges z6 -> readable_share ish -> dstate_ranges s6 ->
  0 <= d_strstart s4 <= Int.max_unsigned -> Int.min_signed <= tr_data_type (fst tt5) <= Int.max_signed ->
  strm_at z6 (p_s p) (p_strm p) pin pout msgv gv *
  out_space z6 pout R *
  @field_at DCS.CS Ews t_ds (DOT _pending_out) (offset_val (d_po s6) (p_pbuf p)) (p_s p) *
  out_at (tr_out (d_tr s6)) (d_pbm s6) (p_s p) (p_pbuf p) *
  @data_at DCS.CS Ews (tarray tuchar (Zlength (mb_val (d_window s4)))) (mb_vals (d_window s4)) (p_window p) *
  ltree_at (tr_ltree (fst tt5)) (p_s p) *
  dtree_at (tr_dtree (fst tt5)) (p_s p) *
  sym_at (fst tt5) (p_s p) (p_pbuf p) *
  @field_at DCS.CS Ews t_ds (DOT _strm) (p_strm p) (p_s p) *
  @field_at DCS.CS Ews t_strm (DOT Zlib.trees.code._data_type) (vi (tr_data_type (fst tt5))) (p_strm p) *
  trees_rest (fst tt5) (p_s p) (p_strm p) gv * trees_globals gv *
  @field_at DCS.CS Ews t_ds (DOT _window) (p_window p) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _window_size) (vl (d_window_size s4)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _w_size) (vi (d_w_size s4)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _w_bits) (vi (d_w_bits s4)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _w_mask) (vi (d_w_mask s4)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _high_water) (vl (d_high_water s4)) (p_s p) *
  hash_at s4 p *
  @field_at DCS.CS Ews t_ds (DOT _block_start) (Vlong (Int64.repr (Int.unsigned (Int.repr (d_strstart s4))))) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _match_length) (vi (d_match_length s4)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _prev_match) (vi (d_prev_match s4)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _match_available) (vi (d_match_available s4)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _strstart) (vi (d_strstart s4)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _match_start) (vi (d_match_start s4)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _lookahead) (vi (d_lookahead s4)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _prev_length) (vi (d_prev_length s4)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _insert) (vi (d_insert s4)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _slid) (vi (d_slid s4)) (p_s p) *
  cfg_at s4 p *
  @field_at DCS.CS Ews t_ds (DOT _status) (vi (d_status s4)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _pending_buf_size) (vl (d_pending_buf_size s4)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _wrap) (vi (d_wrap s4)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _gzhead) (p_gzhead p) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _gzindex) (vl (d_gzindex s4)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _method) (vi (d_method s4)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _last_flush) (vi (d_last_flush s4)) (p_s p) *
  in_obj ish z2 pin * dglobals_rest gv
  |-- dfull s6 z6 p pin pout ish R msgv gv * deflate_globals gv.
Proof.
  intros Es6 Ein Hmsg Hzr Hish Hdr Hss Hdt.
  rewrite out_at_prop. Intros. rename H into Hok6.
  rewrite Es6 in Hdr, Hok6 |- *. unfold set_d_out in Hdr, Hok6 |- *.
  unfold dfull, in_obj. rewrite Ein.
  unfold dstate_at.
  repeat rewrite trees_at_open. repeat rewrite deflate_globals_open.
  repeat rewrite trees_rest_norm.
  unfold ltree_at, out_at, sym_at, dtype_at, match_at, win_at, hash_at, cfg_at, stat_at.
  dsimpl.
  rewrite ?sub_repr32, ?add_repr32, ?sub64_repr, ?add64_repr. unfold vi, vl.
  rewrite ?unsigned_repr_u32, ?repr_u32, ?repr_u64.
  rewrite (Int.unsigned_repr (d_strstart s4)) by assumption.
  entailer!.
Qed.

(** ** FLUSH_BLOCK_ONLY(s, last), as one tactic.
    From a goal [semax _ (PROP P LOCAL L SEP (dfull s4 z2 p pin pout ish (rest_after z z2 rest) msgv2 gv;
    deflate_globals gv)) (FLUSH_BLOCK_ONLY; ...)] with [Hfbo : c_flush_block_only s4 z2 last = Some (s6, z6)],
    [Hrest : Zlength rest = z_avail_out z], [out_grow z z2], [dstate_ranges s4] in the context: runs the macro's
    statements (both cases of block_start) and leaves SEP [dfull s6 z6 p pin pout ish (rest_after z z6 rest) msgv2 gv;
    deflate_globals gv] with [Hg6 : out_grow z2 z6], [dstate_ranges s6], [strm_ranges z6].  The temp of the buffer
    argument is found in the code (the [Sset _ (0 cast to char * )] of the macro's NULL case). *)
Ltac fbo_window_arg T s4 p :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?S))) _ _ =>
    forward_if (PROPx P (LOCALx (temp T (offset_val (d_block_start s4) (p_window p)) :: L) (SEPx S))) end;
  [ forward; forward; forward; entailer!;
    rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia;
    destruct (p_window p); try contradiction; unfold sem_add_ptr_int, offset_val; cbn;
    rewrite Ptrofs.mul_commut, Ptrofs.mul_one; unfold Ptrofs.of_intu, Ptrofs.of_int;
    rewrite Int.unsigned_repr by rep_lia; reflexivity
  | exfalso; match goal with H : Int64.lt _ _ = true |- _ =>
      unfold Int64.lt in H; rewrite !Int64.signed_repr in H by rep_lia; destruct (zlt _ _); [lia|discriminate] end
  | ].

Ltac fbo_null_arg T :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?S))) _ _ =>
    forward_if (PROPx P (LOCALx (temp T nullval :: L) (SEPx S))) end;
  [ exfalso; match goal with H : Int64.lt _ _ = false |- _ =>
      unfold Int64.lt in H; rewrite !Int64.signed_repr in H by drange; destruct (zlt _ _); [discriminate|] end;
    lia
  | forward; entailer!
  | ].

Ltac fbo_trcall_side :=
  try solve [ apply u64_range
            | rewrite ?Int.unsigned_repr by drange; rewrite ?Int64.signed_repr by drange; lia
            | lazymatch goal with |- ENTAIL _, _ |-- _ =>
                go_lower; apply prop_right; cbn; unfold vl, vi;
                rewrite ?Int.unsigned_repr by drange;
                rewrite sub64_repr, repr_u64; reflexivity end ].

(** After _tr_flush_block: block_start = strstart, flush_pending, and back to [dfull s6 z6]. *)
Ltac fbo_after p pin pout ish gv z rest msgv2 s4 z2 tt5 s6 z6 Hfp :=
  forward; forward;
  rewrite trees_at_open; cbn [fst snd]; unfold dtype_at, stat_at; Intros;
  forward;
  forward_call (p_strm p, p_s p, p_pbuf p, pin, pout, msgv2, rest_after z z2 rest,
                set_d_block_start (set_d_trm s4 tt5) (d_strstart s4), z2, (s6, z6), gv);
  cbn [fst snd];
  let Hg6 := fresh "Hg6" in
  pose proof (c_flush_pending_grow _ _ _ Hfp) as Hg6; cbn [snd] in Hg6;
  rewrite (out_space_prop z6 pout (rest_after z2 z6 (rest_after z z2 rest))) at 1; Intros;
  match goal with E : Zlength (rest_after _ _ _) = z_avail_out z6 |- _ =>
    assert (0 <= z_avail_out z6) by (rewrite <- E; apply Zlength_nonneg);
    rewrite rest_after_trans in E |- * by auto end;
  let Hok6 := fresh "Hok6" in let Hpo4 := fresh "Hpo4" in let Hav2 := fresh "Hav2" in
  rewrite (out_at_prop (tr_out (d_tr s6)) (d_pbm s6) (p_s p) (p_pbuf p)) at 1; Intros;
  match goal with H : out_ok (tr_out (d_tr s6)) (d_pbm s6) |- _ => rename H into Hok6 end;
  assert (Hpo4 : 0 <= d_po s4) by (match goal with H : dstate_ranges s4 |- _ => open_dranges H; lia end);
  assert (Hav2 : 0 <= z_avail_out z2) by drange;
  let o6 := fresh "o6" in let po6 := fresh "po6" in let Es6 := fresh "Es6" in let Hpo6 := fresh "Hpo6" in
  destruct (c_flush_pending_shape _ _ _ Hfp Hpo4 Hav2) as (o6 & po6 & Es6 & Hpo6); cbn [fst] in Es6;
  let Ez1 := fresh "Ez" in let Ez2 := fresh "Ez" in let Ez3 := fresh "Ez" in let Ez4 := fresh "Ez" in
  let Ez5 := fresh "Ez" in let Ez6 := fresh "Ez" in
  destruct (c_flush_pending_z _ _ _ Hfp) as (Ez1 & Ez2 & Ez3 & Ez4 & Ez5 & Ez6);
  cbn [snd] in Ez1, Ez2, Ez3, Ez4, Ez5, Ez6;
  let Hzr6 := fresh "Hzr6" in let Hdr6 := fresh "Hdr6" in
  assert (Hzr6 : strm_ranges z6)
    by (apply (c_flush_pending_ranges _ _ _ Hfp (ltac:(assumption) : strm_ranges z2)); cbn [fst];
        destruct Hok6 as [Hmb _]; exact Hmb);
  assert (Hdr6 : dstate_ranges s6)
    by (rewrite Es6; unfold set_d_out; match goal with H : dstate_ranges s4 |- _ => dranges_tac H end);
  sep_apply (fbo_close s4 tt5 s6 z2 z6 o6 po6 p pin pout ish (rest_after z z6 rest) msgv2 gv Es6 Ez1
               ltac:(rewrite Ez6; assumption) Hzr6 ltac:(assumption) Hdr6 ltac:(drange) ltac:(assumption));
  Intros;
  clear Es6 Ez1 Ez2 Ez3 Ez4 Ez5 Ez6 Hok6 Hpo4 Hav2.

Ltac fbo_tac p pin pout ish gv z rest Hfbo :=
  lazymatch type of Hfbo with c_flush_block_only ?s4 ?z2 ?last = Some (?s6, ?z6) =>
  lazymatch goal with |- semax _ (PROPx _ (LOCALx _ (SEPx (dfull _ _ _ _ _ _ _ ?msgv2 _ :: _)))) _ _ =>
  let T := lazymatch goal with |- context [Sifthenelse _ _ (Sset ?T (Ecast (Ecast (Econst_int _ _) _) _))] => T end in
  let bo := fresh "bo" in let tt5 := fresh "tt5" in let kk5 := fresh "kk5" in
  let Hlong := fresh "Hlong" in let Hsome := fresh "Hsome" in let Hnone := fresh "Hnone" in
  let Htr := fresh "Htr" in let Hfp := fresh "Hfp" in
  destruct (c_flush_block_only_inv _ _ _ _ Hfbo) as (bo & tt5 & kk5 & Hlong & Hsome & Hnone & Htr & Hfp);
  unfold dfull, dstate_at; Intros; unfold match_at, win_at; Intros;
  let Hwok4 := fresh "Hwok4" in
  assert (Hwok4 : mb_ok (d_window s4)) by (match goal with H : dstate_ranges s4 |- _ => open_dranges H; assumption end);
  forward;
  let Hbs := fresh "Hbs" in
  destruct (Z_le_gt_dec 0 (d_block_start s4)) as [Hbs|Hbs];
  [ let b := fresh "b" in let Hrd := fresh "Hrd" in
    destruct (Hsome Hbs) as (b & -> & Hrd);
    let Hr1 := fresh "Hr" in let Hr2 := fresh "Hr" in let Hr3 := fresh "Hr" in let Hr4 := fresh "Hr" in
    destruct (mb_read_inv _ _ _ _ Hrd) as (Hr1 & Hr2 & Hr3 & Hr4 & _);
    let Hbs2 := fresh "Hbs2" in
    assert (Hbs2 : 0 <= d_block_start s4 <= Int.max_unsigned)
      by (assert (Zlength (mb_val (d_window s4)) <= Int.max_unsigned) by drange; lia);
    let Hwp := fresh "Hwp" in
    assert_PROP (isptr (p_window p)) as Hwp by entailer!;
    fbo_window_arg T s4 p;
    forward; forward;
    rewrite deflate_globals_open;
    sep_apply (win_slice_open Ews (d_window s4) (p_window p) _ _ b Hwok4 Hrd); Intros;
    sep_apply (opt_buf_some Ews b (offset_val (d_block_start s4) (p_window p)) ltac:(auto)
                 (mb_read_bytes _ _ _ _ Hwok4 Hrd));
    forward_call (p_s p, p_pbuf p, p_strm p, d_trm s4, offset_val (d_block_start s4) (p_window p), Ews,
                  Some b, u64 (d_strstart s4 - d_block_start s4), last, (tt5, kk5), gv);
    fbo_trcall_side;
    sep_apply (opt_buf_some_inv Ews b (offset_val (d_block_start s4) (p_window p)));
    sep_apply (win_slice_close Ews (d_window s4) (p_window p) _ _ b Hwok4 Hrd ltac:(assumption));
    fbo_after p pin pout ish gv z rest msgv2 s4 z2 tt5 s6 z6 Hfp
  | rewrite (Hnone ltac:(lia)) in Htr;
    fbo_null_arg T;
    forward; forward;
    rewrite deflate_globals_open;
    sep_apply (opt_buf_none Ews);
    forward_call (p_s p, p_pbuf p, p_strm p, d_trm s4, nullval, Ews,
                  @None (list Z), u64 (d_strstart s4 - d_block_start s4), last, (tt5, kk5), gv);
    fbo_trcall_side;
    unfold opt_buf_at; Intros;
    fbo_after p pin pout ish gv z rest msgv2 s4 z2 tt5 s6 z6 Hfp ]
  end end.

(** The same in pieces, so that each case of block_start can be [abstract]ed in its own sentence together with
    the rest of its branch (the compressors' Qed is otherwise far beyond the time budget):
      fbo_pre Hfbo.
      1: abstract (fbo_branch p pin pout ish gv z rest Hfbo fb_tt fb_kk fb_Hsome fb_Hnone fb_Hfp fb_Hwok fb_Hbs; <rest>).
      1: abstract (fbo_branch p pin pout ish gv z rest Hfbo fb_tt fb_kk fb_Hsome fb_Hnone fb_Hfp fb_Hwok fb_Hbs; <rest>).
    Fixed hypothesis names fb_*. *)
Ltac fbo_pre Hfbo :=
  lazymatch type of Hfbo with c_flush_block_only ?s4 ?z2 ?last = Some (?s6, ?z6) =>
  destruct (c_flush_block_only_inv _ _ _ _ Hfbo)
    as (fb_bo & fb_tt & fb_kk & fb_Hlong & fb_Hsome & fb_Hnone & fb_Htr & fb_Hfp);
  unfold dfull, dstate_at; Intros; unfold match_at, win_at; Intros;
  assert (fb_Hwok : mb_ok (d_window s4))
    by (match goal with H : dstate_ranges s4 |- _ => open_dranges H; assumption end);
  forward;
  destruct (Z_le_gt_dec 0 (d_block_start s4)) as [fb_Hbs|fb_Hbs]
  end.

Ltac fbo_branch p pin pout ish gv z rest Hfbo fb_tt fb_kk fb_Hsome fb_Hnone fb_Hfp fb_Hwok fb_Hbs :=
  lazymatch type of Hfbo with c_flush_block_only ?s4 ?z2 ?last = Some (?s6, ?z6) =>
  lazymatch goal with |- semax _ (PROPx _ (LOCALx _ (SEPx (_ :: _)))) _ _ =>
  let msgv2 := lazymatch goal with |- context [strm_at z2 _ _ _ _ ?m _] => m end in
  let T := lazymatch goal with |- context [Sifthenelse _ _ (Sset ?T (Ecast (Ecast (Econst_int _ _) _) _))] => T end in
  lazymatch type of fb_Hbs with
  | 0 <= _ =>
    let b := fresh "b" in let Hrd := fresh "Hrd" in
    destruct (fb_Hsome fb_Hbs) as (b & -> & Hrd);
    let Hr1 := fresh "Hr" in let Hr2 := fresh "Hr" in let Hr3 := fresh "Hr" in let Hr4 := fresh "Hr" in
    destruct (mb_read_inv _ _ _ _ Hrd) as (Hr1 & Hr2 & Hr3 & Hr4 & _);
    let Hbs2 := fresh "Hbs2" in
    assert (Hbs2 : 0 <= d_block_start s4 <= Int.max_unsigned)
      by (assert (Zlength (mb_val (d_window s4)) <= Int.max_unsigned) by drange; lia);
    let Hwp := fresh "Hwp" in
    assert_PROP (isptr (p_window p)) as Hwp by entailer!;
    fbo_window_arg T s4 p;
    forward; forward;
    rewrite deflate_globals_open;
    sep_apply (win_slice_open Ews (d_window s4) (p_window p) _ _ b fb_Hwok Hrd); Intros;
    sep_apply (opt_buf_some Ews b (offset_val (d_block_start s4) (p_window p)) ltac:(auto)
                 (mb_read_bytes _ _ _ _ fb_Hwok Hrd));
    forward_call (p_s p, p_pbuf p, p_strm p, d_trm s4, offset_val (d_block_start s4) (p_window p), Ews,
                  Some b, u64 (d_strstart s4 - d_block_start s4), last, (fb_tt, fb_kk), gv);
    fbo_trcall_side;
    sep_apply (opt_buf_some_inv Ews b (offset_val (d_block_start s4) (p_window p)));
    sep_apply (win_slice_close Ews (d_window s4) (p_window p) _ _ b fb_Hwok Hrd ltac:(assumption));
    fbo_after p pin pout ish gv z rest msgv2 s4 z2 fb_tt s6 z6 fb_Hfp
  | 0 > _ =>
    match goal with Ht : c_tr_flush_block _ _ _ _ = _ |- _ => rewrite (fb_Hnone ltac:(lia)) in Ht end;
    fbo_null_arg T;
    forward; forward;
    rewrite deflate_globals_open;
    sep_apply (opt_buf_none Ews);
    forward_call (p_s p, p_pbuf p, p_strm p, d_trm s4, nullval, Ews,
                  @None (list Z), u64 (d_strstart s4 - d_block_start s4), last, (fb_tt, fb_kk), gv);
    fbo_trcall_side;
    unfold opt_buf_at; Intros;
    fbo_after p pin pout ish gv z rest msgv2 s4 z2 fb_tt s6 z6 fb_Hfp
  end end end.




(** ** F5's test *)
Lemma f5_repr01_zero a : a = 0 \/ a = 1 -> Int.repr a = Int.zero -> a = 0.
Proof. intros [->| ->] H; auto. discriminate. Qed.

Lemma f5_repr01_nz a : a = 0 \/ a = 1 -> Int.repr a <> Int.zero -> a = 1.
Proof. intros [->| ->] H; auto. contradiction. Qed.

Lemma f5_b2z_01 b : Z.b2z b = 0 \/ Z.b2z b = 1.
Proof. destruct b; auto. Qed.

Lemma f5_int_eq0 x : Int.min_signed <= x <= Int.max_signed -> Int.eq (Int.repr x) (Int.repr 0) = (x =? 0).
Proof.
  intros Hx. destruct (Z.eqb_spec x 0) as [->|n]; [apply Int.eq_true|].
  apply Int.eq_false. intros E. apply (f_equal Int.signed) in E. rewrite !Int.signed_repr in E by rep_lia. lia.
Qed.

Lemma f5_int64_eq0 x : 0 <= x <= Int64.max_unsigned -> Int64.eq (Int64.repr x) (Int64.repr 0) = (x =? 0).
Proof.
  intros Hx. destruct (Z.eqb_spec x 0) as [->|n]; [apply Int64.eq_true|].
  apply Int64.eq_false. intros E. apply (f_equal Int64.unsigned) in E. rewrite !Int64.unsigned_repr in E by rep_lia. lia.
Qed.

Ltac f5_hyps :=
  change (Int.repr 0) with Int.zero in * |-;
  repeat match goal with
  | H : Int.repr (Z.b2z ?b) = Int.zero |- _ => apply (f5_repr01_zero _ (f5_b2z_01 b)) in H
  | H : Int.repr (Z.b2z ?b) <> Int.zero |- _ => apply (f5_repr01_nz _ (f5_b2z_01 b)) in H
  | H : Int.repr 1 = Int.zero |- _ => apply (f5_repr01_zero 1 (or_intror eq_refl)) in H
  | H : Int.zero <> Int.zero |- _ => exfalso; apply H; reflexivity
  end.

(** The value goals of the test: case on the three booleans. *)
Ltac f5_val s6 z6 :=
  try unfold Int64.cmpu, Int.cmpu, Int.cmp, Int64.cmp;
  f5_hyps; change Int.zero with (Int.repr 0) in *; change Int64.zero with (Int64.repr 0) in *;
  rewrite ?f5_int_eq0 by drange; rewrite ?f5_int64_eq0
    by (unfold d_pending; match goal with H : out_ok _ _ |- _ =>
          let Hc := fresh in pose proof H as Hc; unfold out_ok in Hc; decompose [and] Hc; lia end);
  let E1 := fresh "E" in let E2 := fresh "E" in let E3 := fresh "E" in
  destruct (z_avail_out z6 =? 0) eqn:E1, (d_pending s6 =? 0) eqn:E2, (d_wrap s6 =? 0) eqn:E3;
  cbn [andb orb negb Z.b2z Z.eqb Pos.eqb bool2val] in *;
  first [ reflexivity | discriminate
        | (apply Z.eqb_neq in E1; lia)
        | (apply Z.eqb_eq in E1; exfalso;
           match goal with H : Int.repr _ <> _ |- _ => apply H; rewrite E1; reflexivity end)
        | (apply Z.eqb_neq in E1;
           match goal with H : Int.repr _ = Int.zero |- _ =>
             change Int.zero with (Int.repr 0) in H; apply repr_eq_u32 in H; [lia|drange|drange] end) ].

(** F5's test, from SEP [dfull s6 z6 ...; ...] before [_t'a = s->strm; _t'b = _t'a->avail_out; if (...) ...]
    to the same SEP and LOCAL [temp T6 (Vint (Int.repr (Z.b2z B)))] before [if (T6) return ...].
    The branches are recognised by their code (VST may drop a branch whose condition is a constant). *)
Ltac f5_branch1 s6 z6 :=
  first [ forward; entailer!; f5_val s6 z6 | forward; forward; entailer!; f5_val s6 z6 ].
Ltac f5_branch2 s6 z6 :=
  first [ forward; entailer!; f5_val s6 z6 | forward; forward; forward; entailer!; f5_val s6 z6 ].

Ltac f5_tac :=
  lazymatch goal with |- semax _ (PROPx _ (LOCALx _ (SEPx (dfull ?s6 ?z6 ?p ?pin ?pout ?ish ?rest ?msgv ?gv :: _)))) _ _ =>
  sep_apply (dfull_f5_open s6 z6 p pin pout ish rest msgv gv); Intros;
  forward; forward;
  let l := lazymatch goal with |- context [Eunop Onotbool (Econst_int (Int.repr ?l) _) _] => l end in
  let T7 := lazymatch goal with |- context [Sifthenelse (Eunop Onotbool _ _) (Sset ?T _) _] => T end in
  let T6 := lazymatch goal with
            |- context [Sifthenelse (Etempvar _ tint) (Sset ?T (Ecast (Econst_int _ _) tbool)) _] => T end in
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?S))) _ _ =>
    forward_if (PROPx P (LOCALx (temp T6 (Vint (Int.repr (Z.b2z ((z_avail_out z6 =? 0) &&
        (negb (l =? 1) || negb (d_pending s6 =? 0) || negb (d_wrap s6 =? 0)))))) :: L) (SEPx S))) end;
  [ let Ea := fresh "Ea" in assert (Ea : z_avail_out z6 = 0) by repr_eq;
    match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?S))) _ _ =>
      forward_if (PROPx P (LOCALx (temp T7 (Vint (Int.repr (Z.b2z (negb (l =? 1) || negb (d_pending s6 =? 0)))))
                                   :: L) (SEPx S))) end;
    match goal with
    | |- semax _ _ (Sifthenelse (Etempvar T7 _) _ _) _ => forward_if; f5_branch2 s6 z6
    | |- semax _ _ (Ssequence (Sifthenelse (Etempvar T7 _) _ _) _) _ => forward_if; f5_branch2 s6 z6
    | _ => f5_branch1 s6 z6
    end
  | forward; entailer!; f5_val s6 z6
  | sep_apply (dfull_f5_close s6 z6 p pin pout ish rest msgv gv ltac:(assumption) ltac:(assumption)
                 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)) ]
  end.

(** After [f5_tac] and [forward_if] on its temp: the model's FLUSH_BLOCK test [Hfb] decided by the branch
    (VST leaves the branch condition as a simplified boolean equation [X = true] / [X = false]). *)
Ltac f5_case Hfb :=
  lazymatch type of Hfb with (if ?B then _ else _) = _ =>
  lazymatch B with context [z_avail_out ?z6 =? 0] =>
  lazymatch B with context [d_pending ?s6 =? 0] =>
  match goal with H : ?X = ?bv |- _ =>
    lazymatch X with context [z_avail_out z6 =? 0] =>
    let EB := fresh "EB" in
    first [ assert (EB : B = true)
              by (clear - H; destruct (z_avail_out z6 =? 0), (d_pending s6 =? 0), (d_wrap s6 =? 0);
                  cbn in *; congruence)
          | assert (EB : B = false)
              by (clear - H; destruct (z_avail_out z6 =? 0), (d_pending s6 =? 0), (d_wrap s6 =? 0);
                  cbn in *; congruence) ];
    rewrite EB in Hfb; clear EB H
    end
  end end end end;
  cbn in Hfb.

(** ** Reading s->sym_next from [dfull] (the tails' [if (s->sym_next)]): the field and a wand back. *)
Lemma peek_gen (P F R : mpred) : (P |-- F * R) -> (R * F |-- P) -> P |-- F * (F -* P).
Proof.
  intros H1 H2. eapply derives_trans; [exact H1|]. apply sepcon_derives; [apply derives_refl|].
  apply wand_sepcon_adjoint. exact H2.
Qed.

Definition sym_rest (s : dstate) (z : strm) (p : dptrs) (pin pout : val) (ish : share) (rest : list val)
    (msgv : val) (gv : globals) : mpred :=
  (!! (strm_ranges z /\ msg_ok (z_msg z) msgv /\ readable_share ish /\ dstate_ranges s /\
       0 <= tr_sym_next (d_tr s) <= Int.max_unsigned /\ 0 <= tr_sym_end (d_tr s) <= Int.max_unsigned /\
       0 <= tr_matches (d_tr s) <= Int.max_unsigned /\ 0 <= tr_lit_bufsize (d_tr s) <= Int.max_unsigned) &&
   (ltree_at (tr_ltree (d_tr s)) (p_s p) * dtree_at (tr_dtree (d_tr s)) (p_s p) *
    out_at (tr_out (d_tr s)) (d_pbm s) (p_s p) (p_pbuf p) *
    @field_at DCS.CS Ews t_ds (DOT _sym_buf) (offset_val (tr_lit_bufsize (d_tr s)) (p_pbuf p)) (p_s p) *
    @field_at DCS.CS Ews t_ds (DOT _lit_bufsize) (vi (tr_lit_bufsize (d_tr s))) (p_s p) *
    @field_at DCS.CS Ews t_ds (DOT _sym_end) (vi (tr_sym_end (d_tr s))) (p_s p) *
    @field_at DCS.CS Ews t_ds (DOT _matches) (vi (tr_matches (d_tr s))) (p_s p) *
    dtype_at (d_tr s) (p_s p) (p_strm p) * trees_rest (d_tr s) (p_s p) (p_strm p) gv *
    win_at s p * hash_at s p * match_at s p * cfg_at s p * stat_at s p *
    strm_at z (p_s p) (p_strm p) pin pout msgv gv * in_obj ish z pin * out_space z pout rest))%logic.

Lemma dfull_sym_peek s z p pin pout ish rest msgv gv :
  dfull s z p pin pout ish rest msgv gv |--
  @field_at DCS.CS Ews t_ds (DOT _sym_next) (vi (tr_sym_next (d_tr s))) (p_s p) *
  (@field_at DCS.CS Ews t_ds (DOT _sym_next) (vi (tr_sym_next (d_tr s))) (p_s p) -*
   dfull s z p pin pout ish rest msgv gv).
Proof.
  apply (peek_gen _ _ (sym_rest s z p pin pout ish rest msgv gv)).
  - unfold dfull, dstate_at, sym_rest. rewrite trees_at_open. unfold d_trm, sym_at. cbn [fst snd]. Intros.
    entailer!.
  - unfold dfull, dstate_at, sym_rest. rewrite trees_at_open. unfold d_trm, sym_at. cbn [fst snd]. Intros.
    entailer!.
Qed.

Lemma dfull_sym_range s z p pin pout ish rest msgv gv :
  dfull s z p pin pout ish rest msgv gv |-- !! (0 <= tr_sym_next (d_tr s) <= Int.max_unsigned).
Proof. unfold dfull, dstate_at. rewrite trees_at_open. unfold d_trm, sym_at. cbn [fst snd]. entailer!. Qed.

(** FLUSH_BLOCK followed by more code (the tails): [if (T6) return ...;] with a post that keeps the test's value. *)
Ltac fb_tail_if :=
  match goal with |- context [temp _ (Vint (Int.repr (Z.b2z ?B)))] =>
    lazymatch B with context [z_avail_out _ =? 0] =>
    match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?S))) _ _ =>
      forward_if (PROPx ((Z.b2z B = 0) :: P) (LOCALx L (SEPx S))) end end end.

Ltac f5_b2z0 :=
  match goal with H : ?X = false |- Z.b2z ?B = 0 =>
    lazymatch X with context [z_avail_out ?z6 =? 0] =>
    lazymatch B with context [d_pending ?s6 =? 0] =>
      clear - H; destruct (z_avail_out z6 =? 0), (d_pending s6 =? 0), (d_wrap s6 =? 0); cbn in *; congruence
    end end end.
