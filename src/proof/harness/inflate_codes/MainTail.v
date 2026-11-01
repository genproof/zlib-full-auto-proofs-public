(* Law inflate_codes, main: the statements after the loop (inflateEnd, then every entry point on the ended stream
   and on Z_NULL, free(src), return 0). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessRef Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_codes.LawCS Zlib.proof.harness.inflate_codes.Globals
               Zlib.proof.harness.inflate_codes.Facts Zlib.proof.harness.inflate_codes.MainKit.
Require Import Zlib.harness.x_inflate_codes.code.

Ltac gpa := forward_call (Int.repr 1); [ solve [entailer!; try reflexivity] .. | ].

Lemma tl_istream_opt gv shs (vs: val) z st: isptr vs -> istream_opt gv shs vs z st = istream gv shs vs z st.
Proof. intros P. unfold istream_opt. destruct (eq_dec vs nullval); [subst; contradiction | reflexivity]. Qed.

Lemma tl_istream_opt_null gv shs z st: istream_opt gv shs nullval z st = emp.
Proof. unfold istream_opt. rewrite if_true by reflexivity. reflexivity. Qed.

Lemma tl_is_live_none (p: val): is_live p None = None.
Proof. unfold is_live. destruct (eq_dec p nullval); reflexivity. Qed.

Lemma tl_on_live_none (p: val) z f: on_live p z None f = (Z_STREAM_ERROR, z, None).
Proof. unfold on_live. rewrite tl_is_live_none. reflexivity. Qed.

Definition tl_strm_tuple : Type :=
  (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * val)))))))))))))%type.

Lemma tl_strm_cs sh (v: tl_strm_tuple) q:
  @data_at Zlib.units.Inflate.CS sh Rep.t_strm v q = @data_at CS sh (Tstruct _z_stream_s noattr) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity]. Qed.

Lemma tl_uint_cs sh q:
  @data_at_ Zlib.units.Inflate.CS sh tuint q = @data_at_ CS sh tuint q.
Proof. unfold data_at_, field_at_. apply equal_f; apply (@field_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity]. Qed.

Definition tl_tup (gv: globals) (z: zfields) (sp: val) :=
  (zf_ni z, (Vint (Int.repr (zf_ai z)), (Vlong (Int64.repr (zf_tin z)), (zf_no z, (Vint (Int.repr (zf_ao z)),
   (Vlong (Int64.repr (zf_tout z)), (msg_val gv (zf_msg z), (sp, (gv Zlib.inflate.code._zcalloc,
   (gv Zlib.inflate.code._zcfree, (nullval, (Vint (Int.repr (zf_dt z)), (Vlong (Int64.repr (zf_adler z)),
   zf_res z))))))))))))).

Lemma tl_istream_none gv shs vs z:
  istream gv shs vs z None =
  !! (zf_ok z /\ writable_share shs) &&
  @data_at CS shs (Tstruct _z_stream_s noattr) (tl_tup gv z nullval) vs.
Proof.
  unfold istream, zstrm_at, strm_rep.
  rewrite tl_strm_cs. reflexivity.
Qed.

Lemma tl_fold gv shs vs z:
  zf_ok z -> writable_share shs ->
  @data_at CS shs (Tstruct _z_stream_s noattr) (tl_tup gv z nullval) vs |-- istream gv shs vs z None.
Proof. intros. rewrite tl_istream_none. entailer!. Qed.

Lemma tl_b: upd_Znth 0 (default_val (tarray tuchar 1)) (Vint (Int.zero_ext 8 (Int.repr 0))) = [Vint (Int.repr 0)].
Proof. reflexivity. Qed.

(* the stream after the four stores *)
Definition tl_z (z: zfields) (vb: val) : zfields :=
  ZF vb 1 (zf_tin z) vb 1 (zf_tout z) (zf_msg z) (zf_dt z) (zf_adler z) (zf_res z).

Lemma tl_z_ok z vb: zf_ok z -> zf_ok (tl_z z vb).
Proof. unfold zf_ok, tl_z; simpl. intros; rep_lia. Qed.

Lemma tl_inflate_none flush p z ib inp ob r z2 st2 ow:
  inflate_rel flush p z None ib inp ob r z2 st2 ow -> r = Z_STREAM_ERROR /\ z2 = z /\ st2 = None.
Proof.
  intros [(_ & ? & ? & ? & _) | (_ & L & o & res & winp & E & _)]; [auto | discriminate].
Qed.

Lemma tl_inflate_pre z vb: isptr vb ->
  in_tok_ok false (InBuf Tsh vb 0 1 [Vint (Int.repr 0)]) /\
  out_tok_ok false (Some (OutBuf Tsh vb 0 1 [Vint (Int.repr 0)])) /\
  zf_ni (tl_z z vb) = in_ptr (InBuf Tsh vb 0 1 [Vint (Int.repr 0)]) 0 /\
  in_ok (InBuf Tsh vb 0 1 [Vint (Int.repr 0)]) [0] /\
  (zf_no (tl_z z vb) = out_ptr (OutBuf Tsh vb 0 1 [Vint (Int.repr 0)]) 0 /\
   out_ok (OutBuf Tsh vb 0 1 [Vint (Int.repr 0)]) (zf_ao (tl_z z vb))) /\
  zf_ai (tl_z z vb) <= Int.max_signed /\ zf_ao (tl_z z vb) <= Int.max_signed.
Proof.
  intros P. destruct vb; try contradiction. unfold tl_z, in_ok, out_ok, in_ptr, out_ptr; simpl.
  rewrite Ptrofs.add_zero.
  repeat match goal with |- _ /\ _ => split end; auto; try rep_lia; try apply readable_share_top;
    try apply writable_share_top.
  unfold bytes_ok; repeat constructor; rep_lia.
Qed.

Lemma tl_rstream_opt gv shs (vs: val) z: isptr vs -> rstream_opt gv shs vs z RNone = istream gv shs vs z None.
Proof. intros P. unfold rstream_opt. destruct (eq_dec vs nullval); [subst; contradiction | reflexivity]. Qed.

Lemma tl_rs_live (p: val): rs_live p RNone = None.
Proof. unfold rs_live. destruct (eq_dec p nullval); reflexivity. Qed.

Lemma tl_reset_pre (p: val) f z: reset_pre p RNone f z.
Proof. unfold reset_pre. rewrite tl_rs_live. exact I. Qed.

Lemma tl_reset_post gv shs (p: val) z f: reset_post gv shs p z RNone f = rstream_opt gv shs p z RNone.
Proof. unfold reset_post. rewrite tl_rs_live. reflexivity. Qed.

Lemma tl_reset_ret (p: val) z f: reset_ret p RNone f z = Z_STREAM_ERROR.
Proof. unfold reset_ret. rewrite tl_rs_live. reflexivity. Qed.

Definition tl_z0 : zfields := ZF nullval 0 0 nullval 0 0 None 0 0 nullval.

Lemma seg_tail_ok {Espec: OracleKind} gv vs vo vosn vb vdl srcp src z L Fr :
  isptr srcp -> Zlength src <= 2 ^ 24 ->
  semax Delta_m (tail_pre gv vs vo vosn vb vdl srcp src z L Fr) seg_tail POST_m.
Proof.
  intros Psrc Hsrc.
  unfold tail_pre, seg_tail.
  assert_PROP (live_ok L /\ zf_ok z /\ isptr vs /\ isptr vb /\ isptr vdl) as LZ
    by (unfold istream; entailer!).
  destruct LZ as (LOK & ZOK & Pvs & Pvb & Pvdl).
  forward_call (gv, Tsh, vs, z, Some L).
  { rewrite tl_istream_opt by auto. cancel. }
  rewrite tl_istream_opt by auto.
  unfold is_live; rewrite if_false by (intro; subst; contradiction).
  gpa.
  rewrite tl_istream_none. Intros.
  forward. gpa.
  forward. forward. forward. forward. forward.
  match goal with |- context [data_at Tsh (tarray tuchar 1) ?v vb] =>
    replace v with [Vint (Int.repr 0)] by reflexivity end.
  match goal with |- context [data_at Tsh (Tstruct _z_stream_s noattr) ?v vs] =>
    replace v with (tl_tup gv (tl_z z vb) nullval) by reflexivity end.
  pose proof (tl_z_ok z vb ZOK) as ZOK'.
  sep_apply (tl_fold gv Tsh vs (tl_z z vb) ZOK' H).
  forward_call (gv, Tsh, vs, tl_z z vb, @None live, InBuf Tsh vb 0 1 [Vint (Int.repr 0)], [0],
                Some (OutBuf Tsh vb 0 1 [Vint (Int.repr 0)]), 0, Ers, Ers, false, false).
  { rewrite tl_istream_opt, tl_is_live_none by auto. simpl. cancel. }
  { apply tl_inflate_pre; auto. }
  Intros vret. destruct vret as [[[r z2] st2] ow]; cbn [fst snd] in *.
  match goal with H: inflate_rel _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    destruct (tl_inflate_none _ _ _ _ _ _ _ _ _ _ H) as (-> & -> & ->) end.
  rewrite tl_istream_opt, tl_is_live_none by auto. simpl head_opt; simpl bufs_opt.
  gpa.
  (* inflateEnd *)
  forward_call (gv, Tsh, vs, tl_z z vb, @None live).
  { rewrite tl_istream_opt by auto. cancel. }
  rewrite tl_istream_opt, tl_is_live_none by auto.
  gpa.
  (* inflateReset *)
  forward_call (gv, Tsh, vs, tl_z z vb, RNone).
  { rewrite tl_rstream_opt by auto. cancel. }
  { apply tl_reset_pre. }
  rewrite tl_reset_post, tl_reset_ret, tl_rstream_opt by auto.
  gpa.
  (* inflateReset2 *)
  forward_call (gv, Tsh, vs, tl_z z vb, RNone, 15).
  { rewrite tl_rstream_opt by auto. cancel. }
  { apply tl_reset_pre. }
  rewrite tl_reset_post, tl_reset_ret, tl_rstream_opt by auto.
  gpa.
  (* inflateSetDictionary *)
  rewrite <- (bytes_inflate_cs Tsh 1 _ vb).
  forward_call (gv, Tsh, vs, tl_z z vb, @None live, Tsh, vb, 0, 1, [Vint (Int.repr 0)], [0], false).
  { rewrite tl_istream_opt by auto. cancel. }
  { repeat match goal with |- _ /\ _ => split end; auto; try rep_lia; try apply readable_share_top.
    - discriminate.
    - unfold bytes_ok; repeat constructor; rep_lia. }
  Intros vret. rewrite tl_on_live_none. unfold fst3, snd3, thd3; cbn [fst snd].
  rewrite tl_istream_opt by auto.
  gpa.
  (* inflateGetDictionary *)
  rewrite <- (tl_uint_cs Tsh vdl).
  forward_call (gv, Tsh, vs, tl_z z vb, @None live, DBuf Tsh vb 0 1 [Vint (Int.repr 0)], vdl).
  { rewrite tl_istream_opt by auto. unfold dict_rep, len_rep. rewrite if_false by (intro; subst; contradiction).
    cancel. }
  { rewrite tl_is_live_none. exact I. }
  rewrite tl_istream_opt, tl_is_live_none by auto. unfold dict_rep, len_rep.
  rewrite if_false by (intro; subst; contradiction).
  gpa.
  (* inflateSync *)
  forward_call (gv, Tsh, vs, tl_z z vb, @None live, InBuf Tsh vb 0 1 [Vint (Int.repr 0)], [0]).
  { rewrite tl_istream_opt by auto. unfold in_rep. cancel. }
  { destruct (tl_inflate_pre z vb Pvb) as (_ & _ & E & Hin & _). auto. }
  rewrite tl_on_live_none. unfold fst3, snd3, thd3; cbn [fst snd].
  rewrite tl_istream_opt by auto. unfold in_rep.
  gpa.
  (* inflatePrime *)
  forward_call (gv, Tsh, vs, tl_z z vb, @None live, 1, 1).
  { rewrite tl_istream_opt by auto. cancel. }
  rewrite tl_on_live_none. unfold fst3, snd3, thd3; cbn [fst snd].
  rewrite tl_istream_opt by auto.
  gpa.
  (* inflateValidate *)
  forward_call (gv, Tsh, vs, tl_z z vb, @None live, 1).
  { rewrite tl_istream_opt by auto. cancel. }
  rewrite tl_on_live_none. unfold fst3, snd3, thd3; cbn [fst snd].
  rewrite tl_istream_opt by auto.
  gpa.
  (* inflateMark *)
  forward_call (gv, Tsh, vs, tl_z z vb, @None live).
  { rewrite tl_istream_opt by auto. cancel. }
  rewrite tl_istream_opt, tl_is_live_none by auto.
  gpa.
  (* inflateCodesUsed *)
  forward_call (gv, Tsh, vs, tl_z z vb, @None live).
  { rewrite tl_istream_opt by auto. cancel. }
  rewrite tl_istream_opt, tl_is_live_none by auto.
  gpa.
  (* inflate(Z_NULL, Z_NO_FLUSH) *)
  forward_call (gv, Tsh, nullval, tl_z0, @None live, InNull, @nil Z, @None outbuf, 0, Ers, Ers, false, false).
  { rewrite tl_istream_opt_null, tl_is_live_none. simpl. cancel. }
  { unfold tl_z0; simpl. repeat match goal with |- _ /\ _ => split end; auto; rep_lia. }
  Intros vret2. destruct vret2 as [[[r z2] st2] ow2]; cbn [fst snd] in *.
  match goal with H: inflate_rel _ nullval _ _ _ _ _ _ _ _ _ |- _ =>
    destruct (tl_inflate_none _ _ _ _ _ _ _ _ _ _ H) as (-> & -> & ->) end.
  rewrite tl_istream_opt_null, tl_is_live_none. simpl head_opt; simpl bufs_opt.
  gpa.
  (* inflateEnd(Z_NULL) *)
  forward_call (gv, Tsh, nullval, tl_z0, @None live).
  rewrite tl_istream_opt_null, tl_is_live_none.
  gpa.
  (* free(src) *)
  forward_call (tarray tuchar (Zlength src), srcp, gv).
  { rewrite if_false by (intro; subst; contradiction).
    sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength src)) (bytes_rep src) srcp). cancel. }
  rewrite (bytes_inflate_cs Tsh 1 _ vb), (tl_uint_cs Tsh vdl), tl_istream_none. Intros.
  forward. Exists (Int.repr 0). apply andp_right; [apply prop_right; reflexivity | ].
  sep_apply (data_at_data_at_ Tsh (Tstruct _z_stream_s noattr) (tl_tup gv (tl_z z vb) nullval) vs).
  sep_apply (data_at_data_at_ Tsh (tarray tuchar 1) [Vint (Int.repr 0)] vb).
  cancel.
Qed.
