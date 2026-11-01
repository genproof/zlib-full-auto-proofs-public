(* Law rt_session (harness/rt_session.c): main's final checks without a header (SMKit.v, [segE_W_stmt]), from
   statement 76 on: next_out against out + data_len and out's bytes against expected's, then [if (!with_head) return
   0] (with_head = 0: the header checks 78-84 are not reached). Statements 74 and 75 (SMSegEW.v) only read the
   state, so this part starts from the same assertion IE_W. The lemmas before it are the kit of the three pieces of
   segE: the decompressor's struct as main reads it, the pointer comparisons and the byte objects of bytes_eq. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.deflate.Api_toend.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SDFacts.
Require Import Zlib.proof.harness.rt_session.SIFacts.
Require Import Zlib.proof.harness.rt_session.SMainStmt.
Require Import Zlib.proof.harness.rt_session.SMKit.
Require Import Zlib.harness.rt_session.code.
#[local] Existing Instance SCS.CS.
Local Open Scope logic.

(* the decompressor's struct z_stream as main reads it: istreamA's struct at the law's compspecs, and the
   memory behind strm->state *)
Definition istrm_tup (gv : globals) (z : zfields) (adv sp : val) : reptype t_z :=
  (zf_ni z, (vi (zf_ai z), (vl (zf_tin z), (zf_no z, (vi (zf_ao z), (vl (zf_tout z), (msg_val gv (zf_msg z),
   (sp, (gv Zlib.inflate.code._zcalloc, (gv Zlib.inflate.code._zcfree, (nullval, (vi (zf_dt z),
   (adv, zf_res z))))))))))))).

Lemma strm_cs sh (v : reptype t_z) q :
  @data_at Zlib.units.Inflate.CS sh t_z v q = data_at sh t_z v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity]. Qed.

Lemma istreamA_unfold gv shs vs z av L :
  istreamA gv shs vs z av (Some L) =
  (!! (zf_ok z /\ writable_share shs /\ live_ok L) &&
   (data_at shs t_z (istrm_tup gv z (adler_v (raw_live (Some L)) z av) (l_sp L)) vs * state_mem gv vs L)).
Proof.
  unfold istreamA, zstrm_atA. change Zlib.proof.inflate.Rep.t_strm with t_z.
  rewrite strm_cs.
  apply pred_ext; entailer!.
Qed.

(* input + compressed_len and out + data_len: the pointer arithmetic on a byte object *)
Lemma add_ptr_long_tuchar (p : val) (n : Z) :
  isptr p -> 0 <= n <= Int64.max_unsigned -> force_val (sem_add_ptr_long tuchar p (vl n)) = offset_val n p.
Proof.
  intros Pp Hn. destruct p; try contradiction. unfold sem_add_ptr_long, vl. simpl.
  f_equal. f_equal. rewrite Ptrofs.mul_commut, Ptrofs.mul_one. unfold Ptrofs.of_int64.
  rewrite Int64.unsigned_repr by lia. reflexivity.
Qed.

(* a pointer into or one past a malloc'ed byte object is weakly valid, so comparing it with itself is
   defined (it also holds for an empty object, through its malloc token) *)
Local Transparent denote_tc_test_eq.
Lemma test_eq_self (R : mpred) (p : val) (lo n : Z) (contents : list val) :
  0 <= lo <= n -> isptr p ->
  (malloc_token Ews (tarray tuchar n) p * data_at Ews (tarray tuchar n) contents p) * R
  |-- denote_tc_test_eq (offset_val lo p) (offset_val lo p).
Proof.
  intros Hlo Pp.
  assert (W : (malloc_token Ews (tarray tuchar n) p * data_at Ews (tarray tuchar n) contents p) * R
              |-- weak_valid_pointer (offset_val lo p)).
  { apply sepcon_weak_valid_pointer1.
    apply (cbuf_weak_valid true Ews Ews p lo n contents); auto. }
  destruct p; try contradiction. unfold denote_tc_test_eq, offset_val, test_eq_ptrs.
  unfold sameblock. destruct (peq b b) as [E | NE]; [ | congruence]. cbn [proj_sumbool].
  apply andp_right; apply W.
Qed.
Local Opaque denote_tc_test_eq.

(* byte objects at the compspecs of bytes_eq's specification (the adler32 unit's) and at the law's *)
Lemma bytes_a sh n (v : list val) q :
  @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) v q = data_at sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_adler32); [apply JMeq_refl | reflexivity]. Qed.

(* out holding exactly the data, as bytes_eq takes it *)
Lemma cbuf_ok_data (p : val) (data : list Z) :
  isptr p -> RTDIface.rbytes data ->
  cbuf_ok false p Ews p 0 (Zlength data) (Zlength data) (cbytes (Zlength data) data) data.
Proof.
  intros Pp Hb. unfold cbytes. rewrite Z.sub_diag, Zrepeat_0, app_nil_r.
  apply cbuf_ok_whole; auto.
  unfold is_bytes, RTDIface.rbytes in *. eapply Forall_impl; [ | exact Hb]. simpl. rep_lia.
Qed.

Lemma cbuf_ok_data' (p : val) (data : list Z) :
  isptr p -> RTDIface.rbytes data ->
  cbuf_ok false p Ews p 0 (Zlength data) (Zlength data) (map vi data) data.
Proof.
  intros Pp Hb. pose proof (cbuf_ok_data p data Pp Hb) as C. unfold cbytes in C.
  rewrite Z.sub_diag, Zrepeat_0, app_nil_r in C. exact C.
Qed.

(* at the return: the compressor, whatever deflate's state, gives back the local's memory *)
Lemma cstream_back (gv : globals) (vc ghp : val) (c : cst) : cstream gv vc ghp c |-- data_at_ Tsh t_z vc * TT.
Proof.
  unfold cstream, srest.
  sep_apply (BoundKit.dstream_data_at_ (Some (cs_s c)) vc ghp gv (cs_ni c) (cs_ain c) (cs_tin c) (cs_no c)
               (cs_aout c) (cs_tout c) (cs_msgv c) (cs_adler c) Api_toend.dstream_to_end).
  rewrite (@data_at__change_composite Zlib.proof.deflate.DCS.CS CS CC_dcs Ews Zlib.proof.deflate.Rep.t_strm)
    by reflexivity.
  rewrite (BoundKit.data_at__Tsh_split t_z vc). cancel.
Qed.

(* segE from statement 75 on, from statement 76 on *)
Definition segE_75 : statement := match segE with Ssequence _ r => r | s => s end.
Definition segE_76 : statement := match segE_75 with Ssequence _ r => r | s => s end.

Lemma sm_segE_W_76 : forall {Espec : OracleKind} gv vh vg vc va vd u O c src ip z L,
  semax Delta_s (IE_W gv vh vg vc va vd u O c src ip z L) segE_76 POST_s.
Proof.
  intros Espec gv vh vg vc va vd u O c src ip z L.
  unfold segE_76, segE_75, segE, IE_W. Intros.
  rewrite istreamA_unfold.
  unfold head_opt, oobj, dobj, eobj, lvs, lv_locals, c_locals, d_locals. Intros. cbn [app].
  unfold POST_s.
  destruct H as ((Hlv & Hwb & Hml & Hst & Hpar & Hch & Hdl & Hdb & Hxl & Hxb & Hnl & Hnb & Hcl & Hcb & Hn & Hd & Hc &
    Htx & Htm & Hos & Hhc & Pdict & Px & Pn & Pcm & Pd) & Pdc & Pxc & Pnc & Pcc & Pe & Pc & Po & Pgx & Pgn & Pgc).
  clear Hlv Hml Hst Hpar Hch Hdl Hdb Hxl Hxb Hnl Hnb Hcl Hcb Htx Htm Hos Hhc.
  unfold max_size in Hn.
  unfold istrm_tup, bobj. rewrite H2, H3. Intros.
  forward.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'86 (vi 1) :: Q) (SEPx R))) end.
  { rewrite add_ptr_long_tuchar by (auto; rep_lia).
    eapply derives_trans;
      [ | apply (test_eq_self TT (su_op u) (Zlength (su_data u)) (Zlength (su_data u))
                   (cbytes (Zlength (su_data u)) (su_data u)))];
      [cancel | | auto].
    pose proof (Zlength_nonneg (su_data u)). lia. }
  { rewrite <- (bytes_a Ews (Zlength (su_data u)) (cbytes (Zlength (su_data u)) (su_data u)) (su_op u)).
    rewrite <- (bytes_a Ews (Zlength (su_data u)) (map vi (su_data u)) (su_ep u)).
    forward_call (su_op u, Ews, su_op u, 0, Zlength (su_data u), cbytes (Zlength (su_data u)) (su_data u),
                  su_data u, su_ep u, Ews, su_ep u, 0, Zlength (su_data u), map vi (su_data u), su_data u,
                  Zlength (su_data u)).
    { split; [apply cbuf_ok_data | apply cbuf_ok_data']; auto. }
    rewrite (bytes_a Ews (Zlength (su_data u)) (cbytes (Zlength (su_data u)) (su_data u)) (su_op u)).
    rewrite (bytes_a Ews (Zlength (su_data u)) (map vi (su_data u)) (su_ep u)).
    destruct (list_eq_dec Z.eq_dec (su_data u) (su_data u)) as [_ | NE]; [ | congruence].
    forward. entailer!. }
  { exfalso. rewrite add_ptr_long_tuchar in H by (auto; rep_lia). congruence. }
  forward_call (Int.repr 1).
  rewrite H0. cbn [Z.b2z].
  forward_if.
  2: { exfalso. apply H. reflexivity. }
  sep_apply (cstream_back gv vc (ghp vh u) c).
  unfold hobj, graw. Intros.
  forward.
  Exists (Int.repr 0).
  match goal with |- context [data_at Tsh t_z ?v vd] => sep_apply (data_at_data_at_ Tsh t_z v vd) end.
  sep_apply (data_at_data_at_ Tsh t_g (hvals u) vh).
  sep_apply (data_at_data_at_ Tsh t_g (gval u) vg).
  entailer!.
Qed.
