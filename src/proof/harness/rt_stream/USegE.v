(* Law rt_stream (harness/rt_stream.c, data of any length), main's body: the final checks (statements 31... of
   main's body, UMainKit.segE): from IE to the return. Round 1's proof for the bounded harness, with the sizes of
   UMainKit.su_ok (data and out_size up to PTRDIFF_MAX); out is compared with expected, the copy of the data
   made before compression. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.deflate.Obligations.
Require Zlib.proof.deflate.Api_toend.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_stream.LawCS.
Require Import Zlib.proof.harness.rt_stream.UMainStmt.
Require Import Zlib.proof.harness.rt_stream.UDFacts.
Require Import Zlib.proof.harness.rt_stream.UIFacts.
Require Import Zlib.proof.harness.rt_stream.UMainKit.
Require Import Zlib.harness.rt_stream.code.
#[local] Existing Instance LawCS.CS.
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

(* compressed + compressed_len and out + data_len: the pointer arithmetic on a byte object *)
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
Lemma cstream_back (gv : globals) (vc : val) (c : cst) : cstream gv vc c |-- data_at_ Tsh t_z vc * TT.
Proof.
  unfold cstream, srest.
  sep_apply (BoundKit.dstream_data_at_ (Some (cs_s c)) vc nullval gv (cs_ni c) (cs_ain c) (cs_tin c) (cs_no c)
               (cs_aout c) (cs_tout c) (cs_msgv c) (cs_adler c) Api_toend.dstream_to_end).
  rewrite (@data_at__change_composite Zlib.proof.deflate.DCS.CS CS CC_dcs Ews Zlib.proof.deflate.Rep.t_strm)
    by reflexivity.
  rewrite (BoundKit.data_at__Tsh_split t_z vc). cancel.
Qed.

Lemma useg_e : segE_stmt.
Proof.
  intros Espec gv vc vd va u O c z L.
  unfold segE, IE. Intros.
  rewrite istreamA_unfold. unfold cobj, oobj, dobj, eobj, su_locals, lv_locals. Intros. cbn [app].
  destruct u as [lv wb ml st data cap dp ep cp op]; unfold su_ok in H; simpl in *.
  destruct H as (Hl & Hw & Hm & Hs & Hn & Hd & Hc & Pd & Pc & Po).
  assert_PROP (isptr ep) as Pe by entailer!.
  unfold max_size in Hn, Hc.
  unfold istrm_tup. rewrite H1, H2.
  forward.
  forward_call (Int.repr 1).
  { rewrite add_ptr_long_tuchar by (auto; rep_lia).
    eapply derives_trans; [ | apply (test_eq_self TT cp (Zlength O) cap (cbytes cap O))]; [cancel | | auto].
    pose proof (Zlength_nonneg O). lia. }
  { entailer!. rewrite add_ptr_long_tuchar by (auto; rep_lia). destruct cp; try contradiction.
    simpl. unfold sem_cmp_pp. simpl. rewrite peq_true, Ptrofs.eq_true. reflexivity. }
  forward.
  forward_if (PROP () LOCAL (temp _t'37 (vi 1); temp _compressed_len (vl (Zlength O)); temp _level (vi lv);
    temp _window_bits (vi (IFacts.rts_iw wb)); temp _mem_level (vi ml); temp _strategy (vi st);
    temp _data_len (vl (Zlength data)); temp _out_size (vl cap); temp _data dp; temp _expected ep;
    temp _compressed cp;
    temp _out op; lvar _decompressor t_z vd; lvar _at t_p va; lvar _compressor t_z vc; gvars gv)
   SEP (data_at Tsh t_z
          (offset_val (Zlength O) cp, (vi (zf_ai z), (vl (zf_tin z), (offset_val (Zlength data) op,
           (vi (zf_ao z), (vl (zf_tout z), (msg_val gv (zf_msg z), (l_sp L, (gv Zlib.inflate.code._zcalloc,
           (gv Zlib.inflate.code._zcfree, (nullval, (vi (zf_dt z),
           (adler_v (i_wrap (l_s L) =? 0) z Vundef, zf_res z))))))))))))) vd;
        state_mem gv vd L; head_mem L; cstream gv vc c; mem_mgr gv; zfuncs gv; Rm gv;
        malloc_token Ews (tarray tuchar (Zlength data)) dp;
        data_at Ews (tarray tuchar (Zlength data)) (map vi data) dp;
        malloc_token Ews (tarray tuchar (Zlength data)) ep;
        data_at Ews (tarray tuchar (Zlength data)) (map vi data) ep;
        malloc_token Ews (tarray tuchar cap) cp; data_at Ews (tarray tuchar cap) (cbytes cap O) cp;
        malloc_token Ews (tarray tuchar (Zlength data)) op;
        data_at Ews (tarray tuchar (Zlength data)) (cbytes (Zlength data) data) op; data_at_ Tsh t_p va)).
  { rewrite add_ptr_long_tuchar by (auto; rep_lia).
    eapply derives_trans;
      [ | apply (test_eq_self TT op (Zlength data) (Zlength data) (cbytes (Zlength data) data))];
      [cancel | | auto].
    pose proof (Zlength_nonneg data). lia. }
  { rewrite <- (bytes_a Ews (Zlength data) (cbytes (Zlength data) data) op).
    rewrite <- (bytes_a Ews (Zlength data) (map vi data) ep).
    forward_call (op, Ews, op, 0, Zlength data, cbytes (Zlength data) data, data,
                  ep, Ews, ep, 0, Zlength data, map vi data, data, Zlength data).
    { split; [apply cbuf_ok_data | apply cbuf_ok_data']; auto. }
    rewrite (bytes_a Ews (Zlength data) (cbytes (Zlength data) data) op).
    rewrite (bytes_a Ews (Zlength data) (map vi data) ep).
    destruct (list_eq_dec Z.eq_dec data data) as [_ | NE]; [ | congruence].
    forward. unfold POST_m. simpl RA_normal. entailer!. }
  { exfalso. rewrite add_ptr_long_tuchar in H by (auto; rep_lia). congruence. }
  forward_call (Int.repr 1).
  sep_apply (cstream_back gv vc c).
  forward.
  Exists (Int.repr 0).
  match goal with |- context [data_at Tsh t_z ?v vd] => sep_apply (data_at_data_at_ Tsh t_z v vd) end.
  entailer!.
Qed.
