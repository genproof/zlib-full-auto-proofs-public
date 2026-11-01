(* Law rt_session (harness/rt_session.c): main's final checks (statements 74-84) without a header (SMKit.v, [segE_W_stmt]). *)
(* The proof is rt_stream_trailing's (TSegE.tseg_e) on this program, with the check of the flag asked first and the
   return of [!with_head] (the header checks are not reached without a header): asked is compared with
   with_dict && window_bits > 0 (window_bits as inflateInit2 got it, 8 changed into 9: same sign), next_in with
   input + compressed_len, next_out with out + data_len, and out's bytes with expected's. At the return the
   locals' memory is given back to the stack frame and the rest to TT. Statements 74 and 75 only read the state and
   are proved here from IE_W to IE_W; statements 76-84 are SMEWTail.v's. *)
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
Require Import Zlib.proof.harness.rt_session.SMEWTail.
Require Import Zlib.harness.rt_session.code.
#[local] Existing Instance SCS.CS.
Local Open Scope logic.

(* the flag main compares asked with: window_bits > 0 on the value inflateInit2 got (8 changed into 9), the same
   sign as deflate's windowBits *)
Lemma asked_val (w : Z) : -2147483648 <= w <= 2147483647 ->
  vi (Z.b2z (0 <? w)) = bool2val (Int.lt (Int.repr 0) (Int.repr (rts_iw w))).
Proof.
  intros Hw. unfold rts_iw, Int.lt, bool2val, vi.
  destruct (w =? 8) eqn:E8; [apply Z.eqb_eq in E8; subst; reflexivity | ].
  rewrite !Int.signed_repr by rep_lia.
  destruct (Z.ltb_spec 0 w), (zlt 0 w); try reflexivity; lia.
Qed.

(* statement 74: gp_assert(asked == (with_dict && window_bits > 0)) *)
Lemma sm_segE_W_74 : forall {Espec : OracleKind} gv vh vg vc va vd u O c src ip z L,
  semax Delta_s (IE_W gv vh vg vc va vd u O c src ip z L) (first segE)
    (overridePost (IE_W gv vh vg vc va vd u O c src ip z L) POST_s).
Proof.
  intros Espec gv vh vg vc va vd u O c src ip z L.
  unfold first, segE, IE_W. Intros.
  unfold lvs, lv_locals, c_locals, d_locals. cbn [app].
  unfold POST_s.
  assert (Hwb : rs32 (su_wbits u)) by (destruct H as ((? & ? & _) & _); auto).
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'85 (vi (Z.b2z (with_dict u && (0 <? su_wbits u)))) :: Q) (SEPx R))) end.
  { forward. entailer!. match goal with Hx : with_dict u = _ |- _ => rewrite Hx end. apply asked_val. exact Hwb. }
  { forward. entailer!. match goal with Hx : with_dict u = _ |- _ => rewrite Hx end. reflexivity. }
  forward_call (Int.repr 1).
  { entailer!. rewrite Int.eq_true. reflexivity. }
  entailer!.
Qed.

(* statement 75: gp_assert(decompressor.next_in == input + compressed_len) *)
Lemma sm_segE_W_75 : forall {Espec : OracleKind} gv vh vg vc va vd u O c src ip z L,
  semax Delta_s (IE_W gv vh vg vc va vd u O c src ip z L) (first segE_75)
    (overridePost (IE_W gv vh vg vc va vd u O c src ip z L) POST_s).
Proof.
  intros Espec gv vh vg vc va vd u O c src ip z L.
  unfold first, segE_75, segE, IE_W. Intros.
  rewrite istreamA_unfold.
  unfold lvs, lv_locals, iobj, c_locals, d_locals. Intros. cbn [app].
  unfold POST_s.
  pose proof H4 as (Hso & Hsub & Hsb).
  unfold max_size in Hso.
  unfold istrm_tup. rewrite H2.
  forward.
  forward_call (Int.repr 1).
  { rewrite add_ptr_long_tuchar by (auto; rep_lia).
    eapply derives_trans; [ | apply (test_eq_self TT ip (Zlength O) (Zlength src) (map vi src))]; [cancel | | auto].
    pose proof (Zlength_nonneg O). lia. }
  { entailer!. rewrite add_ptr_long_tuchar by (auto; rep_lia). destruct ip; try contradiction.
    simpl. unfold sem_cmp_pp. simpl. rewrite peq_true, Ptrofs.eq_true. reflexivity. }
  entailer!.
Qed.

(* statements 74 and 75 only read the state; from statement 76 on: SMEWTail.v *)
Lemma sm_segE_W : segE_W_stmt.
Proof.
  intros Espec gv vh vg vc va vd u O c src ip z L.
  change segE with (Ssequence (first segE) (Ssequence (first segE_75) segE_76)).
  eapply semax_seq; [apply sm_segE_W_74 | ].
  eapply semax_seq; [apply sm_segE_W_75 | ].
  apply sm_segE_W_76.
Qed.
