(* Law api_deterministic (data of any length): the loop body from the NULL test of the four objects to the
   nondet_u8 test (DetKit2.det_pre_stmt's second half): when a copy of the piece is NULL main returns 0 (here),
   when an output space is NULL too (DetPreNullOut2.v), else main offers the piece on both streams
   (DetPreOffer2.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Rep.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.deflate.DetFacts2.
Require Zlib.proof.deflate.DModel5.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.api_deterministic.DetCS2.
Require Import Zlib.proof.harness.api_deterministic.DetMainStmt2.
Require Import Zlib.proof.harness.api_deterministic.DetKit2.
Require Import Zlib.proof.harness.api_deterministic.DetPreOffer2.
Require Import Zlib.proof.harness.api_deterministic.DetPreNullOut2.
Require Import Zlib.harness.api_deterministic.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

(* a copy of the piece is NULL: main returns 0 (both streams back to main's locals, everything else dropped) *)
Lemma det_pre_null_in {Espec : OracleKind} J n data datap v1 v2 sp1 sp2 gv ls off fl room in1 in2 out1 out2 :
  in1 = nullval \/ in2 = nullval ->
  semax Delta_m (M_at J n data datap v1 v2 sp1 sp2 gv ls off fl room in1 in2 out1 out2) lsuf7
    (Rbody J n data datap v1 v2 sp1 sp2 gv).
Proof.
  intros Hnn.
  unfold M_at, J_ok, setup_ok. Intros.
  unfold lsuf7, Rbody, loop1_ret_assert, POST_m, overridePost, frame_ret_assert. cbv beta iota.
  set (tk := Z.min (off - ls_read ls) 4294967295) in *.
  assert (Htk0 : 0 <= tk <= 4294967295) by (unfold tk; rep_lia).
  abbreviate_semax.
  (* the NULL test needs only the four objects: the rest is frozen *)
  freeze FR := (mem_mgr gv) (deflate_globals gv) (data_at Ews _ _ datap) (shead v1 _ _ _ _ _ _ _)
                 (shead v2 _ _ _ _ _ _ _) TT.
  destruct (eq_dec in1 nullval) as [E1|E1].
  { subst in1. destruct (eq_dec nullval nullval) as [_|]; [|contradiction].
    forward_if (temp _t'21 (vi 1)); [ | det_false | ]. { forward. apply ENTAIL_refl. }
    forward_if (temp _t'22 (vi 1)); [ | det_false | ]. { forward. apply ENTAIL_refl. }
    forward_if (temp _t'23 (vi 1)); [ | det_false | ]. { forward. apply ENTAIL_refl. }
    forward_if; [ | det_false].
    thaw FR. det_ret. }
  destruct (eq_dec in1 nullval); [contradiction | ]. Intros.
  destruct (eq_dec in2 nullval) as [E2|E2].
  { subst in2. destruct (eq_dec nullval nullval) as [_|]; [|contradiction].
    forward_if (temp _t'21 (vi 1)); [ det_false | | ]. { forward. apply ENTAIL_refl. }
    forward_if (temp _t'22 (vi 1)); [ | det_false | ]. { forward. apply ENTAIL_refl. }
    forward_if (temp _t'23 (vi 1)); [ | det_false | ]. { forward. apply ENTAIL_refl. }
    forward_if; [ | det_false].
    thaw FR. det_ret. }
  destruct Hnn; contradiction.
Qed.

Lemma det_pre_tail {Espec : OracleKind} J n data datap v1 v2 sp1 sp2 gv ls off fl room in1 in2 out1 out2 :
  (forall ci, semax Delta_m (C_at J n data datap v1 v2 sp1 sp2 gv ls ci (c0 ls)) lsuf10
                (Rbody J n data datap v1 v2 sp1 sp2 gv)) ->
  semax Delta_m (M_at J n data datap v1 v2 sp1 sp2 gv ls off fl room in1 in2 out1 out2) lsuf7
    (Rbody J n data datap v1 v2 sp1 sp2 gv).
Proof.
  intros HC.
  destruct (eq_dec in1 nullval); [ apply det_pre_null_in; tauto | ].
  destruct (eq_dec in2 nullval); [ apply det_pre_null_in; tauto | ].
  destruct (eq_dec out1 nullval); [ apply det_pre_null_out; tauto | ].
  destruct (eq_dec out2 nullval); [ apply det_pre_null_out; tauto | ].
  apply det_pre_ok; auto.
Qed.
