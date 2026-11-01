(* Law api_deterministic (data of any length): the loop body from the NULL test of the four objects when both
   copies of the piece were allocated but an output space is NULL: main returns 0.  (DetPreNull2.v: a copy is
   NULL; DetPreOffer2.v: no object is NULL.) *)
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
Require Import Zlib.harness.api_deterministic.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

(* an output space is NULL: main returns 0 (both streams back to main's locals, everything else dropped) *)
Lemma det_pre_null_out {Espec : OracleKind} J n data datap v1 v2 sp1 sp2 gv ls off fl room in1 in2 out1 out2 :
  in1 <> nullval -> in2 <> nullval -> out1 = nullval \/ out2 = nullval ->
  semax Delta_m (M_at J n data datap v1 v2 sp1 sp2 gv ls off fl room in1 in2 out1 out2) lsuf7
    (Rbody J n data datap v1 v2 sp1 sp2 gv).
Proof.
  intros E1 E2 Hnn.
  unfold M_at, J_ok, setup_ok. Intros.
  unfold lsuf7, Rbody, loop1_ret_assert, POST_m, overridePost, frame_ret_assert. cbv beta iota.
  set (tk := Z.min (off - ls_read ls) 4294967295) in *.
  assert (Htk0 : 0 <= tk <= 4294967295) by (unfold tk; rep_lia).
  abbreviate_semax.
  (* the NULL test needs only the four objects: the rest is frozen *)
  freeze FR := (mem_mgr gv) (deflate_globals gv) (data_at Ews _ _ datap) (shead v1 _ _ _ _ _ _ _)
                 (shead v2 _ _ _ _ _ _ _) TT.
  destruct (eq_dec in1 nullval); [contradiction | ]. Intros.
  destruct (eq_dec in2 nullval); [contradiction | ]. Intros.
  forward_if (temp _t'21 (vi 0)); [ det_false | | ]. { forward. entailer!. det_nonnull. }
  destruct (eq_dec out1 nullval) as [E3|E3].
  { subst out1. destruct (eq_dec nullval nullval) as [_|]; [|contradiction].
    forward_if (temp _t'22 (vi 1)); [ det_false | | ]. { forward. apply ENTAIL_refl. }
    forward_if (temp _t'23 (vi 1)); [ | det_false | ]. { forward. apply ENTAIL_refl. }
    forward_if; [ | det_false].
    thaw FR. det_ret. }
  destruct (eq_dec out1 nullval); [contradiction | ]. Intros.
  forward_if (temp _t'22 (vi 0)); [ det_false | | ]. { forward. entailer!. det_nonnull. }
  destruct (eq_dec out2 nullval) as [E4|E4].
  { subst out2. destruct (eq_dec nullval nullval) as [_|]; [|contradiction].
    forward_if (temp _t'23 (vi 1)); [ det_false | | ]. { forward. apply ENTAIL_refl. }
    forward_if; [ | det_false].
    thaw FR. det_ret. }
  destruct Hnn; contradiction.
Qed.
