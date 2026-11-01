(* Law api_deterministic (data of any length): the first check of an iteration (DetCheck2.det_check), the
   statement gp_assert(code_first == code_second && first.adler == second.adler): both streams' codes and adler
   are the same.  The check reads but does not change the memory, so the assertion after it is D_at again. *)
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
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.api_deterministic.DetCS2.
Require Import Zlib.proof.harness.api_deterministic.DetMainStmt2.
Require Import Zlib.proof.harness.api_deterministic.DetKit2.
Require Import Zlib.harness.api_deterministic.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

(* the loop body from its statement 14 on (the other two checks, read, the frees) *)
Definition lsuf14 : statement := ltac:(get_lsuf 14%nat).

Lemma det_check_code {Espec : OracleKind} J n data datap v1 v2 sp1 sp2 gv ls ci c d :
  semax Delta_m (D_at J n data datap v1 v2 sp1 sp2 gv ls ci c d) lsuf14 (Rbody J n data datap v1 v2 sp1 sp2 gv) ->
  semax Delta_m (D_at J n data datap v1 v2 sp1 sp2 gv ls ci c d) lsuf13 (Rbody J n data datap v1 v2 sp1 sp2 gv).
Proof.
  intros HK.
  unfold lsuf13.
  eapply semax_seq' with (P' := D_at J n data datap v1 v2 sp1 sp2 gv ls ci c d); [ | exact HK ].
  clear HK.
  unfold D_at, D_sep, B_loc, Rbody, POST_m, Delta_m, Gmain. simplify_func_tycontext.
  abbreviate_semax. Intros.
  unfold strm_at, api_fields. Intros.
  forward_if (temp _t'31 (vi 1)).
  { forward. forward. forward. entailer!. unfold Int64.cmpu. rewrite Int64.eq_true. reflexivity. }
  { exfalso. auto. }
  forward_call (Int.repr 1).
  unfold strm_at, api_fields. entailer!.
Qed.
