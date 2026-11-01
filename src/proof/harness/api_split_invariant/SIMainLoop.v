(* Law api_split_invariant, main: statement 29, the split's for(;;) with the invariant sm_inv (its body:
   SIMainBody.v), then the rest of main from the break (sm_brk). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.api_split_invariant.SILawCS.
Require Import Zlib.proof.harness.api_split_invariant.SIGlobals.
Require Import Zlib.proof.harness.api_split_invariant.SIFacts.
Require Import Zlib.proof.harness.api_split_invariant.SIMainKit.
Require Import Zlib.harness.api_split_invariant.code.
Local Open Scope logic.

Require Import Zlib.proof.harness.api_split_invariant.SIMainBody.

Lemma seg_loop_ok {Espec: OracleKind} Inv Max gv vwb vone vsplit w src room inp o1 o2 r1 Fr:
  si_facts Inv Max -> si_window w -> is_bytes src -> Zlength src <= Int.max_unsigned ->
  0 <= room <= Int.max_unsigned -> isptr inp -> isptr o2 ->
  Fr |-- data_at_ Tsh (tarray tint 4) vwb * data_at_ Tsh t_zsl vone * TT ->
  semax Delta_m (sm_brk Max gv vwb vone vsplit w src room inp o1 o2 r1 Fr) sm_seg30 POST_B ->
  semax Delta_m (sm_inv Inv gv vwb vone vsplit w src room inp o1 o2 r1 Fr) sm_seg29 POST_B.
Proof.
  intros SF Hw Bs Hl Hr Pi Po HF TL.
  rewrite sm_seg29_eq.
  eapply semax_seq; [ | exact TL].
  apply semax_loop with (sm_inv Inv gv vwb vone vsplit w src room inp o1 o2 r1 Fr).
  - apply (sm_body_ok Inv Max); auto.
  - forward. apply andp_left2. apply derives_refl.
Qed.
