(* RT-H: inflate()'s body against RTHSpec.inflate_spec6 from the header cases (RTHCase.cases6_all)
   and the prologue (pro_part6_stmt): without a partial header Spec5's body (Body5_inflate); with one, the
   prologue, the header passes (case_ok6, hpass), then Spec5's loop/exit parts from the first machine past the
   header. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTHCase.
Require Zlib.proof.inflate_api.Body5_inflate Zlib.proof.inflate.CasesAll5 Zlib.proof.inflate.InvQ5 Zlib.proof.inflate_api.LibProof5.
Require Import Zlib.proof.roundtrip.RTHBody6Kit Zlib.proof.roundtrip.RTHBody6Split Zlib.proof.roundtrip.RTHBody6H.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Lemma rth_body6 : cases6_all -> pro_part6_stmt -> forall {Espec: OracleKind},
  semax_body Vprog_inflate Gprog_inflate3 f_inflate inflate_spec6.
Proof.
  intros HC6 HPRO Espec.
  apply rth_split.
  - exact (Zlib.proof.inflate_api.Body5_inflate.body_inflate_proof5 Zlib.proof.inflate.CasesAll5.cases_all5_proof
             Zlib.proof.inflate.InvQ5.stepf2_mwf3_proof Zlib.proof.inflate_api.LibProof5.stepf2_hd_proof Espec).
  - exact (rth_body6h HC6 HPRO Zlib.proof.inflate.CasesAll5.cases_all5_proof Zlib.proof.inflate.InvQ5.stepf2_mwf3_proof
             Zlib.proof.inflate_api.LibProof5.stepf2_hd_proof).
Qed.
