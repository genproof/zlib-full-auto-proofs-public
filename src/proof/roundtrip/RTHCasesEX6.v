(* RT-H: cases EXLEN, EXTRA (indices 4-5) with a partial gz_header attached (RTHCase.case_ok6). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTHCase.
Require Import Zlib.proof.roundtrip.RTHEXLEN6.
Require Import Zlib.proof.roundtrip.RTHEXTRA6.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Lemma rth_ex : rth_ex_stmt.
Proof.
  intros Espec F HF. split; [apply rth_exlen6 | apply rth_extra6]; exact HF.
Qed.
