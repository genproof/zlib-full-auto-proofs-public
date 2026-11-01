(* Law deflate_roundtrip (gzip header, part H21): part 2 of the header checks: text, time, os, hcrc against
   R.h. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.HarnessRef.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.roundtrip.RTXFacts.
Require Import Zlib.proof.roundtrip.RTRCS Zlib.proof.roundtrip.RTRRunSpec Zlib.proof.roundtrip.RTRRunKit Zlib.proof.roundtrip.RTRApiConv Zlib.proof.roundtrip.RTRMainSpec.
Require Import Zlib.proof.roundtrip.RTIIface.
Require Import Zlib.proof.roundtrip.RTHSpec Zlib.proof.roundtrip.RTHIfDefs.
Require Import Zlib.harness.x_deflate_roundtrip.code.
Require Import Zlib.proof.roundtrip.RTRMKit Zlib.proof.roundtrip.RTRSKit.
Require Zlib.proof.uncompr.URunFrame.
Require Import Zlib.proof.roundtrip.RTRSH21Kit.
#[local] Existing Instance RTRCS.CS.
Local Open Scope logic.

Lemma rmh_X2 {Espec : OracleKind} I Iend rs vR vs vt vih gv v3 v7 v9 v11 v13 xfl xb nb cb F1 F2 F3 F4 R :
  semax (Delta_m6 I Iend) (PH21 rs vR vs vt vih gv v3 v7 v9 v11 v13 xfl xb nb cb F1 F2 F3 F4) chkX2
    (overridePost (PH21 rs vR vs vt vih gv v3 v7 v9 v11 v13 xfl xb nb cb F1 F2 F3 F4) R).
Proof.
  destruct R as [Rn Rb Rc Rr]. unfold overridePost.
  unfold PH21, chkX2. unfold Delta_m6, Gm6. simplify_func_tycontext.
  forward. forward.
  forward_if (temp _t'24 (Vint Int.one)).
  { forward. forward. forward.
    unfold Int64.cmpu. rewrite Int64.eq_true. entailer!. }
  { first [contradiction | exfalso; apply Int.one_not_zero; assumption]. }
  forward_if (temp _t'25 (Vint Int.one)).
  { forward. forward. forward. rewrite Int.eq_true. entailer!. }
  { first [contradiction | exfalso; apply Int.one_not_zero; assumption]. }
  forward_if (temp _t'26 (Vint Int.one)).
  { forward. forward. forward. rewrite Int.eq_true. entailer!. }
  { first [contradiction | exfalso; apply Int.one_not_zero; assumption]. }
  forward_call (Int.one).
  entailer!.
Qed.
