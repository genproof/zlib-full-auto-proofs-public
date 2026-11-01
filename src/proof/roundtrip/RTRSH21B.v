(* Law deflate_roundtrip (gzip header, part H21): parts 1 and 3 of the header checks: ih.done == 1;
   ih.extra_len == R.xlen and bytes_same(ih.extra, R.xf, R.xlen). *)
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

Lemma rmh_X1 {Espec : OracleKind} I Iend rs vR vs vt vih gv v3 v7 v9 v11 v13 xfl xb nb cb F1 F2 F3 F4 R :
  semax (Delta_m6 I Iend) (PH21 rs vR vs vt vih gv v3 v7 v9 v11 v13 xfl xb nb cb F1 F2 F3 F4) chkX1
    (overridePost (PH21 rs vR vs vt vih gv v3 v7 v9 v11 v13 xfl xb nb cb F1 F2 F3 F4) R).
Proof.
  destruct R as [Rn Rb Rc Rr]. unfold overridePost.
  unfold PH21, chkX1. unfold Delta_m6, Gm6. simplify_func_tycontext.
  forward.
  forward_call (Int.one).
  entailer!.
Qed.

Lemma rmh_X3 {Espec : OracleKind} I Iend rs vR vs vt vih gv v3 v7 v9 v11 v13 xfl xb nb cb F1 F2 F3 F4 R :
  PH21_ok rs xb nb cb ->
  semax (Delta_m6 I Iend) (PH21 rs vR vs vt vih gv v3 v7 v9 v11 v13 xfl xb nb cb F1 F2 F3 F4) chkX3
    (overridePost (PH21 rs vR vs vt vih gv v3 v7 v9 v11 v13 xfl xb nb cb F1 F2 F3 F4) R).
Proof.
  intros (RS & Px & Pn & Pc).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hxl4 & Hnl4 & Hcl4 &
                    _ & _ & Hxb & Hnb & Hcb & _ & _ & Pxf & Pnf & Pcf & _).
  destruct R as [Rn Rb Rc Rr]. unfold overridePost.
  unfold PH21, chkX3. unfold Delta_m6, Gm6. simplify_func_tycontext.
  assert (CX1 : cbuf_ok false xb Ews xb 0 (Zlength (rs_xf rs)) (Zlength (rs_xf rs))
                 (byte_vals (rs_xf rs)) (rs_xf rs)) by (apply rmh_cb; auto).
  assert (CX2 : cbuf_ok false (rs_xfp rs) Ews (rs_xfp rs) 0 (Zlength (rs_xf rs)) (Zlength (rs_xf rs))
                 (map vi (rs_xf rs)) (rs_xf rs)) by (apply rmh_cb; auto).
  forward. forward.
  forward_if (temp _t'27 (Vint Int.one)).
  { forward. forward. forward.
    forward_call (xb, Ews, xb, 0, Zlength (rs_xf rs), byte_vals (rs_xf rs), rs_xf rs,
                  rs_xfp rs, Ews, rs_xfp rs, 0, Zlength (rs_xf rs), map vi (rs_xf rs), rs_xf rs,
                  Zlength (rs_xf rs)).
    rewrite if_true by auto.
    forward. entailer!. }
  { first [contradiction | exfalso; apply Int.one_not_zero; assumption]. }
  forward_call (Int.one).
  entailer!.
Qed.
