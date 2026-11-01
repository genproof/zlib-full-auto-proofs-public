(* Law deflate_roundtrip (gzip header, part H21): parts 4-5 of the header checks: bytes_same(ih.name, R.nf_,
   R.nl + 1) and bytes_same(ih.comment, R.cf, R.cl + 1). *)
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

Lemma rmh_X4 {Espec : OracleKind} I Iend rs vR vs vt vih gv v3 v7 v9 v11 v13 xfl xb nb cb F1 F2 F3 F4 R :
  PH21_ok rs xb nb cb ->
  semax (Delta_m6 I Iend) (PH21 rs vR vs vt vih gv v3 v7 v9 v11 v13 xfl xb nb cb F1 F2 F3 F4) chkX4
    (overridePost (PH21 rs vR vs vt vih gv v3 v7 v9 v11 v13 xfl xb nb cb F1 F2 F3 F4) R).
Proof.
  intros (RS & Px & Pn & Pc).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hxl4 & Hnl4 & Hcl4 &
                    _ & _ & Hxb & Hnb & Hcb & _ & _ & Pxf & Pnf & Pcf & _).
  destruct R as [Rn Rb Rc Rr]. unfold overridePost.
  unfold PH21, chkX4. unfold Delta_m6, Gm6. simplify_func_tycontext.
  assert (CN1 : cbuf_ok false nb Ews nb 0 (Zlength (rs_nm rs) + 1) (Zlength (rs_nm rs) + 1)
                 (byte_vals (rs_nm rs ++ [0])) (rs_nm rs ++ [0])).
  { apply rmh_cb; auto; [ apply nz_bytes0'; auto | rewrite rmh_nz0; lia ]. }
  assert (CN2 : cbuf_ok false (rs_nfp rs) Ews (rs_nfp rs) 0 (Zlength (rs_nm rs) + 1) (Zlength (rs_nm rs) + 1)
                 (map vi (rs_nm rs ++ [0])) (rs_nm rs ++ [0])).
  { apply rmh_cb; auto; [ apply nz_bytes0'; auto | rewrite rmh_nz0; lia ]. }
  forward. forward. forward.
  forward_call (nb, Ews, nb, 0, Zlength (rs_nm rs) + 1, byte_vals (rs_nm rs ++ [0]), rs_nm rs ++ [0],
                rs_nfp rs, Ews, rs_nfp rs, 0, Zlength (rs_nm rs) + 1, map vi (rs_nm rs ++ [0]), rs_nm rs ++ [0],
                Zlength (rs_nm rs) + 1).
  rewrite if_true by auto.
  forward_call (Int.one).
  entailer!.
Qed.

Lemma rmh_X5 {Espec : OracleKind} I Iend rs vR vs vt vih gv v3 v7 v9 v11 v13 xfl xb nb cb F1 F2 F3 F4 R :
  PH21_ok rs xb nb cb ->
  semax (Delta_m6 I Iend) (PH21 rs vR vs vt vih gv v3 v7 v9 v11 v13 xfl xb nb cb F1 F2 F3 F4) chkX5
    (overridePost (PH21 rs vR vs vt vih gv v3 v7 v9 v11 v13 xfl xb nb cb F1 F2 F3 F4) R).
Proof.
  intros (RS & Px & Pn & Pc).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hxl4 & Hnl4 & Hcl4 &
                    _ & _ & Hxb & Hnb & Hcb & _ & _ & Pxf & Pnf & Pcf & _).
  destruct R as [Rn Rb Rc Rr]. unfold overridePost.
  unfold PH21, chkX5. unfold Delta_m6, Gm6. simplify_func_tycontext.
  assert (CC1 : cbuf_ok false cb Ews cb 0 (Zlength (rs_cm rs) + 1) (Zlength (rs_cm rs) + 1)
                 (byte_vals (rs_cm rs ++ [0])) (rs_cm rs ++ [0])).
  { apply rmh_cb; auto; [ apply nz_bytes0'; auto | rewrite rmh_nz0; lia ]. }
  assert (CC2 : cbuf_ok false (rs_cfp rs) Ews (rs_cfp rs) 0 (Zlength (rs_cm rs) + 1) (Zlength (rs_cm rs) + 1)
                 (map vi (rs_cm rs ++ [0])) (rs_cm rs ++ [0])).
  { apply rmh_cb; auto; [ apply nz_bytes0'; auto | rewrite rmh_nz0; lia ]. }
  forward. forward. forward.
  forward_call (cb, Ews, cb, 0, Zlength (rs_cm rs) + 1, byte_vals (rs_cm rs ++ [0]), rs_cm rs ++ [0],
                rs_cfp rs, Ews, rs_cfp rs, 0, Zlength (rs_cm rs) + 1, map vi (rs_cm rs ++ [0]), rs_cm rs ++ [0],
                Zlength (rs_cm rs) + 1).
  rewrite if_true by auto.
  forward_call (Int.one).
  entailer!.
Qed.
