(* Law deflate_roundtrip (gzip header, part H6), part A: the body of `if (R.head_set)` up to the NULL test:
   ih.extra = malloc(R.xlen); ih.extra_max = R.xlen; ih.name = malloc(R.nl + 1); ih.name_max = R.nl + 1;
   ih.comment = malloc(R.cl + 1); ih.comm_max = R.cl + 1 (from rmh_P0 to rmh_PA, continuation style). *)
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
Require Import Zlib.proof.roundtrip.RTRMSeg6.
Require Zlib.proof.roundtrip.RTRMSeg8.
Require Import Zlib.proof.roundtrip.RTRSH6Kit.
#[local] Existing Instance RTRCS.CS.
Local Open Scope logic.

Lemma rmh_alloc {Espec : OracleKind} I Iend rf vR vs vt vih gv z sp R :
  rf_ok Iend vR rf ->
  (forall xb nb cb, semax (Delta_m6 I Iend) (rmh_PA rf vR vs vt vih gv z sp xb nb cb) hs_tail R) ->
  semax (Delta_m6 I Iend) (rmh_P0 rf vR vs vt vih gv z sp) hs_then R.
Proof.
  intros H K.
  assert (RS: rs_ok (rf_rs rf)) by (destruct H; auto).
  assert (Lx: Zlength (rs_xf (rf_rs rf)) <= 4096 /\ Zlength (rs_nm (rf_rs rf)) <= 4096 /\
              Zlength (rs_cm (rf_rs rf)) <= 4096) by (unfold rs_ok in RS; tauto).
  pose proof (Zlength_nonneg (rs_xf (rf_rs rf))) as N1. pose proof (Zlength_nonneg (rs_nm (rf_rs rf))) as N2.
  pose proof (Zlength_nonneg (rs_cm (rf_rs rf))) as N3.
  unfold hs_then, rmh_P0, Delta_m6, Gm6. simplify_func_tycontext.
  rewrite rmh_ih0.
  freeze FR := (istream _ _ _ _ _) (rmh_drest _ _) (data_at_ Tsh t_strmL vs) (Rm _) (zfuncs _) TT
                (field_at _ _ (DOT _head_set) _ _).
  forward.
  forward_call (tarray tuchar (Zlength (rs_xf (rf_rs rf))), gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros xb.
  forward. forward. forward. forward.
  forward_call (tarray tuchar (Zlength (rs_nm (rf_rs rf)) + 1), gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros nb.
  forward. forward. forward. forward.
  forward_call (tarray tuchar (Zlength (rs_cm (rf_rs rf)) + 1), gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros cb.
  forward. forward. forward.
  thaw FR.
  rewrite !add_repr.
  eapply semax_pre; [ | apply (K xb nb cb) ].
  unfold rmh_PA, rmh_ih.
  sep_apply rmh_join.
  entailer!.
Qed.
