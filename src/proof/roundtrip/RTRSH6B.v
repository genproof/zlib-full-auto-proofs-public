(* Law deflate_roundtrip (gzip header, part H6), part B: the conditional expressions of the NULL test
   `ih.extra == NULL || ih.name == NULL || ih.comment == NULL` (from rmh_PA to rmh_PT: _t'10 = rmh_any). *)
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

Ltac rmh_contra := first [ contradiction | exfalso; apply Int.one_not_zero; assumption
                         | exfalso; apply Int.one_not_zero; symmetry; assumption ].

Lemma rmh_test {Espec : OracleKind} I Iend rf vR vs vt vih gv z sp xb nb cb R :
  semax (Delta_m6 I Iend) (rmh_PA rf vR vs vt vih gv z sp xb nb cb) hs_t
    (overridePost (rmh_PT rf vR vs vt vih gv z sp xb nb cb) R).
Proof.
  destruct R as [Rn Rb Rc Rr]. unfold overridePost.
  unfold hs_t, rmh_PA, rmh_PT, rmh_ih, rmh_any, Delta_m6, Gm6. simplify_func_tycontext.
  freeze FR := (istream _ _ _ _ _) (rm_dside _ _) (data_at_ Tsh t_strmL vs) (Rm _) (zfuncs _) TT (mem_mgr _).
  destruct (eq_dec xb nullval) as [Ex | Nx]; [ | Intros].
  { forward.
    ifpost _t'9 Int.one.
    { forward. entailer!. }
    { rmh_contra. }
    forward_if.
    { forward. thaw FR. entailer!. }
    { rmh_contra. } }
  destruct (eq_dec nb nullval) as [En | Nn]; [ | Intros].
  { subst nb. forward.
    ifpost _t'9 Int.one.
    { rmh_contra. }
    { forward. forward. entailer!. }
    forward_if.
    { forward. thaw FR. entailer!. }
    { rmh_contra. } }
  forward.
  ifpost _t'9 Int.zero.
  { rmh_contra. }
  { forward. forward. entailer!. destruct nb; try contradiction; reflexivity. }
  forward_if.
  { rmh_contra. }
  destruct (eq_dec cb nullval) as [Ec | Nc]; [ | Intros].
  { subst cb. forward. forward. thaw FR. entailer!. }
  forward. forward. thaw FR. entailer!. destruct cb; try contradiction; reflexivity.
Qed.
