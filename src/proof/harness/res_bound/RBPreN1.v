(* Law res_bound, main: the runs where the data object is NULL (malloc failed): every later test is
   true and main returns 0 (used by RBPreB.part_preB). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.Rep Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.LawFactsW Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.deflate.Obligations.
Require Zlib.proof.harness.bound_common.BoundKit Zlib.proof.harness.deflate_bound.MainKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.res_bound.RBCS Zlib.proof.harness.res_bound.RBString Zlib.proof.harness.res_bound.RBKit.
Require Import Zlib.proof.harness.res_bound.RBPreKit.
Require Import Zlib.harness.res_bound.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

(* the run when the data object is NULL: return 0 *)
Lemma pre_null_data : forall {Espec : OracleKind} (gv : globals) (vh vs : val) (rs : rsetup),
   r_datap rs = nullval -> semax Delta_m (A0 gv vh vs rs) msuf16 POST_m.
Proof.
  intros Espec gv vh vs rs  E.
  destruct rs as [lv wb mm st n ch dl xl nl cl datap dictp xp np cp data dict xf nm cm].
  cbn [r_datap r_dictp r_xp r_np r_cp] in *.
  unfold A0, optobj, rs_locals, msuf16, POST_m, Delta_m. simplify_func_tycontext.
  cbn [r_level r_wbits r_mem r_strategy r_n r_choice r_dlen r_xlen r_nl r_cl r_datap r_dictp r_xp r_np r_cp
    r_data r_dict r_xf r_nm r_cm app].
  Intros.
  subst datap. destruct (eq_dec nullval nullval) as [_ | X]; [ | now contradiction X ].
  ifpost _t'17 Int.one; [forward; entailer! | nob | ]. exit_ones.
Qed.
