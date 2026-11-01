(* Law res_bound, main: the runs where the comment object is NULL (malloc failed): every later test is
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

(* the run when the comment object is NULL (the objects before it are not): return 0 *)
Lemma pre_null_comment : forall {Espec : OracleKind} (gv : globals) (vh vs : val) (rs : rsetup),
  r_datap rs <> nullval -> r_dictp rs <> nullval -> r_xp rs <> nullval -> r_np rs <> nullval -> r_cp rs = nullval -> semax Delta_m (A0 gv vh vs rs) msuf16 POST_m.
Proof.
  intros Espec gv vh vs rs N0 N1 N2 N3 E.
  destruct rs as [lv wb mm st n ch dl xl nl cl datap dictp xp np cp data dict xf nm cm].
  cbn [r_datap r_dictp r_xp r_np r_cp] in *.
  unfold A0, optobj, rs_locals, msuf16, POST_m, Delta_m. simplify_func_tycontext.
  cbn [r_level r_wbits r_mem r_strategy r_n r_choice r_dlen r_xlen r_nl r_cl r_datap r_dictp r_xp r_np r_cp
    r_data r_dict r_xf r_nm r_cm app].
  Intros.
  destruct (eq_dec datap nullval) as [X | Pd]; [ now contradiction N0 | ].
  mkptr datap data bd od.
  destruct (eq_dec dictp nullval) as [X | Pdi]; [ now contradiction N1 | ].
  mkptr dictp dict bdi odi.
  ifpost _t'17 Int.zero; [tceq | nob | forward; [tceq | entailer!] | ].
  destruct (eq_dec xp nullval) as [X | Px]; [ now contradiction N2 | ].
  mkptr xp xf bx ox.
  ifpost _t'18 Int.zero; [nob | forward; [tceq | entailer!] | ].
  destruct (eq_dec np nullval) as [X | Pn]; [ now contradiction N3 | ].
  mkptr np (nm ++ [0]) bn on.
  ifpost _t'19 Int.zero; [nob | forward; [tceq | entailer!] | ].
  subst cp. destruct (eq_dec nullval nullval) as [_ | X]; [ | now contradiction X ].
  ifpost _t'20 Int.one; [nob | forward; entailer! | ]. exit_ones.
Qed.
