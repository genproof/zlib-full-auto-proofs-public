(* Law res_bound, main: the NULL test of the five objects (any NULL ends the run with return 0, RBPreN1 to
   RBPreN5): msuf 16 -> msuf 17 (RBPreKit.part_preB_stmt). *)
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
Require Import Zlib.proof.harness.res_bound.RBPreN1 Zlib.proof.harness.res_bound.RBPreN2 Zlib.proof.harness.res_bound.RBPreN3.
Require Import Zlib.proof.harness.res_bound.RBPreN4 Zlib.proof.harness.res_bound.RBPreN5.
Require Import Zlib.harness.res_bound.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

Lemma part_preB : part_preB_stmt.
Proof.
  intros Espec gv vh vs rs HA1.
  destruct (eq_dec (r_datap rs) nullval) as [E | N0]; [ now apply pre_null_data | ].
  destruct (eq_dec (r_dictp rs) nullval) as [E | N1]; [ now apply pre_null_dict | ].
  destruct (eq_dec (r_xp rs) nullval) as [E | N2]; [ now apply pre_null_extra | ].
  destruct (eq_dec (r_np rs) nullval) as [E | N3]; [ now apply pre_null_name | ].
  destruct (eq_dec (r_cp rs) nullval) as [E | N4]; [ now apply pre_null_comment | ].
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
  destruct (eq_dec cp nullval) as [X | Pc]; [ now contradiction N4 | ].
  mkptr cp (cm ++ [0]) bc oc.
  ifpost _t'20 Int.zero; [nob | forward; [tceq | entailer!] | ].
  forward_if True; [nob | forward; entailer! | ].
  (* A1 *)
  set (rs := mkRS lv wb mm st n ch dl xl nl cl (Vptr bd od) (Vptr bdi odi) (Vptr bx ox) (Vptr bn on) (Vptr bc oc)
               data dict xf nm cm).
  assert (OK : rs_ok rs) by (apply rs_ok_of0; simpl; auto).
  unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
  eapply semax_pre; [ | apply (HA1 rs) ].
  unfold A1, objs, rs_locals. subst rs. cbn [r_level r_wbits r_mem r_strategy r_n r_choice r_dlen r_xlen r_nl r_cl
    r_datap r_dictp r_xp r_np r_cp r_data r_dict r_xf r_nm r_cm app].
  entailer!.
Qed.
