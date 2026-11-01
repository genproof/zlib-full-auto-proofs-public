(* Law rt_session, main's statement 45: the test of _t'46, `if (_t'46) return 0;`: the return when one of the
   seven objects is NULL (the objects go into the postcondition's TT), the state NS otherwise. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.Rep.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SMainStmt.
Require Import Zlib.proof.harness.rt_session.SMKit.
Require Import Zlib.proof.harness.rt_session.SMA2Kit.
Require Import Zlib.harness.rt_session.code.
#[local] Existing Instance SCS.CS.
Local Open Scope logic.

Lemma a2_r45_t {Espec : OracleKind} gv vh vg vc va vd u Q :
  f46 u = true ->
  semax Delta_s (NS gv vh vg vc va vd u [temp _t'46 (vb (f46 u))]) Iret (overridePost Q POST_s).
Proof.
  intros Hf. rewrite Hf. unfold Iret.
  unfold NS, base, cobjs, c_locals, lvs, lv_locals, o_locals, d_locals. cbn [app].
  unfold Delta_s; simplify_func_tycontext. abbreviate_semax.
  Intros.
  change (vb true) with (Vint Int.one). forward_if; [ | a2_nob].
  forward. Exists (Int.repr 0). apply andp_right; [apply prop_right; reflexivity |].
  do 2 match goal with |- context [data_at Tsh t_g ?v ?p] => sep_apply (data_at_data_at_ Tsh t_g v p) end.
  cancel.
Qed.

Lemma a2_r45_f {Espec : OracleKind} gv vh vg vc va vd u :
  f46 u = false ->
  semax Delta_s (NS gv vh vg vc va vd u [temp _t'46 (vb (f46 u))]) Iret
    (overridePost (NS gv vh vg vc va vd u []) POST_s).
Proof.
  intros Hf. rewrite Hf. unfold Iret. a2_tstart u.
  change (vb false) with (Vint Int.zero). forward_if; [ a2_nob | ].
  forward. a2_end.
Qed.
