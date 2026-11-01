(* Law rt_session, main's statement 46: the test of _t'48, `if (_t'48) return 0;`: the return when one of got's
   buffers is NULL, A47 when none of the ten new objects is NULL. *)
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

Lemma a2_r46_t {Espec : OracleKind} gv vh vg vc va vd u Q :
  f48 u = true ->
  semax Delta_s (NS gv vh vg vc va vd u [temp _t'48 (vb (f48 u))]) Jret (overridePost Q POST_s).
Proof.
  intros Hf. rewrite Hf. unfold Jret.
  unfold NS, base, cobjs, c_locals, lvs, lv_locals, o_locals, d_locals. cbn [app].
  unfold Delta_s; simplify_func_tycontext. abbreviate_semax.
  Intros.
  change (vb true) with (Vint Int.one). forward_if; [ | a2_nob].
  forward. Exists (Int.repr 0). apply andp_right; [apply prop_right; reflexivity |].
  do 2 match goal with |- context [data_at Tsh t_g ?v ?p] => sep_apply (data_at_data_at_ Tsh t_g v p) end.
  cancel.
Qed.

Lemma a2_r46_f {Espec : OracleKind} gv vh vg vc va vd u :
  f46 u = false -> f48 u = false ->
  semax Delta_s (NS gv vh vg vc va vd u [temp _t'48 (vb (f48 u))]) Jret
    (overridePost (EX u' : setup, A47 gv vh vg vc va vd u') POST_s).
Proof.
  intros H46 H48. rewrite H48.
  unfold f46, f45, f44, f43, f42, f41 in H46. unfold f48, f47 in H48.
  repeat rewrite orb_false_iff in H46. repeat rewrite orb_false_iff in H48.
  destruct H46 as [[[[[[E1 E2] E3] E4] E5] E6] E7]. destruct H48 as [[E8 E9] E10].
  apply nb_false in E1, E2, E3, E4, E5, E6, E7, E8, E9, E10.
  unfold Jret, NS, cobjs.
  rewrite (obj0_bobj _ _ E1), (obj0_bobj _ _ E2), (obj0_bobj _ _ E3), (obj0_bobj _ _ E4), (obj0_bobj _ _ E5),
    (new0_cnew _ _ E6), (new0_cnew _ _ E7), (new0_cnew _ _ E8), (new0_cnew _ _ E9), (new0_cnew _ _ E10).
  unfold base, c_locals, lvs, lv_locals, o_locals, d_locals. cbn [app].
  unfold Delta_s; simplify_func_tycontext. abbreviate_semax.
  Intros.
  change (vb false) with (Vint Int.zero). forward_if; [ a2_nob | ].
  assert_PROP (isptr (su_dcp u)) as I1 by (sep_apply (bobj_isptr (su_dcp u) (su_dict u)); entailer!).
  assert_PROP (isptr (su_xcp u)) as I2 by (sep_apply (bobj_isptr (su_xcp u) (su_xf u)); entailer!).
  assert_PROP (isptr (su_ncp u)) as I3 by (sep_apply (bobj_isptr (su_ncp u) (su_nm u ++ [0])); entailer!).
  assert_PROP (isptr (su_ccp u)) as I4 by (sep_apply (bobj_isptr (su_ccp u) (su_cm u ++ [0])); entailer!).
  assert_PROP (isptr (su_ep u)) as I5 by (sep_apply (bobj_isptr (su_ep u) (su_data u)); entailer!).
  assert_PROP (isptr (su_cp u)) as I6 by (sep_apply (cnew_isptr (su_cp u) (su_cap u)); entailer!).
  assert_PROP (isptr (su_op u)) as I7 by (sep_apply (cnew_isptr (su_op u) (Zlength (su_data u))); entailer!).
  assert_PROP (isptr (su_gxp u)) as I8 by (sep_apply (cnew_isptr (su_gxp u) (Zlength (su_xf u))); entailer!).
  assert_PROP (isptr (su_gnp u)) as I9 by (sep_apply (cnew_isptr (su_gnp u) (Zlength (su_nm u) + 1)); entailer!).
  assert_PROP (isptr (su_gcp u)) as I10 by (sep_apply (cnew_isptr (su_gcp u) (Zlength (su_cm u) + 1)); entailer!).
  forward.
  destruct POST_s as [r1 r2 r3 r4]; cbn [tycontext.RA_normal].
  Exists u.
  unfold A47, dobj, eobj, cobj, oobj, hobj, hobjs, hcopies, graw, gbufs, dcopy, lvs, lv_locals, c_locals, d_locals.
  cbn [app].
  rewrite <- (cnew_cbytes (su_cp u) (su_cap u)) by (unfold su_dok in *; tauto).
  rewrite <- (cnew_cbytes (su_op u) (Zlength (su_data u))) by apply Zlength_nonneg.
  entailer!.
  unfold su_ok. tauto.
Qed.
