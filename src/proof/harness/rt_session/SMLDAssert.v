(* Law rt_session (harness/rt_session.c), main's deflate loop (SMKit.loopD): the assert after the accounted assert,
   `if (at.avail_out == 0) gp_assert(code == Z_BUF_ERROR && unmoved(&compressor, &at))`, from DA_s to DK_s
   (SMLDKit.assertD_s_stmt).  A call offered no output space returned Z_BUF_ERROR and left the six members as
   position_of recorded them (DA_s), so unmoved returns 1 (laws_session Facts.unmoved_b_iff); its pointer
   comparisons compare next_in (data + |D|) and next_out (compressed + |O|) with themselves, defined in the
   memory of the objects data and compressed (SMLDLib.test_eq_s, Facts.lend_cmp).  && does not call unmoved
   when code is not Z_BUF_ERROR.  The header part of the compressor's state, the rest of head and the objects of
   the dictionary and of got are framed. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.deflate.DCS.
Require Zlib.proof.deflate.DSpecV.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.laws_session.Spec.
Require Zlib.proof.harness.laws_session.Facts.
Require Zlib.proof.harness.rt_stream.ULoopDLib.
Require Zlib.proof.harness.rt_stream.ULoopDCallLib.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SDFacts.
Require Import Zlib.proof.harness.rt_session.SMainStmt.
Require Import Zlib.proof.harness.rt_session.SMKit.
Require Import Zlib.proof.harness.rt_session.SMLDLib.
Require Import Zlib.proof.harness.rt_session.SMLDKit.
Require Import Zlib.harness.rt_session.code.
Require Zlib.deflate.code.
#[local] Existing Instance SCS.CS.
Local Open Scope logic.

Module LS := Zlib.proof.harness.laws_session.Spec.
Module DC := Zlib.deflate.code.

(* VST's after_forward_call simplifies remove_localdef_temp with `simpl rlt_ident_eq`, which runs away on main's
   identifiers; each identifier comparison is decided by vm_compute instead. *)
Ltac cd_rlt_fix u :=
  lazymatch u with
  | context C [rlt_ident_eq ?a ?b] =>
      let v := eval vm_compute in (rlt_ident_eq a b) in
      let u2 := context C [v] in cd_rlt_fix u2
  | _ => u
  end.

Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u := constr:(remove_localdef_temp i L) in
    let u' := eval lazy delta [remove_localdef_temp] beta iota in u in
    let u' := cd_rlt_fix u' in
    let u' := eval lazy beta iota in u' in
    let u' := eval lazy zeta in u' in
    change u with u'
  end.

(* the memory lent to unmoved: with the objects data and compressed, next_in = data + k and
   next_out = compressed + |O| are comparable with themselves *)
Lemma lend_objs_s (u : setup) (O : list Z) (k : Z) (a : LS.posz) :
  su_ok u -> 0 <= k <= Zlength (su_data u) -> 0 <= Zlength O <= su_cap u ->
  LS.pz_next_in a = offset_val k (su_dp u) -> LS.pz_next_out a = offset_val (Zlength O) (su_cp u) ->
  dobj u * cobj u O |-- (dobj u * cobj u O) && LS.unmoved_cmp a a.
Proof.
  intros Hu Hk HO Ei Eo. apply Zlib.proof.harness.laws_session.Facts.lend_cmp.
  unfold LS.unmoved_cmp. rewrite Ei, Eo.
  destruct Hu as (Hd & _ & _ & _ & _ & _ & Pc & _).
  assert (Pd : isptr (su_dp u)) by (unfold su_dok in Hd; tauto).
  apply andp_right.
  - unfold dobj, datobj, bobj. rewrite sepcon_assoc. apply test_eq_s; auto.
  - unfold cobj. rewrite sepcon_comm. apply test_eq_s; auto.
Qed.

(* the end of the statement: DK_s, the postcondition's normal part *)
Ltac da_close :=
  destruct POST_s as [rn rb rc rr]; unfold DK_s; cbn [RA_normal];
  unfold c_locals, d_locals, lvs, lv_locals; simpl app; entailer!.

Lemma sassert_d : assertD_s_stmt.
Proof.
  intros Espec J gv vh vg vc va vd u off flush code l a hx Hr.
  unfold Delta_s. simplify_func_tycontext.
  unfold DA_s, assertD_s.
  abbreviate_semax.
  Intros.
  rewrite at_law_s.
  unfold c_locals, d_locals, lvs, lv_locals; simpl app.
  forward.
  match goal with |- context [temp _t'113 ?v] =>
    replace v with (Vint (Int.repr (LS.pz_avail_out a))) by (destruct a; reflexivity) end.
  pose proof H7 as (Hni & Hno & Hai & Hti & Hao & Hto).
  forward_if.
  - (* no output space was offered: Z_BUF_ERROR, nothing moved *)
    destruct (H8 H11) as [Hc Hp]. subst code.
    assert (Hl : dl_ok J u l) by exact H6.
    pose proof Hl as (_ & _ & HDoff & _ & _ & _ & _ & _ & _ & Eni & _).
    assert (HD0 := Zlength_nonneg (dl_D l)). assert (HO0 := Zlength_nonneg (dl_O l)).
    forward_if (temp _t'60 (Vint Int.one)).
    + sep_apply (cstream_lend_s gv vc (ghp vh u) (dl_c l)). Intros r.
      rewrite Hp.
      sep_apply (lend_objs_s u (dl_O l) (Zlength (dl_D l)) a H ltac:(lia) ltac:(lia)
                   ltac:(rewrite <- Hp; exact Eni) ltac:(rewrite <- Hp; exact H5)).
      rewrite <- at_law_s.
      forward_call (vc, Ews, a, r, va, Tsh, a, dobj u * cobj u (dl_O l)).
      rewrite (proj2 (Zlib.proof.harness.laws_session.Facts.unmoved_b_iff a a) eq_refl).
      Intros.
      forward.
      sep_apply (modus_ponens_wand (@data_at LS.CS_session Ews t_zs (LS.zs_of a r) vc)
                   (cstream gv vc (ghp vh u) (dl_c l))).
      rewrite at_law_s.
      entailer!.
    + exfalso. match goal with E : Int.repr Z_BUF_ERROR <> _ |- _ => apply E; reflexivity end.
    + forward_call (Int.one).
      rewrite <- at_law_s. sep_apply (at_free_s a va).
      da_close.
  - (* output space offered: no assert *)
    forward.
    rewrite <- at_law_s. sep_apply (at_free_s a va).
    da_close.
Qed.
