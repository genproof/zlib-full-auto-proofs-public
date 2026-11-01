(* Law rt_stream (data of any length), main's deflate loop (UMainKit.loopD): the assert after the deflate() call,
   `if (at.avail_out == 0) gp_assert(code == Z_BUF_ERROR && unmoved(&compressor, &at))`, from DA to DK
   (ULoopDKit.assertD_stmt).  A call offered no output space returned Z_BUF_ERROR and left the six members as
   position_of recorded them (DA), so unmoved returns 1 (laws_session Facts.unmoved_b_iff); its pointer
   comparisons compare next_in (data + |D|) and next_out (compressed + |O|) with themselves, defined in the
   memory of the objects data and compressed (ULoopDLib.ld_test_eq, Facts.lend_cmp).  && does not call unmoved
   when code is not Z_BUF_ERROR. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.deflate.Obligations.
Require Zlib.proof.deflate.Api_toend.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.rt_stream.UDFacts.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_stream.LawCS.
Require Import Zlib.proof.harness.rt_stream.UMainStmt.
Require Import Zlib.proof.harness.rt_stream.UMainKit.
Require Import Zlib.proof.harness.rt_stream.ULoopDKit.
Require Import Zlib.proof.harness.rt_stream.ULoopDLib.
Require Import Zlib.harness.rt_stream.code.
Require Zlib.deflate.code.
Require Zlib.proof.harness.laws_session.Spec.
Require Zlib.proof.harness.laws_session.Facts.
Require Import Zlib.proof.harness.rt_stream.ULoopDPos.
#[local] Existing Instance LawCS.CS.
Local Open Scope logic.

Module DC := Zlib.deflate.code.
Module LS := Zlib.proof.harness.laws_session.Spec.

(* at, as position_of wrote it (laws_session's compspecs), at the law's compspecs where main reads at.avail_out *)
Lemma at_law (a : LS.posz) (va : val) :
  @data_at LS.CS_session Tsh LS.t_pos (LS.pos_of a) va = @data_at LawCS.CS Tsh t_p (LS.pos_of a) va.
Proof. apply equal_f. apply (@data_at_change_composite _ _ CC_session); [apply JMeq_refl | reflexivity]. Qed.

(* the memory lent to unmoved: with the objects data and compressed, next_in = data + k and
   next_out = compressed + |O| are comparable with themselves *)
Lemma lend_objs (u : setup) (O : list Z) (k : Z) (a : LS.posz) :
  su_ok u -> 0 <= k <= Zlength (su_data u) -> 0 <= Zlength O <= su_cap u ->
  LS.pz_next_in a = offset_val k (su_dp u) -> LS.pz_next_out a = offset_val (Zlength O) (su_cp u) ->
  dobj u * cobj u O |-- (dobj u * cobj u O) && LS.unmoved_cmp a a.
Proof.
  intros Hu Hk HO Ei Eo. apply Zlib.proof.harness.laws_session.Facts.lend_cmp.
  unfold LS.unmoved_cmp. rewrite Ei, Eo.
  destruct Hu as (_ & _ & _ & _ & _ & _ & _ & Pd & Pc & _).
  apply andp_right.
  - unfold dobj. rewrite sepcon_assoc. apply ld_test_eq; auto.
  - unfold cobj. rewrite sepcon_comm. apply ld_test_eq; auto.
Qed.

(* the end of the statement: DK, the postcondition's normal part *)
Ltac da_close :=
  destruct POST_m as [rn rb rc rr]; unfold DK; cbn [RA_normal];
  unfold su_locals, lv_locals; simpl app; entailer!.

Lemma assert_d : assertD_stmt.
Proof.
  intros Espec J gv vc vd va u off flush code l a.
  unfold Delta_m. simplify_func_tycontext.
  unfold DA, assertD.
  abbreviate_semax.
  Intros.
  rewrite at_law.
  unfold su_locals, lv_locals; simpl app.
  forward.
  match goal with |- context [temp _t'47 ?v] =>
    replace v with (Vint (Int.repr (LS.pz_avail_out a))) by (destruct a; reflexivity) end.
  pose proof H8 as (Hni & Hno & Hai & Hti & Hao & Hto).
  forward_if.
  - (* no output space was offered: Z_BUF_ERROR, nothing moved *)
    destruct (H9 H10) as [Hc Hp]. subst code.
    assert (Hl : dl_ok J u l) by exact H7.
    pose proof Hl as (_ & _ & HDoff & _ & _ & _ & _ & _ & _ & Eni & _).
    assert (HD0 := Zlength_nonneg (dl_D l)). assert (HO0 := Zlength_nonneg (dl_O l)).
    forward_if (temp _t'22 (Vint Int.one)).
    + sep_apply (cstream_lend gv vc (dl_c l)). Intros r.
      rewrite Hp.
      sep_apply (lend_objs u (dl_O l) (Zlength (dl_D l)) a H ltac:(lia) ltac:(lia)
                   ltac:(rewrite <- Hp; exact Eni) ltac:(rewrite <- Hp; exact H6)).
      rewrite <- at_law.
      forward_call (vc, Ews, a, r, va, Tsh, a, dobj u * cobj u (dl_O l)).
      rewrite (proj2 (Zlib.proof.harness.laws_session.Facts.unmoved_b_iff a a) eq_refl).
      Intros.
      forward.
      sep_apply (modus_ponens_wand (@data_at LS.CS_session Ews t_zs (LS.zs_of a r) vc) (cstream gv vc (dl_c l))).
      rewrite at_law.
      entailer!.
    + exfalso. match goal with E : Int.repr Z_BUF_ERROR <> _ |- _ => apply E; reflexivity end.
    + forward_call (Int.one).
      rewrite <- at_law. sep_apply (at_free a va).
      da_close.
  - (* output space offered: no assert *)
    forward.
    rewrite <- at_law. sep_apply (at_free a va).
    da_close.
Qed.
