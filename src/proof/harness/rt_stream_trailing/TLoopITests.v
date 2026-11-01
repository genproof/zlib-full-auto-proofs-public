(* Law rt_stream_trailing, main's inflate loop: the end of the body, from ICr_t (for the code r, the state l
   inflate() returned and the position a main recorded in at before the call) to IC_t, the loop's test:
   gp_assert(code == Z_OK || code == Z_BUF_ERROR || code == Z_STREAM_END), then
   gp_assert(accounted(&decompressor, &at)) (TLoopIKit.acc_ok: it returns 1; its pointer comparisons are defined in
   the memory of the objects input and out, TLoopIKit.acc_cmp), then
   if (at.avail_in == 0 && at.avail_out == 0) gp_assert(code != Z_OK && unmoved(&decompressor, &at)).
   rt_stream's ULoopITests.v on the input object, with the test of accounted. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.rt_stream.UDFacts.
Require Import Zlib.proof.harness.rt_stream.UIFacts.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.laws_session.Facts.
Require Import Zlib.proof.harness.rt_stream.LawCS.
Require Import Zlib.proof.harness.rt_stream.UMainKit.
Require Import Zlib.proof.harness.rt_stream.ULoopIPos.
Require Zlib.proof.harness.rt_stream.ULoopIKit.
Require Import Zlib.proof.harness.rt_stream_trailing.TIFacts.
Require Import Zlib.proof.harness.rt_stream_trailing.TMainStmt.
Require Import Zlib.proof.harness.rt_stream_trailing.TMainKit.
Require Import Zlib.proof.harness.rt_stream_trailing.TLoopIKit.
Require Import Zlib.harness.rt_stream_trailing.code.
#[local] Existing Instance LawCS.CS.
Local Open Scope logic.
Module UK := Zlib.proof.harness.rt_stream.ULoopIKit.

(* gp_assert(code == Z_OK || code == Z_BUF_ERROR || code == Z_STREAM_END) *)
Lemma codes_t_ok {Espec : OracleKind} P gv vc vd va u O c src ip r l a :
  semax Delta_t (ICr_t gv vc vd va P u O c src ip r l a) codesI_t
    (normal_ret_assert (ICr_t gv vc vd va P u O c src ip r l a)).
Proof.
  unfold Delta_t; simplify_func_tycontext.
  unfold ICr_t, codesI_t. Intros.
  unfold su_locals, lv_locals. simpl app.
  match goal with H : r = Z_OK \/ _ |- _ => destruct H as [E|[E|E]]; subst r end.
  - ifk _t'35 1. ifk _t'36 1. forward_call (Int.repr 1). entailer!.
  - ifk _t'35 1. ifk _t'36 1. forward_call (Int.repr 1). entailer!.
  - ifk _t'35 0. ifk _t'36 1. forward_call (Int.repr 1). entailer!.
Qed.

(* gp_assert(accounted(&decompressor, &at)) *)
Lemma acc_t_ok {Espec : OracleKind} P gv vc vd va u O c src ip r l a :
  semax Delta_t (ICr_t gv vc vd va P u O c src ip r l a) accI_t
    (normal_ret_assert (ICr_t gv vc vd va P u O c src ip r l a)).
Proof.
  unfold Delta_t; simplify_func_tycontext.
  unfold ICr_t, accI_t. Intros.
  unfold su_locals, lv_locals. simpl app.
  match goal with H : acc_ok _ _ _ _ _ |- _ => rename H into Hacc end.
  match goal with H : il_ok_t _ _ _ _ _ _ |- _ => pose proof H as (_ & _ & Hpos & (rest & Erest) & Eni & Eno) end.
  match goal with H : su_ok u |- _ => pose proof H as (_ & _ & _ & _ & _ & _ & _ & _ & Pcp & Pop) end.
  pose proof Hacc as (Hb & Pai & Pao & _).
  replace_SEP 9 (@data_at LS.CS_session Tsh LS.t_pos (LS.pos_of a) va).
  { entailer!. rewrite <- UK.at_pos_cs. apply derives_refl. }
  rewrite istreamA_session. Intros.
  assert (Hcmp : oobj u (il_out l) * iobj src ip |-- LS.accounted_cmp (zpos (il_z l)) a)
    by (apply acc_cmp; auto).
  sep_apply (Zlib.proof.harness.laws_session.Facts.lend_cmp _ _ Hcmp).
  forward_call (vd, Tsh, zpos (il_z l), zrest gv (il_z l) (adler_v (raw_live (Some (il_L l))) (il_z l) Vundef)
                  (l_sp (il_L l)), va, Tsh, a, oobj u (il_out l) * iobj src ip).
  { cbn [zpos LS.pz_next_in LS.pz_next_out].
    rewrite Eni, Eno, !isptr_offset_val.
    split; [apply zpos_ok; auto; rewrite ?Eni, ?Eno; apply isptr_is_pointer_or_null;
            rewrite isptr_offset_val; auto | auto]. }
  rewrite Hb. forward_call (Int.repr 1).
  rewrite <- UK.at_pos_cs. entailer!.
Qed.

(* the test of a call offered neither input nor output space *)
Lemma idle_t_ok {Espec : OracleKind} P gv vc vd va u O c src ip r l a :
  semax Delta_t (ICr_t gv vc vd va P u O c src ip r l a) idleI_t (RI_t gv vc vd va P u O c src ip).
Proof.
  unfold Delta_t; simplify_func_tycontext.
  unfold ICr_t, idleI_t, RI_t. Intros.
  match goal with H : LS.posz_ok a |- _ => rename H into Hok end.
  match goal with H : LS.pz_avail_in a = 0 -> _ |- _ => rename H into Hidle end.
  unfold su_locals, lv_locals. simpl app.
  destruct a as [ani aai ati ano aao ato]. cbn [LS.pz_avail_in LS.pz_avail_out] in Hidle.
  unfold LS.pos_of, LS.pos_val. cbn [LS.pz_next_in LS.pz_avail_in LS.pz_total_in LS.pz_next_out LS.pz_avail_out
    LS.pz_total_out].
  pose proof Hok as (_ & _ & Hai & _ & Hao & _). cbn [LS.pz_avail_in LS.pz_avail_out] in Hai, Hao.
  match goal with H : il_ok_t _ _ _ _ _ _ |- _ => pose proof H as (_ & _ & Hpos & (rest & Erest) & Eni & Eno) end.
  assert (Hout : Zlength (il_out l) <= Zlength (su_data u))
    by (rewrite Erest, Zlength_app; pose proof (Zlength_nonneg rest); lia).
  match goal with H : su_ok u |- _ => pose proof H as (_ & _ & _ & _ & _ & _ & _ & _ & Pcp & Pop) end.
  forward.
  destruct (Z.eq_dec aai 0) as [Ei | Ei]; [destruct (Z.eq_dec aao 0) as [Eo | Eo] | ].
  - (* neither input nor output space: not Z_OK, and the stream did not move *)
    subst aai aao. destruct (Hidle eq_refl eq_refl) as (Hr & Ea).
    pose proof (f_equal LS.pz_next_in Ea) as Eni'. pose proof (f_equal LS.pz_next_out Ea) as Eno'.
    cbn [zpos LS.pz_next_in LS.pz_next_out] in Eni', Eno'.
    set (a' := LS.mk_posz ani 0 ati ano 0 ato) in *.
    forward_if (temp _t'40 (Vint (Int.repr 1))).
    { forward. forward. entailer!. }
    { exfalso. auto. }
    forward_if.
    2: { exfalso. match goal with H : Int.repr 1 = Int.zero |- _ => discriminate H end. }
    replace_SEP 9 (@data_at LS.CS_session Tsh LS.t_pos (LS.pos_of a') va).
    { entailer!. rewrite <- UK.at_pos_cs. apply derives_refl. }
    rewrite istreamA_session. Intros. rewrite Ea.
    assert (Hcmp : oobj u (il_out l) * iobj src ip |-- LS.unmoved_cmp a' a').
    { unfold LS.unmoved_cmp. cbn [a' LS.pz_next_in LS.pz_next_out].
      rewrite <- Eni', <- Eno', Eni, Eno. apply objs_cmp_t; auto. pose proof (Zlength_nonneg (il_out l)); lia. }
    sep_apply (Zlib.proof.harness.laws_session.Facts.lend_cmp _ _ Hcmp).
    assert (Hb : LS.unmoved_b a' a' = true) by (apply Zlib.proof.harness.laws_session.Facts.unmoved_b_iff; auto).
    forward_if (temp _t'38 (Vint (Int.repr 1))).
    + forward_call (vd, Tsh, a', zrest gv (il_z l) (adler_v (raw_live (Some (il_L l))) (il_z l) Vundef)
                      (l_sp (il_L l)), va, Tsh, a', oobj u (il_out l) * iobj src ip).
      rewrite Hb. Intros. forward. entailer!. apply (Zlib.proof.harness.laws_session.Facts.lend_cmp _ _ Hcmp).
    + exfalso. apply Hr.
      match goal with H3 : r = Z_OK \/ _ |- _ => destruct H3 as [E|[E|E]]; subst r; auto; infeas end.
    + forward_call (Int.repr 1).
      unfold IC_t, ICe_t. Exists r l. unfold su_locals, lv_locals. simpl app. rewrite istreamA_session, <- Ea.
      assert (Hdrop : (oobj u (il_out l) * iobj src ip) && LS.unmoved_cmp (zpos (il_z l)) (zpos (il_z l))
                      |-- oobj u (il_out l) * iobj src ip) by (apply andp_left1, derives_refl).
      sep_apply Hdrop.
      sep_apply (@data_at_data_at_ LS.CS_session Tsh LS.t_pos (LS.pos_of (zpos (il_z l))) va).
      rewrite <- UK.at_cs.
      entailer!.
  - (* input space only *)
    subst aai.
    forward_if (temp _t'40 (Vint (Int.repr 0))).
    { forward. forward. entailer!. }
    { exfalso. auto. }
    forward_if.
    { exfalso. match goal with H : Int.repr 0 <> Int.zero |- _ => apply H; reflexivity end. }
    forward. unfold IC_t, ICe_t. Exists r l. unfold su_locals, lv_locals. simpl app.
    sep_apply (@data_at_data_at_ LawCS.CS Tsh t_p
      (ani, (Vint (Int.repr 0), (ano, (Vint (Int.repr aao), (Vlong (Int64.repr ati), Vlong (Int64.repr ato)))))) va).
    entailer!.
  - forward_if (temp _t'40 (Vint (Int.repr 0))).
    { exfalso. auto. }
    { forward. entailer!. }
    forward_if.
    { exfalso. match goal with H : Int.repr 0 <> Int.zero |- _ => apply H; reflexivity end. }
    forward. unfold IC_t, ICe_t. Exists r l. unfold su_locals, lv_locals. simpl app.
    sep_apply (@data_at_data_at_ LawCS.CS Tsh t_p
      (ani, (Vint (Int.repr aai), (ano, (Vint (Int.repr aao), (Vlong (Int64.repr ati), Vlong (Int64.repr ato)))))) va).
    entailer!.
Qed.

Lemma tests_t_ok {Espec : OracleKind} P gv vc vd va u O c src ip r l a :
  semax Delta_t (ICr_t gv vc vd va P u O c src ip r l a) (Ssequence codesI_t (Ssequence accI_t idleI_t))
    (RI_t gv vc vd va P u O c src ip).
Proof.
  eapply semax_seq'; [apply codes_t_ok | ].
  eapply semax_seq'; [apply acc_t_ok | apply idle_t_ok].
Qed.
