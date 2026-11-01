(* Law rt_stream (data of any length), main's inflate loop: the end of the body, from ICr (for the code r, the
   state l inflate() returned and the position a main recorded in at before the call) to IC, the loop's test:
   gp_assert(code == Z_OK || code == Z_BUF_ERROR || code == Z_STREAM_END), then
   if (at.avail_in == 0 && at.avail_out == 0) gp_assert(code != Z_OK && unmoved(&decompressor, &at)).
   A call offered neither input nor output space returned a code other than Z_OK and left the stream at a
   (ICr's last fact, from UIFacts.ui_call), so unmoved is called and returns 1; its two pointer comparisons
   compare next_in and next_out with themselves, defined in the memory of the objects compressed and out. *)
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
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.rt_stream.UIFacts.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.laws_session.Facts.
Require Import Zlib.proof.harness.rt_stream.LawCS.
Require Import Zlib.proof.harness.rt_stream.UMainStmt.
Require Import Zlib.proof.harness.rt_stream.UMainKit.
Require Import Zlib.harness.rt_stream.code.
Require Import Zlib.proof.harness.rt_stream.ULoopIPos.
Require Import Zlib.proof.harness.rt_stream.ULoopIKit.
#[local] Existing Instance LawCS.CS.
Local Open Scope logic.

(* gp_assert(code == Z_OK || code == Z_BUF_ERROR || code == Z_STREAM_END) *)
Lemma codes_ok {Espec : OracleKind} P gv vc vd va u O c r l a :
  semax Delta_m (ICr gv vc vd va P u O c r l a) codesI (normal_ret_assert (ICr gv vc vd va P u O c r l a)).
Proof.
  unfold Delta_m; simplify_func_tycontext.
  unfold ICr, codesI. Intros.
  unfold su_locals, lv_locals. simpl app.
  match goal with H : r = Z_OK \/ _ |- _ => destruct H as [E|[E|E]]; subst r end.
  - ifk _t'32 1. ifk _t'33 1. forward_call (Int.repr 1). entailer!.
  - ifk _t'32 1. ifk _t'33 1. forward_call (Int.repr 1). entailer!.
  - ifk _t'32 0. ifk _t'33 1. forward_call (Int.repr 1). entailer!.
Qed.

(* the test of a call offered neither input nor output space *)
Lemma idle_ok {Espec : OracleKind} P gv vc vd va u O c r l a :
  semax Delta_m (ICr gv vc vd va P u O c r l a) idleI (RI gv vc vd va P u O c).
Proof.
  unfold Delta_m; simplify_func_tycontext.
  unfold ICr, idleI, RI. Intros.
  match goal with H : LS.posz_ok a |- _ => rename H into Hok end.
  match goal with H : LS.pz_avail_in a = 0 -> _ |- _ => rename H into Hidle end.
  unfold su_locals, lv_locals. simpl app.
  destruct a as [ani aai ati ano aao ato]. cbn [LS.pz_avail_in LS.pz_avail_out] in Hidle.
  unfold LS.pos_of, LS.pos_val. cbn [LS.pz_next_in LS.pz_avail_in LS.pz_total_in LS.pz_next_out LS.pz_avail_out
    LS.pz_total_out].
  pose proof Hok as (_ & _ & Hai & _ & Hao & _). cbn [LS.pz_avail_in LS.pz_avail_out] in Hai, Hao.
  pose proof H2 as (_ & _ & Hpos & (rest & Erest) & Eni & Eno).
  assert (Hout : Zlength (il_out l) <= Zlength (su_data u))
    by (rewrite Erest, Zlength_app; pose proof (Zlength_nonneg rest); lia).
  pose proof H as (_ & _ & _ & _ & _ & _ & _ & _ & Pcp & Pop).
  forward.
  destruct (Z.eq_dec aai 0) as [Ei | Ei]; [destruct (Z.eq_dec aao 0) as [Eo | Eo] | ].
  - (* neither input nor output space: not Z_OK, and the stream did not move *)
    subst aai aao. destruct (Hidle eq_refl eq_refl) as (Hr & Ea).
    pose proof (f_equal LS.pz_next_in Ea) as Eni'. pose proof (f_equal LS.pz_next_out Ea) as Eno'.
    cbn [zpos LS.pz_next_in LS.pz_next_out] in Eni', Eno'.
    set (a' := LS.mk_posz ani 0 ati ano 0 ato) in *.
    forward_if (temp _t'36 (Vint (Int.repr 1))).
    { forward. forward. entailer!. }
    { exfalso. auto. }
    forward_if.
    2: { exfalso. match goal with H : Int.repr 1 = Int.zero |- _ => discriminate H end. }
    replace_SEP 9 (@data_at LS.CS_session Tsh LS.t_pos (LS.pos_of a') va).
    { entailer!. rewrite <- at_pos_cs. apply derives_refl. }
    rewrite istreamA_session. Intros. rewrite Ea.
    assert (Hcmp : cobj u O * oobj u (il_out l) |-- LS.unmoved_cmp a' a').
    { unfold LS.unmoved_cmp. cbn [a' LS.pz_next_in LS.pz_next_out].
      rewrite <- Eni', <- Eno', Eni, Eno. apply objs_cmp; auto; lia. }
    sep_apply (Zlib.proof.harness.laws_session.Facts.lend_cmp _ _ Hcmp).
    assert (Hb : LS.unmoved_b a' a' = true) by (apply Zlib.proof.harness.laws_session.Facts.unmoved_b_iff; auto).
    forward_if (temp _t'34 (Vint (Int.repr 1))).
    + forward_call (vd, Tsh, a', zrest gv (il_z l) (adler_v (raw_live (Some (il_L l))) (il_z l) Vundef)
                      (l_sp (il_L l)), va, Tsh, a', cobj u O * oobj u (il_out l)).
      rewrite Hb. Intros. forward. entailer!. apply (Zlib.proof.harness.laws_session.Facts.lend_cmp _ _ Hcmp).
    + exfalso. apply Hr.
      match goal with H3 : r = Z_OK \/ _ |- _ => destruct H3 as [E|[E|E]]; subst r; auto; infeas end.
    + forward_call (Int.repr 1).
      unfold IC, ICe. Exists r l. unfold su_locals, lv_locals. simpl app. rewrite istreamA_session, <- Ea.
      assert (Hdrop : (cobj u O * oobj u (il_out l)) && LS.unmoved_cmp (zpos (il_z l)) (zpos (il_z l))
                      |-- cobj u O * oobj u (il_out l)) by (apply andp_left1, derives_refl).
      sep_apply Hdrop.
      sep_apply (@data_at_data_at_ LS.CS_session Tsh LS.t_pos (LS.pos_of (zpos (il_z l))) va). rewrite <- at_cs.
      entailer!.
  - (* input space only *)
    subst aai.
    forward_if (temp _t'36 (Vint (Int.repr 0))).
    { forward. forward. entailer!. }
    { exfalso. auto. }
    forward_if.
    { exfalso. match goal with H : Int.repr 0 <> Int.zero |- _ => apply H; reflexivity end. }
    forward. unfold IC, ICe. Exists r l. unfold su_locals, lv_locals. simpl app.
    sep_apply (@data_at_data_at_ LawCS.CS Tsh t_p
      (ani, (Vint (Int.repr 0), (ano, (Vint (Int.repr aao), (Vlong (Int64.repr ati), Vlong (Int64.repr ato)))))) va).
    entailer!.
  - forward_if (temp _t'36 (Vint (Int.repr 0))).
    { exfalso. auto. }
    { forward. entailer!. }
    forward_if.
    { exfalso. match goal with H : Int.repr 0 <> Int.zero |- _ => apply H; reflexivity end. }
    forward. unfold IC, ICe. Exists r l. unfold su_locals, lv_locals. simpl app.
    sep_apply (@data_at_data_at_ LawCS.CS Tsh t_p
      (ani, (Vint (Int.repr aai), (ano, (Vint (Int.repr aao), (Vlong (Int64.repr ati), Vlong (Int64.repr ato)))))) va).
    entailer!.
Qed.

Lemma tests_ok {Espec : OracleKind} P gv vc vd va u O c r l a :
  semax Delta_m (ICr gv vc vd va P u O c r l a) (Ssequence codesI idleI) (RI gv vc vd va P u O c).
Proof. eapply semax_seq'; [apply codes_ok | apply idle_ok]. Qed.
