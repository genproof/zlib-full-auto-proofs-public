(* Law rt_session, main's inflate loop with a header (SMLoopI9.v): the end of the body, from ICr9 (for the code r,
   the state l inflate() returned and the position a main recorded in at before the call) to IC9, the loop's
   test: gp_assert(code == Z_OK || code == Z_BUF_ERROR || code == Z_STREAM_END || code == Z_NEED_DICT), then
   gp_assert(accounted(&decompressor, &at)) (SLI9Kit.acc_ok9: it returns 1; its pointer comparisons are defined
   in the memory of the objects input and out, SLI9Kit.acc_cmp9), then
   if (at.avail_in == 0 && at.avail_out == 0) gp_assert(code != Z_OK && unmoved(&decompressor, &at)), and the
   Z_NEED_DICT branch, never taken with a header (ICr9: r is Z_OK, Z_BUF_ERROR or Z_STREAM_END). *)
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
Require Zlib.proof.roundtrip.RTH8Spec.
Require Zlib.proof.roundtrip.RTH9Spec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.laws_session.Facts.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SDFacts.
Require Import Zlib.proof.harness.rt_session.SIFacts.
Require Import Zlib.proof.harness.rt_session.SMainStmt.
Require Import Zlib.proof.harness.rt_session.SMKit.
Require Import Zlib.proof.harness.rt_stream.ULoopIPos.
Require Zlib.proof.harness.rt_stream.ULoopIKit.
Require Import Zlib.proof.harness.rt_session.SLI9Kit.
Require Import Zlib.harness.rt_session.code.
#[local] Existing Instance SCS.CS.
Local Open Scope logic.
Module R8 := Zlib.proof.roundtrip.RTH8Spec.
Module R9 := Zlib.proof.roundtrip.RTH9Spec.
Module UK := Zlib.proof.harness.rt_stream.ULoopIKit.

(* the rest of main's locals and memory, a frame of the tests: closed with respect to the temporaries they set *)
Ltac closed9 := unfold i9_locals, lvs, lv_locals; simpl app; unfold closed_wrt_modvars; auto 50 with closed.

(* the frame of the tests of accounted and of an idle call: all but the code, the addresses of decompressor and
   at, and the first four items of the memory *)
Ltac frame9 :=
  match goal with |- semax _ (PROPx _ (LOCALx (?q1 :: ?q2 :: ?q3 :: ?Q2) (SEPx (?a0 :: ?a1 :: ?a2 :: ?a3 :: ?R2))))
                       _ _ =>
    eapply (semax_frame_PQR Q2 R2 _ _ [a0; a1; a2; a3] [] [q1; q2; q3] [])
  end.

(* gp_assert(code == Z_OK || code == Z_BUF_ERROR || code == Z_STREAM_END || code == Z_NEED_DICT), on the code
   alone: the rest of main's state is a frame (semax_frame_PQR), which keeps the tests fast *)
Lemma codes9_core {Espec : OracleKind} r :
  r = Z_OK \/ r = Z_BUF_ERROR \/ r = Z_STREAM_END ->
  semax Delta_9 (PROP () LOCAL (temp _code (vi r)) SEP ()) codesI9
    (normal_ret_assert (PROP () LOCAL (temp _code (vi r)) SEP ())).
Proof.
  intros Hr.
  unfold Delta_9; simplify_func_tycontext.
  unfold codesI9. abbreviate_semax.
  destruct Hr as [E|[E|E]]; subst r.
  - ifk9 _t'75 1. ifk9 _t'76 1. ifk9 _t'77 1. forward_call (Int.repr 1). entailer!.
  - ifk9 _t'75 1. ifk9 _t'76 1. ifk9 _t'77 1. forward_call (Int.repr 1). entailer!.
  - ifk9 _t'75 0. ifk9 _t'76 1. ifk9 _t'77 1. forward_call (Int.repr 1). entailer!.
Qed.

(* The tests of accounted and of a call offered neither input nor output space read the decompressor, at and the
   two objects only: they are proved on these four items of the memory, with the code and the addresses of
   decompressor and at; the rest of main's state is a frame (semax_frame_PQR). *)

(* gp_assert(accounted(&decompressor, &at)) *)
Lemma acc9_core {Espec : OracleKind} gv vd va u src ip r l a :
  su_ok u -> il_mem9 u src ip l -> LS.posz_ok a -> acc_ok9 src ip u l a -> isptr ip ->
  semax Delta_9
    (PROP () LOCAL (temp _code (vi r); lvar _decompressor t_z vd; lvar _at t_p va)
     SEP (R8.istream8 gv Tsh vd (il_z l) (Some (il_L l)); oobj u (il_out l);
          @data_at LS.CS_session Tsh LS.t_pos (LS.pos_of a) va; iobj src ip))
    accI9
    (normal_ret_assert
    (PROP () LOCAL (temp _code (vi r); lvar _decompressor t_z vd; lvar _at t_p va)
     SEP (R8.istream8 gv Tsh vd (il_z l) (Some (il_L l)); oobj u (il_out l);
          @data_at LS.CS_session Tsh LS.t_pos (LS.pos_of a) va; iobj src ip))).
Proof.
  intros SU IM Hok Hacc Pip.
  unfold Delta_9; simplify_func_tycontext.
  unfold accI9. abbreviate_semax.
  pose proof IM as (_ & _ & Eni & Eno).
  pose proof SU as (_ & _ & _ & _ & _ & _ & _ & Pop & _).
  pose proof Hacc as (Hb & Pai & Pao & _).
  rewrite istream8_session. Intros.
  assert (Hcmp : oobj u (il_out l) * iobj src ip |-- LS.accounted_cmp (zpos (il_z l)) a)
    by (apply acc_cmp9; auto).
  sep_apply (Zlib.proof.harness.laws_session.Facts.lend_cmp _ _ Hcmp).
  forward_call (vd, Tsh, zpos (il_z l), zrest gv (il_z l) (vl (zf_adler (il_z l))) (l_sp (il_L l)),
                va, Tsh, a, oobj u (il_out l) * iobj src ip).
  { cbn [zpos LS.pz_next_in LS.pz_next_out].
    rewrite Eni, Eno, !isptr_offset_val.
    split; [apply zpos_ok; auto; rewrite ?Eni, ?Eno; apply isptr_is_pointer_or_null;
            rewrite isptr_offset_val; auto | auto]. }
  rewrite Hb. forward_call (Int.repr 1).
  entailer!. rewrite istream8_session. entailer!.
Qed.

(* if (at.avail_in == 0 && at.avail_out == 0) gp_assert(code != Z_OK && unmoved(&decompressor, &at)); after it,
   at's contents are no longer needed *)
Lemma idle9_core {Espec : OracleKind} gv vd va u src ip r l a :
  su_ok u -> il_mem9 u src ip l -> r = Z_OK \/ r = Z_BUF_ERROR \/ r = Z_STREAM_END -> LS.posz_ok a ->
  (LS.pz_avail_in a = 0 -> LS.pz_avail_out a = 0 -> r <> Z_OK /\ zpos (il_z l) = a) -> isptr ip ->
  semax Delta_9
    (PROP () LOCAL (temp _code (vi r); lvar _decompressor t_z vd; lvar _at t_p va)
     SEP (R8.istream8 gv Tsh vd (il_z l) (Some (il_L l)); oobj u (il_out l);
          @data_at LS.CS_session Tsh LS.t_pos (LS.pos_of a) va; iobj src ip))
    idleI9
    (normal_ret_assert
    (PROP () LOCAL (temp _code (vi r); lvar _decompressor t_z vd; lvar _at t_p va)
     SEP (R8.istream8 gv Tsh vd (il_z l) (Some (il_L l)); oobj u (il_out l); data_at_ Tsh t_p va;
          iobj src ip))).
Proof.
  intros SU IM Hrc Hok Hidle Pip.
  unfold Delta_9; simplify_func_tycontext.
  unfold idleI9. abbreviate_semax.
  rewrite <- at_pos_cs9.
  destruct a as [ani aai ati ano aao ato]. cbn [LS.pz_avail_in LS.pz_avail_out] in Hidle.
  unfold LS.pos_of, LS.pos_val. cbn [LS.pz_next_in LS.pz_avail_in LS.pz_total_in LS.pz_next_out LS.pz_avail_out
    LS.pz_total_out].
  pose proof Hok as (_ & _ & Hai & _ & Hao & _). cbn [LS.pz_avail_in LS.pz_avail_out] in Hai, Hao.
  pose proof IM as (Hpos & Hout & Eni & Eno).
  pose proof SU as (_ & _ & _ & _ & _ & _ & _ & Pop & _).
  forward.
  destruct (Z.eq_dec aai 0) as [Ei | Ei]; [destruct (Z.eq_dec aao 0) as [Eo | Eo] | ].
  - (* neither input nor output space: not Z_OK, and the stream did not move *)
    subst aai aao. destruct (Hidle eq_refl eq_refl) as (Hr & Ea).
    pose proof (f_equal LS.pz_next_in Ea) as Eni'. pose proof (f_equal LS.pz_next_out Ea) as Eno'.
    cbn [zpos LS.pz_next_in LS.pz_next_out] in Eni', Eno'.
    set (a' := LS.mk_posz ani 0 ati ano 0 ato) in *.
    forward_if (temp _t'81 (Vint (Int.repr 1))).
    { forward. forward. entailer!. }
    { exfalso. auto. }
    forward_if.
    2: { exfalso. match goal with H : Int.repr 1 = Int.zero |- _ => discriminate H end. }
    replace_SEP 2 (@data_at LS.CS_session Tsh LS.t_pos (LS.pos_of a') va).
    { entailer!. rewrite <- at_pos_cs9. apply derives_refl. }
    rewrite istream8_session. Intros. rewrite Ea.
    assert (Hcmp : oobj u (il_out l) * iobj src ip |-- LS.unmoved_cmp a' a').
    { unfold LS.unmoved_cmp. cbn [a' LS.pz_next_in LS.pz_next_out].
      rewrite <- Eni', <- Eno', Eni, Eno. apply objs_cmp9; auto. pose proof (Zlength_nonneg (il_out l)); lia. }
    sep_apply (Zlib.proof.harness.laws_session.Facts.lend_cmp _ _ Hcmp).
    assert (Hb : LS.unmoved_b a' a' = true) by (apply Zlib.proof.harness.laws_session.Facts.unmoved_b_iff; auto).
    forward_if (temp _t'79 (Vint (Int.repr 1))).
    + forward_call (vd, Tsh, a', zrest gv (il_z l) (vl (zf_adler (il_z l))) (l_sp (il_L l)),
                    va, Tsh, a', oobj u (il_out l) * iobj src ip).
      rewrite Hb. Intros. forward. entailer!. apply (Zlib.proof.harness.laws_session.Facts.lend_cmp _ _ Hcmp).
    + exfalso. apply Hr.
      match goal with H3 : r = Z_OK \/ _ |- _ => destruct H3 as [E|[E|E]]; subst r; auto; infeas9 end.
    + forward_call (Int.repr 1).
      rewrite istream8_session, <- Ea.
      assert (Hdrop : (oobj u (il_out l) * iobj src ip) && LS.unmoved_cmp (zpos (il_z l)) (zpos (il_z l))
                      |-- oobj u (il_out l) * iobj src ip) by (apply andp_left1, derives_refl).
      sep_apply Hdrop.
      sep_apply (@data_at_data_at_ LS.CS_session Tsh LS.t_pos (LS.pos_of (zpos (il_z l))) va).
      rewrite <- at_cs9.
      entailer!.
  - (* input space only *)
    subst aai.
    forward_if (temp _t'81 (Vint (Int.repr 0))).
    { forward. forward. entailer!. }
    { exfalso. auto. }
    forward_if.
    { exfalso. match goal with H : Int.repr 0 <> Int.zero |- _ => apply H; reflexivity end. }
    forward.
    sep_apply (@data_at_data_at_ SCS.CS Tsh t_p
      (ani, (Vint (Int.repr 0), (ano, (Vint (Int.repr aao), (Vlong (Int64.repr ati), Vlong (Int64.repr ato)))))) va).
    entailer!.
  - forward_if (temp _t'81 (Vint (Int.repr 0))).
    { exfalso. auto. }
    { forward. entailer!. }
    forward_if.
    { exfalso. match goal with H : Int.repr 0 <> Int.zero |- _ => apply H; reflexivity end. }
    forward.
    sep_apply (@data_at_data_at_ SCS.CS Tsh t_p
      (ani, (Vint (Int.repr aai), (ano, (Vint (Int.repr aao), (Vlong (Int64.repr ati), Vlong (Int64.repr ato)))))) va).
    entailer!.
Qed.

(* the tests of the codes, of accounted and of an idle call, on main's whole state *)
Lemma tests3_9_ok {Espec : OracleKind} P gv vh vg vc va vd u O c src ip r l a :
  semax Delta_9 (ICr9 gv vh vg vc va vd P u O c src ip r l a) (Ssequence (Ssequence codesI9 accI9) idleI9)
    (normal_ret_assert (ICe9 gv vh vg vc va vd P u O c src ip r l)).
Proof.
  unfold ICr9. Intros.
  match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx [?s0; ?s1; ?s2; ?s3; ?s4; ?s5; ?s6; ?s7; ?s8; ?s9; ?s10;
                                                      ?s11; ?s12; ?s13; ?s14]))) _ _ =>
    apply semax_pre with (PROPx [] (LOCALx ([temp _code (vi r); lvar _decompressor t_z vd; lvar _at t_p va] ++ Q)
                          (SEPx ([s0; s9; s10; s11] ++ [s1; s2; s3; s4; s5; s6; s7; s8; s12; s13; s14]))))
  end.
  { unfold i9_locals, lvs, lv_locals. simpl app. entailer!. }
  simpl app. eapply semax_seq'.
  { eapply semax_seq'.
    { match goal with |- semax _ (PROPx _ (LOCALx (?q :: ?Q2) (SEPx ?R2))) _ _ =>
        apply (semax_frame_PQR Q2 R2 _ _ [] [] [q] [] [q] []); [closed9 | apply codes9_core; auto] end. }
    simpl app. frame9; [closed9 | apply acc9_core; auto]. }
  simpl app. eapply semax_post'; [ | frame9; [closed9 | apply idle9_core; auto]].
  (* the three locals of the tests are also in main's locals: drop them first *)
  simpl app.
  match goal with |- ENTAIL _, PROPx _ (LOCALx (_ :: _ :: _ :: ?Q) (SEPx ?R)) |-- _ =>
    apply ENTAIL_trans with (PROPx [] (LOCALx Q (SEPx R)));
    [apply andp_left2; do 3 (rewrite <- insert_local; apply andp_left2); apply derives_refl | ]
  end.
  unfold ICe9, i9_locals, lvs, lv_locals. simpl app. entailer!.
Qed.

(* if (code == Z_NEED_DICT) {...}: never taken, since with a header r is Z_OK, Z_BUF_ERROR or Z_STREAM_END *)
Lemma need9_ok {Espec : OracleKind} P gv vh vg vc va vd u O c src ip r l :
  semax Delta_9 (ICe9 gv vh vg vc va vd P u O c src ip r l) needI9 (RI9 gv vh vg vc va vd P u O c src ip).
Proof.
  unfold Delta_9; simplify_func_tycontext.
  unfold ICe9, needI9. Intros.
  unfold i9_locals, lvs, lv_locals. simpl app.
  abbreviate_semax.
  forward_if.
  - exfalso. match goal with H : r = Z_OK \/ _ |- _ => destruct H as [E|[E|E]]; subst r end; infeas9.
  - unfold RI9, loop1_ret_assert. cbn [RA_normal].
    forward. unfold IC9, ICe9. Exists r l. unfold i9_locals, lvs, lv_locals. simpl app. entailer!.
Qed.

Lemma tests9_ok {Espec : OracleKind} P gv vh vg vc va vd u O c src ip r l a :
  semax Delta_9 (ICr9 gv vh vg vc va vd P u O c src ip r l a)
    (Ssequence codesI9 (Ssequence accI9 (Ssequence idleI9 needI9)))
    (RI9 gv vh vg vc va vd P u O c src ip).
Proof.
  rewrite seq_assoc, seq_assoc.
  eapply semax_seq'; [apply tests3_9_ok | apply need9_ok].
Qed.
