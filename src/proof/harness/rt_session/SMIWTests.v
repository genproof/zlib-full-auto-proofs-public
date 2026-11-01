(* Law rt_session, main's inflate loop without a header (SMLoopIW.v): after the call, from ICr_w (for the code r,
   the state l inflate() returned and the position a main recorded in at before the call) to ICd_w:
   gp_assert(code == Z_OK || code == Z_BUF_ERROR || code == Z_STREAM_END || code == Z_NEED_DICT), then
   gp_assert(accounted(&decompressor, &at)) (SMIWKit.acc_ok_w: it returns 1; its pointer comparisons are defined
   in the memory of the objects input and out, SMIWKit.acc_cmp_w), then
   if (at.avail_in == 0 && at.avail_out == 0) gp_assert(code != Z_OK && unmoved(&decompressor, &at)). *)
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
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.laws_session.Facts.
Require Import Zlib.proof.harness.rt_stream.ULoopIPos.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SDFacts.
Require Import Zlib.proof.harness.rt_session.SIFacts.
Require Import Zlib.proof.harness.rt_session.SMainStmt.
Require Import Zlib.proof.harness.rt_session.SMKit.
Require Import Zlib.proof.harness.rt_session.SMIWKit.
Require Import Zlib.harness.rt_session.code.
#[local] Existing Instance SCS.CS.
Local Open Scope logic.

(* forward_call on this program: remove_localdef_temp's identifier tests computed by vm_compute, the rest
   by lazy reduction (floyd's default reduces the long list of locals very slowly) *)
Ltac rlt_fix u :=
  lazymatch u with
  | context C [rlt_ident_eq ?a ?b] =>
      let v := eval vm_compute in (rlt_ident_eq a b) in
      let u2 := context C [v] in rlt_fix u2
  | _ => u
  end.

Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u := constr:(remove_localdef_temp i L) in
    let u' := eval lazy delta [remove_localdef_temp] beta iota in u in
    let u' := rlt_fix u' in
    let u' := eval lazy beta iota in u' in
    let u' := eval lazy zeta in u' in
    change u with u'
  end.

(* a branch that cannot be taken *)
Ltac infeas := exfalso; first [ match goal with H : ?a <> ?b |- _ => solve [apply H; reflexivity] end
                              | match goal with H : _ |- _ => solve [discriminate H] end
                              | contradiction
                              | match goal with H : Int.repr _ = Int.repr _ |- _ =>
                                  apply repr_inj_signed in H; [lia | rep_lia | rep_lia] end
                              | lia ].
(* `if (c) t = 1; else t = (expr);` with the value v of t known *)
Ltac ifk t v := match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_if (PROPx [] (LOCALx (temp t (Vint (Int.repr v)) :: Q) (SEPx R))) end;
  [ first [infeas | forward; entailer!] | first [infeas | forward; entailer!] | ].

(** ** Framing: each test on the locals and the memory it reads *)

(* a part proved on the locals Q1 and the memory R1 it uses (with the facts P as Coq hypotheses), run in an
   assertion whose locals and memory are permutations of Q1 ++ Q2 and R1 ++ R2, the frame Q2, R2 untouched *)
Lemma semax_frame_perm {Espec : OracleKind} {cs : compspecs} Delta P P' Q Q1 Q2 Q1' Q' R R1 R2 R1' R' c :
  Permutation Q (Q1 ++ Q2) -> Permutation R (R1 ++ R2) ->
  Permutation Q' (Q1' ++ Q2) -> Permutation R' (R1' ++ R2) ->
  closed_wrt_modvars c (LOCALx Q2 (SEPx R2)) ->
  (fold_right Logic.and True P ->
   Logic.and (fold_right Logic.and True P')
     (@semax cs Espec Delta (PROPx [] (LOCALx Q1 (SEPx R1))) c (normal_ret_assert (PROPx [] (LOCALx Q1' (SEPx R1')))))) ->
  @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R))) c (normal_ret_assert (PROPx P' (LOCALx Q' (SEPx R')))).
Proof.
  intros HQ HR HQ' HR' Hcl Hs.
  rewrite (LOCALx_Permutation _ _ HQ), (SEPx_Permutation _ _ HR), (LOCALx_Permutation _ _ HQ'),
    (SEPx_Permutation _ _ HR').
  apply semax_pre_simple with (!! (fold_right Logic.and True P) && PROPx [] (LOCALx (Q1 ++ Q2) (SEPx (R1 ++ R2)))).
  { unfold PROPx. apply andp_left2. simpl. normalize. }
  apply semax_extract_prop. intros HP. destruct (Hs HP) as [HP' Hs'].
  eapply semax_post_flipped'.
  { eapply (semax_frame_PQR Q2 R2); [exact Hcl | exact Hs']. }
  unfold PROPx. intro rho. simpl. normalize. apply andp_left2, derives_refl.
Qed.

(* Permutation l r, where r lists the elements of l (syntactically equal) in another order *)
Ltac perm_front x l :=
  lazymatch l with
  | x :: _ => let T := type of x in constr:(@nil T)
  | ?h :: ?t => let p := perm_front x t in constr:(h :: p)
  end.
Ltac perm_back x l :=
  lazymatch l with
  | x :: ?t => t
  | _ :: ?t => perm_back x t
  end.
Ltac perm_solve :=
  simpl app;
  repeat match goal with
  | |- Permutation _ ?r => is_evar r; apply Permutation_refl
  | |- Permutation ?l ?l => apply Permutation_refl
  | |- Permutation (?x :: _) (?x :: _) => apply perm_skip
  | |- Permutation ?l (?x :: ?r) =>
      let l1 := perm_front x l in
      let l2 := perm_back x l in
      change l with (l1 ++ x :: l2);
      apply Permutation_sym, Permutation_cons_app, Permutation_sym; simpl app
  end.

(* gp_assert(code == Z_OK || code == Z_BUF_ERROR || code == Z_STREAM_END || code == Z_NEED_DICT), on code alone *)
Lemma codes_small {Espec : OracleKind} r :
  r = Z_OK \/ r = Z_BUF_ERROR \/ r = Z_STREAM_END \/ r = Z_NEED_DICT ->
  semax Delta_W (PROP () LOCAL (temp _code (vi r)) SEP ()) codesI_w
    (normal_ret_assert (PROP () LOCAL (temp _code (vi r)) SEP ())).
Proof.
  intros Hr.
  unfold Delta_W; simplify_func_tycontext. unfold codesI_w.
  destruct Hr as [E|[E|[E|E]]]; subst r.
  - ifk _t'75 1. ifk _t'76 1. ifk _t'77 1. forward_call (Int.repr 1). entailer!.
  - ifk _t'75 1. ifk _t'76 1. ifk _t'77 1. forward_call (Int.repr 1). entailer!.
  - ifk _t'75 0. ifk _t'76 1. ifk _t'77 1. forward_call (Int.repr 1). entailer!.
  - ifk _t'75 0. ifk _t'76 0. ifk _t'77 1. forward_call (Int.repr 1). entailer!.
Qed.

Lemma codes_w_ok {Espec : OracleKind} P PN gv vh vg vc va vd u O c src ip r l a :
  semax Delta_W (ICr_w gv vh vg vc va vd P PN u O c src ip r l a) codesI_w
    (normal_ret_assert (ICr_w gv vh vg vc va vd P PN u O c src ip r l a)).
Proof.
  unfold ICr_w.
  eapply (semax_frame_perm _ _ _ _ [temp _code (vi r)] _ [temp _code (vi r)] _ _ [] _ []).
  - apply Permutation_refl.
  - apply Permutation_refl.
  - apply Permutation_refl.
  - apply Permutation_refl.
  - unfold iw_locals, iw_rest, c_locals, d_locals, lvs, lv_locals, codesI_w. simpl app. auto 50 with closed.
  - intros HP. split; [exact HP | ]. apply codes_small.
    unfold iw_props in HP. simpl app in HP. simpl in HP. tauto.
Qed.

(* gp_assert(accounted(&decompressor, &at)), on the decompressor, at and the objects input and out *)
Lemma acc_small {Espec : OracleKind} gv vd va u src ip l a :
  isptr ip -> isptr (su_op u) -> il_geo u src ip l -> LS.posz_ok a -> acc_ok_w src ip u l a ->
  semax Delta_W
    (PROP () LOCAL (lvar _decompressor t_z vd; lvar _at t_p va)
     SEP (istreamA gv Tsh vd (il_z l) Vundef (Some (il_L l)); oobj u (il_out l); data_at Tsh t_p (LS.pos_of a) va;
          iobj src ip))
    accI_w
    (normal_ret_assert
    (PROP () LOCAL (lvar _decompressor t_z vd; lvar _at t_p va)
     SEP (istreamA gv Tsh vd (il_z l) Vundef (Some (il_L l)); oobj u (il_out l); data_at Tsh t_p (LS.pos_of a) va;
          iobj src ip))).
Proof.
  intros Pip Pop Hgeo Hok Hacc.
  unfold Delta_W; simplify_func_tycontext. unfold accI_w.
  pose proof Hgeo as (Hpos & (rest & Erest) & Eni & Eno).
  pose proof Hacc as (Hb & Pai & Pao & _).
  replace_SEP 2 (@data_at LS.CS_session Tsh LS.t_pos (LS.pos_of a) va).
  { entailer!. }
  rewrite istreamA_session. Intros.
  assert (Hcmp : oobj u (il_out l) * iobj src ip |-- LS.accounted_cmp (zpos (il_z l)) a)
    by (apply acc_cmp_w; auto).
  sep_apply (Zlib.proof.harness.laws_session.Facts.lend_cmp _ _ Hcmp).
  forward_call (vd, Tsh, zpos (il_z l), zrest gv (il_z l) (adler_v (raw_live (Some (il_L l))) (il_z l) Vundef)
                  (l_sp (il_L l)), va, Tsh, a, oobj u (il_out l) * iobj src ip).
  { cbn [zpos LS.pz_next_in LS.pz_next_out].
    rewrite Eni, Eno, !isptr_offset_val.
    split; [apply zpos_ok; auto; rewrite ?Eni, ?Eno; apply isptr_is_pointer_or_null;
            rewrite isptr_offset_val; auto | auto]. }
  rewrite Hb. forward_call (Int.repr 1).
  entailer!.
Qed.

Lemma acc_w_ok {Espec : OracleKind} P PN gv vh vg vc va vd u O c src ip r l a :
  semax Delta_W (ICr_w gv vh vg vc va vd P PN u O c src ip r l a) accI_w
    (normal_ret_assert (ICr_w gv vh vg vc va vd P PN u O c src ip r l a)).
Proof.
  unfold ICr_w, iw_props, iw_locals, iw_rest, c_locals, d_locals, lvs, lv_locals. simpl app.
  eapply (semax_frame_perm _ _ _ _ [lvar _decompressor t_z vd; lvar _at t_p va] _
            [lvar _decompressor t_z vd; lvar _at t_p va] _ _
            [istreamA gv Tsh vd (il_z l) Vundef (Some (il_L l)); oobj u (il_out l);
             data_at Tsh t_p (LS.pos_of a) va; iobj src ip] _
            [istreamA gv Tsh vd (il_z l) Vundef (Some (il_L l)); oobj u (il_out l);
             data_at Tsh t_p (LS.pos_of a) va; iobj src ip]).
  1-4: perm_solve.
  - unfold accI_w. auto 50 with closed.
  - intros HP. split; [exact HP | ].
    simpl in HP. destruct HP as (SU & _ & _ & _ & _ & _ & Pip & _ & (Hgeo & _) & Hok & _ & Hacc & _).
    pose proof SU as (_ & _ & _ & _ & _ & _ & _ & Pop & _).
    apply acc_small; auto.
Qed.

(* if (at.avail_in == 0 && at.avail_out == 0) gp_assert(code != Z_OK && unmoved(&decompressor, &at)), on code,
   the decompressor, at and the objects input and out; at's contents are dropped *)
Lemma idle_small {Espec : OracleKind} gv vd va u src ip r l a :
  isptr ip -> isptr (su_op u) -> il_geo u src ip l -> LS.posz_ok a ->
  (r = Z_OK \/ r = Z_BUF_ERROR \/ r = Z_STREAM_END \/ r = Z_NEED_DICT) ->
  (LS.pz_avail_in a = 0 -> LS.pz_avail_out a = 0 -> r <> Z_OK /\ zpos (il_z l) = a) ->
  semax Delta_W
    (PROP () LOCAL (temp _code (vi r); lvar _decompressor t_z vd; lvar _at t_p va)
     SEP (istreamA gv Tsh vd (il_z l) Vundef (Some (il_L l)); oobj u (il_out l); data_at Tsh t_p (LS.pos_of a) va;
          iobj src ip))
    idleI_w
    (normal_ret_assert
    (PROP () LOCAL (temp _code (vi r); lvar _decompressor t_z vd; lvar _at t_p va)
     SEP (istreamA gv Tsh vd (il_z l) Vundef (Some (il_L l)); oobj u (il_out l); data_at_ Tsh t_p va;
          iobj src ip))).
Proof.
  intros Pip Pop Hgeo Hok Hr Hidle.
  unfold Delta_W; simplify_func_tycontext. unfold idleI_w.
  destruct a as [ani aai ati ano aao ato]. cbn [LS.pz_avail_in LS.pz_avail_out] in Hidle.
  replace_SEP 2 (data_at Tsh t_p ((ani, (Vint (Int.repr aai), (ano, (Vint (Int.repr aao),
    (Vlong (Int64.repr ati), Vlong (Int64.repr ato)))))) : reptype t_p) va).
  { entailer!. }
  pose proof Hok as (_ & _ & Hai & _ & Hao & _). cbn [LS.pz_avail_in LS.pz_avail_out] in Hai, Hao.
  pose proof Hgeo as (Hpos & (rest & Erest) & Eni & Eno).
  assert (Hout : Zlength (il_out l) <= Zlength (su_data u))
    by (rewrite Erest, Zlength_app; pose proof (Zlength_nonneg rest); lia).
  forward.
  destruct (Z.eq_dec aai 0) as [Ei | Ei]; [destruct (Z.eq_dec aao 0) as [Eo | Eo] | ].
  - (* neither input nor output space: not Z_OK, and the stream did not move *)
    subst aai aao. destruct (Hidle eq_refl eq_refl) as (Hr0 & Ea).
    pose proof (f_equal LS.pz_next_in Ea) as Eni'. pose proof (f_equal LS.pz_next_out Ea) as Eno'.
    cbn [zpos LS.pz_next_in LS.pz_next_out] in Eni', Eno'.
    set (a' := LS.mk_posz ani 0 ati ano 0 ato) in *.
    forward_if (temp _t'81 (Vint (Int.repr 1))).
    { forward. forward. entailer!. }
    { exfalso. auto. }
    forward_if.
    2: { exfalso. match goal with H : Int.repr 1 = Int.zero |- _ => discriminate H end. }
    replace_SEP 2 (@data_at LS.CS_session Tsh LS.t_pos (LS.pos_of a') va).
    { entailer!. rewrite <- at_pos_cs. apply derives_refl. }
    rewrite istreamA_session. Intros. rewrite Ea.
    assert (Hcmp : oobj u (il_out l) * iobj src ip |-- LS.unmoved_cmp a' a').
    { unfold LS.unmoved_cmp. cbn [a' LS.pz_next_in LS.pz_next_out].
      rewrite <- Eni', <- Eno', Eni, Eno. apply objs_cmp_w; auto. pose proof (Zlength_nonneg (il_out l)); lia. }
    sep_apply (Zlib.proof.harness.laws_session.Facts.lend_cmp _ _ Hcmp).
    assert (Hb : LS.unmoved_b a' a' = true) by (apply Zlib.proof.harness.laws_session.Facts.unmoved_b_iff; auto).
    forward_if (temp _t'79 (Vint (Int.repr 1))).
    + forward_call (vd, Tsh, a', zrest gv (il_z l) (adler_v (raw_live (Some (il_L l))) (il_z l) Vundef)
                      (l_sp (il_L l)), va, Tsh, a', oobj u (il_out l) * iobj src ip).
      rewrite Hb. Intros. forward. entailer!. apply (Zlib.proof.harness.laws_session.Facts.lend_cmp _ _ Hcmp).
    + exfalso. apply Hr0.
      destruct Hr as [E|[E|[E|E]]]; subst r; auto; infeas.
    + forward_call (Int.repr 1).
      rewrite istreamA_session, <- Ea.
      assert (Hdrop : (oobj u (il_out l) * iobj src ip) && LS.unmoved_cmp (zpos (il_z l)) (zpos (il_z l))
                      |-- oobj u (il_out l) * iobj src ip) by (apply andp_left1, derives_refl).
      sep_apply Hdrop.
      sep_apply (@data_at_data_at_ LS.CS_session Tsh LS.t_pos (LS.pos_of (zpos (il_z l))) va).
      rewrite <- at_cs.
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

Lemma idle_w_ok {Espec : OracleKind} P PN gv vh vg vc va vd u O c src ip r l a :
  semax Delta_W (ICr_w gv vh vg vc va vd P PN u O c src ip r l a) idleI_w
    (normal_ret_assert (ICd_w gv vh vg vc va vd P PN u O c src ip r l)).
Proof.
  unfold ICr_w, ICd_w, iw_props, iw_locals, iw_rest, c_locals, d_locals, lvs, lv_locals. simpl app.
  eapply (semax_frame_perm _ _ _ _ [temp _code (vi r); lvar _decompressor t_z vd; lvar _at t_p va] _
            [temp _code (vi r); lvar _decompressor t_z vd; lvar _at t_p va] _ _
            [istreamA gv Tsh vd (il_z l) Vundef (Some (il_L l)); oobj u (il_out l);
             data_at Tsh t_p (LS.pos_of a) va; iobj src ip] _
            [istreamA gv Tsh vd (il_z l) Vundef (Some (il_L l)); oobj u (il_out l); data_at_ Tsh t_p va;
             iobj src ip]).
  1-4: perm_solve.
  - unfold idleI_w. auto 50 with closed.
  - intros HP. simpl in HP.
    destruct HP as (SU & Hh & Hsc & Hcap & Hrb & Hsrc & Pip & Hr & Hcf & Hok & Hidle & Hacc & _).
    split; [simpl; tauto | ].
    pose proof SU as (_ & _ & _ & _ & _ & _ & _ & Pop & _).
    apply idle_small; auto. apply Hcf.
Qed.

Lemma tests_w_ok {Espec : OracleKind} P PN gv vh vg vc va vd u O c src ip r l a :
  semax Delta_W (ICr_w gv vh vg vc va vd P PN u O c src ip r l a)
    (Ssequence (Ssequence codesI_w accI_w) idleI_w)
    (normal_ret_assert (ICd_w gv vh vg vc va vd P PN u O c src ip r l)).
Proof.
  eapply semax_seq'; [ | apply idle_w_ok].
  eapply semax_seq'; [apply codes_w_ok | apply acc_w_ok].
Qed.
