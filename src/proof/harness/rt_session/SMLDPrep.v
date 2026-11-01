(* Law rt_session (harness/rt_session.c), main's deflate loop (SMKit.loopD): the third and fourth statements of its body, avail_in = clip(offered - read) and avail_out = clip(any room left in compressed), from DR_s to DC_s (SMLDKit.prepD_s_stmt). *)
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

Lemma sprep_d : prepD_s_stmt.
Proof.
  intros Espec J gv vh vg vc va vd u hx Hr l HC.
  unfold prepD_s, Delta_s; simplify_func_tycontext.
  unfold DR_s. Intros.
  match goal with H: su_ok u |- _ => rename H into SU end.
  match goal with H: dl_ok J u l |- _ => rename H into DL end.
  pose proof DL as (HJ & ED & HDoff & Hfl & Hfin4 & Hfin & HO & BO & Hmsg & Eni & Eno).
  destruct l as [D O fin off flush msg c]. cbn [dl_D dl_O dl_fin dl_off dl_flush dl_msg dl_c] in *.
  destruct c as [s ni ain tin no aout tout msgv adler].
  cbn [cs_s cs_ni cs_ain cs_tin cs_no cs_aout cs_tout cs_msgv cs_adler] in *.
  subst ni no.
  unfold max_size in *.
  assert (HD0 := Zlength_nonneg D). assert (HO0 := Zlength_nonneg O).
  unfold cstream, api_fields. Intros. cbn [cs_s cs_ni cs_ain cs_tin cs_no cs_aout cs_tout cs_msgv cs_adler] in *.
  rewrite avail_in_s, next_out_s, avail_out_s.
  unfold c_locals, d_locals, lvs, lv_locals. simpl app.
  assert (Pdp : isptr (su_dp u)) by (destruct SU as (SD & _); unfold su_dok in SD; tauto).
  assert (Pcp : isptr (su_cp u)) by (destruct SU as (_ & _ & _ & _ & _ & _ & Pcp & _); exact Pcp).
  pose proof SU as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hn & _ & Hcap & _) & _).
  unfold max_size in Hn, Hcap.
  forward_call (off - Zlength D).
  forward.
  forward.
  forward_call (su_cap u - Zlength O).
  all: try solve [ entailer!; first [ apply prop_right, ULoopDLib.ld_sameblock_off; auto
                     | apply ULoopDLib.ld_sameblock_off; auto
                     | unfold vl; rewrite ULoopDLib.ld_ptr_sub by (auto; rep_lia); reflexivity ] ].
  Intros ao.
  forward_call ao.
  forward.
  (* the state before position_of *)
  set (l2 := mkDL D O fin off flush msg
               (mkCS s (offset_val (Zlength D) (su_dp u)) (Z.min (off - Zlength D) Int.max_unsigned) tin
                  (offset_val (Zlength O) (su_cp u)) (Z.min ao Int.max_unsigned) tout msgv adler)).
  pose proof (HC l2) as HC1.
  assert (DL2 : dl_ok J u l2) by exact DL.
  unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
  eapply semax_pre; [ | exact HC1 ].
  unfold DC_s, cstream, api_fields, c_locals, d_locals, lvs, lv_locals. simpl app.
  cbn [dl_D dl_O dl_fin dl_off dl_flush dl_msg dl_c cs_s cs_ni cs_ain cs_tin cs_no cs_aout cs_tout cs_msgv
       cs_adler l2].
  rewrite avail_in_s, next_out_s, avail_out_s.
  entailer!. unfold u32_ok; repeat split; rep_lia.
Qed.
