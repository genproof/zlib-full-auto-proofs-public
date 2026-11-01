(* Law rt_session (harness/rt_session.c), main's deflate loop (SMKit.loopD), as rt_stream_trailing's TLoopDPosOf.v:
   position_of(&compressor, &at) right before the deflate() call, from DC_s to DP_s (SMLDKit.posD_s_stmt).  The
   compressor is lent to position_of as one z_stream (SMLDLib.cstream_lend_s) and comes back unchanged; at then
   holds its six members. *)
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

Lemma spos_d : posD_s_stmt.
Proof.
  intros Espec J gv vh vg vc va vd u hx Hr l.
  unfold Delta_s. simplify_func_tycontext.
  unfold DC_s, posD_s.
  Intros.
  (* next_in and next_out point into data and compressed: the six members are well typed *)
  assert (Hpz : is_pointer_or_null (cs_ni (dl_c l)) /\ is_pointer_or_null (cs_no (dl_c l))).
  { destruct H0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hni & Hno).
    destruct H as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                    & _ & Hd) & _ & _ & _ & _ & _ & Hc & _).
    rewrite Hni, Hno. destruct (su_dp u); try contradiction; destruct (su_cp u); try contradiction; simpl; auto. }
  destruct Hpz as [Hpi Hpo].
  assert_PROP (LS.posz_ok (cpos_s (dl_c l))).
  { go_lowerx. sep_apply (cstream_posz_ok_s gv vc (ghp vh u) (dl_c l) Hpi Hpo). Intros. apply prop_right. auto. }
  (* the compressor is lent to position_of as one z_stream; at is taken at laws_session's compspecs *)
  replace_SEP 0 (EX r : LS.zs_rest, @data_at LS.CS_session Ews t_zs (LS.zs_of (cpos_s (dl_c l)) r) vc *
                   (@data_at LS.CS_session Ews t_zs (LS.zs_of (cpos_s (dl_c l)) r) vc -*
                    cstream gv vc (ghp vh u) (dl_c l))).
  { go_lowerx. rewrite sepcon_emp. apply cstream_lend_s. }
  Intros r. rewrite at_cs_s.
  unfold c_locals, d_locals, lvs, lv_locals; simpl app.
  forward_call (vc, Ews, cpos_s (dl_c l), r, va, Tsh).
  (* the wand gives the compressor back *)
  unfold POST_s. simpl RA_normal. unfold DP_s, c_locals, d_locals, lvs, lv_locals; simpl app.
  entailer!.
  sep_apply (modus_ponens_wand (@data_at LS.CS_session Ews t_zs (LS.zs_of (cpos_s (dl_c l)) r) vc)
               (cstream gv vc (ghp vh u) (dl_c l))).
  cancel.
Qed.
