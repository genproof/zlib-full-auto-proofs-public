(* Law rt_stream_trailing (harness/rt_stream_trailing.c), main's deflate loop (TMainKit.loopD_t), ported from rt_stream's
   rt_stream/ULoopDPosOf.v: position_of(&compressor, &at) right before the deflate() call, from DC_t to DP_t
   (TLoopDKit.posD_t_stmt).  The compressor is lent to position_of as one z_stream (ULoopDPos.cstream_lend) and
   comes back unchanged; at then holds its six members. *)
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
Require Zlib.proof.harness.rt_stream.ULoopDKit.
Require Import Zlib.proof.harness.rt_stream.ULoopDLib.
Require Zlib.deflate.code.
Require Zlib.proof.harness.laws_session.Spec.
Require Import Zlib.proof.harness.rt_stream.ULoopDPos.
Require Import Zlib.proof.harness.rt_stream_trailing.TMainStmt.
Require Import Zlib.proof.harness.rt_stream_trailing.TMainKit.
Require Import Zlib.proof.harness.rt_stream_trailing.TLoopDKit.
Require Import Zlib.harness.rt_stream_trailing.code.
#[local] Existing Instance LawCS.CS.
Local Open Scope logic.

Module DC := Zlib.deflate.code.
Module LS := Zlib.proof.harness.laws_session.Spec.

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

Lemma tpos_d : posD_t_stmt.
Proof.
  intros Espec J gv vc vd va u l.
  unfold Delta_t. simplify_func_tycontext.
  unfold DC_t, posD_t.
  Intros.
  (* next_in and next_out point into data and compressed: the six members are well typed *)
  assert (Hpz : is_pointer_or_null (cs_ni (dl_c l)) /\ is_pointer_or_null (cs_no (dl_c l))).
  { destruct H1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hni & Hno).
    destruct H as (_ & _ & _ & _ & _ & _ & _ & Hd & Hc & _).
    rewrite Hni, Hno. destruct (su_dp u); try contradiction; destruct (su_cp u); try contradiction; simpl; auto. }
  destruct Hpz as [Hpi Hpo].
  assert_PROP (LS.posz_ok (cpos (dl_c l))).
  { go_lowerx. sep_apply (cstream_posz_ok gv vc (dl_c l) Hpi Hpo). Intros. apply prop_right. auto. }
  (* the compressor is lent to position_of as one z_stream; at is taken at laws_session's compspecs *)
  replace_SEP 0 (EX r : LS.zs_rest, @data_at LS.CS_session Ews t_zs (LS.zs_of (cpos (dl_c l)) r) vc *
                   (@data_at LS.CS_session Ews t_zs (LS.zs_of (cpos (dl_c l)) r) vc -* cstream gv vc (dl_c l))).
  { go_lowerx. rewrite sepcon_emp. apply cstream_lend. }
  Intros r. rewrite at_cs.
  unfold su_locals, lv_locals; simpl app.
  forward_call (vc, Ews, cpos (dl_c l), r, va, Tsh).
  (* the wand gives the compressor back *)
  unfold POST_t. simpl RA_normal. unfold DP_t, su_locals, lv_locals; simpl app.
  entailer!.
  sep_apply (modus_ponens_wand (@data_at LS.CS_session Ews t_zs (LS.zs_of (cpos (dl_c l)) r) vc)
               (cstream gv vc (dl_c l))).
  cancel.
Qed.
