(* Law rt_stream_trailing (harness/rt_stream_trailing.c), main's deflate loop (TMainKit.loopD_t): the assert right
   after the deflate() call, `gp_assert(accounted(&compressor, &at))`, from DA_t to DA_t (TLoopDKit.accD_t_stmt).
   The call accounted for what it moved (DA_t's acc_ok, from the call's run: TLoopDCall), so accounted returns 1.
   Its pointer comparisons compare next_in + avail_in (data + ki) and next_out + avail_out (compressed + ko) with
   themselves, defined in the memory of the objects data and compressed, lent to accounted (Facts.lend_cmp); the
   compressor is lent as one z_stream (ULoopDPos.cstream_lend) and comes back unchanged. *)
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
Require Zlib.proof.harness.laws_session.Facts.
Require Import Zlib.proof.harness.rt_stream.ULoopDPos.
Require Import Zlib.proof.harness.rt_stream_trailing.TMainStmt.
Require Import Zlib.proof.harness.rt_stream_trailing.TMainKit.
Require Import Zlib.proof.harness.rt_stream_trailing.TLoopDKit.
Require Import Zlib.harness.rt_stream_trailing.code.
#[local] Existing Instance LawCS.CS.
Local Open Scope logic.

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

(* the memory lent to accounted: with the objects data and compressed, the sums data + ki and compressed + ko are
   comparable with themselves *)
Lemma lend_acc (u : setup) (O : list Z) (c : cst) (a : LS.posz) :
  su_ok u -> acc_ok u c a ->
  dobj u * cobj u O |-- (dobj u * cobj u O) && LS.accounted_cmp (cpos c) a.
Proof.
  intros Hu (_ & _ & _ & _ & _ & ki & ko & Hki & Hko & Eci & Eai & Eco & Eao).
  apply Zlib.proof.harness.laws_session.Facts.lend_cmp.
  unfold LS.accounted_cmp, Zlib.proof.harness.rt_stream.ULoopDKit.cpos.
  cbn [LS.pz_next_in LS.pz_avail_in LS.pz_total_in LS.pz_next_out LS.pz_avail_out LS.pz_total_out].
  rewrite Eci, Eai, Eco, Eao.
  destruct Hu as (_ & _ & _ & _ & _ & _ & _ & Pd & Pc & _).
  apply andp_right.
  - unfold dobj. rewrite sepcon_assoc. apply ld_test_eq; auto.
  - unfold cobj. rewrite sepcon_comm. apply ld_test_eq; auto.
Qed.

Lemma tacc_d : accD_t_stmt.
Proof.
  intros Espec J gv vc vd va u off flush code l a.
  unfold Delta_t. simplify_func_tycontext.
  unfold DA_t, accD_t.
  abbreviate_semax.
  Intros.
  match goal with Ha : acc_ok _ _ _ |- _ => rename Ha into HA end.
  pose proof HA as (Hb & Pci & Pco & Pai & Pao & _).
  assert_PROP (LS.posz_ok (cpos (dl_c l))).
  { go_lowerx. sep_apply (cstream_posz_ok gv vc (dl_c l) (isptr_is_pointer_or_null _ Pci)
                            (isptr_is_pointer_or_null _ Pco)). Intros. apply prop_right. auto. }
  replace_SEP 0 (EX r : LS.zs_rest, @data_at LS.CS_session Ews t_zs (LS.zs_of (cpos (dl_c l)) r) vc *
                   (@data_at LS.CS_session Ews t_zs (LS.zs_of (cpos (dl_c l)) r) vc -* cstream gv vc (dl_c l))).
  { go_lowerx. rewrite sepcon_emp. apply cstream_lend. }
  Intros r.
  gather_SEP 5 6.
  replace_SEP 0 ((dobj u * cobj u (dl_O l)) && LS.accounted_cmp (cpos (dl_c l)) a).
  { go_lowerx. rewrite sepcon_emp. apply (lend_acc u (dl_O l) (dl_c l) a H HA). }
  unfold su_locals, lv_locals; simpl app.
  forward_call (vc, Ews, cpos (dl_c l), r, va, Tsh, a, dobj u * cobj u (dl_O l)).
  (* accounted returned 1: the assert passes; the wand gives the compressor back *)
  rewrite Hb. forward_call (Int.one).
  sep_apply (modus_ponens_wand (@data_at LS.CS_session Ews t_zs (LS.zs_of (cpos (dl_c l)) r) vc)
               (cstream gv vc (dl_c l))).
  clear Hb. destruct POST_t as [rn rb rc rr]; cbn [RA_normal].
  unfold su_locals, lv_locals; simpl app. entailer!.
Qed.
