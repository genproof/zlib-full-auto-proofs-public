(* Law rt_session (harness/rt_session.c), main's deflate loop (SMKit.loopD), as rt_stream_trailing's TLoopDAcc.v:
   gp_assert(accounted(&compressor, &at)) right after the deflate() call, DA_s kept (SMLDKit.accD_s_stmt).  The
   call accounted for what it moved (DA_s's acc_ok_s), so accounted returns 1 and the assert passes; the
   compressor is lent to accounted as one z_stream and the objects data and compressed as the memory in which it
   compares the pointers. *)
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

(* the memory lent to accounted: with the objects data and compressed, the sums data + ki and compressed + ko are
   comparable with themselves *)
Lemma lend_acc_s (u : setup) (O : list Z) (c : cst) (a : LS.posz) :
  su_ok u -> acc_ok_s u c a ->
  dobj u * cobj u O |-- (dobj u * cobj u O) && LS.accounted_cmp (cpos_s c) a.
Proof.
  intros Hu (_ & _ & _ & _ & _ & ki & ko & Hki & Hko & Eci & Eai & Eco & Eao).
  apply Zlib.proof.harness.laws_session.Facts.lend_cmp.
  unfold LS.accounted_cmp, cpos_s.
  cbn [LS.pz_next_in LS.pz_avail_in LS.pz_total_in LS.pz_next_out LS.pz_avail_out LS.pz_total_out].
  rewrite Eci, Eai, Eco, Eao.
  destruct Hu as (Hd & _ & _ & _ & _ & _ & Pc & _).
  assert (Pd : isptr (su_dp u)) by (unfold su_dok in Hd; repeat match type of Hd with _ /\ _ =>
                                     let h := fresh in destruct Hd as [h Hd] end; exact Hd).
  apply andp_right.
  - eapply derives_trans;
      [ | apply (test_eq_s (eobj u * cobj u O) (su_dp u) ki ki (Zlength (su_data u)) (map vi (su_data u))); auto ].
    unfold dobj, datobj, bobj. cancel.
  - eapply derives_trans;
      [ | apply (test_eq_s (dobj u) (su_cp u) ko ko (su_cap u) (cbytes (su_cap u) O)); auto ].
    unfold cobj. cancel.
Qed.

Lemma sacc_d : accD_s_stmt.
Proof.
  intros Espec J gv vh vg vc va vd u off flush code l a hx Hr.
  unfold Delta_s. simplify_func_tycontext.
  unfold DA_s, accD_s.
  abbreviate_semax.
  Intros.
  match goal with Ha : acc_ok_s _ _ _ |- _ => rename Ha into HA end.
  pose proof HA as (Hb & Pci & Pco & Pai & Pao & _).
  assert_PROP (LS.posz_ok (cpos_s (dl_c l))).
  { go_lowerx. sep_apply (cstream_posz_ok_s gv vc (ghp vh u) (dl_c l) (isptr_is_pointer_or_null _ Pci)
                            (isptr_is_pointer_or_null _ Pco)). Intros. apply prop_right. auto. }
  replace_SEP 0 (EX r : LS.zs_rest, @data_at LS.CS_session Ews t_zs (LS.zs_of (cpos_s (dl_c l)) r) vc *
                   (@data_at LS.CS_session Ews t_zs (LS.zs_of (cpos_s (dl_c l)) r) vc -*
                    cstream gv vc (ghp vh u) (dl_c l))).
  { go_lowerx. rewrite sepcon_emp. apply cstream_lend_s. }
  Intros r.
  gather_SEP 5 6.
  replace_SEP 0 ((dobj u * cobj u (dl_O l)) && LS.accounted_cmp (cpos_s (dl_c l)) a).
  { go_lowerx. rewrite sepcon_emp. apply (lend_acc_s u (dl_O l) (dl_c l) a H HA). }
  unfold c_locals, d_locals, lvs, lv_locals; simpl app.
  forward_call (vc, Ews, cpos_s (dl_c l), r, va, Tsh, a, dobj u * cobj u (dl_O l)).
  (* accounted returned 1: the assert passes; the wand gives the compressor back *)
  rewrite Hb. forward_call (Int.one).
  sep_apply (modus_ponens_wand (@data_at LS.CS_session Ews t_zs (LS.zs_of (cpos_s (dl_c l)) r) vc)
               (cstream gv vc (ghp vh u) (dl_c l))).
  clear Hb. destruct POST_s as [rn rb rc rr]; cbn [RA_normal].
  unfold c_locals, d_locals, lvs, lv_locals; simpl app. entailer!.
Qed.
