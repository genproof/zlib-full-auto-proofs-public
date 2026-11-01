(* Law api_deflate_any: the check of 4.1 after deflate (AnyCheck.any_check):
     if (out_size == 0 && !bad_flush) gp_assert(code == Z_BUF_ERROR && unmoved(&strm, &at));
   A call offered no output space with a valid flush returned Z_BUF_ERROR and moved nothing (dr_ok's clause from
   AnyCodes.deflate_no_room), so the stream's position is the one position_of recorded in [at] before the call
   (D_sep's [pos_of (c_pos ...)]) and unmoved returns 1 (laws_session/Facts.unmoved_b_iff).  The stream is lent to
   unmoved as one z_stream (AnyAt.any_strm_lend), with the piece and the output space as the memory in which the
   compared pointers are defined (AnyAt.any_cmp_self).  The check changes no memory: D_at again. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Rep.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.harness.api_deflate_any.AnyFacts.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.laws_session.Spec.
Require Zlib.proof.harness.laws_session.Facts.
Require Zlib.proof.harness.api_deterministic.DetKit2.
Require Import Zlib.proof.harness.api_deflate_any.AnyCS.
Require Import Zlib.proof.harness.api_deflate_any.AnyMainStmt.
Require Import Zlib.proof.harness.api_deflate_any.AnyKit.
Require Import Zlib.proof.harness.api_deflate_any.AnyAt.
Require Import Zlib.harness.api_deflate_any.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

Lemma any_check_unmoved : any_check_unmoved_stmt.
Proof.
  intros Espec J n data datap v sp gv ap ls ci c d HK.
  unfold lsuf16.
  match goal with |- semax _ _ (Ssequence ?a ?rest) _ => change rest with lsuf17 end.
  unfold Dq_at, D_at, D_sep, B_loc, Rbody, POST_m, Delta_m, Gmain in *. simplify_func_tycontext.
  abbreviate_semax. Intros.
  rewrite <- seq_assoc.
  pose proof H0 as (_ & _ & _ & _ & Hroom & _).
  forward_if (temp _t'38 (Val.of_bool ((ci_room ci =? 0) && negb (bad_b (ci_flush ci))))).
  { assert (E : ci_room ci = 0)
      by (apply (f_equal Int64.unsigned) in H3; rewrite Int64.unsigned_repr in H3 by rep_lia; exact H3).
    forward. rewrite E. entailer!. destruct (bad_b (ci_flush ci)); reflexivity. }
  { assert (E : ci_room ci <> 0) by (intro E; apply H3; rewrite E; reflexivity).
    forward. entailer!. rewrite (proj2 (Z.eqb_neq _ _) E). reflexivity. }
  destruct ((ci_room ci =? 0) && negb (bad_b (ci_flush ci)))%bool eqn:Eb.
  (* output space or an invalid flush: no check *)
  2: { forward_if True.
       { exfalso. simpl in *. contradiction. }
       { forward. entailer!. }
       eapply semax_pre; [ | exact HK ]. entailer!. }
  (* no output space and a valid flush: dr_ok's no-room clause, nothing moved, so the stream's position is [P] *)
  apply andb_prop in Eb as [Er Ef]. apply Z.eqb_eq in Er.
  assert (Hfl : 0 <= ci_flush ci <= 5)
    by (unfold bad_b in Ef; destruct (ci_flush ci <? 0) eqn:E1, (5 <? ci_flush ci) eqn:E2; try discriminate;
        apply Z.ltb_ge in E1; apply Z.ltb_ge in E2; lia).
  pose proof H2 as (_ & _ & _ & _ & _ & _ & Hnr & _).
  destruct (Hnr Er Hfl) as (Ecode & Enin & Eain & Etin & Eout & Eaout & Etout).
  pose proof H1 as (_ & Hnin & Hout & _ & _ & Htout & _).
  assert (Eo : cs_out c = [])
    by (rewrite Er in Hout; destruct (cs_out c) as [ | b l]; [reflexivity | ];
        rewrite Zlength_cons in Hout; pose proof (Zlength_nonneg l); lia).
  rewrite Ecode, Enin, Eain, Etin, Eout, Eaout, Etout, Eo in HK |- *.
  change ([] ++ []) with (@nil Z) in HK |- *. rewrite Zlength_nil in HK |- *.
  set (P := c_pos ls ci c) in HK |- *.
  assert (EP : P = AnyAt.sposz (offset_val (cs_nin c) (ci_piece ci)) (ci_take ci - cs_nin c)
                     (ls_read ls + cs_nin c) (offset_val 0 (ci_out ci)) 0 (cs_tout c))
    by (subst P; unfold c_pos, AnyAt.sposz; rewrite Eo, Er; reflexivity).
  assert (Hinb : Zlength (ci_inb data ls ci) = ci_take ci).
  { pose proof H as ((_ & _ & Hlen & _) & _ & Hread & _). pose proof H0 as (Htake & Hle & _).
    unfold ci_inb. rewrite Zlength_sublist by lia. lia. }
  forward_if True.
  2: { exfalso. simpl in *. discriminate. }
  (* code == Z_BUF_ERROR, then unmoved(&strm, &at) on the stream lent as one z_stream *)
  forward_if (temp _t'36 (vi 1)).
  2: { exfalso. simpl in *. contradiction. }
  { sep_apply (AnyAt.any_strm_lend v (dr_s d) sp (offset_val (cs_nin c) (ci_piece ci)) (ci_take ci - cs_nin c)
      (ls_read ls + cs_nin c) (offset_val 0 (ci_out ci)) 0 (cs_tout c) (dr_msgv d) (z_adler (dr_z d)) gv).
    Intros r. rewrite <- EP.
    rewrite Er.
    sep_apply (Facts.lend_cmp (BoundKit.obj (ci_piece ci) (ci_inb data ls ci) *
                               AnyKit.DK.out_at (ci_out ci) 0 (map vi (ovals (ci_bs ci) [])))
                 (LS.unmoved_cmp P P)).
    { rewrite EP. unfold LS.unmoved_cmp. simpl. apply AnyAt.any_cmp_self. lia. }
    forward_call (v, Ews, P, r, ap, Tsh, P,
      BoundKit.obj (ci_piece ci) (ci_inb data ls ci) * AnyKit.DK.out_at (ci_out ci) 0 (map vi (ovals (ci_bs ci) []))).
    { assert (LS.posz_ok P).
      { pose proof H as ((_ & Hn & Hlen & _) & _ & Hread & _).
        pose proof H0 as (Htake & Hle & _ & _ & _ & _ & _ & Hp & Ho & _).
        unfold u64r in Htout.
        rewrite EP. unfold LS.posz_ok, AnyAt.sposz; simpl.
        destruct (ci_piece ci), (ci_out ci); try contradiction; simpl; repeat split; auto; rep_lia. }
      split; assumption. }
    rewrite (proj2 (Facts.unmoved_b_iff P P) eq_refl).
    sep_apply (modus_ponens_wand (data_at Ews t_zs (LS.zs_of P r) v)).
    Intros. forward.
    clear HK. rewrite Er. entailer!. }
  forward_call (Int.repr 1).
  { entailer!. }
  eapply semax_pre; [ | exact HK ]. entailer!.
Qed.
