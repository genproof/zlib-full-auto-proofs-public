(* Law api_deterministic (data of any length): the last check of an iteration (DetCheck2.det_check),
   gp_assert(bytes_eq(out_first, out_second, room - first.avail_out)): both output spaces hold the same bytes.
   The check reads but does not change the memory, so the assertion after it is D_at again. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Rep.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.deflate.DetFacts2.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.api_deterministic.DetCS2.
Require Import Zlib.proof.harness.api_deterministic.DetMainStmt2.
Require Import Zlib.proof.harness.api_deterministic.DetKit2.
Require Import Zlib.proof.harness.api_deterministic.DetCheck2b.
Require Import Zlib.harness.api_deterministic.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

(* the loop body from its statement 16 on (read, the frees) *)
Definition lsuf16 : statement := ltac:(get_lsuf 16%nat).

Lemma det_check_bytes {Espec : OracleKind} J n data datap v1 v2 sp1 sp2 gv ls ci c d :
  semax Delta_m (D_at J n data datap v1 v2 sp1 sp2 gv ls ci c d) lsuf16 (Rbody J n data datap v1 v2 sp1 sp2 gv) ->
  semax Delta_m (D_at J n data datap v1 v2 sp1 sp2 gv ls ci c d) lsuf15
    (Rbody J n data datap v1 v2 sp1 sp2 gv).
Proof.
  intros HK.
  unfold lsuf15.
  eapply semax_seq' with (P' := D_at J n data datap v1 v2 sp1 sp2 gv ls ci c d); [ | exact HK ].
  clear HK.
  unfold D_at, D_sep, B_loc, Rbody, POST_m, Delta_m, Gmain. simplify_func_tycontext.
  abbreviate_semax. Intros.
  unfold strm_at, api_fields. Intros.
  pose proof H0 as (_ & _ & _ & _ & Hroom & _ & _ & Po1 & Po2).
  pose proof H1 as (_ & _ & _ & Hcout & Hcb & _).
  pose proof H2 as (_ & Hok & _).
  pose proof Hok as (_ & _ & _ & _ & Hao & Hzo & _ & Hzb).
  assert (Hol : Zlength (cs_out c ++ z_out (dr_z d)) = ci_room ci - z_avail_out (dr_z d))
    by (rewrite Zlength_app; lia).
  rewrite Hol.
  forward.
  set (o := cs_out c ++ z_out (dr_z d)) in *.
  assert (Hob : bytes o) by (apply Forall_app; auto).
  assert (CB : forall q, isptr q ->
            cbuf_ok false q Ews q 0 (ci_room ci) (ci_room ci - z_avail_out (dr_z d)) (out_vals (ci_room ci) o) o).
  { intros q Pq. unfold cbuf_ok. rewrite isptr_offset_val_zero by auto. split3; [ reflexivity | auto with share | ].
    split3; [ lia | lia | ]. split3; [ lia | | ].
    { unfold is_bytes. eapply Forall_impl; [ | exact Hob ]. intros b Hb. simpl. rep_lia. }
    pose proof (Zlength_nonneg o). unfold out_vals. rewrite <- Hol, Z.add_0_l.
    rewrite sublist_app1 by (rewrite ?Zlength_map; lia).
    rewrite sublist_same by (rewrite ?Zlength_map; lia). reflexivity. }
  unfold out_at.
  rewrite <- (det_bytes_cs Ews (ci_room ci) _ (ci_out1 ci)).
  rewrite <- (det_bytes_cs Ews (ci_room ci) _ (ci_out2 ci)).
  forward_call (ci_out1 ci, Ews, ci_out1 ci, 0, ci_room ci, out_vals (ci_room ci) o, o,
                ci_out2 ci, Ews, ci_out2 ci, 0, ci_room ci, out_vals (ci_room ci) o, o,
                ci_room ci - z_avail_out (dr_z d)).
  { cancel. }
  rewrite (det_bytes_cs Ews (ci_room ci) _ (ci_out1 ci)).
  rewrite (det_bytes_cs Ews (ci_room ci) _ (ci_out2 ci)).
  destruct (list_eq_dec Z.eq_dec o o) as [_ | E]; [ | contradiction ].
  forward_call (Int.repr 1).
  unfold out_at, strm_at, api_fields. rewrite Hol. entailer!.
Qed.
