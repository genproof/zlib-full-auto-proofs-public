(* Law rt_session: the assembly of the law from main's body, the globals, the model facts of both sides and the
   shared bodies of the functions main reaches (deflate.c's against DSpec9 / DSpec / DSpecV, inflate.c's against
   Spec5, SpecW, RTH8Spec and RTH9Spec: inflate's entry is the intersection SMainStmt.inflate_spec_ses, from the two
   bodies by semax_body_binaryintersection), the laws_common.h and laws_session.h helpers' bodies, any_string's and
   same_field's bodies on this program, and the environment. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.laws_session.Spec.
Require Zlib.contracts.rt_session.
Require Zlib.proof.harness.rt_session.SDFacts.
Require Zlib.proof.harness.rt_session.SIFacts.
Require Import Zlib.proof.harness.rt_session.SMainStmt.

Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.MainCoreCfg.
Require Zlib.proof.deflate.GlobalsFixed.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SAsmG.
Require Zlib.proof.harness.rt_session.SHelpers.
Require Zlib.proof.harness.rt_session.SAsmE1.
Require Zlib.proof.harness.rt_session.SAsmE2.
Require Zlib.harness.rt_session.code.
#[local] Existing Instance Zlib.proof.harness.rt_session.SCS.CS.

(* main's body (for the invariants of the model facts), the helpers of laws_common.h, of the harness and of
   laws_session.h *)
Lemma ses_entries_main :
  laws_common_ok -> Zlib.proof.harness.laws_session.Spec.laws_session_ok ->
  Zlib.proof.harness.rt_session.SDFacts.ses_dtheory_stmt -> Zlib.proof.harness.rt_session.SIFacts.ses_itheory_stmt ->
  ses_main_stmt -> ses_globals_stmt -> entries G_main.
Proof.
  intros (B_upto & B_clip & B_any & B_copy & B_eq & B_offer & B_new) (S_params & _ & S_pos & S_unmoved & S_acc & _)
    [J DF] [P [PN IF]] MB GL.
  assert (BM : semax_body (QPvarspecs p) Gmain Zlib.harness.rt_session.code.f_main
                 (Zlib.harness.rt_session.code._main, QPmain_spec_ext' p tt main_post_TT)).
  { eapply (semax_body_main_core_cfg _ _ p Zlib.proof.deflate.GlobalsFixed.cfg_funs _ _ Rm).
    - exact GL.
    - exact (MB J P PN DF IF).
    - vm_compute; reflexivity. }
  unfold entries, G_main.
  ses_entry BM.
  ses_entry B_upto. ses_entry B_clip. ses_entry B_any. ses_entry B_copy. ses_entry B_eq.
  ses_entry B_offer. ses_entry B_new.
  ses_entry Zlib.proof.harness.rt_session.SHelpers.ses_body_any_string.
  ses_entry Zlib.proof.harness.rt_session.SHelpers.ses_body_same_field.
  ses_entry S_params. ses_entry S_pos. ses_entry S_unmoved. ses_entry S_acc.
  apply Forall_nil.
Qed.

(* the environment *)
Lemma ses_entries_env : entries G_env.
Proof.
  unfold entries, G_env.
  entry_external (@external_ok_malloc CS).
  entry_external (@external_ok_free CS).
  entry_external (@external_ok_size CS).
  entry_external (@external_ok_bytes CS).
  entry_external (@external_ok_u8 CS).
  entry_external (@external_ok_u32 CS).
  entry_external (@external_ok_assert CS).
  entry_external (@external_ok_assume CS).
  apply Forall_nil.
Qed.

Theorem ses_asm :
  laws_common_ok -> Zlib.proof.harness.laws_session.Spec.laws_session_ok ->
  Zlib.proof.harness.rt_session.SDFacts.ses_dtheory_stmt -> Zlib.proof.harness.rt_session.SIFacts.ses_itheory_stmt ->
  ses_main_stmt -> ses_globals_stmt -> harness_safe Zlib.contracts.rt_session.whole_prog.
Proof.
  intros LC LS DT IT MB GL.
  pose proof (ses_entries_main LC LS DT IT MB GL) as E_main.
  change Zlib.contracts.rt_session.whole_prog with p.
  harness_safe_by_specs CS G main_post_TT.
  - reflexivity.
  - change (entries (G_main ++ G_trees ++ G_defl ++ G_infl ++ G_env)).
    unfold entries.
    apply Forall_app; split; [exact E_main | ].
    apply Forall_app; split; [exact Zlib.proof.harness.rt_session.SAsmE1.ses_entries_trees | ].
    apply Forall_app; split; [exact Zlib.proof.harness.rt_session.SAsmE1.ses_entries_defl | ].
    apply Forall_app; split; [exact Zlib.proof.harness.rt_session.SAsmE2.ses_entries_infl | ].
    exact ses_entries_env.
Qed.
