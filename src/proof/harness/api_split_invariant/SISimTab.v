(* The simulation of the dynamic block header (TABLE, LENLENS, CODELENS; CODELENS goes on into LEN_). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_split_invariant.SIDefs.
Require Import Zlib.proof.harness.api_split_invariant.SISimTabKit.
Require Import Zlib.proof.harness.api_split_invariant.SISimTabCLCase.
Require Import Zlib.proof.harness.api_split_invariant.SISimTabLL.
Require Import Zlib.proof.harness.api_split_invariant.SISimTabT.
Import ListNotations.
Local Open Scope Z_scope.

(* sim_ok from the outcome of stepf2 (SISimTabKit.sit_out), stated over an arbitrary machine so that
   the kernel compares the two forms without reducing a concrete case *)
Lemma sit_sim_ok_of (P: Z -> Prop) :
  (forall flush src P0 O0 m a, rel src P0 O0 m a -> awf src a -> m_leave m = 0 -> P (m_mode m) ->
     sit_out flush src P0 O0 (P0 + Zlength (m_inp m)) (Zlength O0 + m_aout m) a
       (stepf2 flush lenfix_list distfix_list m)) ->
  sim_ok P.
Proof. intros H flush src P0 O0 m a R W L M. exact (H flush src P0 O0 m a R W L M). Qed.

(* one pass of the switch from TABLE, LENLENS or CODELENS: SISimTabT.v, SISimTabLL.v, SISimTabCLCase.v *)
Lemma si_tab : tab_sim_stmt.
Proof.
  intros K AW DEC. apply sit_sim_ok_of. intros flush src P0 O0 m a R W L Hmd.
  destruct Hmd as [E|[E|E]].
  - rewrite (sit_c_TABLE flush m E). exact (sit_tab_case src P0 O0 K AW DEC flush m a R W L E).
  - rewrite (sit_c_LENLENS flush m E). exact (sit_ll_case src P0 O0 K AW DEC flush m a R W L E).
  - rewrite (sit_c_CODELENS flush m E). exact (sit_cl_case src P0 O0 K AW DEC flush m a R W L E).
Qed.
