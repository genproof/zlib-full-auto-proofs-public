(* Law api_reset, the theory: one pass of the switch on two related machines, for every mode (each mode is in
   one of IRDefs.v's groups: IRRunLoop.irl_mode_groups), under the wide machine invariant. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_reset.ARSimDefs.
Require Import Zlib.proof.harness.inflate_reset.IRRunLoop.
Require Import Zlib.proof.harness.api_reset.ARSimEasy Zlib.proof.harness.api_reset.ARSimTab.
Import ListNotations.
Local Open Scope Z_scope.

Lemma ar_step : sgroup_okW (fun _ => True).
Proof.
  destruct ar_sim_easy as (HE & HD & DI & BL & FA & DE).
  pose proof (DE FA) as DE'. pose proof (ar_tab_sim DE') as TA.
  intros W0 wrap src pos inp aout flush ma mb C K Wa Wb L _.
  pose proof (sw_mode _ (mwW_s _ (proj1 Wb))) as R.
  destruct (irl_mode_groups (m_mode mb) R) as [G|[G|[G|[G|[G|G]]]]].
  - apply HE; auto.
  - apply HD; auto.
  - apply DI; auto.
  - apply BL; auto.
  - apply DE'; auto.
  - apply TA; auto.
Qed.

