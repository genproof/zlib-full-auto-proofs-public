(* The machine invariant of the allocator-generic port is InvW's wide invariant: Inv.mwf_za (generated, the
   bounds raised to 2^32 - 1) has the fields of InvW.mwfW, and Inv3.mwf3_za = mwf_za /\ swf3 /\ InvW.hdrW is
   InvW.mwf3W.  So one pass of the switch keeps mwf3_za (Stmt.za_step_stmt) by InvW.stepf2_mwf3W_stmt. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.za.inflate_api.Stmt.
Require Import Zlib.proof.inflate.InvW.

Lemma mwf_za_mwfW : forall m, mwf_za m <-> mwfW m.
Proof.
  intros m; split; intros W; destruct W; constructor; assumption.
Qed.

Lemma mwf3_za_mwf3W : forall m, mwf3_za m <-> mwf3W m.
Proof.
  intros m. unfold mwf3_za, mwf3W. rewrite mwf_za_mwfW. tauto.
Qed.

Lemma za_step_proof : za_step_stmt.
Proof.
  intros H flush m W L. apply mwf3_za_mwf3W in W.
  specialize (H flush m W L).
  destruct (stepf2 flush lenfix_list distfix_list m); apply mwf3_za_mwf3W; exact H.
Qed.
