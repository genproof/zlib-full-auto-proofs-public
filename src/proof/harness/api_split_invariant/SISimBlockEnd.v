(* The simulation of the modes DONE and BAD: inflate() leaves with Z_STREAM_END or Z_DATA_ERROR, as the
   abstract machine ends. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_split_invariant.SIDefs.
Require Import Zlib.proof.harness.api_split_invariant.SISimBlockKit.
Import ListNotations.
Local Open Scope Z_scope.

Lemma sib_DONE : sib_case DONE.
Proof.
  intros flush src P0 O0 m a R W L M. rewrite sib_c_DONE by exact M. unfold c_DONE.
  apply sib_out_stay.
  - apply sib_rel_leave, sib_rel_ret; [exact R|]. intros _ X. contradiction.
  - intros _. unfold stop_ok. rewrite sib_a_DONE by (rewrite <- (rl_mode _ _ _ _ _ R); exact M).
    sib_cbn. auto.
Qed.

Lemma sib_BAD : sib_case BAD.
Proof.
  intros flush src P0 O0 m a R W L M. rewrite sib_c_BAD by exact M. unfold c_BAD.
  apply sib_out_stay.
  - apply sib_rel_leave, sib_rel_ret; [exact R|]. intros X. contradiction.
  - intros _. unfold stop_ok. rewrite sib_a_BAD by (rewrite <- (rl_mode _ _ _ _ _ R); exact M).
    sib_cbn. auto.
Qed.
