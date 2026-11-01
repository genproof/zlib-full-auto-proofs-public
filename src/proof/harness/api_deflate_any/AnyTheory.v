(* Law api_deflate_any: the model facts of main ([any_theory_stmt], AnyFacts.v), from deflate() on the round
   trips' wide invariant (RTK7Api.api7_deflate_stmt).  The invariant is law api_deterministic's
   (DetTheory2.det_J2, with its facts DetTheory2.det_facts2_J2): [Iapi7] with no dictionary and no gzip header.
   Its phases give the status (INIT, GZIP, BUSY or FINISH; the gzip header phase needs a header), so
   deflateStateCheck passes, and [Iapi7] says that FINISH_STATE comes only after Z_FINISH. *)
From Coq Require Import ZArith.
From Coq Require Import List.
From Coq Require Import Lia.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTK7Api.
Require Import Zlib.proof.deflate.DetTheory2.
Require Import Zlib.proof.harness.api_deflate_any.AnyFacts.
Import ListNotations.
Local Open Scope Z_scope.

Lemma det_J2_live : forall fin s tin adler, det_J2 fin s tin adler ->
  bad_state s = false /\ d_gzhead s = None /\ (fin = None -> d_status s <> FINISH_STATE).
Proof.
  intros fin s tin adler (wrap & D & O & HI' & _ & Hgn & _).
  pose proof HI' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfin & _ & Hph).
  (* the status of each phase; the gzip header phase is excluded, as it needs a gzip header *)
  assert (Hst : d_status s = INIT_STATE \/ d_status s = GZIP_STATE \/ d_status s = BUSY_STATE \/
                d_status s = FINISH_STATE).
  { destruct Hph as [P0 | (_ & [P1 | [P2 | P3]])].
    - destruct P0 as [[[-> _] | [-> _]] _]; tauto.
    - destruct P1 as (_ & _ & _ & _ & _ & H & k & Hh & _).
      destruct Hh as (_ & h & _ & Eh & _). congruence.
    - destruct P2 as [-> _]. tauto.
    - destruct P3 as [-> _]. tauto. }
  split; [|split; [exact Hgn|]].
  - unfold bad_state, c_deflateStateCheck, status_ok.
    destruct Hst as [E|[E|[E|E]]]; rewrite E; reflexivity.
  - intros -> E. specialize (Hfin E). discriminate.
Qed.

Theorem any_theory : api7_deflate_stmt -> any_theory_stmt.
Proof.
  intros AD. exists det_J2. constructor.
  - exact (det_facts2_J2 AD).
  - exact det_J2_live.
Qed.
