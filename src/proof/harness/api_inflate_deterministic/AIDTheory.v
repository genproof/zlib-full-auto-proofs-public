(* Law api_inflate_deterministic, the theory: the facts of AIDFacts.v for api_reset's phase-1 invariant
   (ARTheoryDefs.J1: x_inflate_reset's relation IRinv of two streams, with the windowBits w they were made
   with).  Two streams just made by inflateInit2_ with the same w have the same internal state (init_live
   depends on the state's address only), so they are related; one call on each keeps the relation and gives the
   same outcome (ARRunCall.ar_call over the simulation ARSimAll.ar_step). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_inflate_deterministic.AIDFacts.
Require Import Zlib.proof.harness.api_reset.ARTheoryDefs.
Require Import Zlib.proof.harness.inflate_reset.IRRunLoop.
Require Import Zlib.proof.harness.api_reset.ARSimAll.
Require Import Zlib.proof.harness.api_reset.ARRunCall.
Require Import Zlib.proof.harness.api_reset.ARReset.
Import ListNotations.
Local Open Scope Z_scope.

Lemma aid_theory : aid_theory_stmt.
Proof.
  pose proof ar_step as ST.
  exists J1. constructor.
  - (* the two inflateInit2_ *)
    intros w src za zb spa spb W _ _ _ _ Ma Mb Ia Ib Oa Ob D A _ _ _. split; [exact W|].
    destruct (ar_init_s spb w W) as (M & H & Ho & Bi).
    constructor;
      [apply irl_srel_refl | reflexivity | exact H | left; reflexivity | left; reflexivity |
       intros _ _; rewrite Ho, Bi; apply ar_hd0 | rewrite M; irl_md | congruence ..].
  - (* the state after inflateInit2_ *)
    intros w sp W. destruct (ar_init_s sp w W) as (M & _ & _ & _).
    unfold swfW. rewrite M. split; intros X; exfalso; irl_md.
  - intros w src pos za La zb Lb (_ & IV). split; [|exact (iv_head _ _ _ _ _ _ _ _ IV)].
    rewrite (sr_head _ _ _ (iv_rel _ _ _ _ _ _ _ _ IV)). exact (iv_head _ _ _ _ _ _ _ _ IV).
  - (* one call on each *)
    intros w src pos za La zb Lb strma strmb flush iba ibb inp oa ob ain aout ra za' sta' owa rb zb' stb' owb
      (W & IV) LVa LVb ZFa ZFb SWa SWb SNa SNb P0 A0 PA BS AO FL IBa IBb EI RA NA RB NB.
    destruct (ar_call ST _ _ src pos za La zb Lb strma strmb flush iba ibb inp oa ob ain aout ra za' sta' owa
                rb zb' stb' owb IV LVa LVb ZFa ZFb SWa SWb SNa SNb P0 A0 PA BS AO IBa IBb EI RA NA RB NB)
      as (La' & Lb' & E1 & E2 & R & AI & AO' & OW & LO & B1 & B2 & IV').
    exists La', Lb'.
    do 7 (split; [assumption|]).
    split; [exact (iv_tin _ _ _ _ _ _ _ _ IV')|].
    split; [exact (iv_tout _ _ _ _ _ _ _ _ IV')|].
    split; [exact (iv_dt _ _ _ _ _ _ _ _ IV')|].
    split; [exact (iv_msg _ _ _ _ _ _ _ _ IV')|].
    split; [intros _; exact (iv_adler _ _ _ _ _ _ _ _ IV')|].
    split; [exact B1|]. split; [exact B2|].
    split; [exact W | exact IV'].
Qed.
