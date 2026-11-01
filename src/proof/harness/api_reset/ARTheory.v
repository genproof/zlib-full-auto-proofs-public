(* Law api_reset, the theory: the facts of ARFacts.v for the invariants J0, J1 (ARTheoryDefs.v), from the
   simulation of one call (ARRunCall.ar_call over ARSimAll.ar_step) and the reset (ARReset.ar_reset). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_reset.ARTheoryDefs.
Require Import Zlib.proof.harness.inflate_reset.IRRunLoop.
Require Import Zlib.proof.harness.api_reset.ARSimAll.
Require Import Zlib.proof.harness.api_reset.ARRunCall.
Require Import Zlib.proof.harness.api_reset.ARReset.
Import ListNotations.
Local Open Scope Z_scope.

Lemma ar_theory : ar_theory_stmt.
Proof.
  pose proof ar_step as ST.
  exists J0, J1. constructor.
  - (* inflateInit2_ *)
    intros w src z sp W _ _ _ _ _ _ _ _ _. split; [exact W|].
    destruct (ar_init_s sp w W) as (M & H & Ho & Bi).
    constructor;
      [apply irl_srel_refl | reflexivity | exact H | left; reflexivity | left; reflexivity |
       intros _ _; rewrite Ho, Bi; apply ar_hd0 | rewrite M; irl_md | reflexivity ..].
  - (* the state after inflateInit2_ *)
    intros w sp W. destruct (ar_init_s sp w W) as (M & _ & _ & _).
    unfold swfW. rewrite M. split; intros X; exfalso; irl_md.
  - intros w src pos z L (_ & IV). exact (iv_head _ _ _ _ _ _ _ _ IV).
  - intros w src pos za La zb Lb (_ & IV). split; [|exact (iv_head _ _ _ _ _ _ _ _ IV)].
    rewrite (sr_head _ _ _ (iv_rel _ _ _ _ _ _ _ _ IV)). exact (iv_head _ _ _ _ _ _ _ _ IV).
  - (* phase 0 *)
    intros w src pos z L strmp flush ib inp o ain aout r z' st' ow (W & IV) LV ZF SW SN P0 A0 PA BS AO FL IB EI
      REL NM.
    destruct (ar_call ST _ _ src pos z L z L strmp strmp flush ib ib inp o o ain aout r z' st' ow r z' st' ow
                IV LV LV ZF ZF SW SW SN SN P0 A0 PA BS AO IB IB EI REL NM REL NM)
      as (La' & Lb' & E1 & E2 & _ & _ & _ & _ & _ & B1 & B2 & IV').
    rewrite E1 in E2. inversion E2; subst Lb'.
    exists La'. split; [exact E1|]. split; [lia|]. split; [lia|]. split; [exact W | exact IV'].
  - (* the reset *)
    exact ar_reset.
  - (* phase 1 *)
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
