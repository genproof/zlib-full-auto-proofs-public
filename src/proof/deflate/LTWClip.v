(* The deflateBound accounting for the clip() loops (LawFactsW2.bound_w_big_stmt) from the wide core with its
   level-0 clip facts (LTWIfaceClip.core_w_clip_stmt), the wide header stages (LTWIface.hdr_w_stmt) and lemma (ii)
   (BlockBound.block_bound_statement): the walk of LTBound.bound_theory over calls of up to 2^32 - 1 bytes of
   input and of output space, any number of calls, for any accepted parameters and n <= 2^63 - 1. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.deflate.LTWIfaceClip Zlib.proof.deflate.LawFactsW2.
Require Zlib.proof.huffman.BlockBound.
Require Import Zlib.proof.deflate.LTWBInit Zlib.proof.deflate.LTWBound Zlib.proof.deflate.LTWCWalk.
Local Open Scope Z_scope.

(** deflateBound for n <= 2^63 - 1: the first [BrunC] (phase P0, an empty window). *)
Lemma brunc_of_bpre : forall W HI, core_facts_w W ->
  forall level wbits mem strategy ds s tin tout adler n,
  BpreW W level wbits mem strategy ds s tin tout adler -> 0 <= n <= 9223372036854775807 ->
  exists b, c_deflateBound (Some s) n = Some b /\ 0 <= b <= 18446744073709551615 /\
    BrunC W HI n b 0 false s tin tout adler.
Proof.
  intros W HI CF level wbits mem strategy ds s tin tout adler n HB Hn.
  destruct (bound_of_bpre_w W HI CF level wbits mem strategy ds s tin tout adler n HB Hn) as (b & E & Hb & HR).
  exists b. split; [exact E|]. split; [exact Hb|]. split; [exact HR|].
  intros _. rewrite (brunw_ub0 W HI CF _ _ _ _ _ _ _ HR). lia.
Qed.

Theorem bound_w_big_thm : Zlib.proof.huffman.BlockBound.block_bound_statement ->
  core_w_clip_stmt -> hdr_w_stmt -> bound_w_big_stmt.
Proof.
  intros BB [CF (CC & _ & CU)] [HI HF].
  revert CF CC CU. generalize Zlib.proof.deflate.LTCore.W3 as W. intros W CF CC CU.
  (* the level-0 clip facts in the form the walk uses *)
  assert (CC' : clip_comp W)
    by (intros s z f HW Ho Hq Hf Hz Hw Ha Hl Hu Hao; apply CC; auto; lia).
  assert (CU' : clip_ub W)
    by (intros s z f s' z' bs HW Ho Hq Hf Hz Hw Ha Hl Hu E; exact (CU s z f s' z' bs HW Ho Hq Hf Hz Hw Ha Hl Hu E)).
  exists (BpreW W), (BrunC W HI).
  split; [|split; [|split]].
  - constructor.
    + intros. apply bpre_init_w; auto.
    + intros. eapply bpre_dict_w; eauto.
    + intros. apply bpre_head_w; auto.
    + intros level wbits mem strategy ds s tin tout adler n HB Hn.
      exact (brunc_of_bpre _ HI CF level wbits mem strategy ds s tin tout adler n HB ltac:(lia)).
    + intros n b s tin tout adler data msg [HB _] Hb Hd Hn.
      exact (once_w _ HI CF HF BB n b s tin tout adler data msg HB Hb Hd Hn).
  - intros level wbits mem strategy ds s tin tout adler n HB Hn.
    exact (brunc_of_bpre _ HI CF level wbits mem strategy ds s tin tout adler n HB Hn).
  - intros n b pos fin s tin tout adler [HB _].
    destruct (brunw_facts _ HI CF HF _ _ _ _ _ _ _ _ HB) as (Hpd & _ & Ht & Htb & _ & Hpos & _). lia.
  - intros n b pos fin s tin tout adler inb msg HB Hd Hlen Hfin flush aout.
    destruct (deflate_walk_c _ HI CF HF CC' CU' BB n b pos fin s tin tout adler inb msg flush aout HB Hd Hlen Hfin
                eq_refl eq_refl) as (s' & z' & code & E & P).
    exists s', z', code. split; [exact E|exact P].
Qed.
