(* The bit buffer of the concrete machine (PULLBYTE, NEEDBITS, DROPBITS, INITBITS, BYTEBITS) on the input's
   bits, and the slow path's table lookups against the abstract decoder's table walk: SIKitBuf.v and
   SIKitLook.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_split_invariant.SIDefs.
Require Import Zlib.proof.harness.api_split_invariant.SIKitBuf.
Require Import Zlib.proof.harness.api_split_invariant.SIKitLook.
Import ListNotations.
Local Open Scope Z_scope.

Lemma si_kit : kit_stmt.
Proof.
  split; [exact sik_kit_bits|].
  intros src P0 m kind t nb lk Hb Hl [sz [_ TV]] TR LK q root. split.
  - exact (sik_lookup1 src P0 kind (m_s m) t nb sz lk (bb_src _ _ _ Hb) TV TR LK m Hb Hl eq_refl).
  - intros Lr m1 Hb1 Hl1 Hs1 Inp Hq1 Hr1.
    exact (sik_lookup2 src P0 kind (m_s m) t nb sz lk (bb_src _ _ _ Hb) TV TR LK m Hb Hl eq_refl Lr
             m1 Hb1 Hl1 Hs1 Inp Hq1 Hr1).
Qed.
