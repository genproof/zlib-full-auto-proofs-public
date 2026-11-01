(* Law rj_bad_block: the theory of inflate() fed the broken stream in clip() pieces (BBWDefs.bbw_theory_stmt).
   Kinds 2 and 3 (fixed-Huffman literals, then the code 286/287, or the length code 257 then the distance code
   30/31) from the fixed-block run theory (FRFacts.v, FRTheory.v); kinds 0 (stored, NLEN not the complement of
   LEN), 1 (BTYPE 11) and 4 (HLIT 30/31) from the block header, which the first call (offered at least 5 bytes)
   reads to the error. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.bit_writer.BBWDefs.
Require Import Zlib.proof.harness.bit_writer.FRFacts.
Require Import Zlib.proof.harness.bit_writer.FRDefs.
Require Import Zlib.proof.harness.bit_writer.FRTheory.
Require Import Zlib.proof.harness.bit_writer.BBRun.
Require Import Zlib.proof.harness.bit_writer.BWBits.
Require Import Zlib.proof.harness.bit_writer.BBWThyRun.
Require Import Zlib.proof.harness.bit_writer.BBWThyFR.
Import ListNotations.
Local Open Scope Z_scope.

(* the fixed block of kinds 2 and 3 in the run theory's terms: main's stream, its literals, the bad tail *)
Definition bbw_tail (kind which: Z) : frtail := if kind =? 2 then TLL which else TDCode which.
Definition bbw_C (S0: list Z) (kind which: Z) (lits: list Z) : frc :=
  FRC (bb_bytes S0 kind which lits) lits (bbw_tail kind which).

(* the invariant between calls: kinds 2 and 3, the run theory's (BBWThyFR.bbw_fr_J); kinds 0, 1 and 4, the state
   after inflateInit2_ (the first call reaches the error) *)
Definition bbw_inv : bbw_J := fun S0 kind which lits pos ob s =>
  if orb (kind =? 2) (kind =? 3) then bbw_fr_J (bbw_C S0 kind which lits) pos ob s
  else pos = 0 /\ ob = [] /\ exists sp w, -15 <= w <= -8 /\ s = l_s (init_live sp w).

(* kinds 2 and 3: main's stream is such a fixed block, and its first byte is BFINAL, BTYPE 01 and five bits *)
Lemma bbw_frc_ok S0 kind which lits : bbw_ok S0 kind which lits -> kind = 2 \/ kind = 3 ->
  fr_ok (bbw_C S0 kind which lits) /\ ~ is_far (fr_tail (bbw_C S0 kind which lits)) /\
  exists x c, Znth 0 (bb_bytes S0 kind which lits) = x + 2 * 1 + 8 * c /\ 0 <= x <= 1 /\ 0 <= c < 32.
Proof.
  intros Hok K.
  destruct (bbw_layout S0 kind which lits Hok) as (HlS & HbS & Hfit & Hhd & Hrest & E0 & Rx & Rc).
  pose proof Hok as (Hk & Hwh & Hlits & Hbl & HbS0 & HS0 & Hk0).
  assert (Ht : tail_bits (bbw_tail kind which) = bb_tail_bits kind which /\ bb_btype kind = 1 /\
               tail_ok (Zlength lits) (bbw_tail kind which) /\ ~ is_far (bbw_tail kind which)).
  { destruct K as [-> | ->]; (split; [apply (bbt_tail which Hwh) | split; [reflexivity | split; [cbn; lia | cbn; tauto]]]). }
  destruct Ht as (Ht & Hbt & Hto & Hnf). rewrite Hbt in Hhd, E0.
  change (bval (bits_le 1 2)) with 1 in E0.
  split; [|split].
  - unfold fr_ok, fr_end, fr_body, bbw_C. cbn [fr_src fr_lits fr_tail]. rewrite Ht.
    split; [exact HbS|]. split; [exact (bw_lits_range lits Hbl)|].
    split; [rep_lia|]. split; [exact Hto|]. split; [lia|]. split; [rewrite Hhd; reflexivity|]. exact Hrest.
  - exact Hnf.
  - eexists; eexists. split; [exact E0|]. split; [exact Rx | exact Rc].
Qed.

Lemma bbw_theory : bbw_theory_stmt.
Proof.
  exists bbw_inv. constructor.
  - intros S0 kind which lits sp w Hok Hw. unfold bbw_inv.
    destruct (orb (kind =? 2) (kind =? 3)) eqn:K.
    + assert (K' : kind = 2 \/ kind = 3) by (apply orb_true_iff in K; destruct K as [K|K]; apply Z.eqb_eq in K; auto).
      destruct (bbw_frc_ok _ _ _ _ Hok K') as (Hfr & _ & _).
      split; [exact (bbw_fr_inv_init _ sp w Hw)|]. intros _. left. split; [reflexivity|].
      destruct (bbt_init sp w Hw) as (_ & _ & _ & _ & _ & Ws). exact Ws.
    + split; [reflexivity|]. split; [reflexivity|]. exists sp, w. split; [exact Hw | reflexivity].
  - intros S0 kind which lits room pos ob L z inp flush res Hok S HJ Hlive Hz Hpos Hroom Hob Hinp Hao Hfl Hrun.
    unfold bbw_inv in HJ.
    destruct (orb (kind =? 2) (kind =? 3)) eqn:K.
    + assert (K' : kind = 2 \/ kind = 3) by (apply orb_true_iff in K; destruct K as [K|K]; apply Z.eqb_eq in K; auto).
      destruct (bbw_frc_ok _ _ _ _ Hok K') as (Hfr & Hnf & Hb0).
      apply (bbw_fr_call bbw_inv S0 kind which lits (bbw_C S0 kind which lits) room pos ob L z inp flush res
               Hfr eq_refl eq_refl Hnf Hb0); auto.
      intros p o s Hj. unfold bbw_inv. rewrite K. exact Hj.
    + (* kinds 0, 1 and 4: the first call, offered at least the first 5 bytes, reaches the error *)
      apply orb_false_iff in K. destruct K as [K2 K3]. apply Z.eqb_neq in K2, K3.
      destruct HJ as (-> & -> & sp & w & Hw & HL).
      left.
      destruct (bbw_bits S0 kind which lits Hok) as (HlS & _).
      pose proof Hok as (_ & _ & _ & _ & _ & HS0 & _).
      rewrite Hinp, Z.add_0_l, Z.sub_0_r in Hrun.
      apply (bbw_refused S0 kind which lits (Z.min (Zlength S) Int.max_unsigned) w sp L z flush res Hok K2 K3 Hw HL);
        [|exact Hrun].
      unfold S. rep_lia.
Qed.
