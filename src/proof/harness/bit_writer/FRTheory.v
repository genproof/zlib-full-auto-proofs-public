(* The theory of inflate() on a raw stream whose first block is fixed-Huffman literals then an invalid element
   (FRFacts.v): the invariant between calls and its facts. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.bit_writer.FRFacts.
Require Import Zlib.proof.harness.bit_writer.FRDefs.
Require Import Zlib.proof.harness.bit_writer.FRLayout.
Require Import Zlib.proof.harness.bit_writer.FRBits.
Require Import Zlib.proof.harness.bit_writer.FRHead.
Require Import Zlib.proof.harness.bit_writer.FRLen.
Require Import Zlib.proof.harness.bit_writer.FRTail.
Require Import Zlib.proof.harness.bit_writer.FRFast.
Require Import Zlib.proof.harness.bit_writer.FRLeave.
Require Import Zlib.proof.harness.bit_writer.FRCall.
Import ListNotations.
Local Open Scope Z_scope.

(* after inflateInit2_(strm, w), w raw: HEAD, nothing read, nothing written, wrap 0 *)
Lemma fr_inv_init : forall C sp w, fr_ok C -> -15 <= w <= -8 -> fr_inv C 0 [] (l_s (init_live sp w)).
Proof.
  intros C sp w HC Hw.
  assert (E: reset2_wb w = Some (0, - w)).
  { unfold reset2_wb. destruct (Z.ltb_spec w 0); [|lia]. destruct (Z.ltb_spec w (-15)); [lia|].
    destruct (Z.leb_spec 8 (- w)); [|lia]. destruct (Z.leb_spec (- w) 15); [|lia]. reflexivity. }
  unfold init_live. rewrite E. cbn [l_s].
  (* wb = -w is not 0: wrap stays 0 and inflateReset's header step does nothing *)
  unfold init_s, reset2_s, reset_full_s, reset_hdr_s, reset2_wrap.
  destruct (Z.eqb_spec (- w) 0); [lia | ].
  unfold fr_inv, fr_at.
  cbn [i_mode i_hold i_bits i_last i_wrap i_whave init_s reset2_s reset_s reset_keep_s zero_s set_i_mode set_i_win
       i_win set_i_wbits set_i_wrap set_i_wdata set_i_wnext set_i_whave set_i_wsize set_i_total set_i_last
       set_i_havedict set_i_flags set_i_dmax set_i_head set_i_hold set_i_bits set_i_lencode set_i_distcode
       set_i_next set_i_sane set_i_back andb negb Z.land Z.eqb].
  split; [|rewrite Zlength_nil; lia].
  right. split.
  - unfold hold_ok. split; [lia|]. split; [apply Zlength_nonneg|]. rewrite sublist_nil. reflexivity.
  - left. repeat split; reflexivity.
Qed.

(* the output is a prefix of the literals *)
Lemma fr_inv_out : forall C pos ob s, fr_inv C pos ob s -> Zlength ob <= Zlength (fr_lits C).
Proof.
  intros C pos ob s [A _]. unfold fr_at in A.
  assert (LJ: forall j, 0 <= j -> Zlength (fr_lit C j) <= Zlength (fr_lits C)).
  { intros j Hj. unfold fr_lit. rewrite !Zlength_correct, firstn_length. lia. }
  destruct A as [[_ A]|[_ A]]; [exact A|].
  destruct A as [(_ & _ & _ & -> & _)|[(_ & _ & _ & -> & _)|(_ & A)]];
    [rewrite Zlength_nil; apply Zlength_nonneg|rewrite Zlength_nil; apply Zlength_nonneg|].
  destruct A as [(_ & _ & j & Hj & _ & ->)|[(_ & _ & j & Hj & _ & -> & _)|[(_ & _ & -> & _)|
                [(_ & _ & -> & _)|[(_ & _ & -> & _)|(_ & -> & _)]]]]];
    try (apply LJ; lia); lia.
Qed.

Lemma fr_theory : fr_theory_stmt.
Proof.
  pose proof fr_layout as LA. pose proof fr_bits as BI.
  pose proof (fr_tail_ok LA BI) as TA.
  assert (PS: fr_passes).
  { split; [exact (fr_head LA BI)|]. split; [|exact TA].
    exact (fr_len LA BI (fr_fast LA BI) (proj1 TA)). }
  exists fr_inv. constructor.
  - exact fr_inv_init.
  - exact fr_inv_out.
  - intros. apply (fr_call_ok PS fr_leave); auto.
Qed.
