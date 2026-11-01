(* RT-D: CORRECTED part specs (v2).  Three specs of RTDBits.v / RTDSpecs.v are false as stated:
   - flush_block_fspec: the stored branch needs the block's bytes to be bytes (the history out is
     unconstrained) -> [flush_block_fspec2]: [Forall F.byte_ok b] in the buf clause;
   - fpend_fspec: bi_flush writes at pending_buf[pending], pend starts at pending_out ->
     [fpend_fspec2]: hypothesis [d_bi_valid s < 8 \/ d_po s = 0] (LT: fp_room);
   - ins_fspec: entries above p in p's prev slot, and p unbounded -> [ins_fspec2]: hypotheses
     [wpos s], [chain_ok s], [d_strstart s - d_w_size s <= p].
   The assembly (RTDTheory) uses these.  Each old spec implies the new one ([*_fix] below), so a proof that ASSUMES
   a new spec is the stronger result. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDSpecs.
Import ListNotations.
Local Open Scope Z_scope.

Definition flush_block_fspec2 : Prop :=
  forall t m buf sl last t' m' kind syms out wmax p,
    Zlib.proof.huffman.Overlay.flush_pre t syms -> 0 <= last <= 1 -> 0 <= p -> (p - o_bi_valid (tr_out t)) mod 8 = 0 ->
    syms_rok wmax out syms ->
    (forall b, buf = Some b -> Zlength b = sl /\ sl <= 65535 /\ Forall F.byte_ok b /\
                              F.syms_data out (map fsym syms) = out ++ b) ->
    c_tr_flush_block (t, m) buf sl last = Some ((t', m'), kind) ->
    exists blk,
      F.block_ok wmax out blk /\ F.block_data out blk = F.syms_data out (map fsym syms) /\
      bits_ok (tr_out t') /\ (last = 1 -> o_bi_valid (tr_out t') = 0) /\
      obits (tr_out t') = obits (tr_out t) ++ enc_out p [blk] (last =? 1).

Definition fpend_fspec2 : Prop :=
  forall s z s' z',
    outok s -> zout_ok z -> (d_bi_valid s < 8 \/ d_po s = 0) -> c_flush_pending s z = Some (s', z') ->
    exists x, zout_only z z' x /\ F.bytes_bits (x ++ pend s') ++ bibits s' = F.bytes_bits (pend s) ++ bibits s.

Definition ins_fspec2 : Prop :=
  forall s p s' h,
    prm s -> wstruct s -> wpos s -> chain_ok s -> chain_hok s -> primed s p ->
    0 <= p <= d_strstart s -> d_strstart s - d_w_size s <= p ->
    p + 2 < d_strstart s + d_lookahead s -> p - d_w_size s < lim s ->
    c_insert_string s p = Some (s', h) ->
    d_ins_h s' = h3 s p /\ h = Znth (h3 s p) (d_head s) /\ chain_hok s' /\ primed s' (p + 1).

Lemma flush_block_fix : flush_block_fspec -> flush_block_fspec2.
Proof.
  intros H t m buf sl last t' m' kind syms out wmax p A B C D E G R.
  eapply H; eauto. intros b Hb. destruct (G b Hb) as (? & ? & _ & ?). auto.
Qed.

Lemma fpend_fix : fpend_fspec -> fpend_fspec2.
Proof. intros H s z s' z' A B _ R. eapply H; eauto. Qed.

Lemma ins_fix : ins_fspec -> ins_fspec2.
Proof. intros H s p s' h A B _ _ C E F _ G I R. eapply H; eauto. Qed.
