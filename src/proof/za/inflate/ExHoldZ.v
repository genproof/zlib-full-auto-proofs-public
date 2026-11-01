(* The bit buffer after NEEDBITS(16) in case EXLEN: when the case starts with fewer than 16 bits and only
   those bits in the buffer (hold < 2^bits, InvW.hdrW), the pulls stop at 16..23 bits and hold < 2^24.  So the
   extra field's length that EXLEN stores (u32 hold) is below 2^31 - 1, which the wide invariant's hdrW
   requires in case EXTRA. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.inflate.Inv.
Local Open Scope Z_scope.

(* one PULLBYTE() below 16 bits keeps hold < 2^bits with at most 23 bits *)
Lemma pull_hold_lt: forall m,
  0 <= m_bits m < 16 -> 0 <= m_hold m < 2 ^ m_bits m ->
  bytes_ok (m_inp m) -> 0 <= m_nx m < Zlength (m_inp m) ->
  0 <= m_bits (pull m) <= 23 /\ 0 <= m_hold (pull m) < 2 ^ m_bits (pull m) /\
  m_inp (pull m) = m_inp m /\ 0 <= m_nx (pull m) <= Zlength (m_inp m).
Proof.
  intros m B H BO NX. unfold pull.
  set (b := Znth (m_nx m) (m_inp m)).
  assert (BB: 0 <= b <= 255).
  { unfold b. unfold bytes_ok in BO. rewrite Forall_forall in BO.
    apply BO. apply Znth_In. lia. }
  assert (P: 0 < 2 ^ m_bits m) by (apply Z.pow_pos_nonneg; lia).
  assert (E8: 2 ^ (m_bits m + 8) = 2 ^ m_bits m * 256)
    by (rewrite Z.pow_add_r by lia; reflexivity).
  assert (P23: 2 ^ (m_bits m + 8) <= 2 ^ 23) by (apply Z.pow_le_mono_r; lia).
  assert (LT: 0 <= m_hold m + b * 2 ^ m_bits m < 2 ^ (m_bits m + 8)) by nia.
  cbn [m_bits m_hold m_inp m_nx set_m_bits set_m_hold set_m_nx].
  unfold u32, u64.
  rewrite (Z.mod_small (m_bits m + 8)) by (cbn; lia).
  rewrite Z.mod_small by (split; [lia | eapply Z.lt_le_trans; [apply LT | ]]; eapply Z.le_trans; [apply P23 | cbn; lia]).
  split; [lia | ]. split; [exact LT | ]. split; [reflexivity | lia].
Qed.

Lemma needbits_f_hold_lt: forall k m,
  0 <= m_bits m <= 23 -> 0 <= m_hold m < 2 ^ m_bits m ->
  bytes_ok (m_inp m) -> 0 <= m_nx m <= Zlength (m_inp m) ->
  0 <= m_hold (needbits_f k 16 m) < 2 ^ 24.
Proof.
  assert (W: forall m, 0 <= m_bits m <= 23 -> 0 <= m_hold m < 2 ^ m_bits m -> 0 <= m_hold m < 2 ^ 24).
  { intros m B H. split; [lia | ]. eapply Z.lt_le_trans; [apply H | apply Z.pow_le_mono_r; lia]. }
  induction k as [ | k IH]; intros m B H BO NX; cbn [needbits_f]; [now apply W | ].
  destruct (m_bits m <? 16) eqn:EB; [ | now apply W].
  apply Z.ltb_lt in EB.
  destruct (m_have m =? 0) eqn:EH; [now apply W | ].
  apply Z.eqb_neq in EH. unfold m_have in EH.
  destruct (pull_hold_lt m ltac:(lia) H BO ltac:(lia)) as (B1 & H1 & I1 & N1).
  apply IH; auto; rewrite I1; auto.
Qed.

(* NEEDBITS(16) from a bit buffer of fewer than 16 bits, all of them in hold *)
Lemma needbits16_hold_lt: forall m,
  0 <= m_bits m < 16 -> m_hold m < 2 ^ m_bits m -> 0 <= m_hold m ->
  bytes_ok (m_inp m) -> 0 <= m_nx m <= Zlength (m_inp m) ->
  0 <= m_hold (needbits 16 m) < 2 ^ 24.
Proof. intros. apply needbits_f_hold_lt; auto; lia. Qed.
