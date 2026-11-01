(* mwf (Inv.v) under the small machine updates the cases do: mode changes, the bit buffer operations,
   NEEDBITS. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.inflate.Inv.
Import ListNotations.
Local Open Scope Z_scope.



(* the state fields other than mode unchanged: the mode facts of the new mode *)
Lemma modewf_set_mode: forall s md,
  modewf s ->
  (md = LENLENS -> 4 <= i_ncode s <= 19 /\ 0 <= i_have s <= i_ncode s /\ 257 <= i_nlen s <= 286 /\ 1 <= i_ndist s <= 30 /\
                   (forall k, 0 <= k < i_have s -> Znth (Znth k order) (i_lens s) <= 7)) ->
  (md = CODELENS -> 0 <= i_have s <= i_nlen s + i_ndist s /\ 257 <= i_nlen s <= 286 /\ 1 <= i_ndist s <= 30 /\
                    i_lencode s = TCodes 0 /\ tvalid CODES lenfix_list distfix_list s (i_lencode s) (i_lenbits s) /\
                    (forall k, 0 <= k < i_have s -> Znth k (i_lens s) <= 15)) ->
  (decode_mode md -> tvalid LENS lenfix_list distfix_list s (i_lencode s) (i_lenbits s) /\
                     tvalid DISTS lenfix_list distfix_list s (i_distcode s) (i_distbits s)) ->
  (md = LENEXT -> i_extra s <= 5) -> (md = DISTEXT -> i_extra s <= 13) -> (md = MATCH -> 1 <= i_length s) ->
  (md = LENEXT \/ md = DIST \/ md = DISTEXT -> 1 <= i_length s) ->
  (md = DISTEXT \/ md = MATCH -> 1 <= i_offset s) ->
  (md = LENEXT -> i_back s <= 15) -> (md = DIST -> i_back s <= 20) -> (md = DISTEXT -> i_back s <= 35) ->
  modewf (set_i_mode s md).
Proof.
  intros s md W H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.
  (* tvalid does not depend on the mode *)
  assert (TV: forall kind t rb, tvalid kind lenfix_list distfix_list s t rb ->
                                tvalid kind lenfix_list distfix_list (set_i_mode s md) t rb) by (intros; exact H).
  constructor; simpl; intros; auto.
Qed.

Lemma swf_set_mode: forall s md, swf s -> HEAD <= md <= SYNC -> swf (set_i_mode s md).
Proof. intros s md [] H; constructor; simpl; auto. Qed.

(* a mode change of the machine *)
Lemma mwf_set_mode: forall m md,
  mwf m -> HEAD <= md <= SYNC ->
  (md = LENLENS -> 4 <= i_ncode (m_s m) <= 19 /\ 0 <= i_have (m_s m) <= i_ncode (m_s m) /\
                   257 <= i_nlen (m_s m) <= 286 /\ 1 <= i_ndist (m_s m) <= 30 /\
                   (forall k, 0 <= k < i_have (m_s m) -> Znth (Znth k order) (i_lens (m_s m)) <= 7)) ->
  (md = CODELENS -> 0 <= i_have (m_s m) <= i_nlen (m_s m) + i_ndist (m_s m) /\ 257 <= i_nlen (m_s m) <= 286 /\
                    1 <= i_ndist (m_s m) <= 30 /\ i_lencode (m_s m) = TCodes 0 /\
                    tvalid CODES lenfix_list distfix_list (m_s m) (i_lencode (m_s m)) (i_lenbits (m_s m)) /\
                    (forall k, 0 <= k < i_have (m_s m) -> Znth k (i_lens (m_s m)) <= 15)) ->
  (decode_mode md -> tvalid LENS lenfix_list distfix_list (m_s m) (i_lencode (m_s m)) (i_lenbits (m_s m)) /\
                     tvalid DISTS lenfix_list distfix_list (m_s m) (i_distcode (m_s m)) (i_distbits (m_s m))) ->
  (md = LENEXT -> i_extra (m_s m) <= 5) -> (md = DISTEXT -> i_extra (m_s m) <= 13) ->
  (md = MATCH -> 1 <= i_length (m_s m)) ->
  (md = LENEXT \/ md = DIST \/ md = DISTEXT -> 1 <= i_length (m_s m)) ->
  (md = DISTEXT \/ md = MATCH -> 1 <= i_offset (m_s m)) ->
  (md = LENEXT -> i_back (m_s m) <= 15) -> (md = DIST -> i_back (m_s m) <= 20) ->
  (md = DISTEXT -> i_back (m_s m) <= 35) ->
  (m_out m = m_aout m \/ md = LENGTH \/ md = DONE \/ md = BAD) ->
  mwf (set_mode m md).
Proof.
  intros m md W HR H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 HO. destruct W.
  constructor; simpl; auto.
  - apply modewf_set_mode; auto.
  - apply swf_set_mode; auto.
Qed.

(* a mode that needs nothing *)
Lemma mwf_set_mode_plain: forall m md,
  mwf m -> HEAD <= md <= SYNC -> md <> LENLENS -> md <> CODELENS -> ~ decode_mode md ->
  (m_out m = m_aout m \/ md = LENGTH \/ md = DONE \/ md = BAD) ->
  mwf (set_mode m md).
Proof.
  intros m md W HR H1 H2 H3 HO.
  assert (ND: forall P: Prop, decode_mode md -> P) by (intros P D; contradiction).
  apply mwf_set_mode; auto; try (intros; subst; congruence); try (intros D; apply ND; unfold decode_mode; intuition).
Qed.

(* the bit buffer *)
Lemma mwf_initbits: forall m, mwf m -> mwf (initbits m).
Proof. intros m W. destruct W. constructor; simpl; auto; try (unfold lrange; rep_lia). Qed.

Lemma mwf_set_leave: forall m, mwf m -> mwf (set_leave m).
Proof. intros m W. destruct W. constructor; simpl; auto; try lia. Qed.

Lemma Zshiftr_range: forall x n, 0 <= x <= Int64.max_unsigned -> 0 <= n -> 0 <= Z.shiftr x n <= Int64.max_unsigned.
Proof.
  intros x n H Hn. rewrite Z.shiftr_div_pow2 by lia. split.
  - apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia].
  - apply Z.le_trans with x; [ | lia]. apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia |].
    assert (1 <= 2 ^ n) by (apply Z.pow_le_mono_r with (a := 2) in Hn; [ simpl in Hn; lia | lia]). nia.
Qed.

Lemma mwf_dropbits: forall m n, mwf m -> 0 <= n <= m_bits m -> mwf (dropbits n m).
Proof.
  intros m n W Hn. destruct W. constructor; simpl; auto.
  - apply Zshiftr_range; auto. lia.
  - unfold u32. rewrite Z.mod_small by lia. lia.
Qed.

Lemma mwf_bytebits: forall m, mwf m -> mwf (bytebits m).
Proof.
  intros m W. destruct W. constructor; simpl; auto.
  - apply Zshiftr_range; auto. pose proof (Z.mod_pos_bound (m_bits m) 8). lia.
  - pose proof (Z.mod_pos_bound (m_bits m) 8). pose proof (Z.mod_le (m_bits m) 8). lia.
Qed.

Lemma mwf_pull: forall m, mwf m -> m_have m <> 0 -> m_bits m <= 31 -> mwf (pull m).
Proof.
  intros m W Hh Hb. pose proof (mw_hold _ W) as WH. pose proof (mw_nx _ W) as WNX.
  destruct W. constructor; simpl; auto.
  - unfold m_have in Hh. lia.
  - unfold lrange, u64. pose proof (Z.mod_pos_bound (m_hold m + Znth (m_nx m) (m_inp m) * 2 ^ m_bits m) (2^64)). rep_lia.
  - unfold u32. rewrite Z.mod_small by lia. lia.
Qed.

Lemma mwf_needbits_f: forall k n m, mwf m -> n <= 32 -> mwf (needbits_f k n m).
Proof.
  induction k; intros n m W Hn; simpl; auto.
  destruct (m_bits m <? n) eqn:E; auto.
  destruct (m_have m =? 0) eqn:E2.
  - apply mwf_set_leave; auto.
  - apply IHk; auto. apply mwf_pull; auto. apply Z.eqb_neq; auto. apply Z.ltb_lt in E. lia.
Qed.

Lemma mwf_needbits: forall n m, mwf m -> n <= 32 -> mwf (needbits n m).
Proof. intros. apply mwf_needbits_f; auto. Qed.
