(* Copy of StepKit.v over Step3Inv.v's mwf3x.  Kit for the Step3*.v parts: mwf3x under the small machine
   updates, NEEDBITS's result, the table lookups lookup1 / lookup2 (Model.v), the root / sub-table facts of a valid table (Tables.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.inflate.Step3Inv.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* xwf3 only reads the state                                                                       *)

Lemma xwf3_ext: forall m1 m2, m_s m1 = m_s m2 -> xwf3 m1 -> xwf3 m2.
Proof. intros m1 m2 E [A B C D]. constructor; unfold m_mode in *; rewrite <- E; auto. Qed.

Lemma mwf3x_intro: forall m m0, mwf m -> xwf3 m0 -> m_s m = m_s m0 -> mwf3x m.
Proof. intros m m0 W X E. constructor; auto. apply xwf3_ext with m0; auto. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the bit buffer operations do not touch the state                                              *)

Lemma needbits_f_s: forall k n m, m_s (needbits_f k n m) = m_s m.
Proof.
  induction k; intros n m; simpl; auto.
  destruct (m_bits m <? n); auto. destruct (m_have m =? 0); auto. rewrite IHk. reflexivity.
Qed.

Lemma needbits_s: forall n m, m_s (needbits n m) = m_s m.
Proof. intros. apply needbits_f_s. Qed.

Lemma mwf3x_needbits: forall n m, mwf3x m -> n <= 32 -> mwf3x (needbits n m).
Proof. intros n m [W X] H. apply mwf3x_intro with m; auto using mwf_needbits, needbits_s. Qed.

Lemma mwf3x_dropbits: forall m n, mwf3x m -> 0 <= n <= m_bits m -> mwf3x (dropbits n m).
Proof. intros m n [W X] H. apply mwf3x_intro with m; auto using mwf_dropbits. Qed.

Lemma mwf3x_pull: forall m, mwf3x m -> m_have m <> 0 -> m_bits m <= 31 -> mwf3x (pull m).
Proof. intros m [W X] H1 H2. apply mwf3x_intro with m; auto using mwf_pull. Qed.

Lemma mwf3x_initbits: forall m, mwf3x m -> mwf3x (initbits m).
Proof. intros m [W X]. apply mwf3x_intro with m; auto using mwf_initbits. Qed.

Lemma mwf3x_bytebits: forall m, mwf3x m -> mwf3x (bytebits m).
Proof. intros m [W X]. apply mwf3x_intro with m; auto using mwf_bytebits. Qed.

Lemma mwf3x_set_leave: forall m, mwf3x m -> mwf3x (set_leave m).
Proof. intros m [W X]. apply mwf3x_intro with m; auto using mwf_set_leave. Qed.

(* NEEDBITS(n) without leave: n bits are there *)
Lemma needbits_f_ok: forall k n m,
  m_leave m = 0 -> 0 <= m_bits m -> n <= 32 -> n <= m_bits m + 8 * Z.of_nat k ->
  m_leave (needbits_f k n m) <> 1 -> n <= m_bits (needbits_f k n m) /\ m_leave (needbits_f k n m) = 0.
Proof.
  induction k; intros n m L B N F E; simpl in *.
  - split; [lia | auto].
  - destruct (Z.ltb_spec (m_bits m) n).
    + destruct (m_have m =? 0).
      * simpl in E. lia.
      * apply IHk; auto; unfold pull; simpl; unfold u32; rewrite ?Z.mod_small; lia.
    + split; [lia | auto].
Qed.

Lemma needbits_ok: forall n m,
  mwf m -> m_leave m = 0 -> n <= 32 -> m_leave (needbits n m) <> 1 ->
  n <= m_bits (needbits n m) /\ m_leave (needbits n m) = 0.
Proof. intros n m W L N E. apply needbits_f_ok; auto; try (destruct W; simpl; lia). Qed.

(* leave after a NEEDBITS that left it 0 is 0 or 1 *)
Lemma leave_cases: forall m, mwf m -> m_leave m = 1 \/ m_leave m = 0.
Proof. intros m W. destruct (mw_leave _ W). lia. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the mode                                                                                      *)

(* a mode that needs nothing of the state *)
Lemma mwf3x_set_mode_plain: forall m md,
  mwf3x m -> HEAD < md <= SYNC -> md <> LENLENS -> md <> CODELENS -> ~ decode_mode md ->
  (m_out m = m_aout m \/ md = LENGTH \/ md = DONE \/ md = BAD) ->
  mwf3x (set_mode m md).
Proof.
  intros m md [W X] HR H1 H2 H3 HO. constructor.
  - apply mwf_set_mode_plain; auto; lia.
  - destruct X as [A B C D]. constructor; unfold m_mode; simpl; auto.
    + intros E; exfalso; clear -HR E; lia.
    + intros E; subst; elim H3; unfold decode_mode; auto 10.
    + intros E; subst; elim H3; unfold decode_mode; auto 10.
    + intros E; contradiction.
Qed.

(* the general case: the mode facts of mwf_set_mode (MwfLemmas.v) and of xwf3 for the new mode *)
Lemma mwf3x_set_mode: forall m md,
  mwf3x m -> HEAD < md <= SYNC ->
  (md = LENLENS -> 4 <= i_ncode (m_s m) <= 19 /\ 0 <= i_have (m_s m) <= i_ncode (m_s m) /\
                   257 <= i_nlen (m_s m) <= 286 /\ 1 <= i_ndist (m_s m) <= 30 /\
                   (forall k, 0 <= k < i_have (m_s m) -> Znth (Znth k order) (i_lens (m_s m)) <= 7)) ->
  (md = CODELENS -> 0 <= i_have (m_s m) <= i_nlen (m_s m) + i_ndist (m_s m) /\ 257 <= i_nlen (m_s m) <= 286 /\
                    1 <= i_ndist (m_s m) <= 30 /\ i_lencode (m_s m) = TCodes 0 /\
                    tvalid CODES lenfix_list distfix_list (m_s m) (i_lencode (m_s m)) (i_lenbits (m_s m)) /\
                    (forall k, 0 <= k < i_have (m_s m) -> Znth k (i_lens (m_s m)) <= 15)) ->
  (decode_mode md -> lvalid lenfix_list distfix_list (m_s m) (i_lencode (m_s m)) (i_lenbits (m_s m)) /\
                     tvalid DISTS lenfix_list distfix_list (m_s m) (i_distcode (m_s m)) (i_distbits (m_s m))) ->
  (md = LENEXT -> i_extra (m_s m) <= 5 /\ i_length (m_s m) <= 258) ->
  (md = DISTEXT -> i_extra (m_s m) <= 13 /\ i_offset (m_s m) <= 32768) ->
  (md = MATCH -> 1 <= i_length (m_s m)) ->
  (md = LENEXT \/ md = DIST \/ md = DISTEXT -> 1 <= i_length (m_s m)) ->
  (md = DISTEXT \/ md = MATCH -> 1 <= i_offset (m_s m)) ->
  (md = LENEXT -> i_back (m_s m) <= 15) -> (md = DIST -> i_back (m_s m) <= 20) ->
  (md = DISTEXT -> i_back (m_s m) <= 35) ->
  (m_out m = m_aout m \/ md = LENGTH \/ md = DONE \/ md = BAD) ->
  mwf3x (set_mode m md).
Proof.
  intros m md [W X] HR H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 HO. constructor.
  - assert (HR': HEAD <= md <= SYNC) by lia. apply mwf_set_mode; auto.
    + intros D; destruct (H3 D) as [A B]; split; auto. apply lvalid_tvalid; auto.
    + intros E; destruct (H4 E); auto.
    + intros E; destruct (H5 E); auto.
  - destruct X as [A B C D]. constructor; unfold m_mode; simpl; auto.
    + intros E; exfalso; clear -HR E; lia.
    + intros E; destruct (H4 E); auto.
    + intros E; destruct (H5 E); auto.
    + intros E; destruct (H3 E); auto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* valid tables                                                                                  *)

Lemma tv_root_bits: forall kind get rb sz i,
  tvalid_g kind get rb sz -> 0 <= i < 2 ^ rb -> 0 <= e_bits (get i) <= 15 /\ entry_ok (get i).
Proof.
  intros kind get rb sz i [R S T] Hi. destruct (T i Hi) as [E F]. cbv zeta in F.
  split; auto. destruct E as (_ & E & _).
  destruct (islink kind (e_op (get i))); [destruct F as (F & _); lia | lia].
Qed.

Lemma tv_sub: forall kind get rb sz i,
  tvalid_g kind get rb sz -> 0 <= i < 2 ^ rb -> islink kind (e_op (get i)) = true ->
  sub_ok kind get rb sz (get i).
Proof. intros kind get rb sz i [R S T] Hi L. destruct (T i Hi) as [E F]. cbv zeta in F. rewrite L in F. auto. Qed.

Lemma tv_final: forall kind get rb sz i,
  tvalid_g kind get rb sz -> 0 <= i < 2 ^ rb -> islink kind (e_op (get i)) = false ->
  e_bits (get i) <= rb /\ final_ok kind (get i).
Proof. intros kind get rb sz i [R S T] Hi L. destruct (T i Hi) as [E F]. cbv zeta in F. rewrite L in F. auto. Qed.

Lemma bitsn_range: forall m n, 0 <= n -> 0 <= bitsn m n < 2 ^ n.
Proof. intros m n H. unfold bitsn. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. Qed.

Lemma sub_index_range: forall x b o, 0 <= b -> 0 <= o ->
  0 <= Z.shiftr (x mod 2 ^ (b + o)) b < 2 ^ o.
Proof.
  intros x b o Hb Ho. rewrite Z.shiftr_div_pow2 by lia.
  assert (P: 0 < 2 ^ b) by (apply Z.pow_pos_nonneg; lia).
  assert (Q: 0 <= x mod 2 ^ (b + o) < 2 ^ (b + o)) by (apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
  rewrite Z.pow_add_r in Q |- * by lia. split.
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; nia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the lookups                                                                                   *)

Lemma lookup1_f_ok: forall k fx dx t nb m,
  mwf m -> m_leave m = 0 -> 0 <= nb ->
  (forall i, 0 <= i < 2 ^ nb -> e_bits (tab_entry fx dx (m_s m) t i) <= 15) ->
  15 <= m_bits m + 8 * (Z.of_nat k - 1) ->
  let '(here, m', ok) := lookup1_f k fx dx t nb m in
  mwf m' /\ m_s m' = m_s m /\
  (ok = true -> m_leave m' = 0 /\ e_bits here <= m_bits m' /\
                exists i, 0 <= i < 2 ^ nb /\ here = tab_entry fx dx (m_s m) t i) /\
  (ok = false -> m_leave m' = 1).
Proof.
  induction k; intros fx dx t nb m W L Hnb Hb F; simpl.
  - split; [auto|]. split; [auto|]. split; [|discriminate].
    intros _. split; [auto|]. pose proof (bitsn_range m nb Hnb). split.
    + specialize (Hb _ H). lia.
    + eexists; split; [eassumption | reflexivity].
  - pose proof (bitsn_range m nb Hnb) as BR.
    destruct (Z.leb_spec (e_bits (tab_entry fx dx (m_s m) t (bitsn m nb))) (m_bits m)).
    + split; [auto|]. split; [auto|]. split; [|discriminate].
      intros _. split; [auto|]. split; [auto|]. eexists; split; [eassumption | reflexivity].
    + destruct (Z.eqb_spec (m_have m) 0).
      * split; [apply mwf_set_leave; auto|]. split; [reflexivity|]. split; [discriminate|]. auto.
      * pose proof (Hb _ BR) as Hb1.
        assert (W': mwf (pull m)) by (apply mwf_pull; auto; lia).
        assert (Bp: m_bits (pull m) = m_bits m + 8)
          by (unfold pull; simpl; unfold u32; rewrite Z.mod_small; destruct W; lia).
        specialize (IHk fx dx t nb (pull m) W' L Hnb Hb ltac:(rewrite Bp; lia)).
        destruct (lookup1_f k fx dx t nb (pull m)) as [[h m'] ok]. exact IHk.
Qed.

Lemma lookup1_ok: forall fx dx t nb m,
  mwf m -> m_leave m = 0 -> 0 <= nb ->
  (forall i, 0 <= i < 2 ^ nb -> e_bits (tab_entry fx dx (m_s m) t i) <= 15) ->
  let '(here, m', ok) := lookup1 fx dx t nb m in
  mwf m' /\ m_s m' = m_s m /\
  (ok = true -> m_leave m' = 0 /\ e_bits here <= m_bits m' /\
                exists i, 0 <= i < 2 ^ nb /\ here = tab_entry fx dx (m_s m) t i) /\
  (ok = false -> m_leave m' = 1).
Proof. intros. apply lookup1_f_ok; auto. destruct H. simpl. lia. Qed.

Lemma lookup2_f_ok: forall k fx dx t last m,
  mwf m -> m_leave m = 0 -> 0 <= e_bits last <= m_bits m -> 0 <= e_op last ->
  (forall j, 0 <= j < 2 ^ e_op last -> e_bits last + e_bits (tab_entry fx dx (m_s m) t (e_val last + j)) <= 15) ->
  15 <= m_bits m + 8 * (Z.of_nat k - 1) ->
  let '(here, m', ok) := lookup2_f k fx dx t last m in
  mwf m' /\ m_s m' = m_s m /\
  (ok = true -> m_leave m' = 0 /\ e_bits last + e_bits here <= m_bits m' /\
                exists j, 0 <= j < 2 ^ e_op last /\ here = tab_entry fx dx (m_s m) t (e_val last + j)) /\
  (ok = false -> m_leave m' = 1).
Proof.
  induction k; intros fx dx t last m W L Hl Ho Hb F; simpl.
  - pose proof (sub_index_range (m_hold m) (e_bits last) (e_op last) ltac:(lia) Ho) as BR.
    unfold bitsn. split; [auto|]. split; [auto|]. split; [|discriminate].
    intros _. split; [auto|]. split.
    + specialize (Hb _ BR). lia.
    + eexists; split; [eassumption | reflexivity].
  - pose proof (sub_index_range (m_hold m) (e_bits last) (e_op last) ltac:(lia) Ho) as BR.
    unfold bitsn at 1 2.
    destruct (Z.leb_spec (e_bits last + e_bits (tab_entry fx dx (m_s m) t
                (e_val last + Z.shiftr (m_hold m mod 2 ^ (e_bits last + e_op last)) (e_bits last)))) (m_bits m)).
    + split; [auto|]. split; [auto|]. split; [|discriminate].
      intros _. split; [auto|]. split; [auto|]. eexists; split; [eassumption | reflexivity].
    + destruct (Z.eqb_spec (m_have m) 0).
      * split; [apply mwf_set_leave; auto|]. split; [reflexivity|]. split; [discriminate|]. auto.
      * pose proof (Hb _ BR) as Hb1.
        assert (W': mwf (pull m)) by (apply mwf_pull; auto; lia).
        assert (Bp: m_bits (pull m) = m_bits m + 8)
          by (unfold pull; simpl; unfold u32; rewrite Z.mod_small; destruct W; lia).
        specialize (IHk fx dx t last (pull m) W' L ltac:(rewrite Bp; lia) Ho Hb ltac:(rewrite Bp; lia)).
        destruct (lookup2_f k fx dx t last (pull m)) as [[h m'] ok]. exact IHk.
Qed.

Lemma lookup2_ok: forall fx dx t last m,
  mwf m -> m_leave m = 0 -> 0 <= e_bits last <= m_bits m -> 0 <= e_op last ->
  (forall j, 0 <= j < 2 ^ e_op last -> e_bits last + e_bits (tab_entry fx dx (m_s m) t (e_val last + j)) <= 15) ->
  let '(here, m', ok) := lookup2 fx dx t last m in
  mwf m' /\ m_s m' = m_s m /\
  (ok = true -> m_leave m' = 0 /\ e_bits last + e_bits here <= m_bits m' /\
                exists j, 0 <= j < 2 ^ e_op last /\ here = tab_entry fx dx (m_s m) t (e_val last + j)) /\
  (ok = false -> m_leave m' = 1).
Proof. intros. apply lookup2_f_ok; auto. destruct H. simpl. lia. Qed.
