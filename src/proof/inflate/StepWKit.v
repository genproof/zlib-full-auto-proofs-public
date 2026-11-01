(* The wide invariant mwfW (InvW.v) under the small machine updates of the cases, and the form of the
   invariant the case proofs use: mwf3xW = mwfW + Step3Inv.v's xwf3 + nohdr (the mode is not EXLEN, EXTRA),
   the wide counterpart of Step3Inv.v's mwf3x.  The lemmas are those of MwfLemmas.v and Step3Kit.v that involve mwf, over mwfW (the others are
   reused from there), and the per-case statements of Step3Stmts.v over mwf3xW. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.inflate.InvW.
Require Export Zlib.proof.inflate.Step3Kit.
Import ListNotations.
Local Open Scope Z_scope.

Lemma mwfW_left: forall m, mwfW m -> 0 <= m_left m <= Int.max_unsigned.
Proof. intros m H. destruct H. unfold m_left. pose proof (Zlength_nonneg (m_ow m)). lia. Qed.

Lemma mwfW_have: forall m, mwfW m -> 0 <= m_have m <= Int.max_unsigned.
Proof. intros m H. destruct H. unfold m_have. lia. Qed.

Lemma mwfW_out_eq: forall m, mwfW m -> m_mode m <> LENGTH -> m_mode m <> DONE -> m_mode m <> BAD ->
  m_out m = m_aout m.
Proof. intros m H A B C. destruct (mwW_outeq _ H) as [E | [E | [E | E]]]; congruence. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* mwfW under mode changes and the bit buffer operations (MwfLemmas.v)                            *)

(* a mode change of the machine *)
Lemma mwfW_set_mode: forall m md,
  mwfW m -> HEAD <= md <= SYNC ->
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
  mwfW (set_mode m md).
Proof.
  intros m md W HR H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 HO. destruct W.
  constructor; simpl; auto.
  - apply modewf_set_mode; auto.
  - apply swf_set_mode; auto.
Qed.

(* a mode that needs nothing *)
Lemma mwfW_set_mode_plain: forall m md,
  mwfW m -> HEAD <= md <= SYNC -> md <> LENLENS -> md <> CODELENS -> ~ decode_mode md ->
  (m_out m = m_aout m \/ md = LENGTH \/ md = DONE \/ md = BAD) ->
  mwfW (set_mode m md).
Proof.
  intros m md W HR H1 H2 H3 HO.
  apply mwfW_set_mode; try assumption; intros E; exfalso;
    first [apply H1; exact E | apply H2; exact E | apply H3; exact E | apply H3; unfold decode_mode; tauto].
Qed.

(* the bit buffer *)
Lemma mwfW_initbits: forall m, mwfW m -> mwfW (initbits m).
Proof. intros m W. destruct W. constructor; simpl; auto; try (unfold lrange; rep_lia). Qed.

Lemma mwfW_set_leave: forall m, mwfW m -> mwfW (set_leave m).
Proof. intros m W. destruct W. constructor; simpl; auto; try lia. Qed.

Lemma mwfW_dropbits: forall m n, mwfW m -> 0 <= n <= m_bits m -> mwfW (dropbits n m).
Proof.
  intros m n W Hn. destruct W. constructor; simpl; auto.
  - apply Zshiftr_range; auto. lia.
  - unfold u32. rewrite Z.mod_small by lia. lia.
Qed.

Lemma mwfW_bytebits: forall m, mwfW m -> mwfW (bytebits m).
Proof.
  intros m W. destruct W. constructor; simpl; auto.
  - apply Zshiftr_range; auto. pose proof (Z.mod_pos_bound (m_bits m) 8). lia.
  - pose proof (Z.mod_pos_bound (m_bits m) 8). pose proof (Z.mod_le (m_bits m) 8). lia.
Qed.

Lemma mwfW_pull: forall m, mwfW m -> m_have m <> 0 -> m_bits m <= 31 -> mwfW (pull m).
Proof.
  intros m W Hh Hb. pose proof (mwW_hold _ W) as WH. pose proof (mwW_nx _ W) as WNX.
  destruct W. constructor; simpl; auto.
  - unfold m_have in Hh. lia.
  - unfold lrange, u64. pose proof (Z.mod_pos_bound (m_hold m + Znth (m_nx m) (m_inp m) * 2 ^ m_bits m) (2^64)). rep_lia.
  - unfold u32. rewrite Z.mod_small by lia. lia.
Qed.

Lemma mwfW_needbits_f: forall k n m, mwfW m -> n <= 32 -> mwfW (needbits_f k n m).
Proof.
  induction k; intros n m W Hn; simpl; auto.
  destruct (m_bits m <? n) eqn:E; auto.
  destruct (m_have m =? 0) eqn:E2.
  - apply mwfW_set_leave; auto.
  - apply IHk; auto. apply mwfW_pull; auto. apply Z.eqb_neq; auto. apply Z.ltb_lt in E. lia.
Qed.

Lemma mwfW_needbits: forall n m, mwfW m -> n <= 32 -> mwfW (needbits n m).
Proof. intros. apply mwfW_needbits_f; auto. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* mwf3xW: mwfW and the facts xwf3 of Step3Inv.v                                                  *)

(* the machine is outside the two modes of the gzip extra field, where InvW.v's hdrW says something: the
   cases other than FLAGS .. EXTRA never enter them (StepWHeader.v proves those under hdrW) *)
Definition nohdr (m: mst) : Prop := m_mode m <> EXLEN /\ m_mode m <> EXTRA.

Lemma nohdr_hdrW: forall m, nohdr m -> hdrW m.
Proof. intros m [A B]. split; intros E; contradiction. Qed.

Lemma nohdr_ext: forall m m0, nohdr m0 -> m_s m = m_s m0 -> nohdr m.
Proof. unfold nohdr, m_mode. intros m m0 N E. rewrite E. exact N. Qed.

Ltac nohdr_md := cbv [nohdr m_mode EXLEN EXTRA HEAD FLAGS TIME OS NAME COMMENT HCRC DICTID DICT Model.TYPE TYPEDO
  STORED COPY_ COPY TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC] in *;
  simpl; lia.

Record mwf3xW (m: mst) : Prop := { m3W_w : mwfW m; m3W_x : xwf3 m; m3W_n : nohdr m }.

Lemma mwf3xW_intro: forall m m0, mwfW m -> xwf3 m0 -> m_s m = m_s m0 -> nohdr m0 -> mwf3xW m.
Proof. intros m m0 W X E N. constructor; auto. apply xwf3_ext with m0; auto. apply nohdr_ext with m0; auto. Qed.

(* the bit buffer operations *)
Lemma mwf3xW_needbits: forall n m, mwf3xW m -> n <= 32 -> mwf3xW (needbits n m).
Proof. intros n m [W X N] H. apply mwf3xW_intro with m; auto using mwfW_needbits, needbits_s. Qed.

Lemma mwf3xW_dropbits: forall m n, mwf3xW m -> 0 <= n <= m_bits m -> mwf3xW (dropbits n m).
Proof. intros m n [W X N] H. apply mwf3xW_intro with m; auto using mwfW_dropbits. Qed.

Lemma mwf3xW_pull: forall m, mwf3xW m -> m_have m <> 0 -> m_bits m <= 31 -> mwf3xW (pull m).
Proof. intros m [W X N] H1 H2. apply mwf3xW_intro with m; auto using mwfW_pull. Qed.

Lemma mwf3xW_initbits: forall m, mwf3xW m -> mwf3xW (initbits m).
Proof. intros m [W X N]. apply mwf3xW_intro with m; auto using mwfW_initbits. Qed.

Lemma mwf3xW_bytebits: forall m, mwf3xW m -> mwf3xW (bytebits m).
Proof. intros m [W X N]. apply mwf3xW_intro with m; auto using mwfW_bytebits. Qed.

Lemma mwf3xW_set_leave: forall m, mwf3xW m -> mwf3xW (set_leave m).
Proof. intros m [W X N]. apply mwf3xW_intro with m; auto using mwfW_set_leave. Qed.

Lemma needbits_ok: forall n m,
  mwfW m -> m_leave m = 0 -> n <= 32 -> m_leave (needbits n m) <> 1 ->
  n <= m_bits (needbits n m) /\ m_leave (needbits n m) = 0.
Proof. intros n m W L N E. apply needbits_f_ok; auto; try (destruct W; simpl; lia). Qed.

(* leave after a NEEDBITS that left it 0 is 0 or 1 *)
Lemma leave_cases: forall m, mwfW m -> m_leave m = 1 \/ m_leave m = 0.
Proof. intros m W. destruct (mwW_leave _ W). lia. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the mode                                                                                      *)

(* a mode that needs nothing of the state *)
Lemma mwf3xW_set_mode_plain: forall m md,
  mwf3xW m -> HEAD < md <= SYNC -> md <> LENLENS -> md <> CODELENS -> ~ decode_mode md ->
  (m_out m = m_aout m \/ md = LENGTH \/ md = DONE \/ md = BAD) -> md <> EXLEN -> md <> EXTRA ->
  mwf3xW (set_mode m md).
Proof.
  intros m md [W X] HR H1 H2 H3 HO N1 N2. constructor; [| | split; unfold m_mode; simpl; auto].
  - apply mwfW_set_mode_plain; auto; lia.
  - destruct X as [A B C D]. constructor; unfold m_mode; simpl; auto.
    + intros E; exfalso; clear -HR E; lia.
    + intros E; subst; elim H3; unfold decode_mode; auto 10.
    + intros E; subst; elim H3; unfold decode_mode; auto 10.
    + intros E; contradiction.
Qed.

(* the general case: the mode facts of mwfW_set_mode (MwfLemmas.v) and of xwf3 for the new mode *)
Lemma mwf3xW_set_mode: forall m md,
  mwf3xW m -> HEAD < md <= SYNC ->
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
  (m_out m = m_aout m \/ md = LENGTH \/ md = DONE \/ md = BAD) -> md <> EXLEN -> md <> EXTRA ->
  mwf3xW (set_mode m md).
Proof.
  intros m md [W X] HR H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 HO N1 N2. constructor; [| | split; unfold m_mode; simpl; auto].
  - assert (HR': HEAD <= md <= SYNC) by lia. apply mwfW_set_mode; auto.
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
(* the lookups                                                                                   *)

Lemma lookup1_f_ok: forall k fx dx t nb m,
  mwfW m -> m_leave m = 0 -> 0 <= nb ->
  (forall i, 0 <= i < 2 ^ nb -> e_bits (tab_entry fx dx (m_s m) t i) <= 15) ->
  15 <= m_bits m + 8 * (Z.of_nat k - 1) ->
  let '(here, m', ok) := lookup1_f k fx dx t nb m in
  mwfW m' /\ m_s m' = m_s m /\
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
      * split; [apply mwfW_set_leave; auto|]. split; [reflexivity|]. split; [discriminate|]. auto.
      * pose proof (Hb _ BR) as Hb1.
        assert (W': mwfW (pull m)) by (apply mwfW_pull; auto; lia).
        assert (Bp: m_bits (pull m) = m_bits m + 8)
          by (unfold pull; simpl; unfold u32; rewrite Z.mod_small; destruct W; lia).
        specialize (IHk fx dx t nb (pull m) W' L Hnb Hb ltac:(rewrite Bp; lia)).
        destruct (lookup1_f k fx dx t nb (pull m)) as [[h m'] ok]. exact IHk.
Qed.

Lemma lookup1_ok: forall fx dx t nb m,
  mwfW m -> m_leave m = 0 -> 0 <= nb ->
  (forall i, 0 <= i < 2 ^ nb -> e_bits (tab_entry fx dx (m_s m) t i) <= 15) ->
  let '(here, m', ok) := lookup1 fx dx t nb m in
  mwfW m' /\ m_s m' = m_s m /\
  (ok = true -> m_leave m' = 0 /\ e_bits here <= m_bits m' /\
                exists i, 0 <= i < 2 ^ nb /\ here = tab_entry fx dx (m_s m) t i) /\
  (ok = false -> m_leave m' = 1).
Proof. intros. apply lookup1_f_ok; auto. destruct H. simpl. lia. Qed.

Lemma lookup2_f_ok: forall k fx dx t last m,
  mwfW m -> m_leave m = 0 -> 0 <= e_bits last <= m_bits m -> 0 <= e_op last ->
  (forall j, 0 <= j < 2 ^ e_op last -> e_bits last + e_bits (tab_entry fx dx (m_s m) t (e_val last + j)) <= 15) ->
  15 <= m_bits m + 8 * (Z.of_nat k - 1) ->
  let '(here, m', ok) := lookup2_f k fx dx t last m in
  mwfW m' /\ m_s m' = m_s m /\
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
      * split; [apply mwfW_set_leave; auto|]. split; [reflexivity|]. split; [discriminate|]. auto.
      * pose proof (Hb _ BR) as Hb1.
        assert (W': mwfW (pull m)) by (apply mwfW_pull; auto; lia).
        assert (Bp: m_bits (pull m) = m_bits m + 8)
          by (unfold pull; simpl; unfold u32; rewrite Z.mod_small; destruct W; lia).
        specialize (IHk fx dx t last (pull m) W' L ltac:(rewrite Bp; lia) Ho Hb ltac:(rewrite Bp; lia)).
        destruct (lookup2_f k fx dx t last (pull m)) as [[h m'] ok]. exact IHk.
Qed.

Lemma lookup2_ok: forall fx dx t last m,
  mwfW m -> m_leave m = 0 -> 0 <= e_bits last <= m_bits m -> 0 <= e_op last ->
  (forall j, 0 <= j < 2 ^ e_op last -> e_bits last + e_bits (tab_entry fx dx (m_s m) t (e_val last + j)) <= 15) ->
  let '(here, m', ok) := lookup2 fx dx t last m in
  mwfW m' /\ m_s m' = m_s m /\
  (ok = true -> m_leave m' = 0 /\ e_bits last + e_bits here <= m_bits m' /\
                exists j, 0 <= j < 2 ^ e_op last /\ here = tab_entry fx dx (m_s m) t (e_val last + j)) /\
  (ok = false -> m_leave m' = 1).
Proof. intros. apply lookup2_f_ok; auto. destruct H. simpl. lia. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the per-case statements of Step3Stmts.v over mwf3xW                                            *)

Definition ok_at (md: Z) (f: mst -> iout) : Prop :=
  forall m, mwf3xW m -> m_leave m = 0 -> m_mode m = md -> iout_ok mwf3xW (f m).

(* LEN's fast path: inflate_fast and the `if (state->mode == TYPE) state->back = -1;` after it *)
Definition fast_stmt : Prop :=
  forall m, mwf3xW m -> m_leave m = 0 -> m_mode m = LEN ->
    6 <= m_have m -> 258 <= m_left m -> m_bits m < 8 ->
    mwf3xW (let m := fast lenfix_list distfix_list (restore m) in
          if m_mode m =? Model.TYPE then upd_s m (fun s => set_i_back s (-1)) else m).

Definition ok_MATCH : Prop := ok_at MATCH c_MATCH.
Definition ok_DISTEXT : Prop := ok_at DISTEXT c_DISTEXT.
Definition ok_DIST : Prop := ok_at DIST (c_DIST lenfix_list distfix_list).
Definition ok_LENEXT : Prop := ok_at LENEXT (c_LENEXT lenfix_list distfix_list).
Definition ok_LIT : Prop := ok_at LIT c_LIT.
Definition ok_LEN : Prop := ok_at LEN (c_LEN lenfix_list distfix_list (fast lenfix_list distfix_list)).
Definition ok_LEN_ : Prop := ok_at LEN_ (c_LEN_ lenfix_list distfix_list (fast lenfix_list distfix_list)).

Definition ok_CODELENS : Prop :=
  forall flush, ok_at CODELENS (c_CODELENS flush lenfix_list distfix_list (fast lenfix_list distfix_list)).
Definition ok_LENLENS : Prop :=
  forall flush, ok_at LENLENS (c_LENLENS flush lenfix_list distfix_list (fast lenfix_list distfix_list)).
Definition ok_TABLE : Prop :=
  forall flush, ok_at TABLE (c_TABLE flush lenfix_list distfix_list (fast lenfix_list distfix_list)).

(* c_TYPE falls into c_TYPEDO without setting the mode *)
Definition ok_TYPEDO : Prop :=
  forall flush m, mwf3xW m -> m_leave m = 0 -> (m_mode m = Model.TYPE \/ m_mode m = TYPEDO) ->
    iout_ok mwf3xW (c_TYPEDO flush m).
Definition ok_TYPE : Prop := forall flush, ok_at Model.TYPE (c_TYPE flush).
Definition ok_STORED : Prop := forall flush, ok_at STORED (c_STORED flush).
Definition ok_COPY_ : Prop := ok_at COPY_ c_COPY_.
Definition ok_COPY : Prop := ok_at COPY c_COPY.
Definition ok_CHECK : Prop := ok_at CHECK c_CHECK.
Definition ok_LENGTH : Prop := ok_at LENGTH c_LENGTH.
Definition ok_DONE : Prop := ok_at DONE c_DONE.
Definition ok_BAD : Prop := ok_at BAD c_BAD.

Definition ok_HCRC : Prop := ok_at HCRC c_HCRC.
Definition ok_DICTID : Prop := forall flush, ok_at DICTID (c_DICTID flush).
Definition ok_DICT : Prop := forall flush, ok_at DICT (c_DICT flush).
