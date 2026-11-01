(* Small facts for the simulation of the dynamic block header (SISimTab.v): the case of each machine in the
   modes TABLE, LENLENS, CODELENS, LEN_; traces; the relation after a pass that changes only the bit buffer
   and the table fields (it stays in the data phase, or goes to BAD); the fields that lenlens_zero,
   lens_fill and call_table read and write. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_split_invariant.SIDefs.
Import ListNotations.
Local Open Scope Z_scope.

Local Notation MTYPE := Zlib.proof.inflate.Model.TYPE.

(* ---------------------------------------------------------------------------------------------- *)
(* The case of each machine                                                                       *)

Lemma sit_c_TABLE flush m : m_mode m = TABLE ->
  stepf2 flush lenfix_list distfix_list m =
  c_TABLE flush lenfix_list distfix_list (fast lenfix_list distfix_list) m.
Proof. intros E. unfold stepf2, step2. rewrite E. reflexivity. Qed.
Lemma sit_c_LENLENS flush m : m_mode m = LENLENS ->
  stepf2 flush lenfix_list distfix_list m =
  c_LENLENS flush lenfix_list distfix_list (fast lenfix_list distfix_list) m.
Proof. intros E. unfold stepf2, step2. rewrite E. reflexivity. Qed.
Lemma sit_c_CODELENS flush m : m_mode m = CODELENS ->
  stepf2 flush lenfix_list distfix_list m =
  c_CODELENS flush lenfix_list distfix_list (fast lenfix_list distfix_list) m.
Proof. intros E. unfold stepf2, step2. rewrite E. reflexivity. Qed.
Lemma sit_c_LEN_ flush m : m_mode m = LEN_ ->
  stepf2 flush lenfix_list distfix_list m = c_LEN_ lenfix_list distfix_list (fast lenfix_list distfix_list) m.
Proof. intros E. unfold stepf2, step2. rewrite E. reflexivity. Qed.

Lemma sit_a_TABLE src a : a_mode a = TABLE -> astep lenfix_list distfix_list src a = a_TABLE src a.
Proof. intros E. unfold astep. rewrite E. reflexivity. Qed.
Lemma sit_a_LENLENS src a : a_mode a = LENLENS -> astep lenfix_list distfix_list src a = a_LENLENS src a.
Proof. intros E. unfold astep. rewrite E. reflexivity. Qed.
Lemma sit_a_CODELENS src a : a_mode a = CODELENS ->
  astep lenfix_list distfix_list src a = a_CODELENS lenfix_list distfix_list src a.
Proof. intros E. unfold astep. rewrite E. reflexivity. Qed.
Lemma sit_a_LEN_ src a : a_mode a = LEN_ -> astep lenfix_list distfix_list src a = a_LEN_ a.
Proof. intros E. unfold astep. rewrite E. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Traces                                                                                         *)

Lemma sit_ar_trans src I R a b c : areach src I R a b -> areach src I R b c -> areach src I R a c.
Proof.
  induction 1 as [a|a n w a1 a' S B _ IH]; intros H; [exact H|].
  eapply ar_step; eauto.
Qed.

(* one step that reads up to n <= 8 I and writes nothing *)
Lemma sit_ar1 src I R a n a1 :
  astep lenfix_list distfix_list src a = AGo n false a1 -> n <= 8 * I -> areach src I R a a1.
Proof.
  intros S N. eapply ar_step; [exact S| |apply ar_refl].
  cbn. intros [B|[B1 B2]]; [lia|discriminate].
Qed.

Lemma sit_ar_cons src I R a n a1 a' :
  astep lenfix_list distfix_list src a = AGo n false a1 -> n <= 8 * I ->
  areach src I R a1 a' -> areach src I R a a'.
Proof. intros S N T. eapply sit_ar_trans; [eapply sit_ar1; eauto|exact T]. Qed.

(* the invariant along a trace *)
Lemma sit_ar_awf (AW: awf_stmt) src I R a a' : areach src I R a a' -> awf src a -> awf src a'.
Proof.
  induction 1 as [a|a n w a1 a' S B _ IH]; intros W; [exact W|].
  apply IH. exact (proj1 (proj2 AW) src a n w a1 W S).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* What sim_ok says of the outcome o of one pass, from the abstract state a (I, R: the limits)    *)

Definition sit_out (flush: Z) (src: list Z) (P0: Z) (O0: list Z) (I R: Z) (a: ast) (o: iout) : Prop :=
  match o with
  | IBrk m' => exists a', areach src I R a a' /\ rel src P0 O0 m' a' /\
                 (m_leave m' = 1 -> stop_ok flush src I R m' a')
  | IRet r m' => r = Z_NEED_DICT /\
                 exists a', areach src I R a a' /\ rel src P0 O0 m' a' /\
                   astep lenfix_list distfix_list src a' = AEnd Z_NEED_DICT
  end.

(* free steps first *)
Lemma sit_out_pre flush src P0 O0 I R a a1 o :
  areach src I R a a1 -> sit_out flush src P0 O0 I R a1 o -> sit_out flush src P0 O0 I R a o.
Proof.
  intros T. destruct o as [m'|r m']; cbn.
  - intros (a' & T' & H). exists a'. split; [eapply sit_ar_trans; eauto|exact H].
  - intros (E & a' & T' & H). split; [exact E|]. exists a'. split; [eapply sit_ar_trans; eauto|exact H].
Qed.

(* sim_ok is sit_out of stepf2 *)
Lemma sit_sim_ok_out (P: Z -> Prop) flush src P0 O0 m a :
  sim_ok P -> rel src P0 O0 m a -> awf src a -> m_leave m = 0 -> P (m_mode m) ->
  sit_out flush src P0 O0 (P0 + Zlength (m_inp m)) (Zlength O0 + m_aout m) a
    (stepf2 flush lenfix_list distfix_list m).
Proof. intros S R W L M. exact (S flush src P0 O0 m a R W L M). Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Modes                                                                                          *)

(* a mode fact on the goal (goal only: lia splits the disjunctions of the hypotheses) *)
Ltac sit_mdg :=
  unfold win_mode, hdr_mode, data_mode, post_mode, len_live, off_live, ext_live, decode_mode,
    HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT, MTYPE, TYPEDO, STORED, COPY_, COPY,
    TABLE, LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, CHECK, LENGTH, DONE, BAD, MEM;
  lia.

(* the modes of this group, and LEN_ where CODELENS goes on *)
Definition tmode (md: Z) : Prop := md = TABLE \/ md = LENLENS \/ md = CODELENS \/ md = LEN_.

Lemma sit_tmode_facts md : tmode md ->
  data_mode md /\ win_mode md /\ md <> BAD /\ md <> DONE /\ ~ post_mode md /\ ~ hdr_mode md /\
  md <> COPY_ /\ md <> COPY /\ md <> CHECK /\ md <> LENGTH.
Proof. intros [E|[E|[E|E]]]; subst md; repeat split; sit_mdg. Qed.

Lemma sit_bad_facts : ~ data_mode BAD /\ ~ win_mode BAD /\ ~ post_mode BAD /\ ~ hdr_mode BAD /\ BAD <> DONE.
Proof. repeat split; sit_mdg. Qed.

Lemma sit_bits_ok_t s b : tmode (i_mode s) -> bits_ok s b.
Proof.
  intros T. pose proof (sit_tmode_facts _ T) as (_ & _ & _ & _ & _ & H1 & H2 & H3 & H4 & H5).
  unfold bits_ok. split; [|split]; intros X; try contradiction; destruct X; contradiction.
Qed.

Lemma sit_bits_ok_bad s b : i_mode s = BAD -> bits_ok s b.
Proof.
  intros E. unfold bits_ok. rewrite E. pose proof sit_bad_facts as (_ & _ & _ & H & _).
  split; [|split]; intros X; try contradiction; destruct X as [X|X]; revert X; sit_mdg.
Qed.

(* the projections of the setters *)
Ltac sit_cbn := cbn [m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler m_msg m_tin
  m_tout m_snx m_sow set_m_s set_m_h set_m_inp set_m_aout set_m_nx set_m_ow set_m_hold set_m_bits set_m_in
  set_m_out set_m_ret set_m_leave set_m_adler set_m_msg set_m_tin set_m_tout set_m_snx set_m_sow
  m_mode upd_s set_mode set_leave set_bad dropbits a_s a_q a_O a_mode
  i_mode i_last i_wrap i_havedict i_flags i_dmax i_check i_total i_head i_wbits i_wsize i_whave i_wnext i_win
  i_wdata i_hold i_bits i_length i_offset i_extra i_lencode i_distcode i_lenbits i_distbits i_ncode i_nlen
  i_ndist i_have i_next i_lens i_codes i_sane i_back i_was
  set_i_mode set_i_last set_i_wrap set_i_havedict set_i_flags set_i_dmax set_i_check set_i_total set_i_head
  set_i_wbits set_i_wsize set_i_whave set_i_wnext set_i_win set_i_wdata set_i_hold set_i_bits set_i_length
  set_i_offset set_i_extra set_i_lencode set_i_distcode set_i_lenbits set_i_distbits set_i_ncode set_i_nlen
  set_i_ndist set_i_have set_i_next set_i_lens set_i_codes set_i_sane set_i_back set_i_was] in *.

(* the same on the goal only *)
Ltac sit_cbng := cbn [m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler m_msg m_tin
  m_tout m_snx m_sow set_m_s set_m_h set_m_inp set_m_aout set_m_nx set_m_ow set_m_hold set_m_bits set_m_in
  set_m_out set_m_ret set_m_leave set_m_adler set_m_msg set_m_tin set_m_tout set_m_snx set_m_sow
  m_mode upd_s set_mode set_leave set_bad dropbits a_s a_q a_O a_mode
  i_mode i_last i_wrap i_havedict i_flags i_dmax i_check i_total i_head i_wbits i_wsize i_whave i_wnext i_win
  i_wdata i_hold i_bits i_length i_offset i_extra i_lencode i_distcode i_lenbits i_distbits i_ncode i_nlen
  i_ndist i_have i_next i_lens i_codes i_sane i_back i_was
  set_i_mode set_i_last set_i_wrap set_i_havedict set_i_flags set_i_dmax set_i_check set_i_total set_i_head
  set_i_wbits set_i_wsize set_i_whave set_i_wnext set_i_win set_i_wdata set_i_hold set_i_bits set_i_length
  set_i_offset set_i_extra set_i_lencode set_i_distcode set_i_lenbits set_i_distbits set_i_ncode set_i_nlen
  set_i_ndist set_i_have set_i_next set_i_lens set_i_codes set_i_sane set_i_back set_i_was].

(* ---------------------------------------------------------------------------------------------- *)
(* The machine fields a pass of these modes keeps                                                 *)

(* m' differs from m at most in the bit buffer, the leave flag and the istate *)
Definition sit_keep (m m': mst) : Prop :=
  m_inp m' = m_inp m /\ m_aout m' = m_aout m /\ m_ow m' = m_ow m /\ m_in m' = m_in m /\
  m_out m' = m_out m /\ m_tout m' = m_tout m.

Lemma sit_keep_refl m : sit_keep m m.
Proof. repeat split. Qed.

Lemma sit_keep_trans m1 m2 m3 : sit_keep m1 m2 -> sit_keep m2 m3 -> sit_keep m1 m3.
Proof. unfold sit_keep. intuition congruence. Qed.

(* the form of NEEDBITS' and the lookups' results (kit) *)
Lemma sit_keep_bits m m' :
  m' = set_m_leave (set_m_bits (set_m_hold (set_m_nx m (m_nx m')) (m_hold m')) (m_bits m')) (m_leave m') ->
  sit_keep m m' /\ m_s m' = m_s m /\ m_ret m' = m_ret m.
Proof. intros E. rewrite E. sit_cbn. repeat split. Qed.

(* the istate fields of the data phase the passes of these modes keep *)
Definition sit_skeep (s s': istate) : Prop :=
  i_wrap s' = i_wrap s /\ i_check s' = i_check s /\ i_total s' = i_total s /\ i_head s' = i_head s /\
  i_wsize s' = i_wsize s /\ i_whave s' = i_whave s /\ i_wnext s' = i_wnext s /\ i_win s' = i_win s /\
  i_wdata s' = i_wdata s.

Lemma sit_swin_ext s s' O : sit_skeep s s' -> swin_ok s O -> swin_ok s' O.
Proof.
  intros (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9) W. unfold swin_ok, swin_at in *.
  rewrite A5, A6, A7, A8, A9. exact W.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The relation after a pass                                                                      *)

(* in the data phase (TABLE, LENLENS, CODELENS, LEN_): the bit buffer, the istate fields of the
   table building, the leave flag change; the output, check, total, window do not *)
Lemma sit_rel_tab src P0 O0 m a m' a' :
  rel src P0 O0 m a -> tmode (m_mode m) -> tmode (m_mode m') -> sit_keep m m' ->
  bitbuf src P0 m' -> m_mode m' = a_mode a' -> a_q a' = mq P0 m' -> a_O a' = a_O a -> m_ret m' = Z_OK ->
  seq (m_s m') (a_s a') -> sit_skeep (m_s m) (m_s m') ->
  i_flags (a_s a') = i_flags (a_s a) -> i_check (a_s a') = i_check (a_s a) ->
  rel src P0 O0 m' a'.
Proof.
  intros R T T' (K1 & K2 & K3 & K4 & K5 & K6) BB Md Q O Rt S SK F C.
  pose proof SK as (A1 & A2 & A3 & A4 & _).
  pose proof (sit_tmode_facts _ T) as (Dm & Wm & Nb & Nd & Np & Nh & _).
  pose proof (sit_tmode_facts _ T') as (Dm' & Wm' & Nb' & Nd' & Np' & Nh' & _).
  destruct R as [R1 R2 R3 R4 R5 R6 R7 [R8a [R8b R8c]] R9 R10 [R11a R11b] [R12a R12b] R13 R14 R15].
  constructor; auto.
  - apply sit_bits_ok_t. exact T'.
  - rewrite O, K3. exact R5.
  - rewrite K3, K2. exact R6.
  - rewrite K4, K1. exact R7.
  - unfold m_left. rewrite K5, K3, K2. split; [exact R8a|]. split; [intros; contradiction|].
    intros _. apply R8c. auto.
  - split.
    + intros H. contradiction.
    + intros _ Hw. unfold m_mode in *. rewrite A2, F, C. apply R11b; auto. rewrite <- A1. exact Hw.
  - split.
    + intros _. unfold m_mode in *. rewrite A3. apply R12a. auto.
    + intros P. contradiction.
  - unfold m_left. rewrite K6, K5, K3, K2. exact R13.
  - intros _. eapply sit_swin_ext; [exact SK|]. apply R14. exact Wm.
  - unfold m_mode in *. rewrite A4. exact R15.
Qed.

(* to BAD: only the output fields and the bit buffer's input are left to check *)
Lemma sit_rel_bad src P0 O0 m a m' a' :
  rel src P0 O0 m a -> sit_keep m m' -> bitbuf src P0 m' -> m_mode m' = BAD -> a_mode a' = BAD ->
  a_O a' = a_O a -> i_head (m_s m') = false -> rel src P0 O0 m' a'.
Proof.
  intros R (K1 & K2 & K3 & K4 & K5 & K6) BB Md Ma O H.
  pose proof sit_bad_facts as (Xd & Xw & Xp & Xh & Xn).
  destruct R as [R1 R2 R3 R4 R5 R6 R7 [R8a [R8b R8c]] R9 R10 [R11a R11b] [R12a R12b] R13 R14 R15].
  constructor; auto; rewrite ?Md.
  - congruence.
  - intros X; contradiction.
  - apply sit_bits_ok_bad. exact Md.
  - rewrite O, K3. exact R5.
  - rewrite K3, K2. exact R6.
  - rewrite K4, K1. exact R7.
  - unfold m_left. rewrite K5, K3, K2. split; [exact R8a|]. split; [intros; contradiction|].
    intros [X|[X|[X _]]]; contradiction.
  - intros X; contradiction.
  - intros X; contradiction.
  - split; intros X; contradiction.
  - split; [intros [X|[X|[X _]]]|intros X]; contradiction.
  - unfold m_left. rewrite K6, K5, K3, K2. exact R13.
  - intros X; contradiction.
Qed.

(* the relation with only the leave flag changed *)
Lemma sit_rel_leave src P0 O0 m a l : rel src P0 O0 m a -> rel src P0 O0 (set_m_leave m l) a.
Proof.
  intros R. destruct R as [[B1 B2 B3 B4 B5 B6] R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15].
  unfold m_left, mq in *. constructor; sit_cbn; auto.
  constructor; unfold mq; sit_cbn; auto.
Qed.

(* the relation with the bit buffer only changed (a NEEDBITS or a lookup that leaves) *)
Lemma sit_rel_bits src P0 O0 m a m' :
  rel src P0 O0 m a -> sit_keep m m' -> m_s m' = m_s m -> m_ret m' = m_ret m ->
  bitbuf src P0 m' -> mq P0 m' = mq P0 m -> tmode (m_mode m) -> rel src P0 O0 m' a.
Proof.
  intros R K S Rt BB Q T.
  eapply sit_rel_tab; eauto.
  - unfold m_mode. rewrite S. exact T.
  - unfold m_mode. rewrite S. exact (rl_mode _ _ _ _ _ R).
  - rewrite Q. apply (rl_q _ _ _ _ _ R). apply (sit_tmode_facts _ T).
  - rewrite Rt. apply (rl_ret _ _ _ _ _ R); apply (sit_tmode_facts _ T).
  - rewrite S. apply (rl_s _ _ _ _ _ R). apply (sit_tmode_facts _ T).
  - rewrite S. repeat split.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The istate fields of the table building                                                        *)

(* the fields seq compares that the table modes do not write *)
Definition sit_tsame (s s': istate) : Prop :=
  i_last s' = i_last s /\ i_wrap s' = i_wrap s /\ i_havedict s' = i_havedict s /\ i_flags s' = i_flags s /\
  i_dmax s' = i_dmax s /\ i_head s' = i_head s /\ i_wbits s' = i_wbits s /\ i_sane s' = i_sane s.

(* the fields the table modes write, equal in both machines *)
Definition sit_teq (s t: istate) : Prop :=
  i_lencode s = i_lencode t /\ i_distcode s = i_distcode t /\ i_lenbits s = i_lenbits t /\
  i_distbits s = i_distbits t /\ i_ncode s = i_ncode t /\ i_nlen s = i_nlen t /\ i_ndist s = i_ndist t /\
  i_have s = i_have t /\ i_next s = i_next t /\ i_lens s = i_lens t /\ i_codes s = i_codes t.

Lemma sit_tmode_live md : tmode md -> ~ len_live md /\ ~ off_live md /\ ~ ext_live md.
Proof. intros [E|[E|[E|E]]]; subst md; repeat split; sit_mdg. Qed.

Lemma sit_seq_t s t s' t' :
  seq s t -> sit_tsame s s' -> sit_tsame t t' -> sit_teq s' t' -> tmode (i_mode t') -> seq s' t'.
Proof.
  intros S (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8) (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8)
    (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) T.
  pose proof (sit_tmode_live _ T) as (L1 & L2 & L3).
  destruct S. constructor; try congruence; intros X; contradiction.
Qed.

(* the seq fields of the table building, from seq *)
Lemma sit_teq_of_seq s t : seq s t -> sit_teq s t.
Proof. intros []. repeat split; auto. Qed.

(* lenlens_zero writes have and lens only, and they depend on have and lens only *)
Lemma sit_llz_shape k s :
  lenlens_zero k s = set_i_have (set_i_lens s (i_lens (lenlens_zero k s))) (i_have (lenlens_zero k s)).
Proof.
  revert s. induction k as [|k IH]; intros s; cbn [lenlens_zero].
  - destruct s; reflexivity.
  - destruct (i_have s <? 19); [|destruct s; reflexivity].
    rewrite IH at 1. destruct s; reflexivity.
Qed.

Lemma sit_llz_dep k s t : i_have s = i_have t -> i_lens s = i_lens t ->
  i_have (lenlens_zero k s) = i_have (lenlens_zero k t) /\ i_lens (lenlens_zero k s) = i_lens (lenlens_zero k t).
Proof.
  revert s t. induction k as [|k IH]; intros s t H L; cbn [lenlens_zero]; [auto|].
  rewrite H. destruct (i_have t <? 19); [|auto].
  apply IH; sit_cbn; congruence.
Qed.

(* lens_fill likewise *)
Lemma sit_fill_shape k len s :
  lens_fill k len s = set_i_have (set_i_lens s (i_lens (lens_fill k len s))) (i_have (lens_fill k len s)).
Proof.
  revert s. induction k as [|k IH]; intros s; cbn [lens_fill].
  - destruct s; reflexivity.
  - rewrite IH at 1. destruct s; reflexivity.
Qed.

Lemma sit_fill_dep k len s t : i_have s = i_have t -> i_lens s = i_lens t ->
  i_have (lens_fill k len s) = i_have (lens_fill k len t) /\ i_lens (lens_fill k len s) = i_lens (lens_fill k len t).
Proof.
  revert s t. induction k as [|k IH]; intros s t H L; cbn [lens_fill]; [auto|].
  apply IH; sit_cbn; congruence.
Qed.

Lemma sit_fill_have k len s : i_have (lens_fill k len s) = i_have s + Z.of_nat k.
Proof.
  revert s. induction k as [|k IH]; intros s; cbn [lens_fill]; [lia|].
  rewrite IH. sit_cbn. lia.
Qed.

(* inflate_table's call reads next, codes and lens *)
Lemma sit_call_table_ext type lo n req s t :
  i_next s = i_next t -> i_codes s = i_codes t -> i_lens s = i_lens t ->
  call_table type lo n req s = call_table type lo n req t.
Proof. intros A B C. unfold call_table. rewrite A, B, C. reflexivity. Qed.

(* a table entry reads codes *)
Lemma sit_tab_entry_ext fx dx s t : i_codes s = i_codes t -> tab_entry fx dx s = tab_entry fx dx t.
Proof. intros A. unfold tab_entry. rewrite A. reflexivity. Qed.

(* the bit buffer and the bit position do not see the istate, the output fields, ret, msg *)
Lemma sit_bb_s src P0 m s : bitbuf src P0 m -> bitbuf src P0 (set_m_s m s).
Proof. intros [B1 B2 B3 B4 B5 B6]. constructor; unfold mq in *; sit_cbn; auto. Qed.

Lemma sit_bb_bad src P0 m e : bitbuf src P0 m -> bitbuf src P0 (set_bad m e).
Proof. intros [B1 B2 B3 B4 B5 B6]. constructor; unfold mq in *; sit_cbn; auto. Qed.

Lemma sit_bb_ret src P0 m r : bitbuf src P0 m -> bitbuf src P0 (set_m_ret m r).
Proof. intros [B1 B2 B3 B4 B5 B6]. constructor; unfold mq in *; sit_cbn; auto. Qed.

Lemma sit_bb_leave src P0 m l : bitbuf src P0 m -> bitbuf src P0 (set_m_leave m l).
Proof. intros [B1 B2 B3 B4 B5 B6]. constructor; unfold mq in *; sit_cbn; auto. Qed.

(* the bits in the buffer end at the input consumed, within the call's input *)
Lemma sit_bb_end src P0 m : bitbuf src P0 m -> mq P0 m + m_bits m <= 8 * (P0 + Zlength (m_inp m)).
Proof. intros [B1 B2 B3 B4 B5 B6]. unfold mq. lia. Qed.

(* a root entry of a valid table has at most 15 bits *)
Lemma sit_root_bits kind get rb sz i : tvalid_g kind get rb sz -> 0 <= i < 2 ^ rb -> 0 <= e_bits (get i) <= 15.
Proof.
  intros [R S T] Hi. specialize (T i Hi). cbv zeta in T. destruct T as [E T].
  unfold entry_ok in E. destruct E as [E1 [E2 E3]].
  destruct (islink kind (e_op (get i))).
  - destruct T as (A1 & _). lia.
  - destruct T as [T1 _]. lia.
Qed.

(* an update of have and lens only *)
Lemma sit_hl_facts s h l : let s' := set_i_have (set_i_lens s l) h in
  sit_tsame s s' /\ sit_skeep s s' /\ i_mode s' = i_mode s /\ i_flags s' = i_flags s /\ i_check s' = i_check s.
Proof. cbv zeta. sit_cbn. repeat split. Qed.

Lemma sit_teq_hl s t h l : sit_teq s t -> sit_teq (set_i_have (set_i_lens s l) h) (set_i_have (set_i_lens t l) h).
Proof. intros (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11). sit_cbn. repeat split; auto. Qed.

Lemma sit_fill_facts k len s : let s' := lens_fill k len s in
  sit_tsame s s' /\ sit_skeep s s' /\ i_mode s' = i_mode s /\ i_flags s' = i_flags s /\ i_check s' = i_check s.
Proof. cbv zeta. rewrite sit_fill_shape. apply sit_hl_facts. Qed.

Lemma sit_teq_fill k len s t : sit_teq s t -> sit_teq (lens_fill k len s) (lens_fill k len t).
Proof.
  intros C. pose proof C as (_ & _ & _ & _ & _ & _ & _ & C8 & _ & C10 & _).
  destruct (sit_fill_dep k len s t C8 C10) as [D1 D2].
  rewrite (sit_fill_shape k len s), (sit_fill_shape k len t), D1, D2. apply sit_teq_hl. exact C.
Qed.

Lemma sit_llz_facts k s : let s' := lenlens_zero k s in
  sit_tsame s s' /\ sit_skeep s s' /\ i_mode s' = i_mode s /\ i_flags s' = i_flags s /\ i_check s' = i_check s.
Proof. cbv zeta. rewrite sit_llz_shape. apply sit_hl_facts. Qed.

Lemma sit_teq_llz k s t : sit_teq s t -> sit_teq (lenlens_zero k s) (lenlens_zero k t).
Proof.
  intros C. pose proof C as (_ & _ & _ & _ & _ & _ & _ & C8 & _ & C10 & _).
  destruct (sit_llz_dep k s t C8 C10) as [D1 D2].
  rewrite (sit_llz_shape k s), (sit_llz_shape k t), D1, D2. apply sit_teq_hl. exact C.
Qed.

Lemma sit_tsame_trans s1 s2 s3 : sit_tsame s1 s2 -> sit_tsame s2 s3 -> sit_tsame s1 s3.
Proof. unfold sit_tsame. intuition congruence. Qed.

Lemma sit_skeep_trans s1 s2 s3 : sit_skeep s1 s2 -> sit_skeep s2 s3 -> sit_skeep s1 s3.
Proof. unfold sit_skeep. intuition congruence. Qed.

(* DROPBITS(k) leaves bits - k bits *)
Lemma sit_bits_drop m k : 0 <= k <= m_bits m -> m_bits m <= 39 -> m_bits (dropbits k m) = m_bits m - k.
Proof.
  intros A B. unfold dropbits. sit_cbn. unfold u32. apply Z.mod_small.
  split; [lia|]. apply Z.le_lt_trans with 39; [lia|]. reflexivity.
Qed.

(* the cases of an abstract step written as nested tests: each is a step *)
Ltac sit_split_ea EA :=
  repeat (match type of EA with context [if ?c then _ else _] => destruct c end);
  cbn beta iota in EA; unfold abad, ago in EA.

(* the bit buffer depends only on the input, its position, hold and bits *)
Lemma sit_bb_eq src P0 m m' :
  m_inp m' = m_inp m -> m_nx m' = m_nx m -> m_bits m' = m_bits m -> m_hold m' = m_hold m ->
  bitbuf src P0 m -> bitbuf src P0 m'.
Proof.
  intros A B C D [H1 H2 H3 H4 H5 H6]. unfold mq in *.
  constructor; unfold mq; rewrite ?A, ?B, ?C, ?D; auto.
Qed.

(* the bit position at a loop head is within the call's input *)
Lemma sit_mq_end src P0 m : bitbuf src P0 m -> mq P0 m <= 8 * (P0 + Zlength (m_inp m)).
Proof. intros Hb. pose proof (sit_bb_end _ _ _ Hb). pose proof (bb_bits _ _ _ Hb). lia. Qed.

(* the leave flag under the setters (rewriting with these keeps the kernel from comparing whole records) *)
Lemma sit_leave_bad m e : m_leave (set_bad m e) = m_leave m.
Proof. reflexivity. Qed.
Lemma sit_leave_ret m r : m_leave (set_m_ret m r) = m_leave m.
Proof. reflexivity. Qed.
Lemma sit_leave_s m s : m_leave (set_m_s m s) = m_leave m.
Proof. reflexivity. Qed.
Lemma sit_leave_upd m f : m_leave (upd_s m f) = m_leave m.
Proof. reflexivity. Qed.
Lemma sit_leave_drop m k : m_leave (dropbits k m) = m_leave m.
Proof. reflexivity. Qed.
