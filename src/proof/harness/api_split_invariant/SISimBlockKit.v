(* Small facts for the simulation of the block modes (SISimBlock.v): the cases of the two machines in each
   mode, traces of several abstract steps, the istate fields kept by the setters, the check value of a
   concatenation, and NEEDBITS(32) from a whole number of bytes. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.crc32.Combine.
Require Import Zlib.proof.harness.api_split_invariant.SIDefs.
Import ListNotations.
Local Open Scope Z_scope.

Local Notation MTYPE := Zlib.proof.inflate.Model.TYPE.

(* ---------------------------------------------------------------------------------------------- *)
(* The case of each machine in a block mode                                                       *)

Section Cases.
Variables (flush: Z) (m: mst).

Lemma sib_c_TYPE : m_mode m = MTYPE -> stepf2 flush lenfix_list distfix_list m = c_TYPE flush m.
Proof. intros E. unfold stepf2, step2. rewrite E. reflexivity. Qed.
Lemma sib_c_TYPEDO : m_mode m = TYPEDO ->
  stepf2 flush lenfix_list distfix_list m = c_TYPEDO flush m.
Proof. intros E. unfold stepf2, step2. rewrite E. reflexivity. Qed.
Lemma sib_c_STORED : m_mode m = STORED ->
  stepf2 flush lenfix_list distfix_list m = c_STORED flush m.
Proof. intros E. unfold stepf2, step2. rewrite E. reflexivity. Qed.
Lemma sib_c_COPY_ : m_mode m = COPY_ -> stepf2 flush lenfix_list distfix_list m = c_COPY_ m.
Proof. intros E. unfold stepf2, step2. rewrite E. reflexivity. Qed.
Lemma sib_c_COPY : m_mode m = COPY -> stepf2 flush lenfix_list distfix_list m = c_COPY m.
Proof. intros E. unfold stepf2, step2. rewrite E. reflexivity. Qed.
Lemma sib_c_CHECK : m_mode m = CHECK -> stepf2 flush lenfix_list distfix_list m = c_CHECK m.
Proof. intros E. unfold stepf2, step2. rewrite E. reflexivity. Qed.
Lemma sib_c_LENGTH : m_mode m = LENGTH -> stepf2 flush lenfix_list distfix_list m = c_LENGTH m.
Proof. intros E. unfold stepf2, step2. rewrite E. reflexivity. Qed.
Lemma sib_c_DONE : m_mode m = DONE -> stepf2 flush lenfix_list distfix_list m = c_DONE m.
Proof. intros E. unfold stepf2, step2. rewrite E. reflexivity. Qed.
Lemma sib_c_BAD : m_mode m = BAD -> stepf2 flush lenfix_list distfix_list m = c_BAD m.
Proof. intros E. unfold stepf2, step2. rewrite E. reflexivity. Qed.
End Cases.

Section ACases.
Variables (src: list Z) (a: ast).

Lemma sib_a_TYPE : a_mode a = MTYPE -> astep lenfix_list distfix_list src a = a_TYPE a.
Proof. intros E. unfold astep. rewrite E. reflexivity. Qed.
Lemma sib_a_TYPEDO : a_mode a = TYPEDO -> astep lenfix_list distfix_list src a = a_TYPEDO src a.
Proof. intros E. unfold astep. rewrite E. reflexivity. Qed.
Lemma sib_a_STORED : a_mode a = STORED -> astep lenfix_list distfix_list src a = a_STORED src a.
Proof. intros E. unfold astep. rewrite E. reflexivity. Qed.
Lemma sib_a_COPY_ : a_mode a = COPY_ -> astep lenfix_list distfix_list src a = a_COPY_ a.
Proof. intros E. unfold astep. rewrite E. reflexivity. Qed.
Lemma sib_a_COPY : a_mode a = COPY -> astep lenfix_list distfix_list src a = a_COPY src a.
Proof. intros E. unfold astep. rewrite E. reflexivity. Qed.
Lemma sib_a_CHECK : a_mode a = CHECK -> astep lenfix_list distfix_list src a = a_CHECK src a.
Proof. intros E. unfold astep. rewrite E. reflexivity. Qed.
Lemma sib_a_LENGTH : a_mode a = LENGTH -> astep lenfix_list distfix_list src a = a_LENGTH src a.
Proof. intros E. unfold astep. rewrite E. reflexivity. Qed.
Lemma sib_a_DONE : a_mode a = DONE -> astep lenfix_list distfix_list src a = AEnd Z_STREAM_END.
Proof. intros E. unfold astep. rewrite E. reflexivity. Qed.
Lemma sib_a_BAD : a_mode a = BAD -> astep lenfix_list distfix_list src a = AEnd Z_DATA_ERROR.
Proof. intros E. unfold astep. rewrite E. reflexivity. Qed.
End ACases.

(* ---------------------------------------------------------------------------------------------- *)
(* Traces                                                                                         *)

Lemma sib_ar_trans src I R a b c : areach src I R a b -> areach src I R b c -> areach src I R a c.
Proof.
  induction 1 as [a|a n w a1 a' S B _ IH]; intros H; [exact H|].
  eapply ar_step; eauto.
Qed.

(* one step that reads up to n <= 8 I and writes nothing, or writes below R *)
Lemma sib_ar1 src I R a n w a1 :
  astep lenfix_list distfix_list src a = AGo n w a1 -> n <= 8 * I ->
  (w = true -> Zlength (a_O a) < R) -> areach src I R a a1.
Proof.
  intros S N W. eapply ar_step; [exact S| |apply ar_refl].
  cbn. intros [B|[B1 B2]]; [lia|]. specialize (W B1). lia.
Qed.

(* a step followed by a trace *)
Lemma sib_ar_cons src I R a n w a1 a' :
  astep lenfix_list distfix_list src a = AGo n w a1 -> n <= 8 * I ->
  (w = true -> Zlength (a_O a) < R) -> areach src I R a1 a' -> areach src I R a a'.
Proof. intros S N W T. eapply sib_ar_trans; [eapply sib_ar1; eauto|exact T]. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The check value of a concatenation                                                             *)

Lemma sib_check_app fl c A B :
  bytes_ok A -> (fl = 0 -> adler_valid c) ->
  update_check fl (update_check fl c A) B = update_check fl c (A ++ B).
Proof.
  intros HA HV. unfold update_check. destruct (Z.eqb_spec fl 0) as [E|E].
  - specialize (HV E). rewrite (adler32_z_val_ref c A HV).
    rewrite adler32_z_val_ref by (apply ref_adler32_valid; exact HV).
    rewrite adler32_z_val_ref by exact HV. apply ref_adler32_app; exact HV.
  - apply ref_crc32_app. exact HA.
Qed.

Lemma sib_adler_valid1 : adler_valid 1.
Proof. unfold adler_valid, adler_lo, adler_hi, ADLER_BASE. cbn. lia. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* NEEDBITS(32) from a whole number of bytes ends with exactly 32 bits                            *)

Lemma sib_pull_bits m : 0 <= m_bits m <= 31 -> m_bits (pull m) = m_bits m + 8.
Proof. intros B. unfold pull, set_m_bits. cbn [m_bits]. unfold u32. rewrite Z.mod_small; lia. Qed.

Lemma sib_needbits32_f k m :
  0 <= m_bits m <= 32 -> m_bits m mod 8 = 0 -> 32 - m_bits m <= 8 * Z.of_nat k ->
  m_leave (needbits_f k 32 m) = 0 -> m_bits (needbits_f k 32 m) = 32.
Proof.
  revert m. induction k as [|k IH]; intros m B M K L; cbn [needbits_f] in *; [lia|].
  destruct (Z.ltb_spec (m_bits m) 32) as [Lt|Ge]; [|lia].
  destruct (m_have m =? 0); [cbn in L; discriminate|].
  assert (P: m_bits (pull m) = m_bits m + 8) by (apply sib_pull_bits; lia).
  rewrite Nat2Z.inj_succ in K.
  assert (B24: m_bits m <= 24) by (pose proof (Z.div_mod (m_bits m) 8 ltac:(lia)); rewrite M in *; lia).
  apply IH; [rewrite P; lia | rewrite P; rewrite Z.add_mod by lia; rewrite M; reflexivity | rewrite P; lia | exact L].
Qed.

Lemma sib_needbits32_bits m :
  0 <= m_bits m <= 32 -> m_bits m mod 8 = 0 -> m_leave (needbits 32 m) = 0 -> m_bits (needbits 32 m) = 32.
Proof. intros B M L. apply sib_needbits32_f; auto. cbn. lia. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The bit buffer depends only on the input, its position, hold and bits                         *)

Lemma sib_bb_ext src P0 m m' :
  m_inp m' = m_inp m -> m_nx m' = m_nx m -> m_bits m' = m_bits m -> m_hold m' = m_hold m ->
  bitbuf src P0 m -> bitbuf src P0 m'.
Proof.
  intros A B C D [H1 H2 H3 H4 H5 H6]. unfold mq in *.
  constructor; unfold mq; rewrite ?A, ?B, ?C, ?D; auto.
Qed.

Lemma sib_mq_ext P0 m m' : m_nx m' = m_nx m -> m_bits m' = m_bits m -> mq P0 m' = mq P0 m.
Proof. intros A B. unfold mq. rewrite A, B. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Modes                                                                                          *)

Ltac sib_md :=
  unfold win_mode, hdr_mode, data_mode, post_mode, len_live, off_live, ext_live, decode_mode,
    HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT, MTYPE, TYPEDO, STORED, COPY_, COPY,
    TABLE, LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, CHECK, LENGTH, DONE, BAD, MEM in *;
  lia.
(* the same on the goal only *)
Ltac sib_mdg :=
  unfold win_mode, hdr_mode, data_mode, post_mode, len_live, off_live, ext_live, decode_mode,
    HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT, MTYPE, TYPEDO, STORED, COPY_, COPY,
    TABLE, LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, CHECK, LENGTH, DONE, BAD, MEM;
  lia.

(* ---------------------------------------------------------------------------------------------- *)
(* The window depends only on its fields                                                          *)

Lemma sib_swin_ext s s' O :
  i_wsize s' = i_wsize s -> i_whave s' = i_whave s -> i_wnext s' = i_wnext s -> i_win s' = i_win s ->
  i_wdata s' = i_wdata s -> swin_ok s O -> swin_ok s' O.
Proof.
  intros A B C D E W. unfold swin_ok, swin_at in *. rewrite A, B, C, D, E. exact W.
Qed.

(* the projections of the machine setters *)
Ltac sib_cbn := cbn [m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler m_msg m_tin
  m_tout m_snx m_sow set_m_s set_m_h set_m_inp set_m_aout set_m_nx set_m_ow set_m_hold set_m_bits set_m_in
  set_m_out set_m_ret set_m_leave set_m_adler set_m_msg set_m_tin set_m_tout set_m_snx set_m_sow
  m_mode upd_s set_mode set_leave set_bad a_s a_q a_O a_mode
  i_mode i_last i_wrap i_havedict i_flags i_dmax i_check i_total i_head i_wbits i_wsize i_whave i_wnext i_win i_wdata i_hold i_bits i_length i_offset i_extra i_lencode i_distcode i_lenbits i_distbits i_ncode i_nlen i_ndist i_have i_next i_lens i_codes i_sane i_back i_was
  set_i_mode set_i_last set_i_wrap set_i_havedict set_i_flags set_i_dmax set_i_check set_i_total set_i_head set_i_wbits set_i_wsize set_i_whave set_i_wnext set_i_win set_i_wdata set_i_hold set_i_bits set_i_length set_i_offset set_i_extra set_i_lencode set_i_distcode set_i_lenbits set_i_distbits set_i_ncode set_i_nlen set_i_ndist set_i_have set_i_next set_i_lens set_i_codes set_i_sane set_i_back set_i_was] in *.

(* a step of the bit buffer only (NEEDBITS, a lookup): the relation holds with the same abstract state *)
Lemma sib_rel_bits src P0 O0 m a nx h b l :
  rel src P0 O0 m a ->
  bitbuf src P0 (set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx) h) b) l) ->
  mq P0 (set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx) h) b) l) = mq P0 m ->
  bits_ok (m_s m) b ->
  rel src P0 O0 (set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx) h) b) l) a.
Proof.
  intros R BB Q Bk. destruct R. unfold m_left in *. constructor; sib_cbn; auto.
  intros X. rewrite Q. auto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* What sim_ok says of the outcome o of one pass, from the abstract state a (I, R: the limits)    *)

Definition sib_out (flush: Z) (src: list Z) (P0: Z) (O0: list Z) (I R: Z) (a: ast) (o: iout) : Prop :=
  match o with
  | IBrk m' => exists a', areach src I R a a' /\ rel src P0 O0 m' a' /\
                 (m_leave m' = 1 -> stop_ok flush src I R m' a')
  | IRet r m' => r = Z_NEED_DICT /\
                 exists a', areach src I R a a' /\ rel src P0 O0 m' a' /\
                   astep lenfix_list distfix_list src a' = AEnd Z_NEED_DICT
  end.

(* free steps first *)
Lemma sib_out_pre flush src P0 O0 I R a a1 o :
  areach src I R a a1 -> sib_out flush src P0 O0 I R a1 o -> sib_out flush src P0 O0 I R a o.
Proof.
  intros T. destruct o as [m'|r m']; cbn.
  - intros (a' & T' & H). exists a'. split; [eapply sib_ar_trans; eauto|exact H].
  - intros (E & a' & T' & H). split; [exact E|]. exists a'. split; [eapply sib_ar_trans; eauto|exact H].
Qed.

(* the outcome without a step: the abstract state does not move *)
Lemma sib_out_stay flush src P0 O0 I R a m' :
  rel src P0 O0 m' a -> (m_leave m' = 1 -> stop_ok flush src I R m' a) ->
  sib_out flush src P0 O0 I R a (IBrk m').
Proof. intros H S. exists a. split; [apply ar_refl|auto]. Qed.

(* the case of a mode: from a related loop head in mode md *)
Definition sib_case (md: Z) : Prop :=
  forall flush src P0 O0 m a,
    rel src P0 O0 m a -> awf src a -> m_leave m = 0 -> m_mode m = md ->
    sib_out flush src P0 O0 (P0 + Zlength (m_inp m)) (Zlength O0 + m_aout m) a
      (stepf2 flush lenfix_list distfix_list m).

Lemma sib_sim_ok (P: Z -> Prop) :
  (forall md, P md -> sib_case md) -> sim_ok P.
Proof.
  intros C flush src P0 O0 m a R W L M. exact (C _ M flush src P0 O0 m a R W L eq_refl).
Qed.

Lemma sib_rel_leave src P0 O0 m a l : rel src P0 O0 m a -> rel src P0 O0 (set_m_leave m l) a.
Proof.
  intros R. destruct R. unfold m_left, mq in *. constructor; sib_cbn; auto.
  eapply sib_bb_ext; [..|eassumption]; reflexivity.
Qed.

Lemma sib_rel_ret src P0 O0 m a r :
  rel src P0 O0 m a -> (m_mode m <> BAD -> m_mode m <> DONE -> r = Z_OK) -> rel src P0 O0 (set_m_ret m r) a.
Proof.
  intros R E. destruct R. unfold m_left, mq in *. constructor; sib_cbn; auto.
  eapply sib_bb_ext; [..|eassumption]; reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The equal fields under the setters both machines apply                                         *)

Lemma sib_seq_mode s t v :
  seq s t -> (len_live v -> i_length s = i_length t) -> (off_live v -> i_offset s = i_offset t) ->
  (ext_live v -> i_extra s = i_extra t) -> seq (set_i_mode s v) (set_i_mode t v).
Proof. intros [] A B C. constructor; cbn; auto. Qed.

(* a mode that reads none of length, offset, extra *)
Lemma sib_seq_mode0 s t v :
  seq s t -> ~ len_live v -> ~ off_live v -> ~ ext_live v -> seq (set_i_mode s v) (set_i_mode t v).
Proof. intros S A B C. apply sib_seq_mode; tauto. Qed.

Lemma sib_seq_last s t v : seq s t -> seq (set_i_last s v) (set_i_last t v).
Proof. intros []. constructor; cbn; auto. Qed.
Lemma sib_seq_length s t v : seq s t -> seq (set_i_length s v) (set_i_length t v).
Proof. intros []. constructor; cbn; auto. Qed.
Lemma sib_seq_lencode s t v : seq s t -> seq (set_i_lencode s v) (set_i_lencode t v).
Proof. intros []. constructor; cbn; auto. Qed.
Lemma sib_seq_distcode s t v : seq s t -> seq (set_i_distcode s v) (set_i_distcode t v).
Proof. intros []. constructor; cbn; auto. Qed.
Lemma sib_seq_lenbits s t v : seq s t -> seq (set_i_lenbits s v) (set_i_lenbits t v).
Proof. intros []. constructor; cbn; auto. Qed.
Lemma sib_seq_distbits s t v : seq s t -> seq (set_i_distbits s v) (set_i_distbits t v).
Proof. intros []. constructor; cbn; auto. Qed.
(* the check value is not one of them *)
Lemma sib_seq_check_l s t v : seq s t -> seq (set_i_check s v) t.
Proof. intros []. constructor; cbn; auto. Qed.
Lemma sib_seq_check_r s t v : seq s t -> seq s (set_i_check t v).
Proof. intros []. constructor; cbn; auto. Qed.
Lemma sib_seq_total_l s t v : seq s t -> seq (set_i_total s v) t.
Proof. intros []. constructor; cbn; auto. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Mode classes                                                                                   *)

Lemma sib_data_not_post x : data_mode x -> ~ post_mode x.
Proof. sib_md. Qed.
Lemma sib_data_not_hdr x : data_mode x -> ~ hdr_mode x.
Proof. sib_md. Qed.
Lemma sib_data_not_bad x : data_mode x -> x <> BAD.
Proof. sib_md. Qed.
Lemma sib_bad_cls : ~ hdr_mode BAD /\ ~ data_mode BAD /\ ~ post_mode BAD /\ ~ win_mode BAD.
Proof. sib_md. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* A step between data modes (or to BAD) that writes nothing                                      *)

Lemma sib_rel_dstep src P0 O0 m a m' a' :
  rel src P0 O0 m a -> data_mode (m_mode m) -> m_mode m <> CHECK ->
  bitbuf src P0 m' -> bits_ok (m_s m') (m_bits m') ->
  m_inp m' = m_inp m -> m_aout m' = m_aout m -> m_ow m' = m_ow m -> m_in m' = m_in m ->
  m_out m' = m_out m -> m_tout m' = m_tout m -> m_ret m' = m_ret m ->
  m_mode m' = a_mode a' -> (m_mode m' = BAD \/ data_mode (m_mode m')) ->
  (m_mode m' <> BAD -> a_q a' = mq P0 m') -> a_O a' = a_O a ->
  (m_mode m' <> BAD -> seq (m_s m') (a_s a')) ->
  i_check (m_s m') = i_check (m_s m) -> i_check (a_s a') = i_check (a_s a) ->
  i_flags (a_s a') = i_flags (a_s a) -> i_wrap (m_s m') = i_wrap (m_s m) ->
  i_total (m_s m') = i_total (m_s m) ->
  i_wsize (m_s m') = i_wsize (m_s m) -> i_whave (m_s m') = i_whave (m_s m) ->
  i_wnext (m_s m') = i_wnext (m_s m) -> i_win (m_s m') = i_win (m_s m) ->
  i_wdata (m_s m') = i_wdata (m_s m) -> i_head (m_s m') = i_head (m_s m) ->
  rel src P0 O0 m' a'.
Proof.
  intros R D NC BB Bk Ei Ea Eo Ein Eout Et Er Md Cl Q EO S Ec Eca Ef Ew Etot Ws Wh Wn Wi Wd Hd.
  assert (ND: m_mode m <> BAD) by (apply sib_data_not_bad; exact D).
  assert (NP: ~ post_mode (m_mode m')).
  { destruct Cl as [C|C]; [rewrite C; apply sib_bad_cls|apply sib_data_not_post; exact C]. }
  assert (NH: ~ hdr_mode (m_mode m')).
  { destruct Cl as [C|C]; [rewrite C; apply sib_bad_cls|apply sib_data_not_hdr; exact C]. }
  destruct R. unfold m_left in *.
  constructor.
  - exact BB.
  - exact Md.
  - exact Q.
  - exact Bk.
  - rewrite EO, Eo. exact rl_O.
  - rewrite Eo, Ea. exact rl_aout.
  - rewrite Ein, Ei. exact rl_in.
  - unfold m_left. rewrite Eout, Ea, Eo. split; [lia|]. split; [intros X; contradiction|].
    intros _. apply rl_out. auto.
  - intros _ _. rewrite Er. apply rl_ret; [exact ND|].
    intros C. apply (sib_data_not_post _ D). rewrite C. unfold post_mode. right. reflexivity.
  - exact S.
  - split; [intros X; contradiction|].
    intros X W. destruct rl_chk as [_ C]. rewrite Ec, Eca, Ef. rewrite Ew in W. auto.
  - rewrite Etot. split; [intros _; apply rl_tot; auto|intros X; contradiction].
  - unfold m_left. rewrite Et, Eout, Ea, Eo. exact rl_tout.
  - intros X. eapply sib_swin_ext; eauto. apply rl_win. unfold win_mode. right. split; auto.
  - rewrite Hd. exact rl_head.
Qed.

Lemma sib_mode_mode s x y : set_i_mode (set_i_mode s x) y = set_i_mode s y.
Proof. reflexivity. Qed.

(* the modes that put no condition on the bit count *)
Lemma sib_bits_free s b :
  ~ hdr_mode (i_mode s) -> i_mode s <> COPY_ -> i_mode s <> COPY -> i_mode s <> CHECK -> i_mode s <> LENGTH ->
  bits_ok s b.
Proof.
  intros A B C D E. unfold bits_ok. cbv zeta. split; [|split]; intros X; [contradiction| |]; destruct X; contradiction.
Qed.

Lemma sib_bytebits_bits m : 0 <= m_bits m ->
  m_bits (bytebits m) mod 8 = 0 /\ 0 <= m_bits (bytebits m) <= m_bits m.
Proof.
  intros B. unfold bytebits, set_m_bits. cbn [m_bits].
  pose proof (Z.mod_pos_bound (m_bits m) 8 ltac:(lia)). pose proof (Z.mod_le (m_bits m) 8 B ltac:(lia)).
  split; [|lia]. rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia. reflexivity.
Qed.

Lemma sib_align8_le k b : 0 <= b -> align8 (8 * k - b) <= 8 * k.
Proof.
  intros B. unfold align8.
  assert ((8 * k - b + 7) / 8 <= k) by (apply Z.lt_succ_r; apply Z.div_lt_upper_bound; lia). lia.
Qed.

Lemma sib_align8_ge q : q <= align8 q.
Proof.
  unfold align8. pose proof (Z.div_mod (q + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (q + 7) 8 ltac:(lia)). lia.
Qed.

(* the bit position is in the call's input *)
Lemma sib_mq_le src P0 m : bitbuf src P0 m -> mq P0 m <= 8 * (P0 + Zlength (m_inp m)).
Proof. intros []. unfold mq. lia. Qed.

(* a step that writes nothing *)
Lemma sib_ar1f src I R a n a1 :
  astep lenfix_list distfix_list src a = AGo n false a1 -> n <= 8 * I -> areach src I R a a1.
Proof. intros S N. eapply sib_ar1; [exact S|exact N|discriminate]. Qed.

(* the concrete mode does not count in seq *)
Lemma sib_seq_lmode s t v : seq (set_i_mode s v) t -> seq s t.
Proof. intros []. constructor; cbn in *; auto. Qed.

Lemma sib_a_LEN_ src a : a_mode a = LEN_ -> astep lenfix_list distfix_list src a = a_LEN_ a.
Proof. intros E. unfold astep. rewrite E. reflexivity. Qed.
Lemma sib_a_TABLE src a : a_mode a = TABLE -> astep lenfix_list distfix_list src a = a_TABLE src a.
Proof. intros E. unfold astep. rewrite E. reflexivity. Qed.

Lemma sib_dropbits_bits k m : 0 <= k <= m_bits m -> m_bits m <= 39 -> m_bits (dropbits k m) = m_bits m - k.
Proof.
  intros B C. unfold dropbits, set_m_bits. cbn [m_bits]. unfold u32. apply Z.mod_small. lia.
Qed.

Lemma sib_dropbits_fields k m :
  m_s (dropbits k m) = m_s m /\ m_inp (dropbits k m) = m_inp m /\ m_nx (dropbits k m) = m_nx m /\
  m_aout (dropbits k m) = m_aout m /\ m_ow (dropbits k m) = m_ow m /\ m_in (dropbits k m) = m_in m /\
  m_out (dropbits k m) = m_out m /\ m_tout (dropbits k m) = m_tout m /\ m_ret (dropbits k m) = m_ret m /\
  m_leave (dropbits k m) = m_leave m.
Proof. unfold dropbits. sib_cbn. repeat split. Qed.

(* the loop goes on (no stop to justify) *)
Lemma sib_out_go flush src P0 O0 I R a a' m' :
  areach src I R a a' -> rel src P0 O0 m' a' -> m_leave m' = 0 -> sib_out flush src P0 O0 I R a (IBrk m').
Proof. intros T H L. exists a'. split; [exact T|]. split; [exact H|]. intros X. rewrite L in X. discriminate. Qed.

Lemma sib_align8_mod q : align8 q mod 8 = 0.
Proof. unfold align8. apply Z_mod_mult. Qed.

Lemma sib_align8_id q : q mod 8 = 0 -> align8 q = q.
Proof.
  intros H. unfold align8. pose proof (Z.div_mod q 8 ltac:(lia)). rewrite H in *.
  replace (q + 7) with (q / 8 * 8 + 7) by lia. rewrite Z.div_add_l by lia. change (7 / 8) with 0. lia.
Qed.

(* a step of the bit buffer only, which may move the bit position (BYTEBITS, NEEDBITS): the abstract
   state at the new position *)
Lemma sib_rel_bq src P0 O0 m a m' :
  rel src P0 O0 m a -> m_mode m <> BAD -> bitbuf src P0 m' -> bits_ok (m_s m) (m_bits m') ->
  m_s m' = m_s m -> m_inp m' = m_inp m -> m_aout m' = m_aout m -> m_ow m' = m_ow m -> m_in m' = m_in m ->
  m_out m' = m_out m -> m_tout m' = m_tout m -> m_ret m' = m_ret m ->
  rel src P0 O0 m' (AS (a_s a) (mq P0 m') (a_O a)).
Proof.
  intros R NB BB Bk Es Ei Ea Eo Ein Eout Et Er. destruct R. unfold m_left, m_mode, a_mode in *.
  constructor; unfold m_left, m_mode, a_mode; cbn [a_s a_q a_O];
    rewrite ?Es, ?Ei, ?Ea, ?Eo, ?Ein, ?Eout, ?Et, ?Er; auto.
Qed.
