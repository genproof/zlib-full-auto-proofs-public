(* The kit of the decode simulation (SISimDec.v): the goal of one pass (sim_ok's conclusion), the dispatch of
   the decode modes on both machines, abstract steps in front of the goal, the stops, and the transfer of the
   relation through the decode modes' state updates. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_split_invariant.SIDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The goal of a pass, for the input limit I and the output limit R                               *)

Definition dgoal (flush: Z) (src: list Z) (P0: Z) (O0: list Z) (I R: Z) (a: ast) (o: iout) : Prop :=
  match o with
  | IBrk m' => exists a', areach src I R a a' /\ rel src P0 O0 m' a' /\
                 (m_leave m' = 1 -> stop_ok flush src I R m' a')
  | IRet r m' => r = Z_NEED_DICT /\
                 exists a', areach src I R a a' /\ rel src P0 O0 m' a' /\
                 astep lenfix_list distfix_list src a' = AEnd Z_NEED_DICT
  end.

(* sim_ok P is dgoal of every pass from a related loop head in a mode of P *)
Lemma sim_ok_dgoal (P: Z -> Prop) :
  (forall flush src P0 O0 m a,
     rel src P0 O0 m a -> awf src a -> m_leave m = 0 -> P (m_mode m) ->
     dgoal flush src P0 O0 (P0 + Zlength (m_inp m)) (Zlength O0 + m_aout m) a
           (stepf2 flush lenfix_list distfix_list m)) ->
  sim_ok P.
Proof. intros H flush src P0 O0 m a Rl Aw L Pm. exact (H flush src P0 O0 m a Rl Aw L Pm). Qed.

Lemma dgoal_sim_ok (P: Z -> Prop) flush src P0 O0 m a :
  sim_ok P -> rel src P0 O0 m a -> awf src a -> m_leave m = 0 -> P (m_mode m) ->
  dgoal flush src P0 O0 (P0 + Zlength (m_inp m)) (Zlength O0 + m_aout m) a
        (stepf2 flush lenfix_list distfix_list m).
Proof. intros H Rl Aw L Pm. exact (H flush src P0 O0 m a Rl Aw L Pm). Qed.

(* the continuation: the pass goes on (a fall-through) in the next mode from a related state with the same
   input and output space *)
Lemma dcont (P: Z -> Prop) flush src P0 O0 m1 a1 I R :
  sim_ok P -> rel src P0 O0 m1 a1 -> awf src a1 -> m_leave m1 = 0 -> P (m_mode m1) ->
  I = P0 + Zlength (m_inp m1) -> R = Zlength O0 + m_aout m1 ->
  dgoal flush src P0 O0 I R a1 (stepf2 flush lenfix_list distfix_list m1).
Proof. intros H Rl Aw L Pm -> ->. apply (dgoal_sim_ok P); auto. Qed.

(* an abstract step within the limits in front of the goal *)
Lemma dgoal_step flush src P0 O0 I R a n w a1 o :
  astep lenfix_list distfix_list src a = AGo n w a1 -> ~ blocked I R a (AGo n w a1) ->
  dgoal flush src P0 O0 I R a1 o -> dgoal flush src P0 O0 I R a o.
Proof.
  intros S B G. destruct o as [m'|r m'].
  - destruct G as (a' & A & Rl & St). exists a'. split; [|auto]. eapply ar_step; eauto.
  - destruct G as (Er & a' & A & Rl & St). split; [exact Er|]. exists a'. split; [|auto]. eapply ar_step; eauto.
Qed.

(* a step that writes nothing and reads up to n <= 8 I *)
Lemma dgoal_go flush src P0 O0 I R a n a1 o :
  astep lenfix_list distfix_list src a = AGo n false a1 -> n <= 8 * I ->
  dgoal flush src P0 O0 I R a1 o -> dgoal flush src P0 O0 I R a o.
Proof.
  intros S N G. eapply dgoal_step; [exact S| |exact G].
  cbn [blocked]. intros [B|[B _]]; [lia|discriminate].
Qed.

(* a step that writes one byte, with output space left *)
Lemma dgoal_write flush src P0 O0 I R a n a1 o :
  astep lenfix_list distfix_list src a = AGo n true a1 -> n <= 8 * I -> Zlength (a_O a) < R ->
  dgoal flush src P0 O0 I R a1 o -> dgoal flush src P0 O0 I R a o.
Proof.
  intros S N W G. eapply dgoal_step; [exact S| |exact G].
  cbn [blocked]. intros [B|[_ B]]; lia.
Qed.

(* the pass ends here, at the related state itself *)
Lemma dgoal_here flush src P0 O0 I R a m' :
  rel src P0 O0 m' a -> (m_leave m' = 1 -> stop_ok flush src I R m' a) ->
  dgoal flush src P0 O0 I R a (IBrk m').
Proof. intros Rl St. exists a. split; [constructor|]. auto. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The stops                                                                                      *)

(* the call stops before a step that needs bits past the input *)
Lemma stop_need flush src I R m a n w a1 :
  astep lenfix_list distfix_list src a = AGo n w a1 -> 8 * I < n -> m_ret m = Z_OK ->
  stop_ok flush src I R m a.
Proof.
  intros S N Rt. unfold stop_ok. rewrite S. split; [exact Rt|]. right; right. left. cbn [blocked]. left; exact N.
Qed.

(* the call stops before a step that writes, with no output space left *)
Lemma stop_full flush src I R m a n a1 :
  astep lenfix_list distfix_list src a = AGo n true a1 -> R <= Zlength (a_O a) -> m_ret m = Z_OK ->
  stop_ok flush src I R m a.
Proof.
  intros S N Rt. unfold stop_ok. rewrite S. split; [exact Rt|]. right; right. left. cbn [blocked].
  right; split; [reflexivity|exact N].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The modes                                                                                      *)

Ltac dmd := unfold hdr_mode, data_mode, post_mode, win_mode, len_live, off_live, ext_live, decode_mode,
  HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT, Zlib.proof.inflate.Model.TYPE,
  TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, CHECK,
  LENGTH, DONE, BAD in *; lia.

Lemma bad_modes : ~ hdr_mode BAD /\ ~ data_mode BAD /\ ~ post_mode BAD /\ ~ win_mode BAD.
Proof. unfold data_mode, decode_mode, hdr_mode, post_mode, win_mode. vm_compute. lia. Qed.

(* the dispatch of the switch *)
Lemma stepf2_LEN_ flush fx dx m : m_mode m = LEN_ -> stepf2 flush fx dx m = c_LEN_ fx dx (fast fx dx) m.
Proof. intros E. unfold stepf2, step2. cbv zeta. rewrite E. reflexivity. Qed.
Lemma stepf2_LEN flush fx dx m : m_mode m = LEN -> stepf2 flush fx dx m = c_LEN fx dx (fast fx dx) m.
Proof. intros E. unfold stepf2, step2. cbv zeta. rewrite E. reflexivity. Qed.
Lemma stepf2_LENEXT flush fx dx m : m_mode m = LENEXT -> stepf2 flush fx dx m = c_LENEXT fx dx m.
Proof. intros E. unfold stepf2, step2. cbv zeta. rewrite E. reflexivity. Qed.
Lemma stepf2_DIST flush fx dx m : m_mode m = DIST -> stepf2 flush fx dx m = c_DIST fx dx m.
Proof. intros E. unfold stepf2, step2. cbv zeta. rewrite E. reflexivity. Qed.
Lemma stepf2_DISTEXT flush fx dx m : m_mode m = DISTEXT -> stepf2 flush fx dx m = c_DISTEXT m.
Proof. intros E. unfold stepf2, step2. cbv zeta. rewrite E. reflexivity. Qed.
Lemma stepf2_MATCH flush fx dx m : m_mode m = MATCH -> stepf2 flush fx dx m = c_MATCH m.
Proof. intros E. unfold stepf2, step2. cbv zeta. rewrite E. reflexivity. Qed.
Lemma stepf2_LIT flush fx dx m : m_mode m = LIT -> stepf2 flush fx dx m = c_LIT m.
Proof. intros E. unfold stepf2, step2. cbv zeta. rewrite E. reflexivity. Qed.

(* the abstract dispatch *)
Lemma astep_LEN_ fx dx src a : a_mode a = LEN_ -> astep fx dx src a = a_LEN_ a.
Proof. intros E. unfold astep. cbv zeta. rewrite E. reflexivity. Qed.
Lemma astep_LEN fx dx src a : a_mode a = LEN -> astep fx dx src a = a_LEN fx dx src a.
Proof. intros E. unfold astep. cbv zeta. rewrite E. reflexivity. Qed.
Lemma astep_LENEXT fx dx src a : a_mode a = LENEXT -> astep fx dx src a = a_LENEXT src a.
Proof. intros E. unfold astep. cbv zeta. rewrite E. reflexivity. Qed.
Lemma astep_DIST fx dx src a : a_mode a = DIST -> astep fx dx src a = a_DIST fx dx src a.
Proof. intros E. unfold astep. cbv zeta. rewrite E. reflexivity. Qed.
Lemma astep_DISTEXT fx dx src a : a_mode a = DISTEXT -> astep fx dx src a = a_DISTEXT src a.
Proof. intros E. unfold astep. cbv zeta. rewrite E. reflexivity. Qed.
Lemma astep_MATCH fx dx src a : a_mode a = MATCH -> astep fx dx src a = a_MATCH a.
Proof. intros E. unfold astep. cbv zeta. rewrite E. reflexivity. Qed.
Lemma astep_LIT fx dx src a : a_mode a = LIT -> astep fx dx src a = a_LIT a.
Proof. intros E. unfold astep. cbv zeta. rewrite E. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* seq through the decode modes' updates                                                          *)

(* a new mode: the fields it reads must agree *)
Lemma seq_mode s t v : seq s t ->
  (len_live v -> i_length s = i_length t) -> (off_live v -> i_offset s = i_offset t) ->
  (ext_live v -> i_extra s = i_extra t) -> seq (set_i_mode s v) (set_i_mode t v).
Proof. intros H L O E. destruct H; constructor; cbn; auto. Qed.

Lemma seq_length s t v : seq s t -> seq (set_i_length s v) (set_i_length t v).
Proof. intros H. destruct H; constructor; cbn; auto. Qed.

Lemma seq_offset s t v : seq s t -> seq (set_i_offset s v) (set_i_offset t v).
Proof. intros H. destruct H; constructor; cbn; auto. Qed.

Lemma seq_extra s t v : seq s t -> seq (set_i_extra s v) (set_i_extra t v).
Proof. intros H. destruct H; constructor; cbn; auto. Qed.

(* state->back and state->was (inflateMark's) live on the concrete side only *)
Lemma seq_back s t v : seq s t -> seq (set_i_back s v) t.
Proof. intros H. destruct H; constructor; cbn; auto. Qed.

Lemma seq_was s t v : seq s t -> seq (set_i_was s v) t.
Proof. intros H. destruct H; constructor; cbn; auto. Qed.

(* the tables are equal: the lookups read the same entries *)
Lemma tab_entry_seq fx dx s t tr i : seq s t -> tab_entry fx dx s tr i = tab_entry fx dx t tr i.
Proof. intros H. destruct tr; cbn; auto. rewrite (se_codes _ _ H). reflexivity. Qed.

Lemma adecode_seq fx dx src s t tr nb lk q : seq s t ->
  adecode fx dx src s tr nb lk q = adecode fx dx src t tr nb lk q.
Proof. intros H. unfold adecode. rewrite !(tab_entry_seq fx dx s t _ _ H). reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The bit buffer                                                                                 *)

(* the bit position is inside the call's input *)
Lemma mq_le src P0 m : bitbuf src P0 m -> mq P0 m <= 8 * (P0 + Zlength (m_inp m)).
Proof. intros [A B C D E F]. unfold mq. lia. Qed.

Lemma bitbuf_ext src P0 m m' :
  bitbuf src P0 m -> m_inp m' = m_inp m -> m_nx m' = m_nx m -> m_bits m' = m_bits m -> m_hold m' = m_hold m ->
  bitbuf src P0 m'.
Proof.
  intros [A B C D E F] Ei En Eb Eh. unfold mq in *.
  constructor; unfold mq; rewrite ?Ei, ?En, ?Eb, ?Eh; auto.
Qed.

Lemma mq_ext P0 m m' : m_nx m' = m_nx m -> m_bits m' = m_bits m -> mq P0 m' = mq P0 m.
Proof. intros En Eb. unfold mq. rewrite En, Eb. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The relation after a decode pass                                                               *)

(* the fields of the window *)
Definition win_eq (s t: istate) : Prop :=
  i_wsize s = i_wsize t /\ i_whave s = i_whave t /\ i_wnext s = i_wnext t /\ i_win s = i_win t /\
  i_wdata s = i_wdata t.

Lemma win_eq_refl s : win_eq s s.
Proof. unfold win_eq; auto. Qed.

Lemma swin_ok_eq s t O : win_eq s t -> swin_ok t O -> swin_ok s O.
Proof.
  intros (A & B & C & D & E). unfold swin_ok, swin_at. rewrite A, B, C, D, E. auto.
Qed.

Lemma decode_not_post md : decode_mode md \/ md = Zlib.proof.inflate.Model.TYPE ->
  ~ post_mode md /\ data_mode md /\ win_mode md /\ ~ hdr_mode md /\ md <> BAD /\ md <> DONE /\
  ~ (md = CHECK \/ md = LENGTH) /\ ~ (md = COPY_ \/ md = COPY).
Proof.
  intros [H| ->]; [unfold decode_mode in H; destruct H as [->|[->|[->|[->|[->|[->| ->]]]]]]|];
    unfold hdr_mode, data_mode, post_mode, win_mode, decode_mode; repeat split; vm_compute; try lia;
    intuition discriminate.
Qed.

(* from a decode loop head to a decode mode or TYPE (not BAD): the output may grow (ow' extends the bytes
   written), the check, the total and the window stay *)
Lemma rel_dec_next src P0 O0 m a m' a' :
  rel src P0 O0 m a -> decode_mode (m_mode m) ->
  bitbuf src P0 m' -> m_inp m' = m_inp m -> m_aout m' = m_aout m -> m_in m' = m_in m ->
  m_out m' = m_out m -> m_ret m' = m_ret m -> m_tout m' = m_tout m ->
  Zlength (m_ow m) <= Zlength (m_ow m') <= m_aout m ->
  m_mode m' = a_mode a' -> decode_mode (m_mode m') \/ m_mode m' = Zlib.proof.inflate.Model.TYPE ->
  a_q a' = mq P0 m' -> a_O a' = O0 ++ m_ow m' ->
  seq (m_s m') (a_s a') ->
  i_check (m_s m') = i_check (m_s m) -> i_flags (a_s a') = i_flags (a_s a) ->
  i_check (a_s a') = i_check (a_s a) -> i_wrap (m_s m') = i_wrap (m_s m) ->
  i_total (m_s m') = i_total (m_s m) -> win_eq (m_s m') (m_s m) -> i_head (m_s m') = false ->
  rel src P0 O0 m' a'.
Proof.
  intros Rl Hm BB Ei Ea Ein Eout Er Et Ow Md DM Q O S Ck Fl Ca Wr Tot W Hd.
  destruct (decode_not_post _ (or_introl Hm)) as (NP0 & DD0 & WM0 & NH0 & NB0 & ND0 & NC0 & NCp0).
  destruct (decode_not_post _ DM) as (NP & DD & WM & NH & NB & ND & NC & NCp).
  destruct Rl as [BB0 Md0 Q0 BO0 O0' Ao In Out Ret S0 Ch Tt Tout Win Hd0].
  unfold m_left in *.
  destruct Out as (O1 & O2 & O3). specialize (O3 (or_intror (or_introl DD0))).
  constructor.
  - exact BB.
  - exact Md.
  - intros _. exact Q.
  - unfold bits_ok. fold (m_mode m'). split; [intros P; exfalso; exact (NH P)|].
    split; intros P; exfalso; [exact (NCp P)|exact (NC P)].
  - exact O.
  - rewrite Ea. lia.
  - rewrite Ein, Ei. exact In.
  - unfold m_left. rewrite Eout, Ea. split; [lia|].
    split; [intros P; exfalso; exact (NP P)|intros _; exact O3].
  - intros _ _. rewrite Er. exact (Ret NB0 ND0).
  - intros _. exact S.
  - split; [intros P; exfalso; exact (NH P)|].
    intros _ Wn. rewrite Ck, Fl, Ca. apply (proj2 Ch DD0). rewrite <- Wr. exact Wn.
  - split; [intros _; rewrite Tot; exact (proj1 Tt (or_intror (or_introl DD0)))|intros P; exfalso; exact (NP P)].
  - unfold m_left. rewrite Et, Tout, Eout, Ea, O3. f_equal. lia.
  - intros _. apply swin_ok_eq with (m_s m); [exact W|]. apply Win. exact WM0.
  - exact Hd.
Qed.

(* from a decode loop head to BAD *)
Lemma rel_dec_bad src P0 O0 m a m' a' :
  rel src P0 O0 m a ->
  bitbuf src P0 m' -> m_inp m' = m_inp m -> m_aout m' = m_aout m -> m_ow m' = m_ow m -> m_in m' = m_in m ->
  m_out m' = m_out m -> m_tout m' = m_tout m ->
  m_mode m' = BAD -> a_mode a' = BAD -> a_O a' = a_O a -> i_head (m_s m') = false ->
  rel src P0 O0 m' a'.
Proof.
  intros Rl BB Ei Ea Eo Ein Eout Et Md Ma O Hd.
  destruct bad_modes as (B1 & B2 & B3 & B4).
  destruct Rl as [BB0 Md0 Q0 BO0 O0' Ao In Out Ret S0 Ch Tt Tout Win Hd0].
  unfold m_left in *.
  constructor.
  - exact BB.
  - rewrite Md, Ma. reflexivity.
  - intros N. exfalso. exact (N Md).
  - unfold bits_ok. unfold m_mode in Md. rewrite Md.
    split; [intros P; exfalso; auto|]. split; intros [E|E]; discriminate.
  - rewrite O, O0', Eo. reflexivity.
  - rewrite Eo, Ea. exact Ao.
  - rewrite Ein, Ei. exact In.
  - unfold m_left. rewrite Eout, Ea, Eo. destruct Out as (O1 & O2 & O3). split; [exact O1|].
    rewrite Md. split; [intros P; exfalso; auto|]. intros [P|[P|[P _]]]; exfalso; auto.
  - intros N. exfalso. exact (N Md).
  - intros N. exfalso. exact (N Md).
  - rewrite Md. split; intros P; exfalso; auto.
  - rewrite Md. split; [intros [P|[P|[P _]]]; exfalso; auto|intros P; exfalso; auto].
  - unfold m_left. rewrite Et, Tout, Eo, Eout, Ea. reflexivity.
  - rewrite Md. intros P; exfalso; auto.
  - exact Hd.
Qed.

(* a NEEDBITS / lookup that only pulls bytes (and may leave) keeps the relation *)
Lemma rel_bits src P0 O0 m a nx h b lv :
  rel src P0 O0 m a -> m_mode m <> BAD -> bits_ok (m_s m) b ->
  bitbuf src P0 (set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx) h) b) lv) ->
  mq P0 (set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx) h) b) lv) = mq P0 m ->
  rel src P0 O0 (set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx) h) b) lv) a.
Proof.
  intros Rl NB BO BB Q.
  destruct Rl as [BB0 Md0 Q0 BO0 O0' Ao In Out Ret S0 Ch Tt Tout Win Hd0].
  constructor; cbn [m_mode m_s m_ow m_aout m_in m_inp m_out m_ret m_tout set_m_leave set_m_bits set_m_hold
                    set_m_nx] in *; unfold m_mode, m_left in *; cbn [m_s m_ow m_aout set_m_leave set_m_bits
                    set_m_hold set_m_nx] in *; auto.
  intros _. rewrite Q. exact (Q0 NB).
Qed.

(* bits_ok holds for any buffer in the decode modes *)
Lemma bits_ok_dec s b : decode_mode (i_mode s) -> bits_ok s b.
Proof.
  intros H. destruct (decode_not_post _ (or_introl H)) as (_ & _ & _ & NH & _ & _ & NC & NCp).
  unfold bits_ok. split; [intros P; exfalso; exact (NH P)|].
  split; intros P; exfalso; [exact (NCp P)|exact (NC P)].
Qed.

(* awf after a step *)
Lemma awf_go src a n w a1 :
  awf_stmt -> awf src a -> astep lenfix_list distfix_list src a = AGo n w a1 -> awf src a1.
Proof. intros (_ & A & _) Aw S. eapply A; eauto. Qed.

(* a case whose pass falls through into the modes of Q *)
Definition dcase_next (X: Z) (Q: Z -> Prop) : Prop :=
  kit_stmt -> awf_stmt -> sim_ok Q -> sim_ok (fun md => md = X).
