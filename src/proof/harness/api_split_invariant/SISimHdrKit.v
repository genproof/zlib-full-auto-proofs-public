(* The kit of the header simulation (SISimHdr.v): the goal of one pass from a header mode, the bit buffer
   at a header loop head, the transfer of the relation through the header modes' state updates, and
   NEEDBITS of a whole header field. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.crc32.Combine.
Require Import Zlib.proof.harness.api_split_invariant.SIDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The bit buffer at a header loop head                                                           *)

(* A fixed-width header field is read by NEEDBITS(n) and INITBITS, which drops every bit of the buffer:
   at a loop head the buffer holds fewer bits than the field (whole bytes); the string modes read the
   input bytes directly, with an empty buffer, and so does EXLEN without an extra field (it falls through
   to the name). *)
Definition hbits (m: mst) : Prop :=
  hdr_mode (m_mode m) ->
  m_bits m mod 8 = 0 /\ m_bits m < (if orb (m_mode m =? TIME) (m_mode m =? DICTID) then 32 else 16) /\
  (m_mode m = EXTRA \/ m_mode m = NAME \/ m_mode m = COMMENT \/
   (m_mode m = EXLEN /\ Z.land (i_flags (m_s m)) 1024 = 0) -> m_bits m = 0).

Definition hrel (src: list Z) (P0: Z) (O0: list Z) (m: mst) (a: ast) : Prop :=
  rel src P0 O0 m a /\ hbits m.

(* ---------------------------------------------------------------------------------------------- *)
(* The goal of a pass (sim_ok's conclusion), for the input limit I and the output limit R          *)

Definition hgoal (flush: Z) (src: list Z) (P0: Z) (O0: list Z) (I R: Z) (a: ast) (o: iout) : Prop :=
  match o with
  | IBrk m' => exists a', areach src I R a a' /\ hrel src P0 O0 m' a' /\
                 (m_leave m' = 1 -> stop_ok flush src I R m' a')
  | IRet r m' => r = Z_NEED_DICT /\
                 exists a', areach src I R a a' /\ hrel src P0 O0 m' a' /\
                 astep lenfix_list distfix_list src a' = AEnd Z_NEED_DICT
  end.

(* one pass from a related loop head in a mode of P *)
Definition hcase_ok (P: Z -> Prop) : Prop :=
  forall flush src P0 O0 m a,
    hrel src P0 O0 m a -> awf src a -> m_leave m = 0 -> P (m_mode m) ->
    hgoal flush src P0 O0 (P0 + Zlength (m_inp m)) (Zlength O0 + m_aout m) a
          (stepf2 flush lenfix_list distfix_list m).

(* an abstract step within the limits in front of the goal *)
Lemma hgoal_step flush src P0 O0 I R a n w a1 o :
  astep lenfix_list distfix_list src a = AGo n w a1 -> ~ blocked I R a (AGo n w a1) ->
  hgoal flush src P0 O0 I R a1 o -> hgoal flush src P0 O0 I R a o.
Proof.
  intros S B G. destruct o as [m'|r m'].
  - destruct G as (a' & A & Rl & St). exists a'. split; [|auto]. eapply ar_step; eauto.
  - destruct G as (Er & a' & A & Rl & St). split; [exact Er|]. exists a'. split; [|auto]. eapply ar_step; eauto.
Qed.

(* a header step: reads up to n <= 8 I, writes nothing *)
Lemma hgoal_go flush src P0 O0 I R a n a1 o :
  astep lenfix_list distfix_list src a = AGo n false a1 -> n <= 8 * I ->
  hgoal flush src P0 O0 I R a1 o -> hgoal flush src P0 O0 I R a o.
Proof.
  intros S N G. eapply hgoal_step; [exact S| |exact G].
  cbn [blocked]. intros [B|[B _]]; [lia|discriminate].
Qed.

(* the call stops before a step that needs bits past the input *)
Lemma stop_need flush src I R m a n w a1 :
  astep lenfix_list distfix_list src a = AGo n w a1 -> 8 * I < n -> m_ret m = Z_OK ->
  stop_ok flush src I R m a.
Proof.
  intros S N Rt. unfold stop_ok. rewrite S. split; [exact Rt|]. right; right. left. cbn [blocked]. left; exact N.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The modes                                                                                      *)

Ltac hmd := unfold hdr_mode, data_mode, post_mode, win_mode, len_live, off_live, ext_live, decode_mode,
  HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT, Zlib.proof.inflate.Model.TYPE,
  TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, CHECK,
  LENGTH, DONE, BAD in *; lia.

Lemma hdr_not_post md : hdr_mode md \/ data_mode md -> ~ post_mode md.
Proof. hmd. Qed.

Lemma hdr_not_bad md : hdr_mode md -> md <> BAD /\ md <> DONE.
Proof. hmd. Qed.

Lemma bad_modes : ~ hdr_mode BAD /\ ~ data_mode BAD /\ ~ post_mode BAD /\ ~ win_mode BAD.
Proof. unfold data_mode, decode_mode, hdr_mode, post_mode, win_mode. vm_compute. lia. Qed.

(* the dispatch of the switch *)
Lemma stepf2_HEAD flush fx dx m : m_mode m = HEAD -> stepf2 flush fx dx m = c_HEAD2 m.
Proof. intros E. unfold stepf2, step2. cbv zeta. rewrite E. reflexivity. Qed.
Lemma stepf2_FLAGS flush fx dx m : m_mode m = FLAGS -> stepf2 flush fx dx m = c_FLAGS2 m.
Proof. intros E. unfold stepf2, step2. cbv zeta. rewrite E. reflexivity. Qed.
Lemma stepf2_TIME flush fx dx m : m_mode m = TIME -> stepf2 flush fx dx m = c_TIME2 m.
Proof. intros E. unfold stepf2, step2. cbv zeta. rewrite E. reflexivity. Qed.
Lemma stepf2_OS flush fx dx m : m_mode m = OS -> stepf2 flush fx dx m = c_OS2 m.
Proof. intros E. unfold stepf2, step2. cbv zeta. rewrite E. reflexivity. Qed.
Lemma stepf2_EXLEN flush fx dx m : m_mode m = EXLEN -> stepf2 flush fx dx m = c_EXLEN2 m.
Proof. intros E. unfold stepf2, step2. cbv zeta. rewrite E. reflexivity. Qed.
Lemma stepf2_EXTRA flush fx dx m : m_mode m = EXTRA -> stepf2 flush fx dx m = c_EXTRA2 m.
Proof. intros E. unfold stepf2, step2. cbv zeta. rewrite E. reflexivity. Qed.
Lemma stepf2_NAME flush fx dx m : m_mode m = NAME -> stepf2 flush fx dx m = c_NAME2 m.
Proof. intros E. unfold stepf2, step2. cbv zeta. rewrite E. reflexivity. Qed.
Lemma stepf2_COMMENT flush fx dx m : m_mode m = COMMENT -> stepf2 flush fx dx m = c_COMMENT2 m.
Proof. intros E. unfold stepf2, step2. cbv zeta. rewrite E. reflexivity. Qed.
Lemma stepf2_HCRC flush fx dx m : m_mode m = HCRC -> stepf2 flush fx dx m = c_HCRC m.
Proof. intros E. unfold stepf2, step2. cbv zeta. rewrite E. reflexivity. Qed.
Lemma stepf2_DICTID flush fx dx m : m_mode m = DICTID -> stepf2 flush fx dx m = c_DICTID flush m.
Proof. intros E. unfold stepf2, step2. cbv zeta. rewrite E. reflexivity. Qed.
Lemma stepf2_DICT flush fx dx m : m_mode m = DICT -> stepf2 flush fx dx m = c_DICT flush m.
Proof. intros E. unfold stepf2, step2. cbv zeta. rewrite E. reflexivity. Qed.

(* the abstract dispatch *)
Lemma astep_HEAD fx dx src a : a_mode a = HEAD -> astep fx dx src a = a_HEAD src a.
Proof. intros E. unfold astep. cbv zeta. rewrite E. reflexivity. Qed.
Lemma astep_FLAGS fx dx src a : a_mode a = FLAGS -> astep fx dx src a = a_FLAGS src a.
Proof. intros E. unfold astep. cbv zeta. rewrite E. reflexivity. Qed.
Lemma astep_TIME fx dx src a : a_mode a = TIME -> astep fx dx src a = a_TIME src a.
Proof. intros E. unfold astep. cbv zeta. rewrite E. reflexivity. Qed.
Lemma astep_OS fx dx src a : a_mode a = OS -> astep fx dx src a = a_OS src a.
Proof. intros E. unfold astep. cbv zeta. rewrite E. reflexivity. Qed.
Lemma astep_EXLEN fx dx src a : a_mode a = EXLEN -> astep fx dx src a = a_EXLEN src a.
Proof. intros E. unfold astep. cbv zeta. rewrite E. reflexivity. Qed.
Lemma astep_EXTRA fx dx src a : a_mode a = EXTRA -> astep fx dx src a = a_EXTRA src a.
Proof. intros E. unfold astep. cbv zeta. rewrite E. reflexivity. Qed.
Lemma astep_NAME fx dx src a : a_mode a = NAME -> astep fx dx src a = a_NAME src a.
Proof. intros E. unfold astep. cbv zeta. rewrite E. reflexivity. Qed.
Lemma astep_COMMENT fx dx src a : a_mode a = COMMENT -> astep fx dx src a = a_COMMENT src a.
Proof. intros E. unfold astep. cbv zeta. rewrite E. reflexivity. Qed.
Lemma astep_HCRC fx dx src a : a_mode a = HCRC -> astep fx dx src a = a_HCRC src a.
Proof. intros E. unfold astep. cbv zeta. rewrite E. reflexivity. Qed.
Lemma astep_DICTID fx dx src a : a_mode a = DICTID -> astep fx dx src a = a_DICTID src a.
Proof. intros E. unfold astep. cbv zeta. rewrite E. reflexivity. Qed.
Lemma astep_DICT fx dx src a : a_mode a = DICT -> astep fx dx src a = a_DICT a.
Proof. intros E. unfold astep. cbv zeta. rewrite E. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The state updates of the header modes                                                          *)

(* crc_if is acrc on the machine's state *)
Lemma crc_if_acrc m d : crc_if m d = upd_s m (fun s => acrc s d).
Proof.
  unfold crc_if, acrc, upd_s.
  destruct (_ && _)%bool; [reflexivity|]. destruct m; reflexivity.
Qed.

Lemma acrc_mode s d : i_mode (acrc s d) = i_mode s.
Proof. unfold acrc. destruct (_ && _)%bool; reflexivity. Qed.

(* the CRC of a chunk is the CRC of its bytes one after the other *)
Lemma acrc_app s d1 d2 : bytes_ok d1 -> acrc (acrc s d1) d2 = acrc s (d1 ++ d2).
Proof.
  intros B. unfold acrc.
  destruct (negb (Z.land (i_flags s) 512 =? 0) && negb (Z.land (i_wrap s) 4 =? 0))%bool eqn:G;
    cbn [i_flags i_wrap set_i_check i_check]; rewrite ?G; [|reflexivity].
  rewrite ref_crc32_app by exact B. destruct s; reflexivity.
Qed.

Lemma acrc_check s t d : i_check s = i_check t -> i_flags s = i_flags t -> i_wrap s = i_wrap t ->
  i_check (acrc s d) = i_check (acrc t d).
Proof. intros C F W. unfold acrc. rewrite F, W. destruct (_ && _)%bool; cbn; rewrite ?C; auto. Qed.

(* seq is kept by the same update on both sides *)
Lemma seq_acrc s t d d' : seq s t -> seq (acrc s d) (acrc t d').
Proof.
  intros H. unfold acrc.
  destruct (_ && _)%bool, (_ && _)%bool; destruct H; constructor; cbn; auto.
Qed.

Lemma seq_check s t c c' : seq s t -> seq (set_i_check s c) (set_i_check t c').
Proof. intros H. destruct H; constructor; cbn; auto. Qed.

Lemma seq_flags s t v : seq s t -> seq (set_i_flags s v) (set_i_flags t v).
Proof. intros H. destruct H; constructor; cbn; auto. Qed.

Lemma seq_wbits s t v : seq s t -> seq (set_i_wbits s v) (set_i_wbits t v).
Proof. intros H. destruct H; constructor; cbn; auto. Qed.

Lemma seq_dmax s t v : seq s t -> seq (set_i_dmax s v) (set_i_dmax t v).
Proof. intros H. destruct H; constructor; cbn; auto. Qed.

Lemma seq_length s t v : seq s t -> seq (set_i_length s v) (set_i_length t v).
Proof. intros H. destruct H; constructor; cbn; auto. Qed.

(* a new mode: the fields it reads must agree *)
Lemma seq_mode s t v : seq s t ->
  (len_live v -> i_length s = i_length t) -> (off_live v -> i_offset s = i_offset t) ->
  (ext_live v -> i_extra s = i_extra t) -> seq (set_i_mode s v) (set_i_mode t v).
Proof. intros H L O E. destruct H; constructor; cbn; auto. Qed.

(* a header mode other than EXTRA reads none of them *)
Lemma seq_mode_hdr s t v : seq s t -> hdr_mode v -> v <> EXTRA -> seq (set_i_mode s v) (set_i_mode t v).
Proof. intros H Hv Ne. apply seq_mode; auto; intros; exfalso; hmd. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The bit buffer                                                                                 *)

Lemma bitbuf_ext src P0 m m' :
  bitbuf src P0 m -> m_inp m' = m_inp m -> m_nx m' = m_nx m -> m_bits m' = m_bits m -> m_hold m' = m_hold m ->
  bitbuf src P0 m'.
Proof.
  intros [A B C D E F] Ei En Eb Eh. unfold mq in *.
  constructor; unfold mq; rewrite ?Ei, ?En, ?Eb, ?Eh; auto.
Qed.

Lemma mq_ext P0 m m' : m_nx m' = m_nx m -> m_bits m' = m_bits m -> mq P0 m' = mq P0 m.
Proof. intros En Eb. unfold mq. rewrite En, Eb. reflexivity. Qed.

(* NEEDBITS pulls whole bytes *)
Lemma needbits_f_bytes k n m :
  0 <= m_bits m -> m_bits m + 8 * Z.of_nat k < 2 ^ 32 -> m_bits m mod 8 = 0 ->
  m_bits (needbits_f k n m) mod 8 = 0.
Proof.
  revert m. induction k as [|k IH]; intros m B0 B1 B2; [exact B2|].
  cbn [needbits_f].
  destruct (m_bits m <? n); [|exact B2].
  destruct (m_have m =? 0); [exact B2|].
  rewrite Nat2Z.inj_succ in B1.
  assert (E: m_bits (pull m) = m_bits m + 8).
  { unfold pull. cbn [m_bits set_m_bits set_m_hold set_m_nx]. unfold u32. apply Z.mod_small. lia. }
  apply IH; rewrite E; try lia.
  replace (m_bits m + 8) with (m_bits m + 1 * 8) by lia. rewrite Z.mod_add by lia. exact B2.
Qed.

(* NEEDBITS(n) of a header field (n = 16 or 32) from a buffer of whole bytes, fewer than n *)
Lemma needbits_hdr src P0 m n :
  kit_bits_stmt -> bitbuf src P0 m -> m_leave m = 0 -> (n = 16 \/ n = 32) ->
  m_bits m mod 8 = 0 -> m_bits m < n ->
  let m1 := needbits n m in
  m1 = set_m_leave (set_m_bits (set_m_hold (set_m_nx m (m_nx m1)) (m_hold m1)) (m_bits m1)) (m_leave m1) /\
  bitbuf src P0 m1 /\ mq P0 m1 = mq P0 m /\
  (m_leave m1 = 0 -> m_bits m1 = n /\ m_hold m1 = sbits src (mq P0 m) n /\
                     mq P0 m + n <= 8 * (P0 + Zlength (m_inp m))) /\
  (m_leave m1 <> 0 -> m_leave m1 = 1 /\ m_bits m1 mod 8 = 0 /\ m_bits m1 < n /\
                      8 * (P0 + Zlength (m_inp m)) < mq P0 m + n).
Proof.
  intros KB BB L0 Hn B8 Bn m1.
  destruct KB as (_ & KN & _).
  assert (Hn': 0 <= n <= 32) by lia.
  destruct (KN src P0 m n BB L0 Hn') as (BB1 & Q1 & E1 & S1 & F1). fold m1 in BB1, Q1, E1, S1, F1.
  assert (M8: m_bits m1 mod 8 = 0).
  { unfold m1, needbits. pose proof (bb_bits _ _ _ BB). apply needbits_f_bytes; cbn; lia. }
  assert (Ei: m_inp m1 = m_inp m) by (rewrite E1; reflexivity).
  split; [exact E1|]. split; [exact BB1|]. split; [exact Q1|]. split.
  - intros L1. destruct (S1 L1) as (N1 & N2 & N3).
    assert (Eb: m_bits m1 = n).
    { rewrite Z.max_r in N2 by lia. pose proof (Z.div_mod (m_bits m1) 8 ltac:(lia)). destruct Hn as [-> | ->]; lia. }
    split; [exact Eb|]. split.
    + rewrite (bb_hold _ _ _ BB1), Q1, Eb. reflexivity.
    + pose proof (bb_nx _ _ _ BB1) as X. rewrite Ei in X. unfold mq in *. lia.
  - intros L1. destruct (F1 L1) as (N1 & N2 & N3 & N4). auto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The relation after a header pass                                                               *)

(* the fields of the window *)
Definition win_eq (s t: istate) : Prop :=
  i_wsize s = i_wsize t /\ i_whave s = i_whave t /\ i_wnext s = i_wnext t /\ i_win s = i_win t /\
  i_wdata s = i_wdata t.

Lemma swin_ok_eq s t O : win_eq s t -> swin_ok t O -> swin_ok s O.
Proof.
  intros (A & B & C & D & E). unfold swin_ok, swin_at. rewrite A, B, C, D, E. auto.
Qed.

(* from a header loop head to a non-BAD mode of the header or data phase *)
Lemma rel_hdr_next src P0 O0 m a m' a' :
  rel src P0 O0 m a -> hdr_mode (m_mode m) ->
  bitbuf src P0 m' -> m_inp m' = m_inp m -> m_aout m' = m_aout m -> m_ow m' = m_ow m -> m_in m' = m_in m ->
  m_out m' = m_out m -> m_ret m' = m_ret m -> m_tout m' = m_tout m ->
  m_mode m' = a_mode a' -> a_q a' = mq P0 m' -> a_O a' = a_O a ->
  seq (m_s m') (a_s a') ->
  (hdr_mode (m_mode m') -> i_check (m_s m') = i_check (a_s a')) ->
  (data_mode (m_mode m') -> i_wrap (m_s m') <> 0 ->
     i_check (m_s m') = update_check (i_flags (a_s a')) (i_check (a_s a')) O0) ->
  hdr_mode (m_mode m') \/ data_mode (m_mode m') ->
  i_total (m_s m') = i_total (m_s m) -> win_eq (m_s m') (m_s m) -> i_head (m_s m') = false ->
  bits_ok (m_s m') (m_bits m') ->
  rel src P0 O0 m' a'.
Proof.
  intros Rl Hm BB Ei Ea Eo Ein Eout Er Et Md Q O S C1 C2 HD Tot W Hd BO.
  assert (NP: ~ post_mode (m_mode m')) by (apply hdr_not_post; exact HD).
  destruct (hdr_not_bad _ Hm) as [NB ND].
  destruct Rl as [BB0 Md0 Q0 BO0 O0' Ao In Out Ret S0 Ch Tt Tout Win Hd0].
  unfold m_left in *.
  constructor.
  - exact BB.
  - exact Md.
  - intros _. exact Q.
  - exact BO.
  - rewrite O, O0', Eo. reflexivity.
  - rewrite Eo, Ea. exact Ao.
  - rewrite Ein, Ei. exact In.
  - unfold m_left. rewrite Eout, Ea, Eo. destruct Out as (O1 & O2 & O3).
    specialize (O3 (or_introl Hm)). split; [exact O1|].
    split; [intros P; exfalso; exact (NP P)|intros _; exact O3].
  - intros _ _. rewrite Er. exact (Ret NB ND).
  - intros _. exact S.
  - split; assumption.
  - split; [intros _; rewrite Tot; exact (proj1 Tt (or_introl Hm))|intros P; exfalso; exact (NP P)].
  - unfold m_left. rewrite Et, Tout, Eo, Eout, Ea. reflexivity.
  - intros _. apply swin_ok_eq with (m_s m); [exact W|]. apply Win. left; exact Hm.
  - exact Hd.
Qed.

(* from a header loop head to BAD *)
Lemma rel_hdr_bad src P0 O0 m a m' a' :
  rel src P0 O0 m a -> hdr_mode (m_mode m) ->
  bitbuf src P0 m' -> m_inp m' = m_inp m -> m_aout m' = m_aout m -> m_ow m' = m_ow m -> m_in m' = m_in m ->
  m_out m' = m_out m -> m_tout m' = m_tout m ->
  m_mode m' = BAD -> a_mode a' = BAD -> a_O a' = a_O a -> i_head (m_s m') = false ->
  rel src P0 O0 m' a'.
Proof.
  intros Rl Hm BB Ei Ea Eo Ein Eout Et Md Ma O Hd.
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

(* the bit buffer condition of rel in the header modes is hbits *)
Lemma hbits_rel src P0 O0 m a : rel src P0 O0 m a -> hbits m.
Proof. intros Rl. exact (proj1 (rl_bits _ _ _ _ _ Rl)). Qed.

(* hbits gives bits_ok outside the modes of a stored block and of the trailer *)
Lemma bits_ok_hb m : hbits m -> ~ (m_mode m = COPY_ \/ m_mode m = COPY \/ m_mode m = CHECK \/ m_mode m = LENGTH) ->
  bits_ok (m_s m) (m_bits m).
Proof.
  intros H N. split; [exact H|]. split; intros E; exfalso; apply N; unfold m_mode; tauto.
Qed.

(* building hrel from the relation given its bit buffer condition *)
Lemma hrel_mk src P0 O0 m a :
  (bits_ok (m_s m) (m_bits m) -> rel src P0 O0 m a) -> hbits m ->
  ~ (m_mode m = COPY_ \/ m_mode m = COPY \/ m_mode m = CHECK \/ m_mode m = LENGTH) ->
  hrel src P0 O0 m a.
Proof. intros R H N. split; [apply R, bits_ok_hb; auto | exact H]. Qed.

(* the side condition of hrel_mk, for a machine whose mode computes to a constant *)
Ltac hrel_md := cbn; intros [E|[E|[E|E]]]; discriminate.

(* the header's check is the check of the data phase before any output *)
Lemma update_check_nil01 f c : c = 0 \/ c = 1 -> update_check f c [] = c.
Proof.
  intros [-> | ->]; unfold update_check; destruct (f =? 0); reflexivity.
Qed.

(* acrc changes the check only *)
Lemma acrc_eq s d : acrc s d = set_i_check s (i_check (acrc s d)).
Proof. unfold acrc. destruct (_ && _)%bool; [reflexivity|destruct s; reflexivity]. Qed.

Lemma acrc_fields s d :
  i_mode (acrc s d) = i_mode s /\ i_flags (acrc s d) = i_flags s /\ i_wrap (acrc s d) = i_wrap s /\
  i_total (acrc s d) = i_total s /\ i_head (acrc s d) = i_head s /\ i_length (acrc s d) = i_length s /\
  i_havedict (acrc s d) = i_havedict s /\ win_eq (acrc s d) s.
Proof. rewrite acrc_eq. unfold win_eq. cbn. repeat split; reflexivity. Qed.

(* a NEEDBITS that only pulls bytes keeps the relation *)
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

(* the continuation: the pass goes on in the next mode from a related state *)
Lemma hcont P flush src P0 O0 m1 a1 I R :
  hcase_ok P -> hrel src P0 O0 m1 a1 -> awf src a1 -> m_leave m1 = 0 -> P (m_mode m1) ->
  I = P0 + Zlength (m_inp m1) -> R = Zlength O0 + m_aout m1 ->
  hgoal flush src P0 O0 I R a1 (stepf2 flush lenfix_list distfix_list m1).
Proof. intros H Rl Aw L Pm -> ->. apply H; auto. Qed.

(* awf after a step *)
Lemma awf_go src a n w a1 :
  awf_stmt -> awf src a -> astep lenfix_list distfix_list src a = AGo n w a1 -> awf src a1.
Proof. intros (_ & A & _) Aw S. eapply A; eauto. Qed.

(* a case that continues in the modes of P *)
Definition hcase_next (X: Z) (P: Z -> Prop) : Prop :=
  kit_stmt -> awf_stmt -> hcase_ok P -> hcase_ok (fun md => md = X).

Lemma hdr_not_copy md : hdr_mode md -> ~ (md = COPY_ \/ md = COPY \/ md = CHECK \/ md = LENGTH).
Proof. unfold hdr_mode. vm_compute. lia. Qed.
