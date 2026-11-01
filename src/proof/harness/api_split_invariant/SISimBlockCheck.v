(* The simulation of the modes CHECK and LENGTH: the trailer of a zlib or gzip stream (the check value of
   the whole output, the gzip length), and the end of a raw stream. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_split_invariant.SIDefs.
Require Import Zlib.proof.harness.api_split_invariant.SISimBlockKit.
Import ListNotations.
Local Open Scope Z_scope.

(* NEEDBITS(n), n <= 32, from a whole number of bytes keeps a whole number of bytes (also when it leaves) *)
Lemma sibc_needbits_mod8 k n m :
  n <= 32 -> 0 <= m_bits m -> m_bits m mod 8 = 0 -> m_bits (needbits_f k n m) mod 8 = 0.
Proof.
  revert m. induction k as [|k IH]; intros m N B M; cbn [needbits_f]; [exact M|].
  destruct (Z.ltb_spec (m_bits m) n) as [Lt|Ge]; [|exact M].
  destruct (m_have m =? 0); [exact M|].
  assert (P: m_bits (pull m) = m_bits m + 8) by (apply sib_pull_bits; lia).
  apply IH; [exact N|lia|]. rewrite P, Z.add_mod by lia. rewrite M. reflexivity.
Qed.

(* a whole number of bytes of at most 39 bits is at most 32 bits *)
Lemma sibc_bits32 b : 0 <= b <= 39 -> b mod 8 = 0 -> b <= 32.
Proof. intros B M. pose proof (Z.div_mod b 8 ltac:(lia)). rewrite M in *. lia. Qed.

Lemma sibc_u64_add x y : u64 (u64 x + y) = u64 (x + y).
Proof. unfold u64. rewrite Zplus_mod_idemp_l. reflexivity. Qed.

Lemma sibc_u64_mod32 x : u64 x mod 2 ^ 32 = x mod 2 ^ 32.
Proof.
  unfold u64. replace (2 ^ 64) with (2 ^ 32 * 2 ^ 32) by reflexivity.
  rewrite Z.rem_mul_r by lia. rewrite Z.add_mod, Z.mul_comm, Z.mod_mul, Z.add_0_r, !Z.mod_mod by lia.
  reflexivity.
Qed.

(* a machine in BAD is related to an abstract state in BAD when its output, counters and bit buffer are *)
Lemma sibc_rel_bad src P0 O0 m a :
  bitbuf src P0 m -> m_mode m = BAD -> a_mode a = BAD -> a_O a = O0 ++ m_ow m ->
  Zlength (m_ow m) <= m_aout m <= Int.max_unsigned -> m_in m = Zlength (m_inp m) ->
  m_left m <= m_out m <= m_aout m ->
  m_tout m = u64 (Zlength O0 + Zlength (m_ow m) - (m_out m - m_left m)) -> i_head (m_s m) = false ->
  rel src P0 O0 m a.
Proof.
  intros BB M Ma EO Ea Ein Eout Et Hd.
  pose proof sib_bad_cls as (NH & ND & NP & NW).
  constructor; auto; rewrite ?M; try (intros X; contradiction); try (intros X; contradiction X; reflexivity).
  - rewrite Ma. reflexivity.
  - apply sib_bits_free; unfold m_mode in M; rewrite M; sib_mdg.
  - split; [exact Eout|]. split; intros X; [contradiction|]. destruct X as [X|[X|[X _]]]; contradiction.
  - split; intros X; contradiction.
  - split; intros X; [destruct X as [X|[X|[X _]]]|]; contradiction.
Qed.

(* a machine in DONE is related to an abstract state in DONE *)
Lemma sibc_rel_done src P0 O0 m a :
  bitbuf src P0 m -> m_mode m = DONE -> a_mode a = DONE -> a_q a = mq P0 m -> a_O a = O0 ++ m_ow m ->
  Zlength (m_ow m) <= m_aout m <= Int.max_unsigned -> m_in m = Zlength (m_inp m) ->
  m_left m <= m_out m <= m_aout m ->
  (i_wrap (m_s m) <> 0 -> m_out m = m_left m) -> (i_wrap (m_s m) = 0 -> m_out m = m_aout m) ->
  seq (m_s m) (a_s a) ->
  (i_wrap (m_s m) = 0 -> i_total (m_s m) = u64 (Zlength O0)) ->
  (i_wrap (m_s m) <> 0 -> i_total (m_s m) = u64 (Zlength (a_O a))) ->
  m_tout m = u64 (Zlength O0 + Zlength (m_ow m) - (m_out m - m_left m)) -> i_head (m_s m) = false ->
  rel src P0 O0 m a.
Proof.
  intros BB M Ma Q EO Ea Ein Eout W1 W0 S T0 T1 Et Hd.
  assert (NH: ~ hdr_mode DONE) by sib_mdg. assert (ND: ~ data_mode DONE) by sib_mdg.
  assert (NW: ~ win_mode DONE) by sib_mdg. assert (PD: post_mode DONE) by sib_mdg.
  constructor; auto; rewrite ?M; try (intros X; contradiction).
  - rewrite Ma. reflexivity.
  - apply sib_bits_free; unfold m_mode in M; rewrite M; sib_mdg.
  - split; [exact Eout|]. split; [auto|]. intros [X|[X|[_ X]]]; [contradiction..|auto].
  - split; intros X; contradiction.
  - split; [intros [X|[X|[_ X]]]; [contradiction..|auto]|auto].
Qed.

(* c_LENGTH from a machine in LENGTH related to a (the output limit R plays no part: LENGTH writes nothing);
   CHECK falls through into it *)
Lemma sibc_length (K: kit_bits_stmt) flush src P0 O0 m a R :
  rel src P0 O0 m a -> m_leave m = 0 -> m_mode m = LENGTH ->
  sib_out flush src P0 O0 (P0 + Zlength (m_inp m)) R a (c_LENGTH m).
Proof.
  intros R0 L M.
  pose proof (rl_bb _ _ _ _ _ R0) as BB.
  assert (Ma: a_mode a = LENGTH) by (rewrite <- (rl_mode _ _ _ _ _ R0); exact M).
  assert (Q: a_q a = mq P0 m) by (apply (rl_q _ _ _ _ _ R0); rewrite M; sib_mdg).
  assert (S: seq (m_s m) (a_s a)) by (apply (rl_s _ _ _ _ _ R0); rewrite M; sib_mdg).
  assert (Ret: m_ret m = Z_OK) by (apply (rl_ret _ _ _ _ _ R0); rewrite M; sib_mdg).
  assert (B8: m_bits m mod 8 = 0).
  { pose proof (rl_bits _ _ _ _ _ R0) as Bk. unfold bits_ok in Bk. cbv zeta in Bk.
    destruct Bk as (_ & _ & X). apply X. right. exact M. }
  assert (PM: post_mode (m_mode m)) by (rewrite M; sib_mdg).
  assert (A: astep lenfix_list distfix_list src a = a_LENGTH src a) by (apply sib_a_LENGTH; exact Ma).
  pose proof (se_wrap _ _ S) as Ew. pose proof (se_flags _ _ S) as Ef.
  pose proof (bb_bits _ _ _ BB) as Bb.
  unfold c_LENGTH. rewrite Ew, Ef.
  destruct (andb (negb (i_wrap (a_s a) =? 0)) (negb (i_flags (a_s a) =? 0))) eqn:G.
  - (* gzip: NEEDBITS(32), the length *)
    destruct K as (_ & Knb & _ & Kinit & _).
    assert (W: i_wrap (a_s a) <> 0).
    { intros X. rewrite X in G. discriminate. }
    destruct (Knb src P0 m 32 BB L ltac:(lia)) as (BB1 & Qn & E1 & OK1 & LV1).
    cbv zeta. set (m1 := needbits 32 m) in *.
    assert (Em1: m_s m1 = m_s m /\ m_ret m1 = m_ret m /\ m_inp m1 = m_inp m /\ m_aout m1 = m_aout m /\
                 m_ow m1 = m_ow m /\ m_in m1 = m_in m /\ m_out m1 = m_out m /\ m_tout m1 = m_tout m)
      by (rewrite E1; sib_cbn; repeat split).
    destruct Em1 as (Es1 & Er1 & Ei1 & Ea1 & Eo1 & Ein1 & Eout1 & Et1).
    assert (B81: m_bits m1 mod 8 = 0) by (unfold m1, needbits; apply sibc_needbits_mod8; lia).
    destruct (Z.eqb_spec (m_leave m1) 1) as [Lv|Lv].
    + (* the input ends before the length: the abstract state stays *)
      apply sib_out_stay.
      * rewrite E1. apply sib_rel_bits; [exact R0|rewrite <- E1; exact BB1|rewrite <- E1; exact Qn|].
        unfold bits_ok. cbv zeta. unfold m_mode in M. rewrite M.
        split; [intros X; exfalso; revert X; sib_mdg|].
        split; [intros X; exfalso; revert X; sib_mdg|intros _; exact B81].
      * intros _. unfold stop_ok. rewrite A. unfold a_LENGTH. rewrite G. cbv iota zeta.
        destruct (LV1 ltac:(lia)) as (_ & _ & _ & X).
        match goal with |- context [if ?b then _ else _] => destruct b end; unfold abad, ago; cbv iota;
          (split; [rewrite Er1; exact Ret|right; right; left; left; rewrite Q; exact X]).
    + (* the 32 bits are there: hold is the trailer's length field *)
      assert (L1: m_leave m1 = 0) by (destruct (Z.eq_dec (m_leave m1) 0) as [X|X]; [exact X|];
                                       destruct (LV1 X) as [X1 _]; contradiction).
      assert (Bm1: m_bits m1 = 32)
        by (unfold m1; apply sib_needbits32_bits; [split; [lia|apply sibc_bits32; [lia|exact B8]]|exact B8|exact L1]).
      pose proof (bb_bits _ _ _ BB1) as Bb1. pose proof (bb_nx _ _ _ BB1) as Nx1.
      assert (H1: m_hold m1 = sbits src (a_q a) 32) by (rewrite (bb_hold _ _ _ BB1), Qn, Bm1, Q; reflexivity).
      assert (T1: i_total (m_s m1) = u64 (Zlength (a_O a)))
        by (rewrite Es1; apply (rl_tot _ _ _ _ _ R0); [exact PM|rewrite Ew; exact W]).
      assert (Iq: a_q a + 32 <= 8 * (P0 + Zlength (m_inp m))).
      { rewrite Q, <- Qn. unfold mq. rewrite Ei1 in Nx1. lia. }
      rewrite H1, T1, sibc_u64_mod32, Es1, Ew.
      destruct (andb (negb (Z.land (i_wrap (a_s a)) 4 =? 0)) (negb (sbits src (a_q a) 32 =? Zlength (a_O a) mod 2 ^ 32)))
        eqn:G2.
      * (* the length is wrong *)
        pose proof R0 as R1. destruct R1. unfold m_left in *.
        eapply sib_out_go.
        -- eapply sib_ar1f; [rewrite A; unfold a_LENGTH; rewrite G; cbv iota zeta; rewrite G2; reflexivity|exact Iq].
        -- apply sibc_rel_bad; [eapply sib_bb_ext; [..|exact BB1]; reflexivity|..];
             unfold set_bad, set_mode, upd_s, m_left; sib_cbn; rewrite ?Es1, ?Ei1, ?Ea1, ?Eo1, ?Ein1, ?Eout1, ?Et1;
             try reflexivity; try assumption; lia.
        -- unfold set_bad, set_mode, upd_s. sib_cbn. exact L1.
      * (* the length is right: DONE *)
        unfold c_DONE.
        exists (AS (set_i_mode (a_s a) DONE) (a_q a + 32) (a_O a)). split; [|split].
        -- eapply sib_ar1f; [rewrite A; unfold a_LENGTH; rewrite G; cbv iota zeta; rewrite G2; reflexivity|exact Iq].
        -- destruct (Kinit src P0 m1 BB1) as [BBi Qi]. pose proof R0 as R1. destruct R1. unfold m_left in *.
           apply sibc_rel_done; [eapply sib_bb_ext; [..|exact BBi]; reflexivity|reflexivity|reflexivity|
             cbn [a_q]; rewrite (sib_mq_ext P0 (initbits m1)) by reflexivity; rewrite Qi, Qn, Bm1, Q; reflexivity|..];
             unfold set_leave, set_mode, upd_s, initbits, m_left; sib_cbn; rewrite ?Es1, ?Ei1, ?Ea1, ?Eo1, ?Ein1, ?Eout1, ?Et1;
             try reflexivity; try assumption; try lia.
           ++ intros X. apply rl_out; auto.
           ++ apply sib_seq_mode0; [exact S|sib_mdg..].
           ++ intros X. apply rl_tot; auto.
        -- intros _. unfold stop_ok. rewrite sib_a_DONE by reflexivity. unfold set_leave, set_mode, upd_s; sib_cbn.
           split; [reflexivity|left; reflexivity].
  - (* a raw or zlib stream: no length, DONE *)
    cbv zeta. unfold c_DONE.
    exists (AS (set_i_mode (a_s a) DONE) (a_q a) (a_O a)). split; [|split].
    + eapply sib_ar1f; [rewrite A; unfold a_LENGTH; rewrite G; reflexivity|].
      rewrite Q. apply (sib_mq_le src), BB.
    + pose proof R0 as R1. destruct R1. unfold m_left in *.
      apply sibc_rel_done; unfold set_leave, set_mode, upd_s, m_left; sib_cbn.
      all: try (eapply sib_bb_ext; [..|exact BB]; reflexivity).
      all: try assumption. all: try reflexivity. all: try lia.
      * intros X. apply rl_out; auto.
      * intros X. apply rl_out. right. right. split; auto.
      * apply sib_seq_mode0; [exact S|sib_mdg..].
      * intros X. apply rl_tot. right. right. split; auto.
      * intros X. apply rl_tot; auto.
    + intros _. unfold stop_ok. rewrite sib_a_DONE by reflexivity. unfold set_leave, set_mode, upd_s; sib_cbn.
      split; [reflexivity|left; reflexivity].
Qed.

Lemma sib_LENGTH : kit_stmt -> sib_case LENGTH.
Proof.
  intros [K _] flush src P0 O0 m a R W L M. rewrite sib_c_LENGTH by exact M.
  apply sibc_length; assumption.
Qed.

(* the end of CHECK in a wrapped stream: m2 holds the trailer's 32 bits, its check value is the check of
   the whole output and the output counters are updated; the comparison with the trailer, then LENGTH *)
Lemma sibc_check_tail (K: kit_bits_stmt) flush src P0 O0 a m2 I R :
  I = P0 + Zlength (m_inp m2) -> a_mode a = CHECK ->
  bitbuf src P0 m2 -> mq P0 m2 = a_q a -> m_bits m2 = 32 -> m_hold m2 = sbits src (a_q a) 32 ->
  a_q a + 32 <= 8 * I -> m_mode m2 = CHECK -> seq (m_s m2) (a_s a) ->
  i_wrap (m_s m2) = i_wrap (a_s a) -> i_flags (m_s m2) = i_flags (a_s a) ->
  i_wrap (a_s a) <> 0 -> Z.land (i_wrap (a_s a)) 4 <> 0 ->
  i_check (m_s m2) = update_check (i_flags (a_s a)) (i_check (a_s a)) (a_O a) ->
  i_total (m_s m2) = u64 (Zlength (a_O a)) ->
  a_O a = O0 ++ m_ow m2 -> Zlength (m_ow m2) <= m_aout m2 <= Int.max_unsigned -> m_in m2 = Zlength (m_inp m2) ->
  m_out m2 = m_left m2 -> m_tout m2 = u64 (Zlength O0 + Zlength (m_ow m2)) ->
  m_ret m2 = Z_OK -> m_leave m2 = 0 -> i_head (m_s m2) = false ->
  sib_out flush src P0 O0 I R a
    (if andb (negb (Z.land (i_wrap (m_s m2)) 4 =? 0))
             (negb ((if i_flags (m_s m2) =? 0 then swap32 (m_hold m2) else m_hold m2) =? i_check (m_s m2)))
     then IBrk (set_bad m2 M_dcheck) else c_LENGTH (set_mode (initbits m2) LENGTH)).
Proof.
  intros EI Ma BB Q B32 H Iq M S Ew Ef W W4 Chk Tot EO Ea Ein Eout Et Ret L.
  intros Hd.
  pose proof K as K0. destruct K as (_ & _ & _ & Kinit & _).
  assert (A: astep lenfix_list distfix_list src a = a_CHECK src a) by (apply sib_a_CHECK; exact Ma).
  assert (Ma2: i_mode (m_s m2) = CHECK) by exact M.
  pose proof (Zlength_nonneg (m_ow m2)) as Ow.
  rewrite Ew, Ef, H, Chk.
  destruct (andb (negb (Z.land (i_wrap (a_s a)) 4 =? 0))
                 (negb ((if i_flags (a_s a) =? 0 then swap32 (sbits src (a_q a) 32) else sbits src (a_q a) 32)
                        =? update_check (i_flags (a_s a)) (i_check (a_s a)) (a_O a)))) eqn:G.
  - (* the check value is wrong *)
    eapply sib_out_go.
    + eapply sib_ar1f; [|exact Iq].
      rewrite A; unfold a_CHECK. destruct (Z.eqb_spec (i_wrap (a_s a)) 0) as [X|_]; [contradiction|].
      cbv iota zeta. cbn [negb]. rewrite G. reflexivity.
    + apply sibc_rel_bad; [eapply sib_bb_ext; [..|exact BB]; reflexivity|..];
        unfold set_bad, set_mode, upd_s, m_left in *; sib_cbn; try reflexivity; try assumption; try lia.
      rewrite Et, Eout. f_equal. lia.
    + unfold set_bad, set_mode, upd_s. sib_cbn. exact L.
  - (* the check value is right: LENGTH *)
    apply (sib_out_pre _ _ _ _ _ _ _
             (AS (set_i_mode (set_i_check (a_s a) (update_check (i_flags (a_s a)) (i_check (a_s a)) (a_O a))) LENGTH)
                 (a_q a + 32) (a_O a))).
    { eapply sib_ar1f; [|exact Iq].
      rewrite A; unfold a_CHECK. destruct (Z.eqb_spec (i_wrap (a_s a)) 0) as [X|_]; [contradiction|].
      cbv iota zeta. cbn [negb]. rewrite G. reflexivity. }
    rewrite EI. change (P0 + Zlength (m_inp m2)) with (P0 + Zlength (m_inp (set_mode (initbits m2) LENGTH))).
    apply sibc_length; [exact K0| |exact L|reflexivity].
    destruct (Kinit src P0 m2 BB) as [BBi Qi].
    constructor; [eapply sib_bb_ext; [..|exact BBi]; reflexivity|reflexivity|
      intros _; cbn [a_q]; rewrite (sib_mq_ext P0 (initbits m2)) by reflexivity; rewrite Qi, Q, B32; reflexivity|..];
      unfold set_mode, upd_s, initbits, m_left in *; sib_cbn; try reflexivity; try assumption; try lia.
    + unfold bits_ok. cbn [i_mode set_i_mode]. split; [sib_mdg|]. split; [sib_mdg|intros _; reflexivity].
    + split; [lia|]. split; [intros _ _; exact Eout|]. intros [X|[X|[_ X]]]; [revert X; sib_mdg..|].
      rewrite Ew in X. contradiction.
    + intros _. apply sib_seq_mode0; [apply sib_seq_check_r; exact S|sib_mdg..].
    + split; sib_mdg.
    + split; [intros [X|[X|[_ X]]]; [revert X; sib_mdg..|rewrite Ew in X; contradiction]|intros _ _; exact Tot].
    + rewrite Et, Eout. f_equal. lia.
    + sib_mdg.
Qed.

Lemma sib_CHECK : kit_stmt -> sib_case CHECK.
Proof.
  intros [K _] flush src P0 O0 m a R0 W L M. rewrite sib_c_CHECK by exact M. unfold c_CHECK.
  pose proof (rl_bb _ _ _ _ _ R0) as BB.
  assert (Ma: a_mode a = CHECK) by (rewrite <- (rl_mode _ _ _ _ _ R0); exact M).
  assert (Q: a_q a = mq P0 m) by (apply (rl_q _ _ _ _ _ R0); rewrite M; sib_mdg).
  assert (S: seq (m_s m) (a_s a)) by (apply (rl_s _ _ _ _ _ R0); rewrite M; sib_mdg).
  assert (Ret: m_ret m = Z_OK) by (apply (rl_ret _ _ _ _ _ R0); rewrite M; sib_mdg).
  assert (B8: m_bits m mod 8 = 0).
  { pose proof (rl_bits _ _ _ _ _ R0) as Bk. unfold bits_ok in Bk. cbv zeta in Bk.
    destruct Bk as (_ & _ & X). apply X. left. exact M. }
  assert (DM: data_mode (m_mode m)) by (rewrite M; sib_mdg).
  assert (A: astep lenfix_list distfix_list src a = a_CHECK src a) by (apply sib_a_CHECK; exact Ma).
  pose proof (se_wrap _ _ S) as Ew. pose proof (se_flags _ _ S) as Ef.
  pose proof (bb_bits _ _ _ BB) as Bb.
  assert (Out: m_out m = m_aout m) by (apply (rl_out _ _ _ _ _ R0); right; left; exact DM).
  assert (Tot: i_total (m_s m) = u64 (Zlength O0)) by (apply (rl_tot _ _ _ _ _ R0); right; left; exact DM).
  rewrite Ew. destruct (Z.eqb_spec (i_wrap (a_s a)) 0) as [W0|W0]; cbn [negb].
  - (* a raw stream: no trailer, on to LENGTH *)
    apply (sib_out_pre _ _ _ _ _ _ _ (AS (set_i_mode (a_s a) LENGTH) (a_q a) (a_O a))).
    { eapply sib_ar1f; [rewrite A; unfold a_CHECK; rewrite W0; reflexivity|].
      rewrite Q. apply (sib_mq_le src), BB. }
    change (P0 + Zlength (m_inp m)) with (P0 + Zlength (m_inp (set_mode m LENGTH))).
    apply sibc_length; [exact K| |exact L|reflexivity].
    pose proof R0 as R1. destruct R1. unfold m_left in *.
    constructor; unfold set_mode, upd_s, m_left; sib_cbn.
    all: try (eapply sib_bb_ext; [..|exact BB]; reflexivity).
    all: try assumption. all: try reflexivity. all: try lia.
    + intros _. exact Q.
    + unfold bits_ok. cbn [i_mode set_i_mode]. split; [sib_mdg|]. split; [sib_mdg|intros _; exact B8].
    + intros _. apply sib_seq_mode0; [exact S|sib_mdg..].
    + split; sib_mdg.
    + sib_mdg.
  - (* a zlib or gzip stream: NEEDBITS(32), the check value *)
    pose proof K as K0. destruct K as (_ & Knb & _ & Kinit & _).
    assert (W4: Z.land (i_wrap (a_s a)) 4 <> 0).
    { destruct (aw_wrap _ _ W) as [X|[X|[X|X]]]; rewrite X; [contradiction|..]; intros C; compute in C; discriminate C. }
    pose proof R0 as R1. destruct R1. unfold m_left in *.
    assert (Chk0: i_check (m_s m) = update_check (i_flags (a_s a)) (i_check (a_s a)) O0)
      by (apply rl_chk; [exact DM|rewrite Ew; exact W0]).
    assert (Val: i_flags (a_s a) = 0 -> adler_valid (i_check (a_s a))).
    { intros F. destruct (aw_chk _ _ W) as [[_ C]|[F' _]]; [rewrite <- rl_mode; exact DM|exact W0| |contradiction].
      rewrite C. apply sib_adler_valid1. }
    assert (BO: bytes_ok O0).
    { pose proof (aw_O _ _ W) as X. rewrite rl_O in X. unfold bytes_ok in *. apply Forall_app in X. tauto. }
    destruct (Knb src P0 m 32 BB L ltac:(lia)) as (BB1 & Qn & E1 & OK1 & LV1).
    cbv zeta. set (m1 := needbits 32 m) in *.
    assert (Em1: m_s m1 = m_s m /\ m_ret m1 = m_ret m /\ m_inp m1 = m_inp m /\ m_aout m1 = m_aout m /\
                 m_ow m1 = m_ow m /\ m_in m1 = m_in m /\ m_out m1 = m_out m /\ m_tout m1 = m_tout m)
      by (rewrite E1; sib_cbn; repeat split).
    destruct Em1 as (Es1 & Er1 & Ei1 & Ea1 & Eo1 & Ein1 & Eout1 & Et1).
    assert (B81: m_bits m1 mod 8 = 0) by (unfold m1, needbits; apply sibc_needbits_mod8; lia).
    destruct (Z.eqb_spec (m_leave m1) 1) as [Lv|Lv].
    + (* the input ends before the trailer: the abstract state stays *)
      apply sib_out_stay.
      * rewrite E1. apply sib_rel_bits; [exact R0|rewrite <- E1; exact BB1|rewrite <- E1; exact Qn|].
        unfold bits_ok. cbv zeta. unfold m_mode in M. rewrite M.
        split; [intros X; exfalso; revert X; sib_mdg|].
        split; [intros X; exfalso; revert X; sib_mdg|intros _; exact B81].
      * intros _. unfold stop_ok. rewrite A. unfold a_CHECK.
        destruct (Z.eqb_spec (i_wrap (a_s a)) 0) as [X|_]; [contradiction|]. cbv iota zeta. cbn [negb].
        destruct (LV1 ltac:(lia)) as (_ & _ & _ & X).
        match goal with |- context [if ?b then _ else _] => destruct b end; unfold abad, ago; cbv iota;
          (split; [rewrite Er1; exact Ret|right; right; left; left; rewrite Q; exact X]).
    + (* the 32 bits are there: hold is the trailer's check field *)
      assert (L1: m_leave m1 = 0) by (destruct (Z.eq_dec (m_leave m1) 0) as [X|X]; [exact X|];
                                       destruct (LV1 X) as [X1 _]; contradiction).
      assert (Bm1: m_bits m1 = 32)
        by (unfold m1; apply sib_needbits32_bits; [split; [lia|apply sibc_bits32; [lia|exact B8]]|exact B8|exact L1]).
      pose proof (bb_bits _ _ _ BB1) as Bb1. pose proof (bb_nx _ _ _ BB1) as Nx1.
      assert (H1: m_hold m1 = sbits src (a_q a) 32) by (rewrite (bb_hold _ _ _ BB1), Qn, Bm1, Q; reflexivity).
      assert (Iq: a_q a + 32 <= 8 * (P0 + Zlength (m_inp m))).
      { rewrite Q, <- Qn. unfold mq. rewrite Ei1 in Nx1. lia. }
      (* out: the bytes written by this call *)
      assert (Eo: u32 (m_out m1 - (m_aout m1 - Zlength (m_ow m1))) = Zlength (m_ow m)).
      { rewrite Eout1, Ea1, Eo1, Out. unfold u32. rewrite Z.mod_small; [lia|].
        pose proof (Zlength_nonneg (m_ow m)). rep_lia. }
      rewrite Eo.
      set (mT := upd_s (set_m_tout m1 (u64 (m_tout m1 + Zlength (m_ow m))))
                   (fun s => set_i_total s (u64 (i_total s + Zlength (m_ow m))))).
      assert (WT: i_wrap (m_s mT) = i_wrap (a_s a)) by (unfold mT, upd_s; sib_cbn; rewrite Es1; exact Ew).
      rewrite WT. rewrite (proj2 (Z.eqb_neq _ _) W4). cbn [negb andb].
      destruct (Z.eqb_spec (Zlength (m_ow m)) 0) as [Z0|Z0]; cbn [negb andb].
      * eapply (sibc_check_tail K0 flush src P0 O0 a (set_m_out mT (m_left mT)));
          [unfold mT, upd_s; sib_cbn; rewrite Ei1; reflexivity|exact Ma|eapply sib_bb_ext; [..|exact BB1]; reflexivity|
         rewrite (sib_mq_ext P0 m1) by reflexivity; rewrite Qn; symmetry; exact Q|..];
          unfold mT, m_left, upd_s; sib_cbn; rewrite ?Es1, ?Ei1, ?Ea1, ?Eo1, ?Ein1, ?Eout1, ?Et1, ?Er1, ?L1, ?Bm1, ?H1;
          try assumption; try reflexivity; try lia.
        all: try (apply sib_seq_check_l; apply sib_seq_total_l; exact S).
        all: try (apply sib_seq_total_l; exact S).
        all: try (rewrite Tot, rl_O, Zlength_app, sibc_u64_add; reflexivity).
        all: try (rewrite rl_tout, Out, sibc_u64_add; f_equal; lia).
        apply Zlength_nil_inv in Z0. rewrite Chk0, rl_O, Z0, app_nil_r. reflexivity.
      * eapply (sibc_check_tail K0 flush src P0 O0 a);
          [unfold mT, upd_s; sib_cbn; rewrite Ei1; reflexivity|exact Ma|eapply sib_bb_ext; [..|exact BB1]; reflexivity|
         rewrite (sib_mq_ext P0 m1) by reflexivity; rewrite Qn; symmetry; exact Q|..];
          unfold mT, m_left, upd_s; sib_cbn; rewrite ?Es1, ?Ei1, ?Ea1, ?Eo1, ?Ein1, ?Eout1, ?Et1, ?Er1, ?L1, ?Bm1, ?H1;
          try assumption; try reflexivity; try lia.
        all: try (apply sib_seq_check_l; apply sib_seq_total_l; exact S).
        all: try (apply sib_seq_total_l; exact S).
        all: try (rewrite Tot, rl_O, Zlength_app, sibc_u64_add; reflexivity).
        all: try (rewrite rl_tout, Out, sibc_u64_add; f_equal; lia).
        rewrite Z.sub_diag, sublist_same by reflexivity. rewrite Chk0, Ef, rl_O.
        apply sib_check_app; [exact BO|exact Val].
Qed.
