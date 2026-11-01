(* The simulation of the modes TYPE and TYPEDO: the block header (BFINAL, BTYPE), or the end of the last
   block (BYTEBITS, then CHECK). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_split_invariant.SIDefs.
Require Import Zlib.proof.harness.api_split_invariant.SISimBlockKit.
Import ListNotations.
Local Open Scope Z_scope.

Local Notation MTYPE := Zlib.proof.inflate.Model.TYPE.

(* one block type of TYPEDO: the machine Y after BFINAL (BTYPE still to drop), the abstract state t after
   the header's three bits *)
Lemma sib_typedo_br (K: kit_bits_stmt) src P0 O0 mT a0 a1 I R Y t :
  rel src P0 O0 mT a1 -> data_mode (m_mode mT) -> m_mode mT <> CHECK ->
  areach src I R a0 a1 ->
  astep lenfix_list distfix_list src a1 = AGo (a_q a1 + 3) false (AS t (a_q a1 + 3) (a_O a1)) ->
  a_q a1 + 3 <= 8 * I ->
  bitbuf src P0 Y -> 2 <= m_bits Y -> mq P0 Y = a_q a1 + 1 ->
  m_inp Y = m_inp mT -> m_aout Y = m_aout mT -> m_ow Y = m_ow mT -> m_in Y = m_in mT ->
  m_out Y = m_out mT -> m_tout Y = m_tout mT -> m_ret Y = m_ret mT ->
  m_mode Y = i_mode t -> (i_mode t = BAD \/ data_mode (i_mode t)) -> bits_ok (m_s Y) (m_bits Y - 2) ->
  (i_mode t <> BAD -> seq (m_s Y) t) ->
  i_check (m_s Y) = i_check (m_s mT) -> i_check t = i_check (a_s a1) -> i_flags t = i_flags (a_s a1) ->
  i_wrap (m_s Y) = i_wrap (m_s mT) -> i_total (m_s Y) = i_total (m_s mT) ->
  i_wsize (m_s Y) = i_wsize (m_s mT) -> i_whave (m_s Y) = i_whave (m_s mT) ->
  i_wnext (m_s Y) = i_wnext (m_s mT) -> i_win (m_s Y) = i_win (m_s mT) ->
  i_wdata (m_s Y) = i_wdata (m_s mT) -> i_head (m_s Y) = i_head (m_s mT) ->
  areach src I R a0 (AS t (a_q a1 + 3) (a_O a1)) /\ rel src P0 O0 (dropbits 2 Y) (AS t (a_q a1 + 3) (a_O a1)).
Proof.
  intros R1 D NC T A Iq BBY B2 QY Ei Ea Eo Ein Eout Et Er Md Cl Bk S Ec Eca Ef Ew Etot Ws Wh Wn Wi Wd Hd.
  destruct K as (_ & _ & Kdrop & _).
  pose proof (bb_bits _ _ _ BBY) as BbY.
  destruct (Kdrop src P0 Y 2 BBY ltac:(lia)) as (BB3 & Q3 & _).
  pose proof (sib_dropbits_fields 2 Y) as (Fs & Fi & Fn & Fa & Fo & Fin & Fout & Ft & Fr & Fl).
  split.
  - eapply sib_ar_trans; [exact T|]. eapply sib_ar1f; [exact A|exact Iq].
  - unfold m_mode in Md, Cl.
    eapply sib_rel_dstep; [exact R1|exact D|exact NC|exact BB3|..];
      unfold m_mode; rewrite ?Fs, ?Fi, ?Fn, ?Fa, ?Fo, ?Fin, ?Fout, ?Ft, ?Fr; cbn [a_s a_q a_O a_mode];
      try rewrite Md; auto.
    + rewrite sib_dropbits_bits by lia. exact Bk.
    + intros _. rewrite Q3, QY. lia.
Qed.

(* the field equations of a machine built from Y1 *)
Ltac sib_brf Fs Fi Fa Fo Fin Fout Ft Fr :=
  unfold m_mode; sib_cbn; rewrite ?Fs, ?Fi, ?Fa, ?Fo, ?Fin, ?Fout, ?Ft, ?Fr; sib_cbn; try reflexivity.

(* c_TYPEDO from a machine in TYPE (c_TYPE goes on into it without setting the mode) or in TYPEDO: m is
   related to a0, m in TYPEDO to a1, reached from a0 by free steps; when NEEDBITS(3) leaves, the stop is
   seen from a0 (hypothesis HS) *)
Lemma sib_typedo (K: kit_bits_stmt) flush src P0 O0 m a0 a1 :
  let I := P0 + Zlength (m_inp m) in let R := Zlength O0 + m_aout m in
  rel src P0 O0 m a0 -> rel src P0 O0 (set_mode m TYPEDO) a1 -> m_leave m = 0 ->
  (m_mode m = MTYPE \/ m_mode m = TYPEDO) -> areach src I R a0 a1 ->
  (forall m', m_ret m' = Z_OK -> i_last (a_s a1) = 0 -> 8 * I < a_q a1 + 3 -> stop_ok flush src I R m' a0) ->
  sib_out flush src P0 O0 I R a0 (c_TYPEDO flush m).
Proof.
  intros I R R0 R1 L Md T HS. pose proof K as K0.
  destruct K as (Kpull & Knb & Kdrop & Kinit & Kbyte & Kmod & Kshr & Krange & Kbyte8).
  pose proof (rl_bb _ _ _ _ _ R0) as BB.
  assert (D1: data_mode (m_mode (set_mode m TYPEDO))) by (cbn; sib_mdg).
  assert (Ma1: a_mode a1 = TYPEDO) by (rewrite <- (rl_mode _ _ _ _ _ R1); reflexivity).
  assert (Q1: a_q a1 = mq P0 m) by (rewrite (rl_q _ _ _ _ _ R1) by (cbn; sib_mdg); reflexivity).
  assert (S1: seq (set_i_mode (m_s m) TYPEDO) (a_s a1)) by (apply (rl_s _ _ _ _ _ R1); cbn; sib_mdg).
  assert (A1: astep lenfix_list distfix_list src a1 = a_TYPEDO src a1) by (apply sib_a_TYPEDO; exact Ma1).
  assert (Ret: m_ret m = Z_OK) by (apply (rl_ret _ _ _ _ _ R0); destruct Md as [E|E]; rewrite E; sib_mdg).
  assert (Lst: i_last (m_s m) = i_last (a_s a1)) by (apply (se_last _ _ S1)).
  unfold c_TYPEDO.
  destruct (Z.eqb_spec (i_last (m_s m)) 0) as [L0|L0]; cbn [negb].
  - (* NEEDBITS(3), then BFINAL and BTYPE *)
    destruct (Knb src P0 m 3 BB L ltac:(lia)) as (BB1 & Qn & E1 & OK1 & LV1).
    cbv zeta. set (m1 := needbits 3 m) in *.
    assert (Em1: m_s m1 = m_s m /\ m_ret m1 = m_ret m /\ m_inp m1 = m_inp m /\ m_aout m1 = m_aout m /\
                 m_ow m1 = m_ow m /\ m_in m1 = m_in m /\ m_out m1 = m_out m /\ m_tout m1 = m_tout m)
      by (rewrite E1; sib_cbn; repeat split).
    destruct Em1 as (Es1 & Er1 & Ei1 & Ea1 & Eo1 & Ein1 & Eout1 & Et1).
    destruct (Z.eqb_spec (m_leave m1) 1) as [Lv|Lv].
    + (* the input ends: the abstract state stays *)
      apply sib_out_stay.
      * rewrite E1. apply sib_rel_bits; [exact R0|rewrite <- E1; exact BB1|rewrite <- E1; exact Qn|].
        apply sib_bits_free; destruct Md as [E|E]; unfold m_mode in E; rewrite E; sib_mdg.
      * intros _. apply HS; [rewrite Er1; exact Ret|rewrite <- Lst; exact L0|].
        destruct (LV1 ltac:(lia)) as (_ & _ & _ & X). rewrite Q1. exact X.
    + (* the three bits are there *)
      assert (L1: m_leave m1 = 0) by (destruct (Z.eq_dec (m_leave m1) 0) as [X|X]; [exact X|];
                                       destruct (LV1 X) as [X1 _]; contradiction).
      destruct (OK1 L1) as (B3 & Bmx & Hh).
      pose proof (bb_bits _ _ _ BB1) as Bb1.
      assert (BBX: bitbuf src P0 (upd_s m1 (fun s => set_i_last s (bitsn m1 1))))
        by (eapply sib_bb_ext; [..|exact BB1]; reflexivity).
      destruct (Kdrop _ _ _ 1 BBX ltac:(sib_cbn; lia)) as (BB2 & Q2 & Hb1).
      assert (QX: mq P0 (upd_s m1 (fun s => set_i_last s (bitsn m1 1))) = a_q a1)
        by (rewrite (sib_mq_ext P0 m1) by reflexivity; rewrite Qn, Q1; reflexivity).
      rewrite QX in Q2, Hb1. change (bitsn (upd_s m1 _) 1) with (bitsn m1 1) in Hb1.
      assert (Bm2: m_bits (dropbits 1 (upd_s m1 (fun s => set_i_last s (bitsn m1 1)))) = m_bits m1 - 1)
        by (rewrite sib_dropbits_bits by (sib_cbn; lia); reflexivity).
      destruct (Kdrop _ _ _ 2 BB2 ltac:(rewrite Bm2; lia)) as (_ & _ & Hb2). rewrite Q2 in Hb2.
      rewrite Hb2, Hb1.
      assert (Ea: astep lenfix_list distfix_list src a1 =
                  let s := set_i_last (a_s a1) (sbits src (a_q a1) 1) in
                  let bt := sbits src (a_q a1 + 1) 2 in
                  if bt =? 0 then ago a1 (a_q a1 + 3) (set_i_mode s STORED)
                  else if bt =? 1 then
                    ago a1 (a_q a1 + 3) (set_i_mode (set_i_distbits (set_i_distcode (set_i_lenbits
                      (set_i_lencode s TLenfix) 9) TDistfix) 5) LEN_)
                  else if bt =? 2 then ago a1 (a_q a1 + 3) (set_i_mode s TABLE)
                  else abad (AS s (a_q a1) (a_O a1)) (a_q a1 + 3)).
      { rewrite A1. unfold a_TYPEDO. rewrite <- Lst, L0. reflexivity. }
      clear A1. cbv zeta in Ea.
      set (b1 := sbits src (a_q a1) 1) in *. set (bt := sbits src (a_q a1 + 1) 2) in *.
      rewrite Hb1 in BBX, BB2, Q2, Bm2.
      assert (Iq: a_q a1 + 3 <= 8 * I).
      { rewrite Q1, <- Qn. unfold mq, I. pose proof (bb_nx _ _ _ BB1). rewrite Ei1 in *. lia. }
      assert (S2: seq (set_i_last (m_s m) b1) (set_i_last (a_s a1) b1))
        by (apply sib_seq_last, (sib_seq_lmode _ _ TYPEDO), S1).
      (* Y: the machine before DROPBITS(2); t: the abstract state *)
      set (Y1 := dropbits 1 (upd_s m1 (fun s => set_i_last s b1))) in *.
      assert (FY: m_s Y1 = set_i_last (m_s m) b1 /\ m_inp Y1 = m_inp m /\ m_aout Y1 = m_aout m /\
                  m_ow Y1 = m_ow m /\ m_in Y1 = m_in m /\ m_out Y1 = m_out m /\ m_tout Y1 = m_tout m /\
                  m_ret Y1 = m_ret m /\ m_leave Y1 = 0)
        by (unfold Y1, dropbits; sib_cbn; rewrite Es1, Ei1, Ea1, Eo1, Ein1, Eout1, Et1, Er1, L1; repeat split).
      destruct FY as (Fs & Fi & Fa & Fo & Fin & Fout & Ft & Fr & Fl).
      clearbody Y1.
      destruct (Z.eqb_spec bt 0) as [B0|B0];
        cbv iota in Ea |- *.
      { (* stored *)
        edestruct (sib_typedo_br K0 src P0 O0 (set_mode m TYPEDO) a0 a1 I R (set_mode Y1 STORED)
                     (set_i_mode (set_i_last (a_s a1) b1) STORED)) as [Ta Ra];
          [exact R1|exact D1|sib_cbn; sib_mdg|exact T|exact Ea|exact Iq|..];
          [| |sib_brf Fs Fi Fa Fo Fin Fout Ft Fr..|].
        all: try (eapply sib_bb_ext; [..|exact BB2]; reflexivity).
        all: try (sib_cbn; lia).
        all: try (rewrite <- Q2; apply sib_mq_ext; reflexivity).
        all: try (right; sib_mdg).
        all: try (apply sib_bits_free; sib_cbn; sib_mdg).
        all: try (intros _; apply sib_seq_mode0; [exact S2|sib_mdg..]).
        eapply sib_out_go; [exact Ta|exact Ra|]. unfold dropbits, set_mode, upd_s. sib_cbn. exact Fl. }
      destruct (Z.eqb_spec bt 1) as [B1|B1]; cbv iota in Ea |- *.
      { (* fixed: Z_TREES stops at LEN_ *)
        destruct (Z.eqb_spec flush Z_TREES) as [BT|BT]; cbv iota.
        -         edestruct (sib_typedo_br K0 src P0 O0 (set_mode m TYPEDO) a0 a1 I R (set_mode (upd_s Y1 (fun s : istate => set_i_distbits (set_i_distcode (set_i_lenbits (set_i_lencode s TLenfix) 9) TDistfix) 5)) LEN_)
                     (set_i_mode (set_i_distbits (set_i_distcode (set_i_lenbits (set_i_lencode (set_i_last (a_s a1) b1) TLenfix) 9) TDistfix) 5) LEN_)) as [Ta Ra];
          [exact R1|exact D1|sib_cbn; sib_mdg|exact T|exact Ea|exact Iq|..];
          [| |sib_brf Fs Fi Fa Fo Fin Fout Ft Fr..|].
        all: try (eapply sib_bb_ext; [..|exact BB2]; reflexivity).
        all: try (sib_cbn; lia).
        all: try (rewrite <- Q2; apply sib_mq_ext; reflexivity).
        all: try (right; sib_mdg).
        all: try (left; reflexivity).
        all: try (apply sib_bits_free; sib_cbn; sib_mdg).
        all: try (intros X; contradiction).
        all: try (intros _; apply sib_seq_mode0; [apply sib_seq_distbits, sib_seq_distcode, sib_seq_lenbits, sib_seq_lencode, S2|sib_mdg..]).

        exists (AS (set_i_mode (set_i_distbits (set_i_distcode (set_i_lenbits (set_i_lencode (set_i_last (a_s a1) b1) TLenfix) 9) TDistfix) 5) LEN_) (a_q a1 + 3) (a_O a1)). split; [exact Ta|]. split.
        { unfold set_leave. apply sib_rel_leave. exact Ra. }
        intros _. unfold stop_ok. rewrite sib_a_LEN_ by reflexivity. unfold a_LEN_, ago. cbv iota.
        split; [unfold set_leave, dropbits, set_mode, upd_s; sib_cbn; rewrite Fr; exact Ret|].
        right. left. exact BT.
        -         edestruct (sib_typedo_br K0 src P0 O0 (set_mode m TYPEDO) a0 a1 I R (set_mode (upd_s Y1 (fun s : istate => set_i_distbits (set_i_distcode (set_i_lenbits (set_i_lencode s TLenfix) 9) TDistfix) 5)) LEN_)
                     (set_i_mode (set_i_distbits (set_i_distcode (set_i_lenbits (set_i_lencode (set_i_last (a_s a1) b1) TLenfix) 9) TDistfix) 5) LEN_)) as [Ta Ra];
          [exact R1|exact D1|sib_cbn; sib_mdg|exact T|exact Ea|exact Iq|..];
          [| |sib_brf Fs Fi Fa Fo Fin Fout Ft Fr..|].
        all: try (eapply sib_bb_ext; [..|exact BB2]; reflexivity).
        all: try (sib_cbn; lia).
        all: try (rewrite <- Q2; apply sib_mq_ext; reflexivity).
        all: try (right; sib_mdg).
        all: try (left; reflexivity).
        all: try (apply sib_bits_free; sib_cbn; sib_mdg).
        all: try (intros X; contradiction).
        all: try (intros _; apply sib_seq_mode0; [apply sib_seq_distbits, sib_seq_distcode, sib_seq_lenbits, sib_seq_lencode, S2|sib_mdg..]).
        eapply sib_out_go; [exact Ta|exact Ra|]. unfold dropbits, set_mode, set_bad, upd_s. sib_cbn. exact Fl.
      }
      destruct (Z.eqb_spec bt 2) as [B2|B2]; cbv iota in Ea |- *.
      { (* dynamic *)
        edestruct (sib_typedo_br K0 src P0 O0 (set_mode m TYPEDO) a0 a1 I R (set_mode Y1 TABLE)
                     (set_i_mode (set_i_last (a_s a1) b1) TABLE)) as [Ta Ra];
          [exact R1|exact D1|sib_cbn; sib_mdg|exact T|exact Ea|exact Iq|..];
          [| |sib_brf Fs Fi Fa Fo Fin Fout Ft Fr..|].
        all: try (eapply sib_bb_ext; [..|exact BB2]; reflexivity).
        all: try (sib_cbn; lia).
        all: try (rewrite <- Q2; apply sib_mq_ext; reflexivity).
        all: try (right; sib_mdg).
        all: try (left; reflexivity).
        all: try (apply sib_bits_free; sib_cbn; sib_mdg).
        all: try (intros X; contradiction).
        all: try (intros _; apply sib_seq_mode0; [exact S2|sib_mdg..]).
        eapply sib_out_go; [exact Ta|exact Ra|]. unfold dropbits, set_mode, set_bad, upd_s. sib_cbn. exact Fl. }
      (* reserved block type *)
        edestruct (sib_typedo_br K0 src P0 O0 (set_mode m TYPEDO) a0 a1 I R (set_bad Y1 M_btype)
                     (set_i_mode (set_i_last (a_s a1) b1) BAD)) as [Ta Ra];
          [exact R1|exact D1|sib_cbn; sib_mdg|exact T|exact Ea|exact Iq|..];
          [| |sib_brf Fs Fi Fa Fo Fin Fout Ft Fr..|].
        all: try (eapply sib_bb_ext; [..|exact BB2]; reflexivity).
        all: try (sib_cbn; lia).
        all: try (rewrite <- Q2; apply sib_mq_ext; reflexivity).
        all: try (right; sib_mdg).
        all: try (left; reflexivity).
        all: try (apply sib_bits_free; sib_cbn; sib_mdg).
        all: try (intros X; contradiction).
        all: try (intros _; apply sib_seq_mode0; [exact S2|sib_mdg..]).
        eapply sib_out_go; [exact Ta|exact Ra|]. unfold dropbits, set_mode, set_bad, upd_s. sib_cbn. exact Fl.
  - (* the last block is done: BYTEBITS, CHECK *)
    destruct (Kbyte src P0 m BB) as [BBb Qb].
    pose proof (sib_bytebits_bits m ltac:(pose proof (bb_bits _ _ _ BB); lia)) as [Bb8 Bb].
    assert (Ia: align8 (a_q a1) <= 8 * I).
    { rewrite Q1. unfold mq. pose proof (bb_nx _ _ _ BB). pose proof (bb_bits _ _ _ BB).
      pose proof (sib_align8_le (P0 + m_nx m) (m_bits m) ltac:(lia)). unfold I. lia. }
    exists (AS (set_i_mode (a_s a1) CHECK) (align8 (a_q a1)) (a_O a1)). split; [|split].
    + eapply sib_ar_trans; [exact T|]. eapply sib_ar1f; [|exact Ia].
      rewrite A1. unfold a_TYPEDO. rewrite <- Lst. destruct (Z.eqb_spec (i_last (m_s m)) 0); [contradiction|].
      reflexivity.
    + eapply sib_rel_dstep; [exact R1|exact D1|cbn; sib_mdg|..]; sib_cbn; try reflexivity.
      * eapply sib_bb_ext; [..|exact BBb]; reflexivity.
      * unfold bits_ok. cbn. split; [sib_mdg|]. split; [sib_mdg|]. intros _. exact Bb8.
      * right. sib_mdg.
      * intros _. rewrite (sib_mq_ext P0 (bytebits m) (set_mode (bytebits m) CHECK)) by reflexivity.
        rewrite Qb, Q1. reflexivity.
      * intros _. rewrite <- (sib_mode_mode (m_s m) TYPEDO). apply sib_seq_mode0; [exact S1|sib_mdg..].
    + intros X. unfold bytebits in X. sib_cbn. rewrite L in X. discriminate.
Qed.

(* TYPEDO's step reads three bits when the block is not the last one: it is blocked when they are not in
   the call's input *)
Lemma sib_typedo_blk src I R a1 :
  a_mode a1 = TYPEDO -> i_last (a_s a1) = 0 -> 8 * I < a_q a1 + 3 ->
  blocked I R a1 (astep lenfix_list distfix_list src a1).
Proof.
  intros M L Q. rewrite sib_a_TYPEDO by exact M. unfold a_TYPEDO. rewrite L. cbn [Z.eqb negb].
  destruct (sbits src (a_q a1 + 1) 2 =? 0); [cbn; left; exact Q|].
  destruct (sbits src (a_q a1 + 1) 2 =? 1); [cbn; left; exact Q|].
  destruct (sbits src (a_q a1 + 1) 2 =? 2); cbn; left; exact Q.
Qed.

(* setting the mode a machine already has *)
Lemma sib_rel_mode_same src P0 O0 m a v :
  m_mode m = v -> rel src P0 O0 m a -> rel src P0 O0 (set_mode m v) a.
Proof.
  intros E R. unfold m_mode in E. subst v. destruct R. unfold m_left, m_mode in *.
  constructor; sib_cbn; auto.
  all: try (eapply sib_bb_ext; [..|exact rl_bb]; reflexivity).
  all: try (intros X; destruct (rl_s X); constructor; sib_cbn; auto).
  all: try (intros X; eapply sib_swin_ext; [..|exact (rl_win X)]; reflexivity).
Qed.

Lemma sib_TYPEDO : kit_stmt -> sib_case TYPEDO.
Proof.
  intros [K _] flush src P0 O0 m a R W L M. rewrite sib_c_TYPEDO by exact M.
  apply (sib_typedo K flush src P0 O0 m a a R (sib_rel_mode_same _ _ _ _ _ _ M R) L (or_intror M) (ar_refl _ _ _ _)).
  intros m' Rt L0 Q. pose proof (rl_mode _ _ _ _ _ R) as Ma. rewrite M in Ma.
  pose proof (sib_typedo_blk src (P0 + Zlength (m_inp m)) (Zlength O0 + m_aout m) a (eq_sym Ma) L0 Q) as B.
  unfold stop_ok. destruct (astep lenfix_list distfix_list src a) as [n w a2|r]; [|contradiction].
  split; [exact Rt|]. right. right. left. exact B.
Qed.

Lemma sib_TYPE : kit_stmt -> sib_case MTYPE.
Proof.
  intros [K _] flush src P0 O0 m a R W L M. rewrite sib_c_TYPE by exact M. unfold c_TYPE.
  pose proof (rl_mode _ _ _ _ _ R) as Ma. rewrite M in Ma.
  assert (A: astep lenfix_list distfix_list src a =
             AGo (a_q a) false (AS (set_i_mode (a_s a) TYPEDO) (a_q a) (a_O a)))
    by (rewrite sib_a_TYPE by (symmetry; exact Ma); reflexivity).
  assert (Ret: m_ret m = Z_OK) by (apply (rl_ret _ _ _ _ _ R); rewrite M; sib_mdg).
  destruct (orb (flush =? Z_BLOCK) (flush =? Z_TREES)) eqn:F.
  - (* Z_BLOCK / Z_TREES: stop at the block boundary *)
    apply sib_out_stay; [apply sib_rel_leave; exact R|].
    intros _. unfold stop_ok. rewrite A. split; [exact Ret|].
    apply orb_true_iff in F. destruct F as [F|F]; apply Z.eqb_eq in F; auto.
  - set (a1 := AS (set_i_mode (a_s a) TYPEDO) (a_q a) (a_O a)).
    assert (Q: a_q a = mq P0 m) by (apply (rl_q _ _ _ _ _ R); rewrite M; sib_mdg).
    assert (T: areach src (P0 + Zlength (m_inp m)) (Zlength O0 + m_aout m) a a1).
    { eapply sib_ar1f; [exact A|]. rewrite Q. apply (sib_mq_le src), (rl_bb _ _ _ _ _ R). }
    apply (sib_typedo K flush src P0 O0 m a a1 R); [| |left; exact M|exact T|].
    + unfold a1. eapply sib_rel_dstep; [exact R|rewrite M; sib_mdg|rewrite M; sib_mdg|..]; sib_cbn; try reflexivity.
      * eapply sib_bb_ext; [..|exact (rl_bb _ _ _ _ _ R)]; reflexivity.
      * apply sib_bits_free; sib_cbn; sib_mdg.
      * right. sib_mdg.
      * intros _. rewrite Q. apply sib_mq_ext; reflexivity.
      * intros _. apply sib_seq_mode0; [apply (rl_s _ _ _ _ _ R); rewrite M; sib_mdg|sib_mdg..].
    + exact L.
    + intros m' Rt L0 Qb. unfold stop_ok. rewrite A. split; [exact Rt|]. right. right.
      right. split; [symmetry; exact Ma|]. apply sib_typedo_blk; auto.
Qed.
