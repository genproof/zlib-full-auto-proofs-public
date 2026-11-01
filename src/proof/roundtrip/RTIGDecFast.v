(* RT-I: copy of rfc1951/DecFast.v over the generalized definitions RTIGDefs.v. *)
(* Part of the decode theory: inflate_fast.  Definitions: DecodeDefs.v / Decode.v.
   The parts: RTIGDecFastKit.v (the invariant of the loop and the statements),
   RTIGDecFast{Walk,Blk,Copy,Iter}.v (one pass of the loop); here the loop, the unused bytes given back, and Kd. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTIGDefs.
Require Import Zlib.proof.roundtrip.RTIGDecFastKit.
Require Import Zlib.proof.roundtrip.RTIGDecFastWalk Zlib.proof.roundtrip.RTIGDecFastBlk Zlib.proof.roundtrip.RTIGDecFastCopy Zlib.proof.roundtrip.RTIGDecFastIter.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* the loop                                                                                       *)

Lemma fset_proj m0 nx ow hold bits :
  m_inp (fset m0 nx ow hold bits) = m_inp m0 /\ m_aout (fset m0 nx ow hold bits) = m_aout m0 /\
  m_s (fset m0 nx ow hold bits) = m_s m0.
Proof. repeat split. Qed.

Lemma dfast_loop (K: dkit_stmt) (I: iter_stmt) : forall n G pos ob m0 m k j ll dl syms,
    dctx_ok G -> 0 <= pos -> pos + Zlength (m_inp m0) <= Zlength (dc_src G) ->
    m_inp m0 = sublist pos (pos + Zlength (m_inp m0)) (dc_src G) ->
    mwf3 m0 -> m_mode m0 = LEN -> win_ok G (m_s m0) ob -> glob_ok G (m_s m0) ->
    fi G pos ob m0 m k j ll dl syms ->
    m_nx m + 6 <= Zlength (m_inp m0) -> Zlength (m_ow m) + 258 <= m_aout m0 ->
    m_aout m0 - Zlength (m_ow m) < Z.of_nat n ->
    let mf := fast_loop lenfix_list distfix_list n m in
    (exists j', fi G pos ob m0 mf k j' ll dl syms) \/
    (exists mt, mf = set_mode mt Zlib.proof.inflate.Model.TYPE /\ fe G pos ob m0 mt k).
Proof.
  induction n; intros G pos ob m0 m k j ll dl syms HG Hp Hl Hi W HM Hw Hgl F Hn Ho Hf.
  - simpl in Hf. lia.
  - cbv zeta. cbn [fast_loop].
    pose proof (I G pos ob m0 m k j ll dl syms HG Hp Hl Hi W HM Hw Hgl F Hn Ho) as IT.
    destruct (fast_iter lenfix_list distfix_list m) as [go m1].
    destruct IT as [(Hj & -> & F1 & Hgrow) | (Hj & -> & mt & -> & FE)].
    + pose proof (fi_m _ _ _ _ _ _ _ _ _ _ F1) as E1.
      assert (Ei: m_inp m1 = m_inp m0) by (rewrite E1; reflexivity).
      assert (Ea: m_aout m1 = m_aout m0) by (rewrite E1; reflexivity).
      rewrite Ei, Ea.
      destruct (m_nx m1 <? Zlength (m_inp m0) - 5) eqn:C1; cbn [andb];
        [destruct (Zlength (m_ow m1) <? m_aout m0 - 257) eqn:C2|].
      * apply Z.ltb_lt in C1, C2.
        apply (IHn G pos ob m0 m1 k (j + 1) ll dl syms); auto; try lia.
      * left. exists (j + 1). exact F1.
      * left. exists (j + 1). exact F1.
    + right. exists mt. split; [reflexivity | exact FE].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the fields of the state inflate_fast keeps                                                     *)

Definition ssame (s s': istate) : Prop :=
  i_last s' = i_last s /\ i_wrap s' = i_wrap s /\ i_head s' = i_head s /\ i_wbits s' = i_wbits s /\
  i_flags s' = i_flags s /\ i_wsize s' = i_wsize s /\ i_whave s' = i_whave s /\ i_wnext s' = i_wnext s /\
  i_wdata s' = i_wdata s /\ i_check s' = i_check s /\ i_total s' = i_total s /\
  i_lencode s' = i_lencode s /\ i_lenbits s' = i_lenbits s /\ i_distcode s' = i_distcode s /\
  i_distbits s' = i_distbits s /\ i_codes s' = i_codes s.

Lemma tdec_ext s s' t root type lens :
  i_codes s' = i_codes s -> tdec s t root type lens -> tdec s' t root type lens.
Proof. intros E. unfold tdec, twalk, tab_entry. rewrite E. auto. Qed.

Lemma in_huff_ext G s s' k j ll dl syms p0 :
  ssame s s' -> in_huff G s k j ll dl syms p0 -> in_huff G s' k j ll dl syms p0.
Proof.
  intros (E1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E12 & E13 & E14 & E15 & E16).
  unfold in_huff, in_blk. rewrite E1, E12, E13, E14, E15.
  intros (A & B & C & D & E & F).
  refine (conj A (conj B (conj C (conj _ (conj _ F))))); eapply tdec_ext; eauto.
Qed.

Lemma win_ok_ext G s s' ob : ssame s s' -> win_ok G s ob -> win_ok G s' ob.
Proof.
  intros (_ & _ & _ & E4 & _ & E6 & E7 & E8 & E9 & _).
  unfold win_ok, win_at. rewrite E4, E6, E7, E8, E9. auto.
Qed.

Lemma glob_ok_ext G s s' :
  ssame s s' -> i_mode s <> HEAD -> i_mode s <> FLAGS -> i_mode s' <> HEAD -> i_mode s' <> FLAGS ->
  glob_ok G s -> glob_ok G s'.
Proof.
  intros (_ & E2 & E3 & E4 & E5 & _) H1 H0 H2 H3 (A & B & C & D).
  unfold glob_ok. rewrite E2, E3, E4, E5.
  destruct A as (wb0 & A1 & _). split; [exists wb0; split; [exact A1 | intros; contradiction]|].
  split; [exact B|]. split; [intros _; apply C; exact H1|].
  intros W _ _. apply D; auto.
Qed.

Lemma chk_ok_ext G s s' ob ow ow' :
  ssame s s' -> i_mode s = LEN -> (i_mode s' = LEN \/ i_mode s' = Zlib.proof.inflate.Model.TYPE) ->
  chk_ok G s ob ow -> chk_ok G s' ob ow'.
Proof.
  intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & E10 & E11 & _) H1 H2 C.
  unfold chk_ok in *. rewrite E10, E11. rewrite H1 in C.
  intros W _ _ _ _. specialize (C W ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)).
  destruct H2 as [H2|H2]; rewrite H2; exact C.
Qed.

(* Kd moves to a machine with the same fields but the locals and the state's mode (LEN or TYPE) *)
Lemma kd_final G pos inp ob m m' :
  Kd G pos inp ob m -> m_mode m = LEN ->
  (m_mode m' = LEN \/ m_mode m' = Zlib.proof.inflate.Model.TYPE) -> ssame (m_s m) (m_s m') ->
  m_inp m' = m_inp m -> m_tout m' = m_tout m -> m_out m' = m_out m -> m_aout m' = m_aout m ->
  m_ret m' = m_ret m ->
  at_mode G (m_s m') (pos + m_nx m') (m_hold m') (m_bits m') (ob ++ m_ow m') ->
  Kd G pos inp ob m'.
Proof.
  intros KD HM HM' S Ei Et Eo Ea Er AT.
  assert (N1: m_mode m' <> HEAD) by (unfold HEAD; destruct HM' as [-> | ->]; discriminate).
  assert (N2: m_mode m' <> FLAGS) by (unfold FLAGS; destruct HM' as [-> | ->]; discriminate).
  assert (AC: after_check G (m_mode m') = false).
  { unfold after_check. destruct HM' as [-> | ->]; cbn; apply andb_false_r. }
  assert (AC0: after_check G (m_mode m) = false).
  { unfold after_check. rewrite HM. cbn. apply andb_false_r. }
  destruct KD as [K1 K2 K3 K4 K5 K6 K7 K8].
  constructor.
  - congruence.
  - exact AT.
  - apply (glob_ok_ext G (m_s m)); auto; unfold m_mode in HM; rewrite HM; discriminate.
  - intros _. apply (win_ok_ext G (m_s m)); auto. apply K4. rewrite HM. unfold LEN, CHECK. lia.
  - exact (chk_ok_ext G (m_s m) (m_s m') ob (m_ow m) (m_ow m') S HM HM' K5).
  - rewrite AC. rewrite AC0 in K6. congruence.
  - rewrite AC. rewrite AC0 in K7. unfold m_left in *. congruence.
  - rewrite Er, K8. rewrite HM. unfold m_mode in *.
    destruct HM' as [E|E]; rewrite E; reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* at_mode at LEN and TYPE                                                                        *)

Ltac unfold_modes :=
  unfold HEAD, FLAGS, TIME, OS, Zlib.proof.inflate.Model.TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS,
    CODELENS, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, CHECK, LENGTH, DONE.

Lemma at_mode_len G s c hold bits out :
  at_mode G s c hold bits out -> i_mode s = LEN -> hold_ok G c hold bits /\ at_len G s (8 * c - bits) bits out.
Proof.
  intros [H D] HM. split; [exact H|]. cbv zeta in D. rewrite HM in D.
  repeat (destruct D as [[E A]|D]; [first [exact A | revert E; unfold_modes; intros E; exfalso; lia] |]).
  destruct D as [E _]. revert E; unfold_modes; intros E; exfalso; lia.
Qed.

Lemma at_mode_of_len G s c hold bits out :
  hold_ok G c hold bits -> i_mode s = LEN -> at_len G s (8 * c - bits) bits out -> at_mode G s c hold bits out.
Proof.
  intros H HM A. split; [exact H|]. cbv zeta. rewrite HM.
  do 8 right. left. split; [right; reflexivity | exact A].
Qed.

Lemma at_mode_of_type G s c hold bits out :
  hold_ok G c hold bits -> i_mode s = Zlib.proof.inflate.Model.TYPE -> at_type G s (8 * c - bits) bits out ->
  at_mode G s c hold bits out.
Proof.
  intros H HM A. split; [exact H|]. cbv zeta. rewrite HM.
  do 2 right. left. split; [left; reflexivity | exact A].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the unused bytes given back                                                                    *)

Definition ftail (m: mst) : mst :=
  let len := Z.shiftr (m_bits m) 3 in
  let m := set_m_nx m (m_nx m - len) in
  let bits := m_bits m - len * 8 in
  set_m_bits (set_m_hold m (m_hold m mod 2 ^ bits)) bits.

Lemma fast_eq m :
  fast lenfix_list distfix_list m = restore (ftail (fast_loop lenfix_list distfix_list (Z.to_nat (m_aout m) + 1) m)).
Proof. reflexivity. Qed.

Lemma tail_hold (K: dkit_stmt) G c hold bits :
  hold_ok G c hold bits ->
  let len := Z.shiftr bits 3 in let b' := bits - len * 8 in
  hold_ok G (c - len) (hold mod 2 ^ b') b' /\ 0 <= b' < 8 /\ 8 * (c - len) - b' = 8 * c - bits.
Proof.
  intros H. cbv zeta. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  pose proof H as (H1 & H2 & H3).
  pose proof (Z.mod_pos_bound bits 8 ltac:(lia)). pose proof (Z.div_mod bits 8 ltac:(lia)).
  pose proof (Z.div_pos bits 8 ltac:(lia) ltac:(lia)).
  assert (Eb: bits - bits / 8 * 8 = bits mod 8) by lia.
  rewrite Eb.
  pose proof (dk_bitsn K G c hold bits (bits mod 8) H ltac:(lia)) as Hn.
  split; [|split; lia].
  split; [lia|]. split; [lia|].
  rewrite Hn. f_equal. f_equal; lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the start: RESTORE, then the invariant of the loop                                              *)

Lemma mwf3_restore m : mwf3 m -> mwf3 (restore m).
Proof.
  intros [W S3]. split.
  - pose proof (mw_hold _ W) as WH. pose proof (mw_bits _ W) as WB. pose proof (mw_nx _ W) as WN.
    destruct W. constructor; cbn [restore upd_s set_m_s set_m_sow set_m_snx m_s m_h m_inp m_aout m_nx m_ow m_hold
      m_bits m_in m_out m_ret m_leave m_adler m_msg m_tin m_tout m_snx m_sow m_mode]; auto.
    + destruct mw_md; constructor; assumption.
    + destruct mw_s; constructor; cbn [set_i_bits set_i_hold i_mode i_last i_wrap i_havedict i_flags i_dmax i_check
        i_total i_head i_wbits i_wsize i_whave i_wnext i_win i_wdata i_hold i_bits i_length i_offset i_extra
        i_lencode i_distcode i_lenbits i_distbits i_ncode i_nlen i_ndist i_have i_next i_lens i_codes i_sane
        i_back i_was]; auto.
    + pose proof (Zlength_nonneg (m_ow m)). lia.
  - destruct S3; constructor; assumption.
Qed.

Lemma fset_self m : m = fset m (m_nx m) (m_ow m) (m_hold m) (m_bits m).
Proof. destruct m; reflexivity. Qed.

Lemma ssame_refl_restore m : ssame (m_s m) (m_s (restore m)).
Proof. repeat split. Qed.

Lemma fi_start G pos inp ob m :
  Kd G pos inp ob m -> mwf3 m -> m_mode m = LEN -> m_bits m < 8 ->
  exists k j ll dl syms, fi G pos ob (restore m) (restore m) k j ll dl syms.
Proof.
  intros KD W HM Hb.
  destruct (at_mode_len _ _ _ _ _ _ (kd_at _ _ _ _ _ KD) HM) as [HO AL].
  destruct AL as (k & j & ll & dl & syms & p0 & HU & Eo & Eq & _).
  exists k, j, ll, dl, syms.
  pose proof (mw_nx _ (mwf3_mwf _ W)) as WN. pose proof HO as (H1 & _).
  constructor.
  - apply fset_self.
  - apply (in_huff_ext G (m_s m)); [apply ssame_refl_restore|]. cbn. rewrite <- Eq in HU. exact HU.
  - exact Eo.
  - exact HO.
  - cbn. lia.
  - cbn. lia.
  - exists []. rewrite app_nil_r. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the end: the loop stopped at LEN (input or output margin) or at the end of the block (TYPE)        *)

Lemma final_len (K: dkit_stmt) G pos inp ob m mf k j ll dl syms :
  Kd G pos inp ob m -> m_mode m = LEN -> m_leave m = 0 ->
  fi G pos ob (restore m) mf k j ll dl syms ->
  let m' := restore (ftail mf) in
  m_mode m' = LEN /\ Kd G pos inp ob m' /\ m_leave m' = 0 /\ exists d, m_ow m' = m_ow m ++ d.
Proof.
  intros KD HM Hlv F.
  destruct F as [Em HU Eo HO Hb Hn Hw].
  pose proof (tail_hold K G (pos + m_nx mf) (m_hold mf) (m_bits mf) HO) as (T1 & T2 & T3).
  rewrite Em. cbv zeta.
  assert (Md: m_mode (restore (ftail (fset (restore m) (m_nx mf) (m_ow mf) (m_hold mf) (m_bits mf)))) = LEN)
    by exact HM.
  split; [exact Md|]. split; [|split; [exact Hlv | exact Hw]].
  apply (kd_final G pos inp ob m); auto; try reflexivity.
  - repeat split.
  - apply at_mode_of_len; [| exact HM |].
    + cbn -[Z.shiftr Z.pow Z.modulo Z.mul Z.sub Z.add]. replace (pos + (m_nx mf - Z.shiftr (m_bits mf) 3)) with (pos + m_nx mf - Z.shiftr (m_bits mf) 3) by lia.
      exact T1.
    + cbn -[Z.shiftr Z.pow Z.modulo Z.mul Z.sub Z.add]. exists k, j, ll, dl, syms, (8 * (pos + m_nx mf) - m_bits mf).
      split; [apply (in_huff_ext G (m_s (restore m))); [repeat split | exact HU]|].
      split; [exact Eo|]. split; [lia|]. left; lia.
Qed.

Lemma final_type (K: dkit_stmt) G pos inp ob m mt k :
  Kd G pos inp ob m -> m_mode m = LEN -> m_leave m = 0 ->
  fe G pos ob (restore m) mt k ->
  let m' := restore (ftail (set_mode mt Zlib.proof.inflate.Model.TYPE)) in
  m_mode m' = Zlib.proof.inflate.Model.TYPE /\
  let m'' := upd_s m' (fun s => set_i_back s (-1)) in
  Kd G pos inp ob m'' /\ m_leave m'' = 0 /\ exists d, m_ow m'' = m_ow m ++ d.
Proof.
  intros KD HM Hlv F.
  destruct F as [Em [Hk Hlast] Hq Eo HO Hb Hn Hw].
  pose proof (tail_hold K G (pos + m_nx mt) (m_hold mt) (m_bits mt) HO) as (T1 & T2 & T3).
  rewrite Em. cbv zeta. split; [reflexivity|].
  split; [|split; [exact Hlv | exact Hw]].
  apply (kd_final G pos inp ob m); auto; try reflexivity.
  - repeat split.
  - apply at_mode_of_type; [| reflexivity |].
    + cbn -[Z.shiftr Z.pow Z.modulo Z.mul Z.sub Z.add].
      replace (pos + (m_nx mt - Z.shiftr (m_bits mt) 3)) with (pos + m_nx mt - Z.shiftr (m_bits mt) 3) by lia.
      exact T1.
    + cbn -[Z.shiftr Z.pow Z.modulo Z.mul Z.sub Z.add lastflag]. exists (k + 1).
      split; [lia|]. split; [lia|]. split; [exact Eo|]. split; [lia|].
      replace (k + 1 =? 0) with false by lia. replace (k + 1 - 1) with k by lia. exact Hlast.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* inflate_fast from LEN                                                                          *)

Lemma dfast : dkit_stmt -> dfast_stmt.
Proof.
  intros K G pos inp ob m HG Hp Hl Hi KD W Hlv HM Hh Hlf Hb.
  pose proof (kd_inp _ _ _ _ _ KD) as Ei.
  destruct (fi_start G pos inp ob m KD W HM Hb) as (k & j & ll & dl & syms & F0).
  pose proof (mwf3_restore m W) as W1.
  assert (Hw1: win_ok G (m_s (restore m)) ob).
  { apply (win_ok_ext G (m_s m)); [apply ssame_refl_restore|]. apply (kd_win _ _ _ _ _ KD).
    rewrite HM. unfold LEN, CHECK. lia. }
  assert (Hg1: glob_ok G (m_s (restore m))).
  { apply (glob_ok_ext G (m_s m)); [apply ssame_refl_restore| | | | | exact (kd_glob _ _ _ _ _ KD)];
      cbn; unfold m_mode in HM; rewrite HM; discriminate. }
  assert (Ei1: m_inp (restore m) = inp) by exact Ei.
  unfold m_have, m_left in Hh, Hlf.
  assert (A1: Zlength (m_ow (restore m)) + 258 <= m_aout (restore m))
    by (change (Zlength (m_ow m) + 258 <= m_aout m); lia).
  assert (A2: m_nx (restore m) + 6 <= Zlength (m_inp (restore m)))
    by (change (m_nx m + 6 <= Zlength (m_inp m)); lia).
  assert (A3: m_aout (restore m) - Zlength (m_ow (restore m)) < Z.of_nat (Z.to_nat (m_aout (restore m)) + 1)).
  { change (m_aout m - Zlength (m_ow m) < Z.of_nat (Z.to_nat (m_aout m) + 1)).
    pose proof (Zlength_nonneg (m_ow m)). rewrite Nat2Z.inj_add, Z2Nat.id by lia. lia. }
  assert (A4: pos + Zlength (m_inp (restore m)) <= Zlength (dc_src G)) by (rewrite Ei1; exact Hl).
  assert (A5: m_inp (restore m) = sublist pos (pos + Zlength (m_inp (restore m))) (dc_src G))
    by (rewrite Ei1; exact Hi).
  pose proof (dfast_loop K (dfi K dfw (dfb K) dfc) (Z.to_nat (m_aout (restore m)) + 1) G pos ob (restore m) (restore m)
                k j ll dl syms HG Hp A4 A5 W1 HM Hw1 Hg1 F0 A2 A1 A3) as LP.
  cbv zeta. rewrite fast_eq. cbv zeta in LP.
  destruct LP as [(j' & FJ) | (mt & EM & FE)].
  - destruct (final_len K G pos inp ob m _ k j' ll dl syms KD HM Hlv FJ) as (M1 & K1 & L1 & D1).
    revert M1 K1 L1 D1. generalize (restore (ftail (fast_loop lenfix_list distfix_list
      (Z.to_nat (m_aout (restore m)) + 1) (restore m)))). intros X M1 K1 L1 D1.
    rewrite M1. replace (LEN =? Zlib.proof.inflate.Model.TYPE) with false by reflexivity.
    split; [exact K1|]. split; [exact L1|]. split; [exact D1|]. left. exact M1.
  - rewrite EM. destruct (final_type K G pos inp ob m mt k KD HM Hlv FE) as (M1 & K1 & L1 & D1).
    revert M1 K1 L1 D1. generalize (restore (ftail (set_mode mt Zlib.proof.inflate.Model.TYPE))).
    intros X M1 K1 L1 D1.
    rewrite M1, Z.eqb_refl. split; [exact K1|]. split; [exact L1|]. split; [exact D1|]. right. exact M1.
Qed.
