(* One pass of the switch of the corrected model (Model2.v's stepf2) preserves Inv3.v's mwf3: the case lemmas
   of ICStep5Header.v (the header cases) and of the ICStep3*.v files (the others), assembled. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.inflate.Steps2.
Require Import Zlib.proof.harness.inflate_codes.ICStep3Fast.
Require Import Zlib.proof.harness.inflate_codes.ICStep3Decode.
Require Import Zlib.proof.harness.inflate_codes.ICStep3Tables.
Require Import Zlib.proof.harness.inflate_codes.ICStep3Block.
Require Import Zlib.proof.harness.inflate_codes.ICStep3Header.
Require Import Zlib.proof.harness.inflate_codes.ICStep5Header.
Require Zlib.proof.inflate.Inv3 Zlib.proof.inflate.Cover3.
Local Open Scope Z_scope.

Lemma mode_cases (z: Z) : HEAD <= z <= SYNC -> z = HEAD \/ z = FLAGS \/ z = TIME \/ z = OS \/ z = EXLEN \/ z = EXTRA \/ z = NAME \/ z = COMMENT \/ z = HCRC \/ z = DICTID \/ z = DICT \/ z = TYPE \/ z = TYPEDO \/ z = STORED \/ z = COPY_ \/ z = COPY \/ z = TABLE \/ z = LENLENS \/ z = CODELENS \/ z = LEN_ \/ z = LEN \/ z = LENEXT \/ z = DIST \/ z = DISTEXT \/ z = MATCH \/ z = LIT \/ z = CHECK \/ z = LENGTH \/ z = DONE \/ z = BAD \/ z = MEM \/ z = SYNC.
Proof.
  unfold HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT, TYPE, TYPEDO, STORED,
    COPY_, COPY, TABLE, LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, CHECK, LENGTH,
    DONE, BAD, MEM, SYNC.
  intros H.
  assert (exists n, (n < 32)%nat /\ z = 16180 + Z.of_nat n) as [n [Hn ->]]
    by (exists (Z.to_nat (z - 16180)); split; [lia | rewrite Z2Nat.id; lia]).
  do 32 (destruct n as [|n]; [simpl; lia|]). lia.
Qed.

(* over ICStep3Inv.v's mwf3x *)
(* case HEAD with patch F7 (Model2.c_HEAD2: the window size is checked before it is stored) *)
Lemma HEAD2_ok : ok_at HEAD c_HEAD2.
Proof.
  intros m W L M. unfold c_HEAD2.
  assert (HM: HEAD <= m_mode m <= TYPEDO) by (rewrite M; unfold_modes; lia).
  destruct (i_wrap (m_s m) =? 0) eqn:WR; [simpl; fin2 W HM |].
  nb 16 m W L.
  assert (HM1: HEAD <= m_mode m1 <= TYPEDO) by (unfold m_mode in *; rewrite S1, M; unfold_modes; lia).
  assert (XW0: i_wbits (m_s m1) = 0 -> i_wsize (m_s m1) = 0).
  { intros Z0. apply (x3_head _ (m3_x _ W1)); [unfold m_mode; rewrite S1; exact M | exact Z0 |].
    rewrite S1. apply Z.eqb_neq. exact WR. }
  destruct (andb (negb (Z.land (i_wrap (m_s m1)) 2 =? 0)) (m_hold m1 =? 35615)) eqn:GZ.
  { simpl. fin2 W1 HM1. }
  destruct (i_head (m_s m1)) eqn:HD; simpl.
  all: destruct (orb _ _); [simpl; apply mwf3x_set_bad; fin2 W1 HM1 |].
  all: destruct (negb (m_hold m1 mod 16 =? 8)); [simpl; apply mwf3x_set_bad; fin2 W1 HM1 |].
  all: remember (Z.shiftr (m_hold m1) 4 mod 16 + 8) as len eqn:EL.
  all: assert (LN: 8 <= len <= 23)
         by (rewrite EL; pose proof (Z.mod_pos_bound (Z.shiftr (m_hold m1) 4) 16); lia).
  all: clear EL.
  all: destruct (orb _ _) eqn:C; [simpl; apply mwf3x_set_bad; fin2 W1 HM1 |].
  all: apply orb_false_iff in C; destruct C as [C1 C2]; apply Z.ltb_ge in C1.
  all: assert (C3: len <= (if i_wbits (m_s m1) =? 0 then len else i_wbits (m_s m1)))
         by (destruct (Z.eqb_spec (i_wbits (m_s m1)) 0); [lia |];
             cbn [negb andb] in C2; apply Z.ltb_ge in C2; exact C2).
  all: clear C2.
  all: assert (P: 0 <= 2 ^ len <= 32768)
         by (split; [apply Z.pow_nonneg; lia | change 32768 with (2 ^ 15); apply Z.pow_le_mono_r; lia]).
  all: destruct (Z.land (Z.shiftr (m_hold m1) 4) 512 =? 0); simpl; fin2 W1 HM1.
Qed.

Lemma stepf2_mwf3x_x : cover2_stmt -> cover3_stmt -> forall flush m,
  mwf3x m -> m_leave m = 0 ->
  match stepf2 flush lenfix_list distfix_list m with IBrk m' => mwf3x m' | IRet _ m' => mwf3x m' end.
Proof.
  intros C2 C3 flush m W L.
  pose proof fast_ok as FA.
  pose proof (LEN__ok FA) as L_. pose proof TYPE_ok as TY.
  change (iout_ok mwf3x (stepf2 flush lenfix_list distfix_list m)).
  destruct (mode_cases (m_mode m) (sw_mode _ (mw_s _ (m3_w _ W)))) as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
  - rewrite (stepf2_HEAD _ _ _ _ E). apply HEAD2_ok; auto.
  - rewrite (stepf2_FLAGS _ _ _ _ E). apply FLAGS2_ok; auto.
  - rewrite (stepf2_TIME _ _ _ _ E). apply TIME2_ok; auto.
  - rewrite (stepf2_OS _ _ _ _ E). apply OS2_ok; auto.
  - rewrite (stepf2_EXLEN _ _ _ _ E). apply EXLEN2_ok; auto.
  - rewrite (stepf2_EXTRA _ _ _ _ E). apply EXTRA2_ok; auto.
  - rewrite (stepf2_NAME _ _ _ _ E). apply NAME2_ok; auto.
  - rewrite (stepf2_COMMENT _ _ _ _ E). apply COMMENT2_ok; auto.
  - rewrite (stepf2_HCRC _ _ _ _ E). apply HCRC_ok; auto.
  - rewrite (stepf2_DICTID _ _ _ _ E). apply (DICTID_ok TY flush); auto.
  - rewrite (stepf2_DICT _ _ _ _ E). apply (DICT_ok TY flush); auto.
  - rewrite (stepf2_TYPE _ _ _ _ E). apply (TY flush); auto.
  - rewrite (stepf2_TYPEDO _ _ _ _ E). apply TYPEDO_ok; auto.
  - rewrite (stepf2_STORED _ _ _ _ E). apply (STORED_ok flush); auto.
  - rewrite (stepf2_COPY_ _ _ _ _ E). apply COPY__ok; auto.
  - rewrite (stepf2_COPY _ _ _ _ E). apply COPY_ok; auto.
  - rewrite (stepf2_TABLE _ _ _ _ E). apply (TABLE_ok C2 C3 L_ flush); auto.
  - rewrite (stepf2_LENLENS _ _ _ _ E). apply (LENLENS_ok C2 C3 L_ flush); auto.
  - rewrite (stepf2_CODELENS _ _ _ _ E). apply (CODELENS_ok C2 C3 L_ flush); auto.
  - rewrite (stepf2_LEN_ _ _ _ _ E). apply L_; auto.
  - rewrite (stepf2_LEN _ _ _ _ E). apply (LEN_ok FA); auto.
  - rewrite (stepf2_LENEXT _ _ _ _ E). apply LENEXT_ok; auto.
  - rewrite (stepf2_DIST _ _ _ _ E). apply DIST_ok; auto.
  - rewrite (stepf2_DISTEXT _ _ _ _ E). apply DISTEXT_ok; auto.
  - rewrite (stepf2_MATCH _ _ _ _ E). apply MATCH_ok; auto.
  - rewrite (stepf2_LIT _ _ _ _ E). apply LIT_ok; auto.
  - rewrite (stepf2_CHECK _ _ _ _ E). apply CHECK_ok; auto.
  - rewrite (stepf2_LENGTH _ _ _ _ E). apply LENGTH_ok; auto.
  - rewrite (stepf2_DONE _ _ _ _ E). apply DONE_ok; auto.
  - rewrite (stepf2_BAD _ _ _ _ E). apply BAD_ok; auto.
  - rewrite (stepf2_MEM _ _ _ _ E). exact W.
  - rewrite (stepf2_SYNC _ _ _ _ E). exact W.
Qed.

(* the two forms of the invariant *)
Lemma len_ok_iff: forall e, Inv2.len_ok e <-> len_ok e.
Proof. intros e. unfold Inv2.len_ok, len_ok. split; intros H R; specialize (H R); lia. Qed.

Lemma mwf3x_iff: forall m, Inv3.mwf3 m <-> mwf3x m.
Proof.
  intros m. split.
  - intros [W [A B C D]]. constructor; auto. constructor; auto.
    intros E. destruct (B E) as (sz & S1 & S2 & S3). exists sz. split; auto. split; auto.
    intros i Hi. apply len_ok_iff. auto.
  - intros [W [A B C D]]. split; auto. constructor; auto.
    intros E. destruct (D E) as (sz & S1 & S2 & S3). exists sz. split; auto. split; auto.
    intros i Hi. apply len_ok_iff. auto.
Qed.

Lemma cover3_cover2: Cover3.cover3_stmt -> cover2_stmt.
Proof.
  intros C type lens req old root used t A B D E F.
  destruct (C type lens req old root used t A B D E F) as (G & H & _). auto.
Qed.

Lemma cover3_len: Cover3.cover3_stmt -> cover3_stmt.
Proof.
  intros C lens req old root used t A D E F i Hi.
  destruct (C LENS lens req old root used t A ltac:(unfold LENS, CODES; congruence) D E F) as (_ & _ & G).
  apply len_ok_iff. auto.
Qed.

(* THE result, over Inv3.v's mwf3 *)
Lemma stepf2_mwf3_x : Cover3.cover3_stmt -> forall flush m,
  Inv3.mwf3 m -> m_leave m = 0 ->
  match stepf2 flush lenfix_list distfix_list m with IBrk m' => Inv3.mwf3 m' | IRet _ m' => Inv3.mwf3 m' end.
Proof.
  intros C flush m W L. apply mwf3x_iff in W.
  pose proof (stepf2_mwf3x_x (cover3_cover2 C) (cover3_len C) flush m W L) as R.
  destruct (stepf2 flush lenfix_list distfix_list m); apply mwf3x_iff; auto.
Qed.
