(* One pass of the switch of the inflate model (Model2.v's stepf2) preserves the wide machine invariant mwf3W
   (InvW.v: Inv3.v's mwf3 for inputs and output spaces of up to 2^32-1 bytes, with hdrW).  The proof is
   Step5Mwf.v's over the wide case lemmas (StepWFast/Decode/Tables/Block/Header.v): the narrow bounds 2^31-1
   of mwf are not needed by the cases, every size the cases compute stays within the unsigned range, except
   in EXTRA, where hdrW bounds the extra field's length (StepWHeader.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.inflate.InvW.
Require Import Zlib.proof.inflate.Steps2.
Require Import Zlib.proof.inflate.Step3Header.
Require Import Zlib.proof.inflate.StepWFast.
Require Import Zlib.proof.inflate.StepWDecode.
Require Import Zlib.proof.inflate.StepWTables.
Require Import Zlib.proof.inflate.StepWBlock.
Require Import Zlib.proof.inflate.StepWHeader.
Require Zlib.proof.inflate.Step5Mwf Zlib.proof.inflate.InvQ5.
Local Open Scope Z_scope.

(* case HEAD with patch F7 (Model2.c_HEAD2: the window size is checked before it is stored) *)
Lemma HEAD2_ok : ok_at HEAD c_HEAD2.
Proof.
  intros m W L M. unfold c_HEAD2.
  assert (HM: HEAD <= m_mode m <= TYPEDO) by (rewrite M; unfold_modes; lia).
  destruct (i_wrap (m_s m) =? 0) eqn:WR; [simpl; fin2 W HM |].
  nb 16 m W L.
  assert (HM1: HEAD <= m_mode m1 <= TYPEDO) by (unfold m_mode in *; rewrite S1, M; unfold_modes; lia).
  assert (XW0: i_wbits (m_s m1) = 0 -> i_wsize (m_s m1) = 0).
  { intros Z0. apply (x3_head _ (m3W_x _ W1)); [unfold m_mode; rewrite S1; exact M | exact Z0 |].
    rewrite S1. apply Z.eqb_neq. exact WR. }
  destruct (andb (negb (Z.land (i_wrap (m_s m1)) 2 =? 0)) (m_hold m1 =? 35615)) eqn:GZ.
  { simpl. fin2 W1 HM1. }
  destruct (i_head (m_s m1)) eqn:HD; simpl.
  all: destruct (orb _ _); [simpl; apply mwf3xW_set_bad; fin2 W1 HM1 |].
  all: destruct (negb (m_hold m1 mod 16 =? 8)); [simpl; apply mwf3xW_set_bad; fin2 W1 HM1 |].
  all: remember (Z.shiftr (m_hold m1) 4 mod 16 + 8) as len eqn:EL.
  all: assert (LN: 8 <= len <= 23)
         by (rewrite EL; pose proof (Z.mod_pos_bound (Z.shiftr (m_hold m1) 4) 16); lia).
  all: clear EL.
  all: destruct (orb _ _) eqn:C; [simpl; apply mwf3xW_set_bad; fin2 W1 HM1 |].
  all: apply orb_false_iff in C; destruct C as [C1 C2]; apply Z.ltb_ge in C1.
  all: assert (C3: len <= (if i_wbits (m_s m1) =? 0 then len else i_wbits (m_s m1)))
         by (destruct (Z.eqb_spec (i_wbits (m_s m1)) 0); [lia |];
             cbn [negb andb] in C2; apply Z.ltb_ge in C2; exact C2).
  all: clear C2.
  all: assert (P: 0 <= 2 ^ len <= 32768)
         by (split; [apply Z.pow_nonneg; lia | change 32768 with (2 ^ 15); apply Z.pow_le_mono_r; lia]).
  all: destruct (Z.land (Z.shiftr (m_hold m1) 4) 512 =? 0); simpl; fin2 W1 HM1.
Qed.

(* the invariant of the statement and the forms the case lemmas use *)
Lemma swf3_xwf3: forall m, swf3 (m_s m) -> xwf3 m.
Proof.
  intros m [A B C D]. constructor; auto.
  intros E. destruct (B E) as (sz & S1 & S2 & S3). exists sz. split; auto. split; auto.
  intros i Hi. apply Step5Mwf.len_ok_iff. auto.
Qed.

Lemma xwf3_swf3: forall m, xwf3 m -> swf3 (m_s m).
Proof.
  intros m [A B C D]. constructor; auto.
  intros E. destruct (D E) as (sz & S1 & S2 & S3). exists sz. split; auto. split; auto.
  intros i Hi. apply Step5Mwf.len_ok_iff. auto.
Qed.

Lemma mwf3W_xW: forall m, mwf3W m -> nohdr m -> mwf3xW m.
Proof. intros m (W & S & H) N. constructor; auto. apply swf3_xwf3; auto. Qed.

Lemma mwf3W_hW: forall m, mwf3W m -> mwf3hW m.
Proof. intros m (W & S & H). constructor; auto. apply swf3_xwf3; auto. Qed.

Lemma mwf3xW_W: forall m, mwf3xW m -> mwf3W m.
Proof. intros m [W X N]. split; [auto | split; [apply xwf3_swf3; auto | apply nohdr_hdrW; auto]]. Qed.

Lemma mwf3hW_W: forall m, mwf3hW m -> mwf3W m.
Proof. intros m [W X H]. split; [auto | split; [apply xwf3_swf3; auto | auto]]. Qed.

Lemma stepf2_mwf3W_of : cover2_stmt -> cover3_stmt -> forall flush m,
  mwf3W m -> m_leave m = 0 -> iout_ok mwf3W (stepf2 flush lenfix_list distfix_list m).
Proof.
  intros C2 C3 flush m W L.
  pose proof fast_ok as FA.
  pose proof (LEN__ok FA) as L_. pose proof TYPE_ok as TY.
  assert (OX: forall o, iout_ok mwf3xW o -> iout_ok mwf3W o) by (intros o; destruct o; apply mwf3xW_W).
  assert (OH: forall o, iout_ok mwf3hW o -> iout_ok mwf3W o) by (intros o; destruct o; apply mwf3hW_W).
  assert (XW: nohdr m -> mwf3xW m) by (apply mwf3W_xW; auto).
  destruct (Step5Mwf.mode_cases (m_mode m) (sw_mode _ (mwW_s _ (proj1 W)))) as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
  all: try (assert (W3: mwf3xW m) by (apply XW; nohdr_md)).
  - rewrite (stepf2_HEAD _ _ _ _ E). apply OX, HEAD2_ok; auto.
  - rewrite (stepf2_FLAGS _ _ _ _ E). apply OH, FLAGS2_ok; auto.
  - rewrite (stepf2_TIME _ _ _ _ E). apply OH, TIME2_ok; auto.
  - rewrite (stepf2_OS _ _ _ _ E). apply OH, OS2_ok; auto.
  - rewrite (stepf2_EXLEN _ _ _ _ E). apply OH, EXLEN2_ok; auto. apply mwf3W_hW; auto.
  - rewrite (stepf2_EXTRA _ _ _ _ E). apply OH, EXTRA2_ok; auto.
    + apply hW_x, mwf3W_hW; auto.
    + apply (proj2 (proj2 (proj2 W))). exact E.
  - rewrite (stepf2_NAME _ _ _ _ E). apply OX, NAME2_ok; auto.
  - rewrite (stepf2_COMMENT _ _ _ _ E). apply OX, COMMENT2_ok; auto.
  - rewrite (stepf2_HCRC _ _ _ _ E). apply OX, HCRC_ok; auto.
  - rewrite (stepf2_DICTID _ _ _ _ E). apply OX, (DICTID_ok TY flush); auto.
  - rewrite (stepf2_DICT _ _ _ _ E). apply OX, (DICT_ok TY flush); auto.
  - rewrite (stepf2_TYPE _ _ _ _ E). apply OX, (TY flush); auto.
  - rewrite (stepf2_TYPEDO _ _ _ _ E). apply OX, TYPEDO_ok; auto.
  - rewrite (stepf2_STORED _ _ _ _ E). apply OX, (STORED_ok flush); auto.
  - rewrite (stepf2_COPY_ _ _ _ _ E). apply OX, COPY__ok; auto.
  - rewrite (stepf2_COPY _ _ _ _ E). apply OX, COPY_ok; auto.
  - rewrite (stepf2_TABLE _ _ _ _ E). apply OX, (TABLE_ok C2 C3 L_ flush); auto.
  - rewrite (stepf2_LENLENS _ _ _ _ E). apply OX, (LENLENS_ok C2 C3 L_ flush); auto.
  - rewrite (stepf2_CODELENS _ _ _ _ E). apply OX, (CODELENS_ok C2 C3 L_ flush); auto.
  - rewrite (stepf2_LEN_ _ _ _ _ E). apply OX, L_; auto.
  - rewrite (stepf2_LEN _ _ _ _ E). apply OX, (LEN_ok FA); auto.
  - rewrite (stepf2_LENEXT _ _ _ _ E). apply OX, LENEXT_ok; auto.
  - rewrite (stepf2_DIST _ _ _ _ E). apply OX, DIST_ok; auto.
  - rewrite (stepf2_DISTEXT _ _ _ _ E). apply OX, DISTEXT_ok; auto.
  - rewrite (stepf2_MATCH _ _ _ _ E). apply OX, MATCH_ok; auto.
  - rewrite (stepf2_LIT _ _ _ _ E). apply OX, LIT_ok; auto.
  - rewrite (stepf2_CHECK _ _ _ _ E). apply OX, CHECK_ok; auto.
  - rewrite (stepf2_LENGTH _ _ _ _ E). apply OX, LENGTH_ok; auto.
  - rewrite (stepf2_DONE _ _ _ _ E). apply OX, DONE_ok; auto.
  - rewrite (stepf2_BAD _ _ _ _ E). apply OX, BAD_ok; auto.
  - rewrite (stepf2_MEM _ _ _ _ E). exact W.
  - rewrite (stepf2_SYNC _ _ _ _ E). exact W.
Qed.

Lemma stepf2_mwf3W : stepf2_mwf3W_stmt.
Proof.
  intros flush m W L.
  pose proof InvQ5.cover3_proof as C.
  pose proof (stepf2_mwf3W_of (Step5Mwf.cover3_cover2 C) (Step5Mwf.cover3_len C) flush m W L) as R.
  exact R.
Qed.
