(* Frame facts of inflate()'s model (src/proof/inflate/Model2.v run2) for uncompr.c's loop: a run from a
   machine in a mode HEAD..BAD keeps the input bytes (m_inp), the output space (m_aout) and i_head, ends
   with the stored next_out at the bytes written (m_sow = |m_ow|), and returns Z_OK only in a mode
   HEAD..BAD. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.inflate.Model2.
Import ListNotations.
Local Open Scope Z_scope.

Definition vmode (md: Z) : Prop := HEAD <= md <= BAD.

(* ---------------------------------------------------------------------------------------------- *)
(* helpers                                                                                        *)

Lemma needbits_f_fr: forall k n m,
  m_inp (needbits_f k n m) = m_inp m /\ m_aout (needbits_f k n m) = m_aout m /\
  m_s (needbits_f k n m) = m_s m.
Proof.
  induction k as [|k IH]; intros n m; simpl; auto.
  destruct (m_bits m <? n); auto.
  destruct (m_have m =? 0); auto.
  destruct (IH n (pull m)) as (A & B & C). rewrite A, B, C. auto.
Qed.

Lemma needbits_inp: forall n m, m_inp (needbits n m) = m_inp m.
Proof. intros. apply needbits_f_fr. Qed.
Lemma needbits_aout: forall n m, m_aout (needbits n m) = m_aout m.
Proof. intros. apply needbits_f_fr. Qed.
Lemma needbits_ms: forall n m, m_s (needbits n m) = m_s m.
Proof. intros. apply needbits_f_fr. Qed.

Local Opaque needbits.

Lemma crc_if_inp: forall m d, m_inp (crc_if m d) = m_inp m.
Proof. intros. unfold crc_if. destruct (_ && _); reflexivity. Qed.
Lemma crc_if_aout: forall m d, m_aout (crc_if m d) = m_aout m.
Proof. intros. unfold crc_if. destruct (_ && _); reflexivity. Qed.
Lemma crc_if_mode: forall m d, i_mode (m_s (crc_if m d)) = i_mode (m_s m).
Proof. intros. unfold crc_if. destruct (_ && _); reflexivity. Qed.
Lemma crc_if_head: forall m d, i_head (m_s (crc_if m d)) = i_head (m_s m).
Proof. intros. unfold crc_if. destruct (_ && _); reflexivity. Qed.

Lemma lookup1_f_fr: forall k fx dx t nb m h m' ok,
  lookup1_f k fx dx t nb m = (h, m', ok) ->
  m_inp m' = m_inp m /\ m_aout m' = m_aout m /\ m_s m' = m_s m.
Proof.
  induction k as [|k IH]; intros fx dx t nb m h m' ok E; simpl in E.
  - inversion E; subst; auto.
  - destruct (_ <=? _); [inversion E; subst; auto|].
    destruct (m_have m =? 0); [inversion E; subst; auto|].
    apply IH in E. simpl in E. exact E.
Qed.

Lemma lookup2_f_fr: forall k fx dx t last m h m' ok,
  lookup2_f k fx dx t last m = (h, m', ok) ->
  m_inp m' = m_inp m /\ m_aout m' = m_aout m /\ m_s m' = m_s m.
Proof.
  induction k as [|k IH]; intros fx dx t last m h m' ok E; simpl in E.
  - inversion E; subst; auto.
  - destruct (_ <=? _); [inversion E; subst; auto|].
    destruct (m_have m =? 0); [inversion E; subst; auto|].
    apply IH in E. simpl in E. exact E.
Qed.

Lemma lens_fill_mode: forall k len s, i_mode (lens_fill k len s) = i_mode s.
Proof. induction k as [|k IH]; intros; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma lens_fill_head: forall k len s, i_head (lens_fill k len s) = i_head s.
Proof. induction k as [|k IH]; intros; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma lenlens_zero_mode: forall k s, i_mode (lenlens_zero k s) = i_mode s.
Proof.
  induction k as [|k IH]; intros; simpl; [reflexivity|].
  destruct (_ <? 19); [rewrite IH|]; reflexivity.
Qed.
Lemma lenlens_zero_head: forall k s, i_head (lenlens_zero k s) = i_head s.
Proof.
  induction k as [|k IH]; intros; simpl; [reflexivity|].
  destruct (_ <? 19); [rewrite IH|]; reflexivity.
Qed.

Lemma lenlens_loop_fr: forall k m,
  m_inp (lenlens_loop k m) = m_inp m /\ m_aout (lenlens_loop k m) = m_aout m /\
  i_mode (m_s (lenlens_loop k m)) = i_mode (m_s m) /\ i_head (m_s (lenlens_loop k m)) = i_head (m_s m).
Proof.
  induction k as [|k IH]; intros m; simpl; auto.
  destruct (_ <? _); auto.
  destruct (m_leave (needbits 3 m) =? 1).
  - rewrite needbits_inp, needbits_aout, needbits_ms; auto.
  - edestruct IH as (A & B & C & D). rewrite A, B, C, D. simpl.
    rewrite needbits_inp, needbits_aout, needbits_ms; auto.
Qed.

Lemma lenlens_loop_inp: forall k m, m_inp (lenlens_loop k m) = m_inp m.
Proof. intros. apply lenlens_loop_fr. Qed.
Lemma lenlens_loop_aout: forall k m, m_aout (lenlens_loop k m) = m_aout m.
Proof. intros. apply lenlens_loop_fr. Qed.
Lemma lenlens_loop_mode: forall k m, i_mode (m_s (lenlens_loop k m)) = i_mode (m_s m).
Proof. intros. apply lenlens_loop_fr. Qed.
Lemma lenlens_loop_head: forall k m, i_head (m_s (lenlens_loop k m)) = i_head (m_s m).
Proof. intros. apply lenlens_loop_fr. Qed.

Local Opaque crc_if lens_fill lenlens_zero lenlens_loop.

(* ---------------------------------------------------------------------------------------------- *)
(* the frame relation and its tactics                                                            *)

Definition fr (m m': mst) : Prop :=
  m_inp m' = m_inp m /\ m_aout m' = m_aout m /\ i_head (m_s m') = i_head (m_s m) /\
  (vmode (i_mode (m_s m)) -> vmode (i_mode (m_s m'))).

Lemma fr_refl: forall m, fr m m.
Proof. intros. unfold fr. auto. Qed.

Lemma fr_trans: forall m1 m2 m3, fr m1 m2 -> fr m2 m3 -> fr m1 m3.
Proof. unfold fr. intros m1 m2 m3 (A & B & D & C) (A' & B' & D' & C'). rewrite A', B', D', A, B, D. split; [|split; [|split]]; auto. Qed.

Lemma lookup1_fr: forall fx dx t nb m h m' ok,
  lookup1 fx dx t nb m = (h, m', ok) -> m_inp m' = m_inp m /\ m_aout m' = m_aout m /\ m_s m' = m_s m.
Proof. intros. eapply lookup1_f_fr. exact H. Qed.
Lemma lookup2_fr: forall fx dx t last m h m' ok,
  lookup2 fx dx t last m = (h, m', ok) -> m_inp m' = m_inp m /\ m_aout m' = m_aout m /\ m_s m' = m_s m.
Proof. intros. eapply lookup2_f_fr. exact H. Qed.

Local Opaque lookup1 lookup2.

(* split every if / match whose scrutinee has no match inside *)
Ltac dsplit :=
  repeat match goal with
  | |- context [match ?x with _ => _ end] =>
      lazymatch x with context [match _ with _ => _ end] => fail | _ =>
        lazymatch type of x with bool => destruct x | _ => destruct x eqn:? end end
  end.

(* turn the equations of the helpers into frame facts *)
Ltac facts :=
  repeat match goal with
  | H: lookup1 _ _ _ _ _ = (_, _, _) |- _ => apply lookup1_fr in H; simpl in H; destruct H as (? & ? & ?)
  | H: lookup2 _ _ _ _ _ = (_, _, _) |- _ => apply lookup2_fr in H; simpl in H; destruct H as (? & ? & ?)
  end.

Ltac mode_consts := cbv [vmode HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID DICT TYPE TYPEDO
  STORED COPY_ COPY TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD
  MEM SYNC] in *.

Ltac rw_facts :=
  repeat match goal with
  | H: m_inp ?a = _ |- context [m_inp ?a] => rewrite H
  | H: m_aout ?a = _ |- context [m_aout ?a] => rewrite H
  | H: m_s ?a = _ |- context [m_s ?a] => rewrite H
  | |- context [m_inp (needbits _ _)] => rewrite needbits_inp
  | |- context [m_aout (needbits _ _)] => rewrite needbits_aout
  | |- context [m_s (needbits _ _)] => rewrite needbits_ms
  | |- context [m_inp (crc_if _ _)] => rewrite crc_if_inp
  | |- context [m_aout (crc_if _ _)] => rewrite crc_if_aout
  | |- context [i_mode (m_s (crc_if _ _))] => rewrite crc_if_mode
  | |- context [i_head (m_s (crc_if _ _))] => rewrite crc_if_head
  | |- context [i_head (lens_fill _ _ _)] => rewrite lens_fill_head
  | |- context [i_head (m_s (lenlens_loop _ _))] => rewrite lenlens_loop_head
  | |- context [i_head (lenlens_zero _ _)] => rewrite lenlens_zero_head
  | |- context [i_mode (lens_fill _ _ _)] => rewrite lens_fill_mode
  | |- context [m_inp (lenlens_loop _ _)] => rewrite lenlens_loop_inp
  | |- context [m_aout (lenlens_loop _ _)] => rewrite lenlens_loop_aout
  | |- context [i_mode (m_s (lenlens_loop _ _))] => rewrite lenlens_loop_mode
  | |- context [i_mode (lenlens_zero _ _)] => rewrite lenlens_zero_mode
  end.

Ltac fr_leaf :=
  unfold fr; do 4 (simpl; rw_facts);
  repeat split; try reflexivity; intros; mode_consts; try assumption; try lia; auto.

Lemma codelens_iter_fr: forall fx dx m,
  fr m (match codelens_iter fx dx m with CLnext m' => m' | CLleave m' => m' | CLbad m' => m' end).
Proof.
  intros. unfold codelens_iter. cbv beta zeta. dsplit; facts; fr_leaf.
Qed.

Definition cl_m (o: clout) : mst := match o with CLnext m' => m' | CLleave m' => m' | CLbad m' => m' end.

Lemma codelens_loop_fr: forall fx dx k m, fr m (cl_m (codelens_loop fx dx k m)).
Proof.
  induction k as [|k IH]; intros m; simpl; [apply fr_refl|].
  destruct (_ <? _); [|apply fr_refl].
  pose proof (codelens_iter_fr fx dx m) as F.
  destruct (codelens_iter fx dx m) as [m'|m'|m'] eqn:E; simpl in F |- *; auto.
  eapply fr_trans; [exact F | apply IH].
Qed.

Local Opaque codelens_loop codelens_iter.

(* inflate_fast *)
Lemma fwalk_f_fr: forall fx dx k il t here m h m',
  fwalk_f fx dx k il t here m = (h, m') -> m_inp m' = m_inp m /\ m_aout m' = m_aout m /\ m_s m' = m_s m.
Proof.
  induction k as [|k IH]; intros il t here m h m' E; simpl in E.
  - inversion E; subst; auto.
  - destruct (il (e_op here)); [apply IH in E; simpl in E; exact E | inversion E; subst; auto].
Qed.

Local Opaque fwalk_f.

Ltac facts2 :=
  repeat match goal with
  | H: fwalk_f _ _ _ _ _ _ _ = (_, _) |- _ => apply fwalk_f_fr in H; simpl in H; destruct H as (? & ? & ?)
  end.
Lemma fast_iter_fr: forall fx dx m, fr m (snd (fast_iter fx dx m)).
Proof.
  intros. unfold fast_iter, fpull. cbv beta zeta. dsplit. all: (facts2; fr_leaf).
Qed.

Lemma fast_loop_fr: forall fx dx k m, fr m (fast_loop fx dx k m).
Proof.
  induction k as [|k IH]; intros m; simpl; [apply fr_refl|].
  pose proof (fast_iter_fr fx dx m) as F.
  destruct (fast_iter fx dx m) as [go m'] eqn:E; simpl in F |- *.
  destruct (_ && _ && _); [eapply fr_trans; [exact F | apply IH] | exact F].
Qed.

Lemma fast_fr: forall fx dx m, fr m (fast fx dx m).
Proof.
  intros. unfold fast. cbv beta zeta.
  pose proof (fast_loop_fr fx dx (Z.to_nat (m_aout m) + 1) m) as F.
  eapply fr_trans; [exact F|]. fr_leaf.
Qed.

Local Opaque fast fast_iter fast_loop.

(* ---------------------------------------------------------------------------------------------- *)
(* the cases                                                                                      *)

Definition iok (m: mst) (o: iout) : Prop :=
  match o with
  | IBrk m' => fr m m'
  | IRet r m' => m_inp m' = m_inp m /\ m_aout m' = m_aout m /\ i_head (m_s m') = i_head (m_s m) /\
                 r = Z_NEED_DICT /\ m_sow m' = Zlength (m_ow m')
  end.

Lemma iok_after: forall m m2 o, iok m2 o -> fr m m2 -> iok m o.
Proof.
  intros m m2 [m'|r m'] H F; simpl in *.
  - eapply fr_trans; eauto.
  - destruct F as (A & B & D & _). destruct H as (A' & B' & D' & R & S). rewrite A', B', D', A, B, D. auto.
Qed.

Ltac facts3 :=
  repeat match goal with
  | H: codelens_loop ?a ?b ?k ?m0 = ?c |- _ =>
      let F := fresh "F" in
      pose proof (codelens_loop_fr a b k m0) as F; rewrite H in F; simpl in F; clear H;
      destruct F as (? & ? & ? & ?)
  end.

Create HintDb caseok.

Ltac case_leaf :=
  lazymatch goal with
  | |- iok _ (IBrk _) => unfold iok; fr_leaf
  | |- iok _ (IRet _ _) => unfold iok; simpl; rw_facts; repeat split; reflexivity
  | |- iok _ _ => eapply iok_after; [solve [eauto with caseok] | fr_leaf]
  end.

Ltac case_tac := intros; cbv beta zeta; dsplit; facts; facts2; facts3; case_leaf.

Section Cases.
Variables (flush: Z) (fx dx: list entry) (fst: mst -> mst).
Variable Hfast: forall m, fr m (fst m).

Lemma DONE_ok: forall m, iok m (c_DONE m).
Proof. unfold c_DONE. case_tac. Qed.
Hint Resolve DONE_ok : caseok.
Local Opaque c_DONE.
Lemma BAD_ok: forall m, iok m (c_BAD m).
Proof. unfold c_BAD. case_tac. Qed.
Hint Resolve BAD_ok : caseok.
Local Opaque c_BAD.
Lemma LENGTH_ok: forall m, iok m (c_LENGTH m).
Proof. unfold c_LENGTH. case_tac. Qed.
Hint Resolve LENGTH_ok : caseok.
Local Opaque c_LENGTH.
Lemma CHECK_ok: forall m, iok m (c_CHECK m).
Proof. unfold c_CHECK. case_tac. Qed.
Hint Resolve CHECK_ok : caseok.
Local Opaque c_CHECK.
Lemma LIT_ok: forall m, iok m (c_LIT m).
Proof. unfold c_LIT. case_tac. Qed.
Hint Resolve LIT_ok : caseok.
Local Opaque c_LIT.
Lemma MATCH_ok: forall m, iok m (c_MATCH m).
Proof. unfold c_MATCH. case_tac. Qed.
Hint Resolve MATCH_ok : caseok.
Local Opaque c_MATCH.
Lemma DISTEXT_ok: forall m, iok m (c_DISTEXT m).
Proof. unfold c_DISTEXT. case_tac. Qed.
Hint Resolve DISTEXT_ok : caseok.
Local Opaque c_DISTEXT.
Lemma DIST_ok: forall m, iok m (c_DIST fx dx m).
Proof. unfold c_DIST. case_tac. Qed.
Hint Resolve DIST_ok : caseok.
Local Opaque c_DIST.
Lemma LENEXT_ok: forall m, iok m (c_LENEXT fx dx m).
Proof. unfold c_LENEXT. case_tac. Qed.
Hint Resolve LENEXT_ok : caseok.
Local Opaque c_LENEXT.
Lemma LEN_ok: forall m, iok m (c_LEN fx dx fst m).
Proof.
  intros m. pose proof (Hfast (restore m)) as F. destruct F as (FA & FB & FD & FC). simpl in FA, FB, FD, FC.
  unfold c_LEN. case_tac.
Qed.
Hint Resolve LEN_ok : caseok.
Local Opaque c_LEN.
Lemma LEN__ok: forall m, iok m (c_LEN_ fx dx fst m).
Proof. unfold c_LEN_. case_tac. Qed.
Hint Resolve LEN__ok : caseok.
Local Opaque c_LEN_.
Lemma CODELENS_ok: forall m, iok m (c_CODELENS flush fx dx fst m).
Proof. unfold c_CODELENS. case_tac. Qed.
Hint Resolve CODELENS_ok : caseok.
Local Opaque c_CODELENS.
Lemma LENLENS_ok: forall m, iok m (c_LENLENS flush fx dx fst m).
Proof.
  intros m. unfold c_LENLENS. cbv beta zeta.
  pose proof (lenlens_loop_fr 19 m) as (A & B & C & D).
  set (m1 := lenlens_loop 19 m) in *. clearbody m1.
  destruct (m_leave m1 =? 1).
  { unfold iok, fr. rewrite A, B, C, D. auto. }
  pose proof (lenlens_zero_mode 19 (m_s m1)) as C2. pose proof (lenlens_zero_head 19 (m_s m1)) as D2.
  set (s1 := lenlens_zero 19 (m_s m1)) in *. clearbody s1.
  destruct (call_table _ _ _ _ _) as [[[r codes] nxt] lb].
  destruct (negb (r =? 0)).
  - unfold iok, fr. simpl. rewrite ?A, ?B, ?C2, ?D2, ?C, ?D. split; [reflexivity|split; [reflexivity|split; [reflexivity|]]].
    intros _. mode_consts. lia.
  - eapply iok_after; [apply CODELENS_ok|].
    unfold fr. simpl. rewrite ?A, ?B, ?C2, ?D2, ?C, ?D. split; [reflexivity|split; [reflexivity|split; [reflexivity|]]].
    intros _. mode_consts. lia.
Qed.
Hint Resolve LENLENS_ok : caseok.
Local Opaque c_LENLENS.
Lemma TABLE_ok: forall m, iok m (c_TABLE flush fx dx fst m).
Proof. unfold c_TABLE. case_tac. Qed.
Hint Resolve TABLE_ok : caseok.
Local Opaque c_TABLE.
Lemma COPY_ok: forall m, iok m (c_COPY m).
Proof. unfold c_COPY. case_tac. Qed.
Hint Resolve COPY_ok : caseok.
Local Opaque c_COPY.
Lemma COPY__ok: forall m, iok m (c_COPY_ m).
Proof. unfold c_COPY_. case_tac. Qed.
Hint Resolve COPY__ok : caseok.
Local Opaque c_COPY_.
Lemma STORED_ok: forall m, iok m (c_STORED flush m).
Proof. unfold c_STORED. case_tac. Qed.
Hint Resolve STORED_ok : caseok.
Local Opaque c_STORED.
Lemma TYPEDO_ok: forall m, iok m (c_TYPEDO flush m).
Proof. unfold c_TYPEDO. case_tac. Qed.
Hint Resolve TYPEDO_ok : caseok.
Local Opaque c_TYPEDO.
Lemma TYPE_ok: forall m, iok m (c_TYPE flush m).
Proof. unfold c_TYPE. case_tac. Qed.
Hint Resolve TYPE_ok : caseok.
Local Opaque c_TYPE.
Lemma DICT_ok: forall m, iok m (c_DICT flush m).
Proof. unfold c_DICT. case_tac. Qed.
Hint Resolve DICT_ok : caseok.
Local Opaque c_DICT.
Lemma DICTID_ok: forall m, iok m (c_DICTID flush m).
Proof. unfold c_DICTID. case_tac. Qed.
Hint Resolve DICTID_ok : caseok.
Local Opaque c_DICTID.
Lemma HCRC_ok: forall m, iok m (c_HCRC m).
Proof. unfold c_HCRC. case_tac. Qed.
Hint Resolve HCRC_ok : caseok.
Local Opaque c_HCRC.
Lemma COMMENT_ok: forall m, iok m (c_COMMENT m).
Proof. unfold c_COMMENT. case_tac. Qed.
Hint Resolve COMMENT_ok : caseok.
Local Opaque c_COMMENT.
Lemma NAME_ok: forall m, iok m (c_NAME m).
Proof. unfold c_NAME. case_tac. Qed.
Hint Resolve NAME_ok : caseok.
Local Opaque c_NAME.
Lemma EXTRA_ok: forall m, iok m (c_EXTRA m).
Proof. unfold c_EXTRA. case_tac. Qed.
Hint Resolve EXTRA_ok : caseok.
Local Opaque c_EXTRA.
Lemma EXLEN_ok: forall m, iok m (c_EXLEN m).
Proof. unfold c_EXLEN. case_tac. Qed.
Hint Resolve EXLEN_ok : caseok.
Local Opaque c_EXLEN.
Lemma OS_ok: forall m, iok m (c_OS m).
Proof. unfold c_OS. case_tac. Qed.
Hint Resolve OS_ok : caseok.
Local Opaque c_OS.
Lemma TIME_ok: forall m, iok m (c_TIME m).
Proof. unfold c_TIME. case_tac. Qed.
Hint Resolve TIME_ok : caseok.
Local Opaque c_TIME.
Lemma FLAGS_ok: forall m, iok m (c_FLAGS m).
Proof. unfold c_FLAGS. case_tac. Qed.
Hint Resolve FLAGS_ok : caseok.
Local Opaque c_FLAGS.
Lemma COMMENT2_ok: forall m, iok m (c_COMMENT2 m).
Proof. unfold c_COMMENT2. case_tac. Qed.
Hint Resolve COMMENT2_ok : caseok.
Local Opaque c_COMMENT2.
Lemma NAME2_ok: forall m, iok m (c_NAME2 m).
Proof. unfold c_NAME2. case_tac. Qed.
Hint Resolve NAME2_ok : caseok.
Local Opaque c_NAME2.
Lemma EXTRA2_ok: forall m, iok m (c_EXTRA2 m).
Proof. unfold c_EXTRA2. case_tac. Qed.
Hint Resolve EXTRA2_ok : caseok.
Local Opaque c_EXTRA2.
Lemma EXLEN2_ok: forall m, iok m (c_EXLEN2 m).
Proof. unfold c_EXLEN2. case_tac. Qed.
Hint Resolve EXLEN2_ok : caseok.
Local Opaque c_EXLEN2.
Lemma OS2_ok: forall m, iok m (c_OS2 m).
Proof. unfold c_OS2. case_tac. Qed.
Hint Resolve OS2_ok : caseok.
Local Opaque c_OS2.
Lemma TIME2_ok: forall m, iok m (c_TIME2 m).
Proof. unfold c_TIME2. case_tac. Qed.
Hint Resolve TIME2_ok : caseok.
Local Opaque c_TIME2.
Lemma FLAGS2_ok: forall m, iok m (c_FLAGS2 m).
Proof. unfold c_FLAGS2. case_tac. Qed.
Hint Resolve FLAGS2_ok : caseok.
Local Opaque c_FLAGS2.
Lemma HEAD_ok: forall m, iok m (c_HEAD m).
Proof.
  unfold c_HEAD. intros; cbv beta zeta; dsplit; facts; facts2; facts3. all: try case_leaf.
  all: destruct (_ || _); case_leaf. all: destruct (_ =? _); lia.
Qed.

Hint Resolve HEAD_ok : caseok.
Local Opaque c_HEAD.
Lemma HEAD2_ok: forall m, iok m (c_HEAD2 m).
Proof.
  unfold c_HEAD2. intros; cbv beta zeta; dsplit; facts; facts2; facts3. all: try case_leaf.
  all: repeat match goal with |- context [if ?c then _ else _] => destruct c eqn:? end.
  all: try case_leaf. all: try lia.
Qed.
Hint Resolve HEAD2_ok : caseok.
Local Opaque c_HEAD2.

Lemma step2_ok: forall m, vmode (i_mode (m_s m)) -> iok m (step2 flush fx dx fst m).
Proof.
  intros m V. unfold step2.
  repeat match goal with |- iok _ (if ?c then _ else _) => destruct c eqn:?; [solve [eauto with caseok] |] end.
  exfalso. unfold m_mode in *. repeat match goal with H: (_ =? _) = false |- _ => apply Z.eqb_neq in H end.
  mode_consts. lia.
Qed.

End Cases.

Lemma loop2_ok: forall flush fx dx m o, loop2 flush fx dx m o -> vmode (i_mode (m_s m)) -> iok m o.
Proof.
  intros flush fx dx m o L. induction L as [m r m' E|m m' E Lv|m m' o E Lv L IH]; intros V;
    pose proof (step2_ok flush fx dx (fast fx dx) (fast_fr fx dx) m V) as S; unfold stepf2 in E;
    rewrite E in S; auto.
  eapply iok_after; [apply IH|exact S]. apply S. exact V.
Qed.

Lemma updatewindow_mh: forall s d,
  i_mode (updatewindow s d) = i_mode s /\ i_head (updatewindow s d) = i_head s.
Proof.
  intros. unfold updatewindow. cbv beta zeta.
  destruct (i_wsize s =? 0); simpl; destruct (_ <=? _); simpl; auto; destruct (negb _); simpl; auto.
Qed.

Local Opaque updatewindow.

Lemma leave_fin_fr: forall flush m,
  m_inp (r_m (leave_fin flush m)) = m_inp m /\ m_aout (r_m (leave_fin flush m)) = m_aout m /\
  m_sow (r_m (leave_fin flush m)) = Zlength (m_ow (r_m (leave_fin flush m))) /\
  i_head (m_s (r_m (leave_fin flush m))) = i_head (m_s m) /\
  i_mode (m_s (r_m (leave_fin flush m))) = i_mode (m_s m).
Proof.
  intros. unfold leave_fin. cbv beta zeta. simpl r_m.
  destruct (leave_ok flush m); dsplit; simpl;
    rewrite ?(proj1 (updatewindow_mh _ _)), ?(proj2 (updatewindow_mh _ _)); simpl; auto.
Qed.

Lemma run2_frame: forall flush fx dx m0 res,
  vmode (i_mode (m_s m0)) ->
  run2 flush fx dx m0 res ->
  m_inp (r_m res) = m_inp m0 /\ m_aout (r_m res) = m_aout m0 /\
  m_sow (r_m res) = Zlength (m_ow (r_m res)) /\
  i_head (m_s (r_m res)) = i_head (m_s m0) /\
  (r_ret res = Z_OK -> vmode (i_mode (m_s (r_m res)))).
Proof.
  intros flush fx dx m0 res V (o & L & R). apply loop2_ok in L; [|exact V].
  destruct o as [m|r m]; simpl in L.
  - destruct L as (A & B & D & C). specialize (C V). destruct R.
    + simpl. rewrite A, B, D. split; [reflexivity|split; [reflexivity|split; [reflexivity|split; [reflexivity|]]]].
      cbv; congruence.
    + destruct (leave_fin_fr flush m) as (A2 & B2 & S2 & D2 & C2).
      rewrite A2, B2, S2, D2, C2, A, B, D.
      split; [reflexivity|split; [reflexivity|split; [reflexivity|split; [reflexivity|]]]]. intros _; exact C.
  - subst res. simpl. destruct L as (A & B & D & R & S). subst r.
    split; [assumption|split; [assumption|split; [assumption|split; [assumption|]]]]. cbv; congruence.
Qed.
