(* The return code of inflate()'s model (src/proof/inflate/Model2.v run2) is one of zlib's codes
   Z_BUF_ERROR (-5) .. Z_NEED_DICT (2): uncompr.c's loop compares it (an int) with Z_OK. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.inflate.Model2.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* helpers: the functions under the cases keep m_ret                                             *)

Definition rok (m: mst) : Prop := -5 <= m_ret m <= 2.

Lemma needbits_f_ret: forall k n m, m_ret (needbits_f k n m) = m_ret m.
Proof.
  induction k as [|k IH]; intros n m; simpl; auto.
  destruct (m_bits m <? n); auto.
  destruct (m_have m =? 0); auto.
  rewrite IH. reflexivity.
Qed.

Lemma needbits_ret: forall n m, m_ret (needbits n m) = m_ret m.
Proof. intros. apply needbits_f_ret. Qed.

Local Opaque needbits.

Lemma crc_if_ret: forall m d, m_ret (crc_if m d) = m_ret m.
Proof. intros. unfold crc_if. destruct (_ && _); reflexivity. Qed.

Lemma lookup1_f_ret: forall k fx dx t nb m h m' ok,
  lookup1_f k fx dx t nb m = (h, m', ok) -> m_ret m' = m_ret m.
Proof.
  induction k as [|k IH]; intros fx dx t nb m h m' ok E; simpl in E.
  - inversion E; subst; auto.
  - destruct (_ <=? _); [inversion E; subst; auto|].
    destruct (m_have m =? 0); [inversion E; subst; auto|].
    apply IH in E. simpl in E. exact E.
Qed.

Lemma lookup2_f_ret: forall k fx dx t last m h m' ok,
  lookup2_f k fx dx t last m = (h, m', ok) -> m_ret m' = m_ret m.
Proof.
  induction k as [|k IH]; intros fx dx t last m h m' ok E; simpl in E.
  - inversion E; subst; auto.
  - destruct (_ <=? _); [inversion E; subst; auto|].
    destruct (m_have m =? 0); [inversion E; subst; auto|].
    apply IH in E. simpl in E. exact E.
Qed.

Lemma lookup1_ret: forall fx dx t nb m h m' ok,
  lookup1 fx dx t nb m = (h, m', ok) -> m_ret m' = m_ret m.
Proof. intros. eapply lookup1_f_ret. exact H. Qed.
Lemma lookup2_ret: forall fx dx t last m h m' ok,
  lookup2 fx dx t last m = (h, m', ok) -> m_ret m' = m_ret m.
Proof. intros. eapply lookup2_f_ret. exact H. Qed.

Lemma lenlens_loop_ret: forall k m, m_ret (lenlens_loop k m) = m_ret m.
Proof.
  induction k as [|k IH]; intros m; simpl; auto.
  destruct (_ <? _); auto.
  destruct (m_leave (needbits 3 m) =? 1).
  - rewrite needbits_ret; auto.
  - rewrite IH. simpl. rewrite needbits_ret; auto.
Qed.

Lemma call_table_ret: forall type lo n req s r codes nxt b,
  call_table type lo n req s = (r, codes, nxt, b) -> -1 <= r <= 1.
Proof.
  intros. unfold call_table in H. inversion H; subst.
  destruct (inflate_table_model _ _ _ _); simpl; lia.
Qed.

Local Opaque crc_if lenlens_loop lookup1 lookup2 call_table.

(* ---------------------------------------------------------------------------------------------- *)
(* the frame relation and its tactics                                                            *)

Definition fr (m m': mst) : Prop := rok m -> rok m'.

Lemma fr_refl: forall m, fr m m.
Proof. unfold fr. auto. Qed.

Lemma fr_trans: forall m1 m2 m3, fr m1 m2 -> fr m2 m3 -> fr m1 m3.
Proof. unfold fr. auto. Qed.

(* split every if / match whose scrutinee has no match inside *)
Ltac dsplit :=
  repeat match goal with
  | |- context [match ?x with _ => _ end] =>
      lazymatch x with context [match _ with _ => _ end] => fail | _ =>
        lazymatch type of x with bool => destruct x | _ => destruct x eqn:? end end
  end.

Ltac facts :=
  repeat match goal with
  | H: lookup1 _ _ _ _ _ = (_, _, _) |- _ => apply lookup1_ret in H; simpl in H
  | H: lookup2 _ _ _ _ _ = (_, _, _) |- _ => apply lookup2_ret in H; simpl in H
  | H: call_table _ _ _ _ _ = (_, _, _, _) |- _ => apply call_table_ret in H
  end.

Ltac rw_facts :=
  repeat match goal with
  | H: m_ret ?a = _ |- context [m_ret ?a] => rewrite H
  | |- context [m_ret (needbits _ _)] => rewrite needbits_ret
  | |- context [m_ret (crc_if _ _)] => rewrite crc_if_ret
  | |- context [m_ret (lenlens_loop _ _)] => rewrite lenlens_loop_ret
  end.

Ltac fr_leaf :=
  unfold fr, rok in *; do 4 (simpl; rw_facts);
  intros;
  repeat match goal with H: ?A -> ?B, H2: ?A |- _ => specialize (H H2) end;
  cbv [Z_STREAM_END Z_DATA_ERROR] in *; try lia; auto.

Definition cl_m (o: clout) : mst := match o with CLnext m' => m' | CLleave m' => m' | CLbad m' => m' end.

Lemma codelens_iter_fr: forall fx dx m, fr m (cl_m (codelens_iter fx dx m)).
Proof.
  intros. unfold codelens_iter. cbv beta zeta. dsplit; facts; fr_leaf.
Qed.

Lemma codelens_loop_fr: forall fx dx k m, fr m (cl_m (codelens_loop fx dx k m)).
Proof.
  induction k as [|k IH]; intros m; simpl; [apply fr_refl|].
  destruct (_ <? _); [|apply fr_refl].
  pose proof (codelens_iter_fr fx dx m) as F.
  destruct (codelens_iter fx dx m) as [m'|m'|m'] eqn:E; simpl in F |- *; auto.
  eapply fr_trans; [exact F | apply IH].
Qed.

Local Opaque codelens_loop codelens_iter.

(* inflate_fast keeps m_ret *)
Lemma fwalk_f_ret: forall fx dx k il t here m h m',
  fwalk_f fx dx k il t here m = (h, m') -> m_ret m' = m_ret m.
Proof.
  induction k as [|k IH]; intros il t here m h m' E; simpl in E.
  - inversion E; subst; auto.
  - destruct (il (e_op here)); [apply IH in E; simpl in E; exact E | inversion E; subst; auto].
Qed.

Local Opaque fwalk_f.

Ltac facts2 :=
  repeat match goal with
  | H: fwalk_f _ _ _ _ _ _ _ = (_, _) |- _ => apply fwalk_f_ret in H; simpl in H
  end.

Lemma fast_iter_ret: forall fx dx m, m_ret (snd (fast_iter fx dx m)) = m_ret m.
Proof.
  intros. unfold fast_iter, fpull. cbv beta zeta. dsplit. all: facts2; simpl; rw_facts; simpl; rw_facts;
  simpl; rw_facts; reflexivity.
Qed.

Lemma fast_loop_ret: forall fx dx k m, m_ret (fast_loop fx dx k m) = m_ret m.
Proof.
  induction k as [|k IH]; intros m; simpl; [reflexivity|].
  pose proof (fast_iter_ret fx dx m) as F.
  destruct (fast_iter fx dx m) as [go m'] eqn:E; simpl in F |- *.
  destruct (_ && _ && _); [rewrite IH|]; exact F.
Qed.

Lemma fast_ret: forall fx dx m, m_ret (fast fx dx m) = m_ret m.
Proof.
  intros. unfold fast. cbv beta zeta. simpl. rewrite fast_loop_ret. reflexivity.
Qed.

Local Opaque fast fast_iter fast_loop.

(* ---------------------------------------------------------------------------------------------- *)
(* the cases                                                                                      *)

Definition iok (m: mst) (o: iout) : Prop :=
  match o with
  | IBrk m' => fr m m'
  | IRet r m' => -5 <= r <= 2
  end.

Lemma iok_after: forall m m2 o, iok m2 o -> fr m m2 -> iok m o.
Proof.
  intros m m2 [m'|r m'] H F; simpl in *; auto.
  eapply fr_trans; eauto.
Qed.

Ltac facts3 :=
  repeat match goal with
  | H: codelens_loop ?a ?b ?k ?m0 = ?c |- _ =>
      let F := fresh "F" in
      pose proof (codelens_loop_fr a b k m0) as F; rewrite H in F; simpl in F; clear H
  end.

Create HintDb caseok.

Ltac case_leaf :=
  lazymatch goal with
  | |- iok _ (IBrk _) => unfold iok; fr_leaf
  | |- iok _ (IRet _ _) => unfold iok; cbv [Z_NEED_DICT Z_MEM_ERROR Z_STREAM_ERROR]; lia
  | |- iok _ _ => eapply iok_after; [solve [eauto with caseok] | fr_leaf]
  end.

Ltac fr_leaf3 :=
  unfold fr in *; unfold rok in *; do 4 (simpl in *; rw_facts);
  intros; cbv [Z_STREAM_END Z_DATA_ERROR] in *; try lia; auto.

Ltac case_tac := intros; cbv beta zeta;
  repeat progress (dsplit; try match goal with |- iok _ (if ?c then _ else _) => destruct c end); facts; facts2; facts3;
  first [case_leaf | lazymatch goal with
                     | |- iok _ (IBrk _) => unfold iok; fr_leaf3
                     | |- iok _ _ => eapply iok_after; [solve [eauto with caseok] | fr_leaf3]
                     end].

Section Cases.
Variables (flush: Z) (fx dx: list entry) (fst: mst -> mst).

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
Lemma LEN_ok: (forall m, m_ret (fst m) = m_ret m) -> forall m, iok m (c_LEN fx dx fst m).
Proof.
  intros Hf m. pose proof (Hf (restore m)) as F. simpl in F.
  unfold c_LEN. case_tac.
Qed.
Hint Resolve LEN_ok : caseok.
Local Opaque c_LEN.
Lemma LEN__ok: (forall m, m_ret (fst m) = m_ret m) -> forall m, iok m (c_LEN_ fx dx fst m).
Proof. intros Hf. unfold c_LEN_. case_tac. Qed.
Hint Resolve LEN__ok : caseok.
Local Opaque c_LEN_.
Lemma CODELENS_ok: (forall m, m_ret (fst m) = m_ret m) -> forall m, iok m (c_CODELENS flush fx dx fst m).
Proof. intros Hf. unfold c_CODELENS. case_tac. Qed.
Hint Resolve CODELENS_ok : caseok.
Local Opaque c_CODELENS.
Lemma LENLENS_ok: (forall m, m_ret (fst m) = m_ret m) -> forall m, iok m (c_LENLENS flush fx dx fst m).
Proof. intros Hf. unfold c_LENLENS. case_tac. Qed.
Hint Resolve LENLENS_ok : caseok.
Local Opaque c_LENLENS.
Lemma TABLE_ok: (forall m, m_ret (fst m) = m_ret m) -> forall m, iok m (c_TABLE flush fx dx fst m).
Proof. intros Hf. unfold c_TABLE. case_tac. Qed.
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
Proof. unfold c_HEAD. case_tac. Qed.
Hint Resolve HEAD_ok : caseok.
Local Opaque c_HEAD.
Lemma HEAD2_ok: forall m, iok m (c_HEAD2 m).
Proof. unfold c_HEAD2. case_tac. Qed.
Hint Resolve HEAD2_ok : caseok.
Local Opaque c_HEAD2.

Lemma step2_ok: (forall m, m_ret (fst m) = m_ret m) -> forall m, iok m (step2 flush fx dx fst m).
Proof.
  intros Hf m. unfold step2.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end;
  first [solve [eauto with caseok] | unfold iok; cbv [Z_MEM_ERROR Z_STREAM_ERROR]; lia].
Qed.

End Cases.

Lemma stepf2_ok: forall flush fx dx m, iok m (stepf2 flush fx dx m).
Proof. intros. unfold stepf2. apply step2_ok. intros. apply fast_ret. Qed.

Lemma loop2_ok: forall flush fx dx m o, loop2 flush fx dx m o -> iok m o.
Proof.
  intros flush fx dx m o L. induction L.
  - pose proof (stepf2_ok flush fx dx m) as S. rewrite H in S. exact S.
  - pose proof (stepf2_ok flush fx dx m) as S. rewrite H in S. exact S.
  - pose proof (stepf2_ok flush fx dx m) as S. rewrite H in S.
    eapply iok_after; eauto.
Qed.

Lemma leave_fin_ret: forall flush m, rok m -> -5 <= r_ret (leave_fin flush m) <= 2.
Proof.
  intros flush m R. unfold rok in R. unfold leave_fin. cbv beta zeta.
  dsplit; simpl; cbv [Z_BUF_ERROR]; lia.
Qed.

Lemma run2_ret: forall flush fx dx m0 res,
  -5 <= m_ret m0 <= 2 ->
  run2 flush fx dx m0 res ->
  -5 <= r_ret res <= 2.
Proof.
  intros flush fx dx m0 res R (o & L & E).
  apply loop2_ok in L.
  destruct o as [m|r m]; simpl in L.
  - destruct E.
    + simpl. cbv [Z_MEM_ERROR]. lia.
    + apply leave_fin_ret. apply L. exact R.
  - subst res. simpl. exact L.
Qed.
