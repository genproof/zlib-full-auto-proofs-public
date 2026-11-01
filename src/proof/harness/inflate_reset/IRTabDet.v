(* Law inflate_reset, theory part: inflate_table's reachable entries do not depend on the old contents of its table space (IRDefs.tabdet_stmt). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_reset.IRDefs.
Import ListNotations.
Local Open Scope Z_scope.


Local Notation step := Zlib.proof.inftrees.model.step.
Local Notation run := Zlib.proof.inftrees.model.run.
Local Notation state := Zlib.proof.inftrees.model.state.
Local Notation mkSt := Zlib.proof.inftrees.model.mkSt.
Local Notation outcome := Zlib.proof.inftrees.model.outcome.
Local Notation Continue := Zlib.proof.inftrees.model.Continue.
Local Notation Break := Zlib.proof.inftrees.model.Break.
Local Notation Full := Zlib.proof.inftrees.model.Full.
Local Notation finish := Zlib.proof.inftrees.model.finish.
Local Notation result := Zlib.proof.inftrees.model.result.

(* Two tables built by the same writes on two old contents o1 o2: per index equal, or both still old. *)
Definition irtd_trel (o1 o2 t1 t2: list entry) : Prop :=
  Zlength t1 = Zlength t2 /\
  forall i, Znth i t1 = Znth i t2 \/ (Znth i t1 = Znth i o1 /\ Znth i t2 = Znth i o2).

Lemma irtd_trel_refl: forall o1 o2, Zlength o1 = Zlength o2 -> irtd_trel o1 o2 o1 o2.
Proof. intros o1 o2 L. split; auto. Qed.

Lemma irtd_trel_upd: forall o1 o2 t1 t2 j e,
  irtd_trel o1 o2 t1 t2 -> irtd_trel o1 o2 (upd_Znth j t1 e) (upd_Znth j t2 e).
Proof.
  intros o1 o2 t1 t2 j e [L R].
  destruct (zle 0 j); [destruct (zlt j (Zlength t1))|].
  - split. { rewrite !upd_Znth_Zlength by lia. auto. }
    intros i. destruct (Z.eq_dec i j).
    + subst. left. rewrite !upd_Znth_same by lia. auto.
    + rewrite !upd_Znth_diff' by lia. apply R.
  - rewrite !upd_Znth_out_of_range by lia. split; auto.
  - rewrite !upd_Znth_out_of_range by lia. split; auto.
Qed.

Lemma irtd_trel_rep_fill: forall n o1 o2 t1 t2 base incr e,
  irtd_trel o1 o2 t1 t2 -> irtd_trel o1 o2 (rep_fill t1 base incr n e) (rep_fill t2 base incr n e).
Proof.
  induction n; intros; simpl; auto. apply IHn. apply irtd_trel_upd. auto.
Qed.

Definition irtd_strip (s: state) : state :=
  mkSt (s_huff s) (s_sym s) (s_len s) (s_curr s) (s_drop s) (s_low s) (s_used s) (s_next s) (s_cnt s) [].

Definition irtd_srel (o1 o2: list entry) (s1 s2: state) : Prop :=
  irtd_strip s1 = irtd_strip s2 /\ irtd_trel o1 o2 (s_tab s1) (s_tab s2).

Definition irtd_orel (o1 o2: list entry) (r1 r2: outcome) : Prop :=
  match r1, r2 with
  | Continue a, Continue b => irtd_srel o1 o2 a b
  | Break a, Break b => irtd_srel o1 o2 a b
  | Full a, Full b => irtd_srel o1 o2 a b
  | _, _ => False
  end.

Lemma irtd_step: forall o1 o2 type lens W root mx s1 s2,
  irtd_srel o1 o2 s1 s2 -> irtd_orel o1 o2 (step type lens W root mx s1) (step type lens W root mx s2).
Proof.
  intros o1 o2 type lens W root mx [h1 y1 l1 c1 d1 w1 u1 n1 k1 t1] [h2 y2 l2 c2 d2 w2 u2 n2 k2 t2] [E T].
  unfold irtd_strip in E; simpl in E, T. inversion E; subst; clear E.
  unfold step; simpl.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
  simpl; split; simpl; auto;
  repeat first [apply irtd_trel_upd | apply irtd_trel_rep_fill]; auto.
Qed.

Lemma irtd_run: forall k o1 o2 type lens W root mx s1 s2,
  irtd_srel o1 o2 s1 s2 -> irtd_orel o1 o2 (run type lens W root mx k s1) (run type lens W root mx k s2).
Proof.
  induction k; intros; simpl; auto.
  pose proof (irtd_step o1 o2 type lens W root mx s1 s2 H) as S.
  destruct (step type lens W root mx s1), (step type lens W root mx s2); simpl in S; try contradiction; auto.
Qed.

Definition irtd_rrel (o1 o2: list entry) (r1 r2: result) : Prop :=
  match r1, r2 with
  | RErr, RErr => True
  | REnough _, REnough _ => True
  | ROk r1 u1 a, ROk r2 u2 b => r1 = r2 /\ u1 = u2 /\ irtd_trel o1 o2 a b
  | _, _ => False
  end.

Lemma irtd_finish: forall o1 o2 s1 s2, irtd_srel o1 o2 s1 s2 ->
  s_used s1 = s_used s2 /\ irtd_trel o1 o2 (finish s1) (finish s2).
Proof.
  intros o1 o2 [h1 y1 l1 c1 d1 w1 u1 n1 k1 t1] [h2 y2 l2 c2 d2 w2 u2 n2 k2 t2] [E T].
  unfold irtd_strip in E; simpl in E, T. inversion E; subst; clear E.
  unfold finish; simpl. split; auto. destruct (h2 =? 0); auto. apply irtd_trel_upd; auto.
Qed.

Lemma irtd_model: forall type lens req o1 o2, Zlength o1 = Zlength o2 ->
  irtd_rrel o1 o2 (inflate_table_model type lens req o1) (inflate_table_model type lens req o2).
Proof.
  intros type lens req o1 o2 L. unfold inflate_table_model.
  destruct (maxlen lens =? 0).
  { simpl. split; auto. split; auto. apply irtd_trel_upd, irtd_trel_upd, irtd_trel_refl; auto. }
  destruct (left_final (counts lens)); simpl; auto.
  match goal with |- context [if ?b then _ else _] => destruct b end; simpl; auto.
  match goal with |- context [if ?b then _ else _] => destruct b end; simpl; auto.
  assert (S: irtd_srel o1 o2 (init_state lens (root_of req lens) o1) (init_state lens (root_of req lens) o2)).
  { split; [reflexivity|]. apply irtd_trel_refl; auto. }
  pose proof (irtd_run (length (sorted_syms lens)) _ _ type lens (sorted_syms lens) (root_of req lens) (maxlen lens)
                _ _ S) as R.
  destruct (run _ _ _ _ _ _ (init_state lens (root_of req lens) o1)),
           (run _ _ _ _ _ _ (init_state lens (root_of req lens) o2)); simpl in R; try contradiction; auto;
  destruct (irtd_finish _ _ _ _ R); simpl; auto.
Qed.

(* the poison entry: entry_ok, neither a link nor final for any kind *)
Definition irtd_P : entry := mkE 32 0 0.

Lemma irtd_P_ok: entry_ok irtd_P.
Proof. unfold entry_ok, irtd_P; simpl; lia. Qed.

Lemma irtd_P_link: forall kind, islink kind (e_op irtd_P) = false.
Proof. intros. unfold islink, irtd_P; simpl. apply andb_false_r. Qed.

Lemma irtd_P_final: forall kind, ~ final_ok kind irtd_P.
Proof.
  intros kind F. unfold final_ok, irtd_P in F; simpl in F.
  destruct (kind =? CODES); [|destruct (kind =? LENS)]; simpl in F; unfold CODES, LENS in *;
  repeat match goal with H: _ \/ _ |- _ => destruct H end; try lia;
  match goal with H: Z.land _ _ <> 0 /\ _ |- _ => destruct H as [H _]; apply H; reflexivity end.
Qed.

Lemma tabdet_proof : Zlib.proof.inflate.Cover3.cover3_stmt -> tabdet_stmt.
Proof.
  intros C type lens req old1 old2 I Ic Cap E1 L2 E2.
  set (P := Zrepeat irtd_P (Zlength old1)).
  assert (LP: Zlength P = Zlength old1) by (unfold P; rewrite Zlength_Zrepeat; pose proof (Zlength_nonneg old1); lia).
  assert (EP: Forall entry_ok P).
  { unfold P, Zrepeat. apply Forall_forall. intros x Hx. apply repeat_spec in Hx. subst. apply irtd_P_ok. }
  pose proof (irtd_model type lens req old1 P (eq_sym LP)) as R1.
  pose proof (irtd_model type lens req old2 P ltac:(lia)) as R2.
  pose proof (C type lens req P) as CP.
  destruct (inflate_table_model type lens req old1) as [|a1|r1 u1 t1] eqn:H1;
  destruct (inflate_table_model type lens req old2) as [|a2|r2 u2 t2] eqn:H2;
  destruct (inflate_table_model type lens req P) as [|ap|rp up tp] eqn:HP;
  simpl in R1, R2; try contradiction;
  try (split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; intros; discriminate).
  destruct R1 as (<- & <- & T1). destruct R2 as (<- & <- & T2).
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  intros root used t Hok. inversion Hok; subst root used t; clear Hok.
  exists t2. split; [reflexivity|].
  destruct (CP _ _ tp I Ic ltac:(rewrite LP; exact Cap) EP eq_refl) as (TV & Hu & _).
  assert (Kq: forall i, 0 <= i < Zlength P -> Znth i tp <> irtd_P -> Znth i t1 = Znth i tp /\ Znth i t2 = Znth i tp).
  { intros i Hi NP.
    assert (ZP: Znth i P = irtd_P) by (unfold P; apply Znth_Zrepeat; lia).
    destruct T1 as [_ T1]. destruct T2 as [_ T2].
    destruct (T1 i) as [A|[_ A]]; [|rewrite ZP in A; congruence].
    destruct (T2 i) as [B|[_ B]]; [|rewrite ZP in B; congruence].
    auto. }
  destruct TV as [Rb Sz Rt].
  intros i Hi. specialize (Rt i Hi). cbv zeta in Rt. destruct Rt as [Eok Rt].
  assert (NP: Znth i tp <> irtd_P).
  { intro EQ. rewrite EQ in Rt. rewrite irtd_P_link in Rt. destruct Rt as [_ F]. exact (irtd_P_final _ F). }
  destruct (Kq i ltac:(lia) NP) as [A B]. rewrite A, B. split; [reflexivity|].
  intros Lk j Hj. rewrite Lk in Rt. destruct Rt as (_ & _ & _ & Sj).
  destruct (Sj j Hj) as (Rj & _ & _ & _ & Fj). cbv zeta in *.
  assert (NPj: Znth (e_val (Znth i tp) + j) tp <> irtd_P).
  { intro EQ. rewrite EQ in Fj. exact (irtd_P_final _ Fj). }
  destruct (Kq (e_val (Znth i tp) + j)) as [A' B']; [lia|exact NPj|]. rewrite A', B'. reflexivity.
Qed.
