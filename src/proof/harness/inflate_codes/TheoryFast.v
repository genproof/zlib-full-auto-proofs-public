(* Law inflate_codes, theory part: LEN's fast path (inflate_fast's model) keeps Kc *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_codes.TheoryDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* the fields inflate_fast keeps; the mode stays, or becomes TYPE, or BAD with a message *)
Definition tf_keep (m m': mst) : Prop :=
  m_inp m' = m_inp m /\ m_aout m' = m_aout m /\ i_wrap (m_s m') = i_wrap (m_s m) /\
  i_head (m_s m') = i_head (m_s m) /\ m_ret m' = m_ret m /\ m_leave m' = m_leave m /\
  m_out m' = m_out m /\
  ((m_mode m' = m_mode m /\ m_msg m' = m_msg m) \/ m_mode m' = Zlib.proof.inflate.Model.TYPE \/
   (m_mode m' = BAD /\ m_msg m' <> None)).

Lemma tf_keep_refl m : tf_keep m m.
Proof. unfold tf_keep; repeat split; auto. Qed.

Lemma tf_keep_trans m1 m2 m3 : tf_keep m1 m2 -> tf_keep m2 m3 -> tf_keep m1 m3.
Proof.
  unfold tf_keep; intros (A1 & B1 & C1 & D1 & E1 & F1 & G1 & H1) (A2 & B2 & C2 & D2 & E2 & F2 & G2 & H2).
  repeat split; try congruence.
  destruct H2 as [[H2 H2']|[H2|[H2 H2']]]; [|auto|auto].
  destruct H1 as [[H1 H1']|[H1|[H1 H1']]]; [left; split; congruence|right; left; congruence|].
  right; right; split; congruence.
Qed.

Lemma tf_fwalk fx dx k il t here m h' m' :
  fwalk_f fx dx k il t here m = (h', m') ->
  m_s m' = m_s m /\ m_inp m' = m_inp m /\ m_aout m' = m_aout m /\ m_ret m' = m_ret m /\
  m_leave m' = m_leave m /\ m_out m' = m_out m /\ m_msg m' = m_msg m.
Proof.
  revert here m; induction k; intros here m E; cbn [fwalk_f] in E.
  - inversion E; subst; cbn; repeat split.
  - destruct (il (e_op here)).
    + apply IHk in E; destruct E as (-> & -> & -> & -> & -> & -> & ->); cbn; repeat split.
    + inversion E; subst; cbn; repeat split.
Qed.

(* destruct every closed if / match of the goal, innermost scrutinee first *)
Ltac tf_hdest x :=
  lazymatch x with
  | match ?c with _ => _ end => tf_hdest c
  | context [match ?c with _ => _ end] => tf_hdest c
  | _ => tryif is_var x then destruct x else (let E := fresh "E" in destruct x eqn:E)
  end.
Ltac tf_hsplit :=
  repeat (cbv beta iota zeta;
          match goal with
          | |- context [match ?x with _ => _ end] => tf_hdest x
          end).

Ltac tf_huse :=
  repeat match goal with
  | E: fwalk_f _ _ _ _ _ _ _ = (_, _) |- _ =>
      apply tf_fwalk in E; destruct E as (? & ? & ? & ? & ? & ? & ?)
  | E: copy_bytes _ _ _ _ = (_, _) |- _ => clear E
  end.

Ltac tf_cbn := cbn -[copy_bytes fwalk_f fast_iter fast_loop fast Zlib.proof.inflate.Model.TYPE BAD LEN].

Ltac tf_rw :=
  repeat match goal with
  | H: m_s ?a = _ |- context [m_s ?a] => rewrite H
  | H: m_inp ?a = _ |- context [m_inp ?a] => rewrite H
  | H: m_aout ?a = _ |- context [m_aout ?a] => rewrite H
  | H: m_ret ?a = _ |- context [m_ret ?a] => rewrite H
  | H: m_leave ?a = _ |- context [m_leave ?a] => rewrite H
  | H: m_out ?a = _ |- context [m_out ?a] => rewrite H
  | H: m_msg ?a = _ |- context [m_msg ?a] => rewrite H
  end.

Ltac tf_close :=
  unfold tf_keep, m_mode; repeat progress (tf_cbn; tf_rw);
  repeat split; try reflexivity;
  first [ left; split; reflexivity
        | right; left; reflexivity
        | right; right; split; [reflexivity | discriminate] ].

Lemma tf_iter fx dx m : tf_keep m (snd (fast_iter fx dx m)).
Proof. unfold fast_iter. tf_hsplit; tf_huse; tf_close. Qed.

Lemma tf_loop fx dx k m : tf_keep m (fast_loop fx dx k m).
Proof.
  revert m; induction k; intros m; cbn [fast_loop]; [apply tf_keep_refl|].
  pose proof (tf_iter fx dx m) as A.
  destruct (fast_iter fx dx m) as [go m1] eqn:E; cbn in A |- *.
  destruct ((go && _ && _)%bool); [eapply tf_keep_trans; [exact A | apply IHk] | exact A].
Qed.

Lemma tf_fast fx dx m : tf_keep m (fast fx dx m) /\ 0 <= m_bits (fast fx dx m) <= 7.
Proof.
  unfold fast. cbv zeta.
  pose proof (tf_loop fx dx (Z.to_nat (m_aout m) + 1) m) as A; revert A.
  generalize (fast_loop fx dx (Z.to_nat (m_aout m) + 1) m); intros m1 A.
  split.
  - eapply tf_keep_trans; [exact A|]. clear A. unfold tf_keep, m_mode; cbn.
    repeat split; auto.
  - cbn [m_bits restore upd_s set_m_bits set_m_hold set_m_nx set_m_s set_m_sow set_m_snx]. rewrite Z.shiftr_div_pow2 by lia.
    replace (m_bits m1 - m_bits m1 / 2 ^ 3 * 8) with (m_bits m1 mod 8)
      by (rewrite Z.mod_eq by lia; change (2 ^ 3) with 8; lia).
    pose proof (Z.mod_pos_bound (m_bits m1) 8); lia.
Qed.

(* setting back keeps Kc *)
Lemma tf_back wrap src pos inp aout m :
  Kc wrap src pos inp aout m -> Kc wrap src pos inp aout (upd_s m (fun s => set_i_back s (-1))).
Proof. intros []; constructor; assumption. Qed.

Lemma th_fast : fast_kc_stmt.
Proof.
  unfold fast_kc_stmt; intros wrap src pos inp aout m HK Hlv Hmd Hout. cbv zeta.
  destruct (tf_fast lenfix_list distfix_list (restore m)) as [A Hb]; revert A Hb.
  generalize (fast lenfix_list distfix_list (restore m)); intros mf A Hb.
  unfold tf_keep, m_mode in A; cbn [restore upd_s set_m_s set_m_sow set_m_snx m_s m_inp m_aout m_ret
    m_leave m_out m_msg set_i_bits set_i_hold i_wrap i_head i_mode] in A.
  destruct A as (Ai & Aa & Aw & Ah & Ar & Al & Ao & Am).
  unfold m_mode in Hmd; rewrite Hmd in Am.
  assert (Hm : m_mode mf = LEN \/ m_mode mf = Zlib.proof.inflate.Model.TYPE \/ m_mode mf = BAD)
    by (unfold m_mode; destruct Am as [[E _]|[E|[E _]]]; auto).
  assert (Hmsg : m_mode mf = BAD -> m_msg mf <> None).
  { unfold m_mode; destruct Am as [[E _]|[E|[E N]]]; rewrite E; auto;
      intros X; unfold LEN, BAD, Zlib.proof.inflate.Model.TYPE in X; discriminate. }
  clear Am.
  assert (Kf : Kc wrap src pos inp aout mf).
  { destruct HK; constructor.
    - congruence.
    - congruence.
    - congruence.
    - congruence.
    - destruct Hm as [E|[E|E]]; rewrite E; unfold LEN, BAD, SYNC, Zlib.proof.inflate.Model.TYPE; discriminate.
    - intros _ _. rewrite Ar. apply kc_ret; unfold m_mode; rewrite Hmd; unfold LEN, BAD, DONE; discriminate.
    - intros X; rewrite Al, Hlv in X; discriminate.
    - exact Hmsg.
    - intros _ _; lia.
    - intros X; exfalso; apply X; congruence.
    - intros _ X; destruct Hm as [E|[E|E]]; rewrite E in X;
        unfold LEN, BAD, HEAD, Zlib.proof.inflate.Model.TYPE in X; discriminate.
    - intros X; destruct Hm as [E|[E|E]]; rewrite E in X;
        unfold LEN, BAD, DICTID, Zlib.proof.inflate.Model.TYPE in X; discriminate.
    - intros X; destruct Hm as [E|[E|E]]; rewrite E in X;
        unfold LEN, BAD, DICT, Zlib.proof.inflate.Model.TYPE in X; discriminate. }
  clear HK Hmsg Hb Ai Aa Aw Ah Ar Ao.
  destruct (m_mode mf =? Zlib.proof.inflate.Model.TYPE) eqn:ET.
  - apply Z.eqb_eq in ET. split; [apply tf_back, Kf|]. split; [exact (eq_trans Al Hlv)|].
    right; left; exact ET.
  - split; [exact Kf|]. split; [exact (eq_trans Al Hlv)|exact Hm].
Qed.
