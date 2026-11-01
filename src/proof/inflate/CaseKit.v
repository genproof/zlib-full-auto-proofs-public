(* Fallthrough between the cases of inflate()'s switch: case i's lemma from the proof of case i's own
   body (case_body i) and the lemma of case i+1 (a hypothesis, next_ok), so that the case lemmas can be
   proved independently. *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.inflate.CaseCommon.

#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* the statements of case i alone *)
Definition case_body (i: nat) : statement :=
  match ls_drop i inflate_LS with LScons _ b _ => b | LSnil => Sskip end.

Ltac case_body_stmt :=
  cbv beta iota zeta delta [case_body inflate_LS find_switch f_inflate fn_body ls_drop].

Lemma ls_drop_S: forall i ls,
  ls_drop (S i) ls = match ls_drop i ls with LScons _ _ r => r | LSnil => LSnil end.
Proof.
  induction i; intros [ | l b r]; try reflexivity. apply IHi.
Qed.

Lemma seq_split: forall i, (i <= 32)%nat ->
  seq_of_labeled_statement (ls_drop i inflate_LS) =
  Ssequence (case_body i) (seq_of_labeled_statement (ls_drop (S i) inflate_LS)).
Proof.
  intros i Hi. unfold case_body. rewrite ls_drop_S.
  assert (exists l b r, ls_drop i inflate_LS = LScons l b r) as (l & b & r & E).
  { do 33 (destruct i as [|i]; [eexists; eexists; eexists; reflexivity | ]). lia. }
  rewrite E. reflexivity.
Qed.

(* the lemma of the case at index i (mode Y) *)
Definition case_ok {Espec: OracleKind} (F: frame) (Y: Z) (i: nat) : Prop :=
  forall m', m_mode m' = Y -> m_leave m' = 0 -> mwf m' ->
    semax Delta_inflate (loop_state F m') (seq_of_labeled_statement (ls_drop i inflate_LS))
      (switch_ret_assert (case_post F m')).

(* the end of case i's body when it falls through into mode Y: the machine m' with the same outcome
   of the pass *)
Definition fall_post (F: frame) (m: mst) (Y: Z) : environ -> mpred :=
  EX m': mst,
    !! (stepf (f_flush F) lenfix_list distfix_list m = stepf (f_flush F) lenfix_list distfix_list m' /\
        m_mode m' = Y /\ m_leave m' = 0 /\ mwf m') && loop_state F m'.

Lemma case_post_eq: forall F m m',
  stepf (f_flush F) lenfix_list distfix_list m = stepf (f_flush F) lenfix_list distfix_list m' ->
  case_post F m = case_post F m'.
Proof. intros F m m' E. unfold case_post. rewrite E. reflexivity. Qed.

Lemma case_fallthrough {Espec: OracleKind} (F: frame) (m: mst) (Y: Z) (i: nat):
  (i < 32)%nat ->
  case_ok F Y (S i) ->
  semax Delta_inflate (loop_state F m) (case_body i)
    (overridePost (fall_post F m Y) (switch_ret_assert (case_post F m))) ->
  semax Delta_inflate (loop_state F m) (seq_of_labeled_statement (ls_drop i inflate_LS))
    (switch_ret_assert (case_post F m)).
Proof.
  intros Hi HY HB. rewrite seq_split by lia.
  eapply semax_seq; [exact HB | ].
  unfold fall_post. Intros m'.
  apply semax_extract_prop. intros (E & HM & HL & W).
  rewrite (case_post_eq F m m' E).
  apply HY; auto.
Qed.
