(* RT-H: mechanical port of inflate/CaseKit.v to the header-external loop state (RTHLoop.v); identifiers whose meaning changes carry the suffix H. *)
(* Fallthrough between the cases of inflate()'s switch: case i's lemma from the proof of case i's own
   body (case_body i) and the lemma of case i+1 (a hypothesis, next_ok), so that the case lemmas can be
   proved independently. *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.roundtrip.RTHCaseCommon.
Require Export Zlib.proof.inflate.CaseKit.

#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* the statements of case i alone *)




(* the lemma of the case at index i (mode Y) *)
Definition case_okH {Espec: OracleKind} (F: frame) (Y: Z) (i: nat) : Prop :=
  forall m', m_mode m' = Y -> m_leave m' = 0 -> mwf m' ->
    semax Delta_inflate (loop_stateH F m') (seq_of_labeled_statement (ls_drop i inflate_LS))
      (switch_ret_assert (case_postH F m')).

(* the end of case i's body when it falls through into mode Y: the machine m' with the same outcome
   of the pass *)
Definition fall_postH (F: frame) (m: mst) (Y: Z) : environ -> mpred :=
  EX m': mst,
    !! (stepf (f_flush F) lenfix_list distfix_list m = stepf (f_flush F) lenfix_list distfix_list m' /\
        m_mode m' = Y /\ m_leave m' = 0 /\ mwf m') && loop_stateH F m'.

Lemma case_post_eqH: forall F m m',
  stepf (f_flush F) lenfix_list distfix_list m = stepf (f_flush F) lenfix_list distfix_list m' ->
  case_postH F m = case_postH F m'.
Proof. intros F m m' E. unfold case_postH. rewrite E. reflexivity. Qed.

Lemma case_fallthroughH {Espec: OracleKind} (F: frame) (m: mst) (Y: Z) (i: nat):
  (i < 32)%nat ->
  case_okH F Y (S i) ->
  semax Delta_inflate (loop_stateH F m) (case_body i)
    (overridePost (fall_postH F m Y) (switch_ret_assert (case_postH F m))) ->
  semax Delta_inflate (loop_stateH F m) (seq_of_labeled_statement (ls_drop i inflate_LS))
    (switch_ret_assert (case_postH F m)).
Proof.
  intros Hi HY HB. rewrite seq_split by lia.
  eapply semax_seq; [exact HB | ].
  unfold fall_postH. Intros m'.
  apply semax_extract_prop. intros (E & HM & HL & W).
  rewrite (case_post_eqH F m m' E).
  apply HY; auto.
Qed.
