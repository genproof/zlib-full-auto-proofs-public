(* RT-H: mechanical port of inflate/CaseKit5.v to the header-external loop state (RTHLoop.v); identifiers whose meaning changes carry the suffix H. *)
(* CaseKit.v in Delta_cases5 over Model2.v (case_post2H) with the invariant mwf3 (Inv2.v): the lemma of case i for any machine of
   mode Y satisfying mwf3, and the fallthrough between cases (a fallthrough machine must satisfy mwf3). *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.roundtrip.RTHCaseKit.
Require Export Zlib.proof.inflate.Callees5.
Require Export Zlib.proof.roundtrip.RTHCaseCommon.
Require Export Zlib.proof.inflate.CaseKit5.

#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Definition case_ok5H {Espec: OracleKind} (F: frame) (Y: Z) (i: nat) : Prop :=
  forall m', m_mode m' = Y -> m_leave m' = 0 -> mwf3 m' ->
    semax Delta_cases5 (loop_stateH F m') (seq_of_labeled_statement (ls_drop i inflate_LS))
      (switch_ret_assert (case_post2H F m')).

Definition fall_post5H (F: frame) (m: mst) (Y: Z) : environ -> mpred :=
  EX m': mst,
    !! (stepf2 (f_flush F) lenfix_list distfix_list m = stepf2 (f_flush F) lenfix_list distfix_list m' /\
        m_mode m' = Y /\ m_leave m' = 0 /\ mwf3 m') && loop_stateH F m'.

Lemma case_fallthrough5H {Espec: OracleKind} (F: frame) (m: mst) (Y: Z) (i: nat):
  (i < 32)%nat ->
  case_ok5H F Y (S i) ->
  semax Delta_cases5 (loop_stateH F m) (case_body i)
    (overridePost (fall_post5H F m Y) (switch_ret_assert (case_post2H F m))) ->
  semax Delta_cases5 (loop_stateH F m) (seq_of_labeled_statement (ls_drop i inflate_LS))
    (switch_ret_assert (case_post2H F m)).
Proof.
  intros Hi HY HB. rewrite seq_split by lia.
  eapply semax_seq; [exact HB | ].
  unfold fall_post5H. Intros m'.
  apply semax_extract_prop. intros (E & HM & HL & W).
  rewrite (case_post2_eqH F m m' E).
  apply HY; auto.
Qed.

(* a case proved for mwf machines is a case_ok5H *)
Lemma case_ok5_of_mwfH {Espec: OracleKind} (F: frame) (Y: Z) (i: nat):
  (forall m', m_mode m' = Y -> m_leave m' = 0 -> mwf m' ->
     semax Delta_cases5 (loop_stateH F m') (seq_of_labeled_statement (ls_drop i inflate_LS))
       (switch_ret_assert (case_post2H F m'))) ->
  case_ok5H F Y i.
Proof. intros H m' A B [W _]. apply H; auto. Qed.
