(* RT-H: mechanical port of inflate/CaseHyps5.v to the header-external loop state (RTHLoop.v); identifiers whose meaning changes carry the suffix H. *)
(* The hypotheses and statements of the switch cases, version 5 (Delta_cases5, case_post2H over Model2.v,
   invariant mwf3):
   - frame_ok5: frame_ok + flush is an int (C compares it as an int);
   - the header cases FLAGS .. COMMENT (indices 1..7) hold the application's zero-size header buffers'
     malloc tokens (hdr_tok: `head->extra != Z_NULL` needs a valid pointer) and know
     that a header field marked present has a non-NULL buffer (hd_ok);
   - cases_all5H: every case, the header cases with the tokens. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.roundtrip.RTHCaseKit5.
Require Export Zlib.proof.roundtrip.RTHCaseHyps.
Require Export Zlib.proof.inflate.Cover3.
Require Export Zlib.proof.inflate.CaseHyps5.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* the malloc token of a non-NULL header buffer of size 0 *)
(* a header field marked present has a buffer *)
(* the lemma of a header case: with the tokens framed in *)
Definition case_okT5H {Espec: OracleKind} (F: frame) (Y: Z) (i: nat) : Prop :=
  forall m', m_mode m' = Y -> m_leave m' = 0 -> mwf3 m' -> hd_ok F m' ->
    semax Delta_cases5 (loop_stateH F m' * (fun _ => hdr_tok F m'))
      (seq_of_labeled_statement (ls_drop i inflate_LS))
      (frame_ret_assert (switch_ret_assert (case_post2H F m')) (fun _ => hdr_tok F m')).

Lemma case_okT5_of_ok5H {Espec: OracleKind} (F: frame) (Y: Z) (i: nat):
  case_ok5H F Y i -> case_okT5H F Y i.
Proof.
  intros H m' A B C D. apply semax_frame; [ | apply H; auto].
  intros rho te _. reflexivity.
Qed.

(* the fixed tables are valid, the length table with the length bound *)
(* every case: the header cases (indices 1..7) with the tokens *)
Definition cases_all5H : Prop :=
  forall {Espec: OracleKind} (F: frame), frame_ok5 F ->
    (forall i, (i < 32)%nat -> (i < 1 \/ 7 < i)%nat -> case_ok5H F (HEAD + Z.of_nat i) i) /\
    (forall i, (1 <= i <= 7)%nat -> case_okT5H F (HEAD + Z.of_nat i) i).

(* one pass of the switch (Model2.v) preserves mwf3 *)
