(* The hypotheses the case lemmas of inflate()'s switch may use (discharged by the body assembly), and
   the statement that every case is proved (cases_all). *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.inflate.CaseKit.
#[local] Existing Instance Zlib.units.Inflate.CS.

(* the shares of the frame *)
Definition frame_ok (F: frame) : Prop :=
  writable_share (f_shs F) /\ writable_share (f_hsh F) /\ readable_share (f_gsh F) /\ readable_share (f_tsh F).

(* the fixed tables are valid (FixedValid2.v tvalid_fixed2) *)
Definition fixed_ok : Prop :=
  forall s, tvalid LENS lenfix_list distfix_list s TLenfix 9 /\ tvalid DISTS lenfix_list distfix_list s TDistfix 5.

(* the case lemma of every mode HEAD .. SYNC (index i = mode - HEAD) *)
Definition cases_all : Prop :=
  forall {Espec: OracleKind} (F: frame), frame_ok F -> forall i, (i < 32)%nat -> case_ok F (HEAD + Z.of_nat i) i.

(* one pass of the switch keeps mwf *)
Definition stepf_mwf_stmt : Prop :=
  forall flush m, mwf m -> m_leave m = 0 ->
  match stepf flush lenfix_list distfix_list m with IBrk m' => mwf m' | IRet _ m' => mwf m' end.
