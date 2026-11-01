(* inflate(), the switch cases LEN (20), version 5 (Delta_cases5, case_post2 over Model2.v, mwf3; header cases
   FLAGS .. COMMENT with the header buffers' tokens: CaseHyps5.v, CaseKitT5.v) *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.CaseHyps5.
Require Import Zlib.proof.inflate.LnKit5 Zlib.proof.inflate.LnCase5 Zlib.proof.inflate.LnTab5
  Zlib.proof.inflate.LnFast5 Zlib.proof.inflate.LnLoop1_5 Zlib.proof.inflate.LnLoop2_5 Zlib.proof.inflate.LnTail5.
(* the cases LEN falls through into: copies of cases5_LD and cases5_DM *)
Require Import Zlib.proof.inflate.LnLD5 Zlib.proof.inflate.LnDM5.
#[local] Existing Instance Zlib.units.Inflate.CS.

(* case LEN (falls through into LENEXT) from its parts: LnKit5.v, LnCase5.v *)
Lemma cases5_LEN_next {Espec: OracleKind} (F: frame) : frame_ok5 F ->
  case_ok5 F LENEXT 21 -> case_ok5 F LEN 20.
Proof.
  intros FO HY. apply (ln_case F FO); auto.
  - exact ln_fast_ok.
  - exact (ln_loop1_ok ln_tab_ok).
  - exact (ln_loop2_ok ln_tab_ok).
  - exact ln_tail_ok.
Qed.

Lemma cases5_LEN {Espec: OracleKind} (F: frame) : frame_ok5 F -> 
  case_ok5 F LEN 20.
Proof.
  intros FO.
  destruct (ln_cases5_DM F FO) as [HDX HMT].
  destruct (ln_cases5_LD F FO) as [HLX HDS].
  apply (cases5_LEN_next F FO). apply HLX, HDS, HDX, HMT.
Qed.
