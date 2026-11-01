(* The switch case LEN of inflate() in the allocator-generic port, falling through into LENEXT: Cases5_LEN.v's cases5_LEN_next from the generated parts LnKit5 .. LnTail5 (patches in docs/port-za/inflate/cases_len.py); the cases LENEXT .. MATCH it falls into are CasesLdZ.v and CasesDmZ.v. *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.za.inflate.CaseHyps5.
Require Import Zlib.proof.zutil.ZAlloc.
Require Import Zlib.proof.za.inflate.ZAV.
Require Import Zlib.proof.za.inflate.LnKit5 Zlib.proof.za.inflate.LnCase5 Zlib.proof.za.inflate.LnTab5
  Zlib.proof.za.inflate.LnFast5 Zlib.proof.za.inflate.LnLoop1_5 Zlib.proof.za.inflate.LnLoop2_5
  Zlib.proof.za.inflate.LnTail5.
#[local] Existing Instance Zlib.units.Inflate.CS.

Section ZAlloc.
Context {ZA : zallocator} {ZAV : adler_cell}.

Lemma za_cases5_LEN_next {Espec: OracleKind} (F: frame) : frame_ok5 F ->
  case_ok5_za F LENEXT 21 -> case_ok5_za F LEN 20.
Proof.
  intros FO HY. apply (ln_case_za F FO); auto.
  - exact ln_fast_ok_za.
  - exact (ln_loop1_ok_za ln_tab_ok_za).
  - exact (ln_loop2_ok_za ln_tab_ok_za).
  - exact ln_tail_ok_za.
Qed.

End ZAlloc.
