(* Round-trip laws, part RT-H: inflate()'s and inflateGetHeader's bodies against the
   specifications for a gz_header with undefined fields (RTHSpec.v).
   Parts: RTHGetHeader (inflateGetHeader), RTHBody6 (inflate's assembly), RTHPro6 (prologue), the header
   cases RTHCaseHEAD6, RTHCasesFTO6, RTHCasesEX6, RTHCasesNC6, RTHCaseHCRC6 (interface RTHCase.v), over the
   headless kit RTH<orig>.v (mechanical ports of the inflate area's case kit). *)
Require Import VST.floyd.proofauto.
Require Zlib.proof.inflate_api.LibStmt5.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTHCase.
Require Zlib.proof.roundtrip.RTHGetHeader Zlib.proof.roundtrip.RTHBody6 Zlib.proof.roundtrip.RTHPro6.
Require Zlib.proof.roundtrip.RTHCaseHEAD6 Zlib.proof.roundtrip.RTHCasesFTO6 Zlib.proof.roundtrip.RTHCasesEX6.
Require Zlib.proof.roundtrip.RTHCasesNC6 Zlib.proof.roundtrip.RTHCaseHCRC6.

Theorem rt_head6 : Zlib.proof.inflate_api.LibStmt5.inflate_lib5_stmt -> rt_head6_stmt.
Proof.
  intros _ Espec. split.
  - exact (@Zlib.proof.roundtrip.RTHGetHeader.rth_getheader Espec).
  - exact (@Zlib.proof.roundtrip.RTHBody6.rth_body6
             (cases6_all_proof Zlib.proof.roundtrip.RTHCaseHEAD6.rth_head Zlib.proof.roundtrip.RTHCasesFTO6.rth_fto
                Zlib.proof.roundtrip.RTHCasesEX6.rth_ex Zlib.proof.roundtrip.RTHCasesNC6.rth_nc
                Zlib.proof.roundtrip.RTHCaseHCRC6.rth_hcrc)
             Zlib.proof.roundtrip.RTHPro6.pro_part6 Espec).
Qed.
