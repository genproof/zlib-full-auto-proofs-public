(* inflate(), case EXTRA (index 5) in Delta_cases5: with FEXTRA, copy = min(length, have) input bytes, the part
   that fits into head->extra (below extra_max) copied there (zmemcpy), crc32 over the bytes (when the header
   CRC is on), length -= copy; leave while length is not 0; then length = 0, mode = NAME, falls into NAME *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.ExKit5.
Require Import Zlib.proof.inflate.ExtraBody5.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Lemma case_EXTRA5 {Espec: OracleKind} (F: frame) : frame_ok5 F -> case_okT5 F NAME 6 -> case_okT5 F EXTRA 5.
Proof.
  intros FOK HY m HM HL W HD.
  apply (case_fallthroughT5 F m NAME 5); [lia | exact HY | ].
  apply extra_body5; auto.
Qed.
