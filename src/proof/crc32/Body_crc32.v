(* The bodies of crc32 (crc32_z with the length widened) and get_crc_table. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.crc32.code.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Crc32.CS.

Lemma body_crc32: semax_body Vprog Gprog_crc32 f_crc32 crc32_spec.
Proof.
  start_function.
  forward_call (crc, buf, len, isnull, sh, p, lo, n, contents, data, tok, vsh, gv, tsh).
  forward.
Qed.

Lemma body_get_crc_table: semax_body Vprog Gprog_get_crc_table f_get_crc_table get_crc_table_spec.
Proof.
  start_function. unfold crc_table_at. forward.
Qed.
