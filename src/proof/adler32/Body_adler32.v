(* The body of adler32: adler32_z with the length widened. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.adler32.code.
Require Import Zlib.proof.adler32.Spec.
#[local] Existing Instance Zlib.units.Adler32.CS.

Lemma body_adler32: semax_body Vprog Gprog_adler32 f_adler32 adler32_spec.
Proof.
  start_function.
  forward_call (adler, buf, len, isnull, sh, p, lo, n, contents, data, tok, vsh).
  forward.
Qed.
