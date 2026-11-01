(* More machine-integer facts for the harness mains (constants in the forms VST leaves them). *)
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.adler32.Facts.

Lemma adler_lo_int2 a: 0 <= a <= Int64.max_unsigned ->
  Int64.and (Int64.repr a) (Int64.repr 65535) = Int64.repr (adler_lo a).
Proof. intros. rewrite <- adler_lo_int by auto. reflexivity. Qed.

Lemma adler_hi_int2 a: 0 <= a <= Int64.max_unsigned ->
  Int64.and (Int64.shru (Int64.repr a) (Int64.repr 16)) (Int64.repr 65535) = Int64.repr (adler_hi a).
Proof. intros. rewrite <- adler_hi_int by auto. reflexivity. Qed.
