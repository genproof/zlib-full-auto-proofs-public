(* The round trips without the limits of deflate_roundtrip: deflateInit2 starts K7 (RTK7Defs.v). *)
Require Import Zlib.proof.roundtrip.RTK7Defs.
Require Zlib.proof.huffman.Lemmas Zlib.proof.roundtrip.RTDPM3 Zlib.proof.roundtrip.RTK7Conv.

(* deflateInit2 starts Krt3 (RTDPM3.rtd_pm3_ok); a fresh stream has no data and no dictionary, so it is in K7 *)
Theorem rtk7_init_ok : kf7_init_stmt K7.
Proof.
  intros level method wbits mem strategy a1 a2 a3 a4 a5 z s z' H1 H2 H3 H4 H5 E.
  destruct (proj1 (proj2 (Zlib.proof.roundtrip.RTDPM3.rtd_pm3_ok
              (proj1 Zlib.proof.huffman.Lemmas.huffman_lemmas)))
              level method wbits mem strategy a1 a2 a3 a4 a5 z s z' H1 H2 H3 H4 H5 E) as (Hwb & Hgz & HK).
  split; [exact Hwb|]. split; [exact Hgz|].
  apply Zlib.proof.roundtrip.RTK7Conv.Krt3_K7; [exact HK|reflexivity].
Qed.
