(* RT-I: the generalized decode theory (RTIGDefs.v) from its parts (copies RTIGDec*.v of rfc1951's
   proofs); the code tables (tabdec_stmt) and the machine's well-formedness (stepf2_mwf3_stmt) are rfc1951's
   statements, unchanged, taken from Decode.decode_parts. *)
Require Import Zlib.proof.roundtrip.RTIGDefs.
Require Zlib.proof.roundtrip.RTIGDecKit Zlib.proof.roundtrip.RTIGDecType Zlib.proof.roundtrip.RTIGDecTab Zlib.proof.roundtrip.RTIGDecDec Zlib.proof.roundtrip.RTIGDecFast Zlib.proof.roundtrip.RTIGDecTrl Zlib.proof.roundtrip.RTIGDecCall.

Lemma rtig_parts_ok : rtig_parts.
Proof.
  exact (conj Zlib.proof.roundtrip.RTIGDecKit.dkit (conj Zlib.proof.roundtrip.RTIGDecType.group_type
    (conj Zlib.proof.roundtrip.RTIGDecTab.group_tab (conj Zlib.proof.roundtrip.RTIGDecDec.group_dec
    (conj Zlib.proof.roundtrip.RTIGDecFast.dfast (conj Zlib.proof.roundtrip.RTIGDecTrl.group_trl
     Zlib.proof.roundtrip.RTIGDecCall.rtig_loop)))))).
Qed.

Lemma rtig_loop_ok : Zlib.proof.rfc1951.Decode.decode_parts -> rtig_loop_stmt.
Proof.
  intros (_ & T & S & _). exact (rtig_of_parts rtig_parts_ok T S).
Qed.
