(* Law inflate_dict: the decode theory's call theorem (rfc1951/Decode.v decode_call_stmt) under DecodeDefs v4
   (dctx_ok allows the zlib FDICT dictionary id; chk_ok: the output starts with the history), from the parts of
   the decode theory (rfc1951/Dec*.v, TabDec.v) ported to v4: decode_of_parts. *)
Require Import Zlib.proof.rfc1951.Decode.
Require Zlib.proof.rfc1951.DecKit Zlib.proof.rfc1951.TabDec Zlib.proof.rfc1951.DecMwf Zlib.proof.rfc1951.DecHdr
        Zlib.proof.rfc1951.DecType Zlib.proof.rfc1951.DecTab Zlib.proof.rfc1951.DecDec Zlib.proof.rfc1951.DecFast
        Zlib.proof.rfc1951.DecTrl Zlib.proof.rfc1951.DecCall.

Lemma it_decode_call_v4 : decode_call_stmt.
Proof.
  exact (proj2 (decode_of_parts
    (conj Zlib.proof.rfc1951.DecKit.dkit (conj Zlib.proof.rfc1951.TabDec.tabdec
    (conj Zlib.proof.rfc1951.DecMwf.dm_stepf2_mwf3
    (conj (proj1 Zlib.proof.rfc1951.DecHdr.dec_hdr_part) (conj (proj2 Zlib.proof.rfc1951.DecHdr.dec_hdr_part)
    (conj Zlib.proof.rfc1951.DecType.group_type (conj Zlib.proof.rfc1951.DecTab.group_tab
    (conj Zlib.proof.rfc1951.DecDec.group_dec (conj Zlib.proof.rfc1951.DecFast.dfast
    (conj Zlib.proof.rfc1951.DecTrl.group_trl Zlib.proof.rfc1951.DecCall.dec_call)))))))))))).
Qed.
