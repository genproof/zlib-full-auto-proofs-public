(* Law x_inflate_decode (harness/x_inflate_decode.c), from the inflate area's library bodies (LibStmt5.v). *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require Zlib.contracts.x_inflate_decode.
Require Import Zlib.proof.inflate_api.LibStmt5.
Require Import Zlib.proof.rfc1951.Decode.
Require Zlib.proof.rfc1951.DecKit Zlib.proof.rfc1951.TabDec Zlib.proof.rfc1951.DecMwf Zlib.proof.rfc1951.DecHdr
        Zlib.proof.rfc1951.DecType Zlib.proof.rfc1951.DecTab Zlib.proof.rfc1951.DecDec Zlib.proof.rfc1951.DecFast
        Zlib.proof.rfc1951.DecTrl Zlib.proof.rfc1951.DecCall.
Require Zlib.proof.harness.inflate_common.DRefBw Zlib.proof.harness.inflate_common.DRefCodes
        Zlib.proof.harness.inflate_common.DRefCanon Zlib.proof.harness.inflate_common.DRefDyn.
Require Zlib.proof.harness.inflate_decode.IDLawAsm.

(* the decode theory from its parts (Decode.decode_of_parts) *)
Lemma id_decode : decode_init_stmt /\ decode_call_stmt.
Proof.
  apply decode_of_parts.
  exact (conj Zlib.proof.rfc1951.DecKit.dkit (conj Zlib.proof.rfc1951.TabDec.tabdec
        (conj Zlib.proof.rfc1951.DecMwf.dm_stepf2_mwf3
        (conj (proj1 Zlib.proof.rfc1951.DecHdr.dec_hdr_part) (conj (proj2 Zlib.proof.rfc1951.DecHdr.dec_hdr_part)
        (conj Zlib.proof.rfc1951.DecType.group_type (conj Zlib.proof.rfc1951.DecTab.group_tab
        (conj Zlib.proof.rfc1951.DecDec.group_dec (conj Zlib.proof.rfc1951.DecFast.dfast
        (conj Zlib.proof.rfc1951.DecTrl.group_trl Zlib.proof.rfc1951.DecCall.dec_call)))))))))).
Qed.

Lemma law5_inflate_decode : inflate_lib5_stmt -> harness_safe Zlib.contracts.x_inflate_decode.whole_prog.
Proof.
  intros H. destruct id_decode as [DI DC].
  exact (Zlib.proof.harness.inflate_decode.IDLawAsm.id_core H
           Zlib.proof.harness.inflate_common.DRefBw.dref_bw_bodies_proof
           Zlib.proof.harness.inflate_common.DRefCodes.dref_code_bodies_proof
           Zlib.proof.harness.inflate_common.DRefCanon.dref_canon_bodies_proof
           Zlib.proof.harness.inflate_common.DRefDyn.dref_dyn_body_proof DI DC).
Qed.
