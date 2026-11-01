(* inflate()'s body against RTH9Spec.inflate_spec9 (a gz_header whose absent fields stay undefined, buffers of any
   uInt size, avail_in / avail_out any uInt, the header over several calls), with some specification of
   inflate_fast proved of its body, and inflateGetHeader's body against RTH8Spec.inflateGetHeader_spec8.
   The parts: RTH9Fast.v (inflate_fast's specification, its body, the headless switch cases after the header),
   RTH9Hdr.v (the header cases), RTH9Exit.v and RTH9Pro.v (the exit and the prologue), RTH9Asm.v (the body from
   them); inflateGetHeader's body is round 1's RTH8GetHdr.rth8_gethdr. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.roundtrip.RTH9Spec.
Require Import Zlib.proof.roundtrip.RTH9Defs.
Require Zlib.proof.roundtrip.RTH9Fast.
Require Zlib.proof.roundtrip.RTH9Hdr.
Require Zlib.proof.roundtrip.RTH9Exit.
Require Zlib.proof.roundtrip.RTH9Pro.
Require Zlib.proof.roundtrip.RTH9Asm.
Require Zlib.proof.roundtrip.RTH8GetHdr.

Theorem rth9_body : inflate_body9_stmt.
Proof.
  destruct Zlib.proof.roundtrip.RTH9Fast.rth9_fast as (fast & CC & FB & FS & NH).
  exists fast. split; [exact CC | split; [exact FB | split]].
  - intros Espec.
    exact (@Zlib.proof.roundtrip.RTH9Asm.body9_of fast FS NH Zlib.proof.roundtrip.RTH9Hdr.cases9h_proof
             Zlib.proof.roundtrip.RTH9Exit.exit_part9 Zlib.proof.roundtrip.RTH9Pro.pro_part9 Espec).
  - exact Zlib.proof.roundtrip.RTH8GetHdr.rth8_gethdr.
Qed.
