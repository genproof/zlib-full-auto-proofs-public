(* inflate()'s body against RTH9Spec.inflate_spec9 from its parts: the headless switch cases of the modes after the
   header and their inflate_fast specification (RTH9Defs.cases_nh9), the header cases (RTH9HDefs.cases9h_all), the
   exit and the prologue for calls of any uInt size (RTH9Parts). *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTH9HDefs.
#[local] Existing Instance Zlib.units.Inflate.CS.

Definition body9_of_stmt : Prop :=
  forall fast : funspec,
    funspec_sub fast (snd inflate_fast_spec3_hl) -> cases_nh9 fast ->
    cases9h_all -> exit_part9_stmt -> pro_part9_stmt ->
    forall {Espec: OracleKind}, semax_body Vprog_inflate (Gprog_inflate8 fast) f_inflate inflate_spec9.

(* the parts: RTH9AKit.v (their statements, the contexts, the wide machine facts), RTH9AHdrInv.v (a pass from a
   header mode), RTH9ALoop.v (the main loop), RTH9AExit.v (the exit), RTH9ABody.v (the body from them) *)
Require Zlib.proof.roundtrip.RTH9AKit.
Require Zlib.proof.roundtrip.RTH9AHdrInv.
Require Zlib.proof.roundtrip.RTH9ALoop.
Require Zlib.proof.roundtrip.RTH9AExit.
Require Zlib.proof.roundtrip.RTH9ABody.

Lemma body9_of : body9_of_stmt.
Proof.
  intros fast FS NH HC XT PRO Espec.
  exact (@Zlib.proof.roundtrip.RTH9ABody.body9_from fast FS PRO
           (Zlib.proof.roundtrip.RTH9ALoop.loop9 fast FS NH HC Zlib.proof.roundtrip.RTH9AHdrInv.hdr9_inv)
           (Zlib.proof.roundtrip.RTH9AExit.exit9 XT) Espec).
Qed.
