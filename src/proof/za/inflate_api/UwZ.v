(* The body of updatewindow (inflate.c) with a caller-supplied allocator: ZALLOC of the window (2^wbits bytes,
   event uw_ev) through strm->zalloc.  Proved by the generated port src/proof/za/inflate/BodyUw5.v. *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.zutil.ZAlloc Zlib.proof.za.inflate.ZAV.
Require Import Zlib.proof.za.inflate_api.Stmt.
Require Zlib.proof.za.inflate.BodyUw5.
#[local] Existing Instance Zlib.units.Inflate.CS.

Section ZA.
Context {ZA : zallocator} {ZAV : adler_cell}.

Lemma za_uw_proof {Espec : OracleKind} :
  semax_body Vprog_inflate Gp_updatewindow_za f_updatewindow updatewindow_spec3_za.
Proof.
  exact Zlib.proof.za.inflate.BodyUw5.body_updatewindow5_za.
Qed.

End ZA.
