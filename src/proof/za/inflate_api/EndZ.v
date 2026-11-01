(* The body of inflateEnd with a caller-supplied allocator: ZFREE of the window (when allocated), then of the
   state (events end_ev).  Proved by the generated port src/proof/za/inflate_api/Body5_end.v. *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.zutil.ZAlloc Zlib.proof.za.inflate.ZAV.
Require Import Zlib.proof.za.inflate_api.Stmt.
Require Zlib.proof.za.inflate_api.Body5_end.
#[local] Existing Instance Zlib.units.Inflate.CS.

Section ZA.
Context {ZA : zallocator} {ZAV : adler_cell}.

Lemma za_end_proof {Espec : OracleKind} :
  semax_body Vprog_inflate Gp_end_za f_inflateEnd inflateEnd_spec_za.
Proof.
  exact Zlib.proof.za.inflate_api.Body5_end.body5_inflateEnd_za.
Qed.

End ZA.
