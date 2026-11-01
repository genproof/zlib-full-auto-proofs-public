(* The body of inflateInit2_ with a caller-supplied allocator: ZALLOC of the state, ZFREE of it when
   inflateReset2 rejects windowBits (events init_ev).  Proved by the generated port
   src/proof/za/inflate_api/Body5_init.v. *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.zutil.ZAlloc Zlib.proof.za.inflate.ZAV.
Require Import Zlib.proof.za.inflate_api.Stmt.
Require Zlib.proof.za.inflate_api.Body5_init.
#[local] Existing Instance Zlib.units.Inflate.CS.

Section ZA.
Context {ZA : zallocator} {ZAV : adler_cell}.

Lemma za_init_proof {Espec : OracleKind} :
  semax_body Vprog_inflate Gp_init2_za f_inflateInit2_ inflateInit2__spec_za.
Proof.
  exact Zlib.proof.za.inflate_api.Body5_init.body_inflateInit2__za.
Qed.

End ZA.
