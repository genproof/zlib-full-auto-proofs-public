(* The bodies of inflateResetKeep, inflateReset and inflateReset2 with a caller-supplied allocator (inflateReset2
   gives the window back when its size changes: events reset2_ev).  Proved by the generated port
   src/proof/za/inflate_api/Body5_reset.v. *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.zutil.ZAlloc Zlib.proof.za.inflate.ZAV.
Require Import Zlib.proof.za.inflate_api.Stmt.
Require Zlib.proof.za.inflate_api.Body5_reset.
#[local] Existing Instance Zlib.units.Inflate.CS.

Section ZA.
Context {ZA : zallocator} {ZAV : adler_cell}.

Lemma za_reset_proof {Espec : OracleKind} :
  semax_body Vprog_inflate Gp_resetkeep_za f_inflateResetKeep inflateResetKeep_spec_za /\
  semax_body Vprog_inflate Gp_reset_za f_inflateReset inflateReset_spec_za /\
  semax_body Vprog_inflate Gp_reset2_za f_inflateReset2 inflateReset2_spec_za.
Proof.
  split; [exact Zlib.proof.za.inflate_api.Body5_reset.body_inflateResetKeep_za |].
  split; [exact Zlib.proof.za.inflate_api.Body5_reset.body_inflateReset_za |].
  exact Zlib.proof.za.inflate_api.Body5_reset.body_inflateReset2_za.
Qed.

End ZA.
