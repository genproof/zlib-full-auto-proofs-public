(* The body of inflateSetDictionary with a caller-supplied allocator (the window allocated by updatewindow
   when the dictionary is taken and there is none, or its failed allocation: events dict_ev).  Proved by the generated port
   src/proof/za/inflate_api/Body5_dict.v. *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.zutil.ZAlloc Zlib.proof.za.inflate.ZAV.
Require Import Zlib.proof.za.inflate_api.Stmt.
Require Zlib.proof.za.inflate_api.Body5_dict.
#[local] Existing Instance Zlib.units.Inflate.CS.

Section ZA.
Context {ZA : zallocator} {ZAV : adler_cell}.

Lemma za_dict_proof {Espec : OracleKind} :
  semax_body Vprog_inflate Gp_setdict_za f_inflateSetDictionary inflateSetDictionary_spec_za.
Proof.
  exact Zlib.proof.za.inflate_api.Body5_dict.body_setdict_za.
Qed.

End ZA.
