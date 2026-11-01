(* SpecWLib.specw_lib_stmt: the bodies of inflate.c at zlib's default allocator, from the allocator-generic port
   of inflate's proofs (ULib.za_ulib with its parts: the switch cases, inflate_fast, inflate()'s body, the API
   functions, the wide machine invariant), and the bridge to SpecW's specifications (SpecWBridge). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.inflate_api.SpecWLib.
Require Import Zlib.proof.inflate_api.SpecWBridge.
Require Import Zlib.proof.za.inflate_api.ULib.
Require Import Zlib.proof.za.inflate.CasesAllZ.
Require Import Zlib.proof.za.inffast.FastZ.
Require Import Zlib.proof.za.inflate_api.BodyZ.
Require Import Zlib.proof.za.inflate_api.ApiZ.
Require Import Zlib.proof.za.inflate.StepZ.
Require Import Zlib.proof.inflate.StepW.

Lemma specw_lib : specw_lib_stmt.
Proof.
  split; [ | exact specw_bridge ].
  destruct (za_ulib _ zc_alloc) as [_ Hlib].
  apply Hlib.
  - exact za_cases_proof.
  - exact za_body_inflate_proof.
  - exact (za_step_proof stepf2_mwf3W).
  - exact za_fast_proof.
  - exact za_api_proof.
Qed.
