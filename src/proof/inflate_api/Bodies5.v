(* Version 5 (Spec5.v, Callees5.v, Model2.v; inflate.c's global variables explicitly: Vprog_inflate). The body obligations of inflate.c's API functions, each with the context of its callees,
   at the compspecs of the inflate unit.  Proved in src/proof/inflate_api/Body_*.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.inflate_api.Spec5.
Require Zlib.proof.zutil.Spec Zlib.proof.zutil.Libc Zlib.proof.adler32.Spec.

#[local] Existing Instance Zlib.units.Inflate.CS.

Definition zcalloc_i := (_zcalloc, snd (@Zlib.proof.zutil.Spec.zcalloc_spec Zlib.units.Inflate.CS)).
Definition zcfree_i := (_zcfree, snd (@Zlib.proof.zutil.Spec.zcfree_spec Zlib.units.Inflate.CS)).
Definition memcpy_i := (_memcpy, snd (@Zlib.proof.zutil.Libc.memcpy_spec Zlib.units.Inflate.CS)).
Definition memset_i := (_memset, snd (@Zlib.proof.zutil.Libc.memset_spec Zlib.units.Inflate.CS)).

Definition Gp_init2 : funspecs := [inflateReset2_spec; zcalloc_i; zcfree_i; memset_i].
Definition Gp_init : funspecs := [inflateInit2__spec].
Definition Gp_resetkeep : funspecs := [inflateStateCheck_spec].
Definition Gp_reset : funspecs := [inflateStateCheck_spec; inflateResetKeep_spec; zcfree_i].
Definition Gp_reset2 : funspecs := [inflateStateCheck_spec; inflateReset_spec; zcfree_i].
Definition Gp_end : funspecs := [inflateStateCheck_spec; zcfree_i].
Definition Gp_getdict : funspecs := [inflateStateCheck_spec; memcpy_i].
Definition Gp_setdict : funspecs := [inflateStateCheck_spec; Zlib.proof.adler32.Spec.adler32_spec; updatewindow_spec3].
Definition Gp_check : funspecs := [inflateStateCheck_spec].
Definition Gp_sync : funspecs := [inflateStateCheck_spec; syncsearch_spec; inflateReset_spec].

Definition body_inflate_stmt : Prop :=
  forall {Espec: OracleKind}, semax_body Vprog_inflate Gprog_inflate3 f_inflate inflate_spec.

(* one pass of the switch keeps the header pointer facts *)
Definition stepf2_hd_stmt : Prop :=
  forall F flush m, hd_ok F m ->
  match stepf2 flush lenfix_list distfix_list m with IBrk m' => hd_ok F m' | IRet _ m' => hd_ok F m' end.

(* inflate()'s body from the case lemmas (CaseHyps5.v, in Delta_cases5: move them to Delta_inflate5 with
   Callees5.semax_cases_inflate5) and the loop invariants' preservation *)
Definition body_inflate_from_cases5 : Prop :=
  cases_all5 -> stepf2_mwf3_stmt -> stepf2_hd_stmt -> body_inflate_stmt.

Definition api_init_stmt : Prop :=
  forall {Espec: OracleKind},
  semax_body Vprog_inflate Gp_init2 f_inflateInit2_ inflateInit2__spec /\
  semax_body Vprog_inflate Gp_init f_inflateInit_ inflateInit__spec.

(* a live stream's reset is live (the clients of inflateReset need its precondition) *)
Definition live_reset_stmt : Prop :=
  forall z L, live_ok L -> live_ok (thd3 (reset_f z L)).

Definition api_reset_stmt : Prop :=
  live_reset_stmt /\
  forall {Espec: OracleKind},
  semax_body Vprog_inflate Gp_resetkeep f_inflateResetKeep inflateResetKeep_spec /\
  semax_body Vprog_inflate Gp_reset f_inflateReset inflateReset_spec /\
  semax_body Vprog_inflate Gp_reset2 f_inflateReset2 inflateReset2_spec /\
  semax_body Vprog_inflate Gp_end f_inflateEnd inflateEnd_spec.

Definition api_dict_stmt : Prop :=
  forall {Espec: OracleKind},
  semax_body Vprog_inflate Gp_getdict f_inflateGetDictionary inflateGetDictionary_spec /\
  semax_body Vprog_inflate Gp_setdict f_inflateSetDictionary inflateSetDictionary_spec.

Definition api_misc_stmt : Prop :=
  forall {Espec: OracleKind},
  semax_body Vprog_inflate Gp_check f_inflateGetHeader inflateGetHeader_spec /\
  semax_body Vprog_inflate Gp_check f_inflatePrime inflatePrime_spec /\
  semax_body Vprog_inflate Gp_check f_inflateValidate inflateValidate_spec /\
  semax_body Vprog_inflate Gp_check f_inflateMark inflateMark_spec /\
  semax_body Vprog_inflate Gp_check f_inflateCodesUsed inflateCodesUsed_spec /\
  semax_body Vprog_inflate Gp_check f_inflateSyncPoint inflateSyncPoint_spec.

Definition api_sync_stmt : Prop :=
  forall {Espec: OracleKind},
  semax_body Vprog_inflate [] f_syncsearch syncsearch_spec /\
  semax_body Vprog_inflate Gp_sync f_inflateSync inflateSync_spec.
