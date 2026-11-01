(* What a law that calls inflate() and inflateSetDictionary through the wide specifications of SpecW.v needs
   of inflate.c: THE Prop `specw_lib_stmt`, for zlib's default allocator (strm->zalloc = zfree = Z_NULL
   before inflateInit2_, which installs zcalloc / zcfree).

   The bodies come from the allocator-generic port of inflate's proofs (src/proof/za/inflate_api/USpec.v:
   one specification per function, `uspec`, a general_intersection over the allocator and the adler cell) at
   the zcalloc allocator `zc_alloc gv`; the bridge lemmas say that these specifications give SpecW's
   inflate_specW and inflateSetDictionary_specW, and Spec5's inflateStateCheck_spec (which the bodies of
   inflateInit2_ and the reset functions of LibStmt5.v call: inflateInit2_ with strm->zalloc = Z_NULL is
   Spec5's, the port's inflateInit2_ keeps a caller's allocator).

   A law's context then lists, for inflate.c: inflate_uspec, inflate_fast_uspec, updatewindow_uspec,
   inflateStateCheck_uspec, inflateSetDictionary_uspec (at zc_alloc; bodies from za_inflate_ulib_stmt) and
   Spec5's inflateInit2__spec, inflateReset2_spec, inflateReset_spec, inflateResetKeep_spec (bodies from
   LibStmt5.inflate_lib5_stmt), and moves main's callee specifications (SpecW's) to them by the bridge. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.inflate_api.SpecW.
Require Export Zlib.proof.za.inflate_api.USpec.
#[local] Existing Instance Zlib.units.Inflate.CS.

(* zlib's default allocator as a zallocator: zcalloc / zcfree with opaque Z_NULL, malloc's resource and
   tokens; it accounts any number of bytes up to 2^64-1 *)
Definition zc_alloc (gv: globals) : zallocator :=
  ZAllocator (gv _zcalloc) (gv _zcfree) nullval (fun g _ => mem_mgr g)
    (fun cs t p => @malloc_token cs Ews t p) Int64.max_unsigned.

(* the port's specifications at zc_alloc give the wide ones and Spec5's inflateStateCheck_spec *)
Definition specw_bridge_stmt : Prop :=
  funspec_sub (snd (@inflate_uspec globals zc_alloc)) (snd inflate_specW) /\
  funspec_sub (snd (@inflateSetDictionary_uspec globals zc_alloc)) (snd inflateSetDictionary_specW) /\
  funspec_sub (snd (@inflateStateCheck_uspec globals zc_alloc)) (snd inflateStateCheck_spec).

(* the bodies of inflate.c against the port's specifications at zc_alloc, and the bridge *)
Definition specw_lib_stmt : Prop :=
  @za_inflate_ulib_stmt globals zc_alloc /\ specw_bridge_stmt.
