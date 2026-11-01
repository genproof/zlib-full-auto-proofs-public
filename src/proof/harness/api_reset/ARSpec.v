(* Law api_reset: inflateReset as its main calls it.  The main calls inflateReset on a stream that went
   through SpecW.inflate_specW, so on a raw stream strm->adler may be undefined (zlib never writes it there):
   the stream is SpecW's istreamA.  inflateReset_specA is Spec5.inflateReset_spec on such a stream (a live one;
   with fix F8 inflateReset may free the window, hence mem_mgr); it is a view of the one specification of
   inflateReset (the allocator-generic one of the za port, USpec.inflateReset_uspec, at zlib's default allocator,
   as SpecWLib.v does for inflate()): ar_bridge_stmt states the subsumptions the law's assembly uses. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.inflate_api.SpecW.
Require Export Zlib.proof.inflate_api.SpecWLib.

#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Definition inflateReset_specA :=
  DECLARE _inflateReset
  WITH gv: globals, shs: share, strmp: val, z: zfields, av: val, L: live
  PRE [ tptr t_strm ]
    PROP (isptr strmp; fst3 (reset_f z L) = Z_OK -> live_ok (thd3 (reset_f z L)))
    PARAMS (strmp) GLOBALS (gv)
    SEP (istreamA gv shs strmp z av (Some L); mem_mgr gv; zfuncs gv)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (fst3 (reset_f z L))))
    SEP (istreamA gv shs strmp (snd3 (reset_f z L)) Vundef (Some (thd3 (reset_f z L))); mem_mgr gv; zfuncs gv).

(* inflateReset's uspec at zlib's default allocator gives the main's view and Spec5's specification (which
   inflateReset2's body calls) *)
Definition ar_bridge_stmt : Prop :=
  funspec_sub (snd (@inflateReset_uspec globals zc_alloc)) (snd inflateReset_specA) /\
  funspec_sub (snd (@inflateReset_uspec globals zc_alloc)) (snd inflateReset_spec).
