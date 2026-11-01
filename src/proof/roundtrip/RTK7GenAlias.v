(* A second name for the loop invariant of the first phase of deflate_stored (RTDLTCStoredLoop.linv), used by the
   wide port of the round-trip theory (docs/port-wide/cfg_rtd.py): the generator scopes names by the modules a
   module requires, and cannot tell this invariant, which needs no port, from RTDLTCLiveKit.linv, which does. *)
Require Zlib.proof.roundtrip.RTDLTCStoredLoop.

Notation ds_linv := Zlib.proof.roundtrip.RTDLTCStoredLoop.linv.
