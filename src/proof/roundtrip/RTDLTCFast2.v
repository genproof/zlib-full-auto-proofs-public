(** * Core part of the deflate law theory: deflate_fast, against the corrected specs of RTDLTCSpecs2.v.
    With RTDLTCSpecs2.tally_spec_2 / fpend_spec_2 it also holds under the original specifications of
    RTDLTCSpecs.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDLTCSpecs2.
Require Import Zlib.proof.roundtrip.RTDLTCFastGlue Zlib.proof.roundtrip.RTDLTCFastRefill Zlib.proof.roundtrip.RTDLTCFastSearch Zlib.proof.roundtrip.RTDLTCFastLit2 Zlib.proof.roundtrip.RTDLTCFastMatch2 Zlib.proof.roundtrip.RTDLTCFastInsLoop Zlib.proof.roundtrip.RTDLTCFastFbw Zlib.proof.roundtrip.RTDLTCFastBflush Zlib.proof.roundtrip.RTDLTCFastTail.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Theorem fast_ok2 : fill_spec -> ins_spec -> lm_spec -> tally_spec2 -> fbo_spec -> fpend_spec2 -> fast_spec.
Proof.
  intros Hfi Hin Hlm Hta Hfb _. apply fast_from_parts.
  - exact (refill_ok Hfi).
  - exact (search_ok Hin Hlm).
  - exact (lit_ok2 Hta).
  - exact (match_ok2 Hta (insloop_ok Hin)).
  - exact (bflush_ok (fbw_ok Hfb)).
  - exact (tail_ok (fbw_ok Hfb)).
Qed.
