(* The mains of harness/rj_any_input.c, api_counters.c and api_untouched_output.c, each proved against
   MainLib.main_core_spec R (Globals.v) for ANY invariant P with the facts of Facts.v (pieces_facts P) and
   Progress.v (pieces_progress P), calling
   inflate.c's API through its shared specifications (inflateInit2_: Spec5.v; inflate, inflateSetDictionary:
   the wide SpecW.v; at the inflate unit's compspecs, moved to each law's with LawCS's instances) and the
   helpers of harness/laws_common.h and laws_session.h through theirs (laws_common/Spec.v,
   laws_session/Spec.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5 Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.inflate_pieces.LawCS.
Require Import Zlib.proof.harness.inflate_pieces.Globals.
Require Import Zlib.proof.harness.inflate_pieces.Facts.
Require Import Zlib.proof.harness.inflate_pieces.Progress.
Require Import Zlib.proof.harness.inflate_pieces.MainSession.
Require Zlib.harness.rj_any_input.code Zlib.harness.api_counters.code Zlib.harness.api_untouched_output.code.
Require Zlib.proof.harness.inflate_pieces.MainAny.
Require Zlib.proof.harness.inflate_pieces.MainCnt.
Require Zlib.proof.harness.inflate_pieces.MainUnt.

(* the specifications main calls (the same in the three programs, but laws_session.h's helpers and gp_assume:
   rj_any_input and api_untouched_output only; bytes_eq and accounted: api_untouched_output only) *)
Definition Gmain_of {cs: compspecs} (extra: funspecs) : funspecs :=
  [inflateInit2__spec; inflate_specW; inflateSetDictionary_specW; zcalloc_i; zcfree_i;
   upto_spec; clip_spec; any_bytes_spec; copy_of_spec; offer_spec; new_stream_spec] ++ extra ++
  [(_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec');
   nondet_u32_spec; nondet_u8_spec; gp_assert_spec].

Definition Gmain_any := @Gmain_of Any.CS Gk_extra_any.
Definition Gmain_cnt := @Gmain_of Cnt.CS [].
Definition Gmain_unt := @Gmain_of Unt.CS Gk_extra_unt.

Lemma pieces_mains : forall P, pieces_facts P -> pieces_progress P ->
  @semax_body (QPvarspecs Any.p) Gmain_any Any.CS Zlib.harness.rj_any_input.code.f_main
    (Zlib.harness.rj_any_input.code._main, main_core_spec R_any) /\
  @semax_body (QPvarspecs Cnt.p) Gmain_cnt Cnt.CS Zlib.harness.api_counters.code.f_main
    (Zlib.harness.api_counters.code._main, main_core_spec R_cnt) /\
  @semax_body (QPvarspecs Unt.p) Gmain_unt Unt.CS Zlib.harness.api_untouched_output.code.f_main
    (Zlib.harness.api_untouched_output.code._main, main_core_spec R_unt).
Proof.
  intros P PF PG. split; [ | split ].
  - exact (Zlib.proof.harness.inflate_pieces.MainAny.body_any P PF PG).
  - exact (Zlib.proof.harness.inflate_pieces.MainCnt.body_cnt P PF).
  - exact (Zlib.proof.harness.inflate_pieces.MainUnt.body_unt P PF PG).
Qed.
