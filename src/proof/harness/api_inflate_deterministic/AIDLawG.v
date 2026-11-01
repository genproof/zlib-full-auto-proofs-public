(* Law api_inflate_deterministic: the context of the assembly (AIDLawAsm.v) of harness_safe.  The program has
   api_reset's shape: main calls inflateInit2_ and inflate through the shared specifications, and inflateInit2_'s
   body reaches inflateReset2, inflateReset and inflateResetKeep, so inflate.c's part of the context is api_reset's
   (ARLawG.G_inflate: inflateReset and inflateResetKeep at their allocator-generic specifications of the za port
   at zlib's default allocator).  Spec5's inflateReset_spec, which inflateReset2's body calls, follows from the
   former by ARBridge.ar_reset_sub5. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.SpecWLib.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.laws_session.Spec.
Require Import Zlib.proof.harness.api_inflate_deterministic.AIDMainDefs.
Require Zlib.proof.harness.api_reset.ARLawG.
Require Zlib.proof.harness.api_reset.ARBridge.
Require Zlib.harness.api_inflate_deterministic.code.

Definition G : funspecs :=
  [(Zlib.harness.api_inflate_deterministic.code._main, QPmain_spec_ext' p tt main_post_TT);
   upto_spec; clip_spec; any_bytes_spec; copy_of_spec; bytes_eq_spec; offer_spec; new_stream_spec;
   Zlib.proof.harness.laws_session.Spec.inflate_window_ok_spec] ++
  Zlib.proof.harness.api_reset.ARLawG.G_inflate ++
  [(_quickproof_malloc, @malloc_spec' CS); (_quickproof_free, @free_spec' CS);
   nondet_size_spec; @nondet_bytes_spec CS; nondet_u8_spec; nondet_u32_spec; gp_assert_spec; gp_assume_spec].

(* ctx_sub with, besides the environment's transports, SpecWLib's bridges (BR) and Spec5's inflateReset_spec *)
Ltac aid_spec_sub BR :=
  first [ env_spec_sub
        | apply (proj1 BR) | apply (proj1 (proj2 BR)) | apply (proj2 (proj2 BR))
        | apply Zlib.proof.harness.api_reset.ARBridge.ar_reset_sub5 ].

Ltac aid_ctx_sub BR :=
  let i := fresh "i" in let phi := fresh "phi" in let E := fresh "E" in
  intros i phi E; simpl in E;
  repeat (if_tac in E; [ inv E; eexists; split; [ reflexivity | aid_spec_sub BR ] | ]);
  try discriminate.

Ltac aid_entry B BR :=
  lazymatch type of B with
  | @semax_body _ _ ?cs1 ?f ?spec =>
    apply Forall_cons;
    [ eapply (entry_moved _ _ cs1 _ _ _ _ (fst spec) (snd spec) f B);
      [ reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | find_ids_V | vm_compute; reflexivity | vm_compute; reflexivity | aid_ctx_sub BR ]
    | ]
  end.
