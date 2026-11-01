(* Law deflate_api: the body of deflate_run from its parts (RunKit.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.roundtrip.RTRCS Zlib.proof.roundtrip.RTRRunSpec
               Zlib.proof.roundtrip.RTRApiConv Zlib.proof.roundtrip.RTRRunKit.
Require Import Zlib.proof.roundtrip.RTRRunPrefix Zlib.proof.roundtrip.RTRRunInit
               Zlib.proof.roundtrip.RTRRunOpts Zlib.proof.roundtrip.RTRLoopPre
               Zlib.proof.roundtrip.RTRLoopCall Zlib.proof.roundtrip.RTRLoopCheck
               Zlib.proof.roundtrip.RTRLoopPost Zlib.proof.roundtrip.RTRRunMem.
Require Import Zlib.harness.x_deflate_roundtrip.code.
#[local] Existing Instance RTRCS.CS.
Local Open Scope logic.

Lemma body_deflate_run I Iend :
  semax_body (QPvarspecs p) Grun f_deflate_run (deflate_run_spec I Iend).
Proof.
  start_function.
  eapply semax_pre; [ | apply (run_prefix_ok I Iend Rp sp api v_osnap gv) ].
  { unfold PRE0. entailer!. }
  intros rs. apply run_init_ok. intros s tin tout adler ain aout msg msgv.
  apply run_opts_ok; [ simpl; auto | intros ls ].
  rewrite rsuf57_eq.
  eapply semax_seq with (Q := E_inv Iend Rp sp api v_osnap gv rs).
  - eapply semax_pre with (P' := J_inv I Iend Rp sp api v_osnap gv rs).
    { unfold J_inv. Exists ls. apply ENTAIL_refl. }
    apply semax_loop with (Q' := J_inv I Iend Rp sp api v_osnap gv rs).
    + unfold J_inv at 1. Intros ls'.
      apply loop_pre_ok; [ exact run_mem | intros ci ].
      apply loop_call_ok. intros s' z' code msgv'.
      apply loop_check_ok. apply loop_post_ok.
    + forward. apply ENTAIL_refl.
  - unfold E_inv. Intros rf. unfold E_at.
    apply semax_extract_prop; intros Hrs. unfold drun_rest, rsuf58. Intros.
    forward. forward.
    Exists 1. unfold run_post. simpl. Exists 0. simpl. Exists rf.
    unfold run_ok_at, drun_rest. entailer!. unfold hdr_at, hx_of. cancel.
Qed.
