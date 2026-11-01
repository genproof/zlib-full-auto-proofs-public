(* Law res_memory_deflate: main of harness/res_memory_deflate.c against main_core_spec (Ra lit) at the law's
   compspecs CSa, with the callees of Gmain_mem (src/proof/harness/res_alloc_deflate/).

   main draws the parameters (assumed in zlib.h's ranges: deflate_params_ok) and the data, makes the stream count
   through the harness's counting allocator (counted_stream), calls deflateInit2_ (it returns Z_OK, or Z_MEM_ERROR
   after a failed allocation, which ends the run), then loops over deflate() calls on pieces of the data, each with a fresh
   output space and any flush.  The allocator's events stay deflateInit2_'s five allocations [dinit_events s]
   (deflate() allocates nothing: its specification does not touch the allocator's state), so count.peak is
   their sum after every call, exactly the harness's bound (Peak.v, PeakExact.v); every call is defined by the invariant of
   deflate/AnyCalls.v.  The parts (MemKit.v): the prefix up to the loop (MemPrefix.v), the loop body up to
   set_buffer (MemBodyPre.v) and from deflate() on (MemBodyCall.v); here the loop, its test and return 0. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.za.deflate.Stmt.
Require Import Zlib.proof.deflate.AnyCalls.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.counted.Spec.
Require Import Zlib.proof.harness.counted.Kit.
Require Import Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.res_alloc_deflate.ACS.
Require Import Zlib.proof.harness.res_alloc_deflate.Specs.
Require Import Zlib.proof.harness.res_alloc_deflate.Gmain.
Require Import Zlib.proof.harness.res_alloc_deflate.InitFacts.
Require Import Zlib.proof.harness.res_alloc_deflate.StrmKit.
Require Import Zlib.proof.harness.res_alloc_deflate.MainKit.
Require Import Zlib.proof.harness.res_memory_deflate.Peak.
Require Import Zlib.proof.harness.res_memory_deflate.PeakExact.
Require Import Zlib.proof.harness.res_memory_deflate.MainStmt.
Require Import Zlib.proof.harness.res_memory_deflate.MemKit.
Require Import Zlib.proof.harness.res_memory_deflate.MemPrefix.
Require Import Zlib.proof.harness.res_memory_deflate.MemBodyPre.
Require Import Zlib.proof.harness.res_memory_deflate.MemBodyCall.
Require Zlib.contracts.res_memory_deflate.
Require Import Zlib.harness.res_memory_deflate.code.
Local Open Scope logic.
Local Ltac simplify_remove_localdef_temp ::= mem_simplify_rlt.

(* the harness's string literal ZLIB_VERSION, deflateInit2's version argument (the same as MemKit.vlit) *)
Definition vlit : ident := ___stringlit_res_memory_deflate_1.

(* main's body from its parts: the prefix continued at the loop invariant, the do-while loop (body, then the
   test nondet_u8() != 0), return 0 with the two locals given back *)
Lemma body_main_of_parts :
  prefix_stmt -> body_stmt ->
  any_calls_stmt -> (forall ZA : zallocator, @ob_dstream_to_end_za ZA) -> main_memory_stmt.
Proof.
  intros Hprefix Hbody [K AC] TE. unfold main_memory_stmt.
  start_function.
  (* main's body always returns: its normal postcondition is FF *)
  eapply semax_seq with (Q := FF); [ | apply semax_ff ].
  eapply semax_post with (R' := POST_m); [ | | | | ].
  all: try (intros; unfold POST_m; simpl; normalize; fail).
  { intros. subst POSTCONDITION. unfold abbreviate, POST_m. simpl. intro x. apply andp_left2.
    apply derives_refl. }
  eapply semax_pre; [ | apply (Hprefix _ K v_count__1 v_strm gv AC) ].
  { unfold PRE0, MemKit.vlit. entailer!. }
  intros dp bs mem W tr spp L.
  rewrite msuf17_eq.
  eapply semax_seq with (Q := J_inv K gv v_count__1 v_strm dp bs mem W tr spp).
  - eapply semax_pre with (P' := J_inv K gv v_count__1 v_strm dp bs mem W tr spp).
    { unfold J_inv. Exists L. apply ENTAIL_refl. }
    apply semax_loop with (Q' := J_inv K gv v_count__1 v_strm dp bs mem W tr spp).
    + unfold J_inv at 1. Intros L'. apply (Hbody _ K gv v_count__1 v_strm dp bs mem W tr spp L' AC TE).
    + (* the loop test: continue unless nondet_u8() returned 0 *)
      unfold J_inv at 1. Intros L'. unfold J_at, J_loc, J_sep. unfold ltest. abbreviate_semax.
      forward_call tt. Intros b.
      forward_if.
      * forward. unfold J_inv. Exists L'. unfold J_at, J_loc, J_sep. entailer!.
      * eapply semax_pre; [ | apply semax_break ].
        unfold abbreviate in POSTCONDITION. subst POSTCONDITION. unfold loop2_ret_assert, overridePost.
        destruct POST_m. cbv beta iota. unfold J_inv. Exists L'. unfold J_at, J_loc, J_sep. entailer!.
  - (* return 0 *)
    unfold J_inv. Intros L'. unfold J_at, J_loc, J_sep. Intros.
    sep_apply (strm_head_back K gv v_count__1 v_strm spp (ms_s L') (ms_read L') (ms_tout L') (ms_msgv L')
                 (ms_adler L') TE).
    sep_apply (count_at_back gv v_count__1 tr).
    forward. Exists (Int.repr 0). entailer!.
Qed.

Lemma body_main :
  any_calls_stmt -> (forall ZA : zallocator, @ob_dstream_to_end_za ZA) -> main_memory_stmt.
Proof. exact (body_main_of_parts mem_prefix (body_of_parts mem_body_pre mem_body_call)). Qed.
