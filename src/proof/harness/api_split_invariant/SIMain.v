(* Law api_split_invariant, main(): proved against MainLib.main_core_spec R (SIGlobals.v) for ANY Inv, Max with
   the facts of SIFacts.v (si_facts), calling inflate.c's API through its shared specifications (inflateInit2_:
   Spec5.v; inflate: the wide SpecW.v, calls of up to 2^32-1 bytes and a raw stream's undefined adler), and the
   helpers of harness/laws_common.h through theirs (laws_common/Spec.v).  The harness's own `final` has its
   specification here. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5 Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.api_split_invariant.SILawCS Zlib.proof.harness.api_split_invariant.SIGlobals
               Zlib.proof.harness.api_split_invariant.SIFacts.
Require Import Zlib.harness.api_split_invariant.code.
Require Import Zlib.proof.harness.api_split_invariant.SIMainKit.
Require Import Zlib.proof.harness.api_split_invariant.SIMainPre.
Require Import Zlib.proof.harness.api_split_invariant.SIMainOne.
Require Import Zlib.proof.harness.api_split_invariant.SIMainInit.
Require Import Zlib.proof.harness.api_split_invariant.SIMainLoop.
Require Import Zlib.proof.harness.api_split_invariant.SIMainTail.

(* final(code): the codes that end the split loop *)
Definition final_spec :=
  DECLARE _final
  WITH r: Z
  PRE [ tint ]
    PROP (Int.min_signed <= r <= Int.max_signed)
    PARAMS (Vint (Int.repr r))
    SEP ()
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (if final_code r then 1 else 0)))
    SEP ().

Definition Gmain : funspecs :=
  [inflateInit2__spec; inflate_specW; zcalloc_i; zcfree_i;
   upto_spec; any_bytes_spec; copy_of_spec; bytes_eq_spec; offer_spec; new_stream_spec; final_spec;
   (_quickproof_malloc, malloc_spec'); nondet_u32_spec; gp_assume_spec; gp_assert_spec].

Lemma si_main : forall Inv Max, si_facts Inv Max ->
  semax_body (QPvarspecs p) Gmain f_main (_main, main_core_spec R).
Proof.
  intros Inv Max SF. change Gmain with Gmain_k.
  start_function.
  unfold R. Intros.
  make_func_ptr Zlib.inflate.code._zcalloc. make_func_ptr Zlib.inflate.code._zcfree.
  gather_SEP (func_ptr' _ (gv inflate.code._zcalloc)) (func_ptr' _ (gv inflate.code._zcfree)).
  fold (zfuncs gv).
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  apply semax_seq with FF; [ | apply semax_ff].
  (* the chain of main's statements, segment by segment *)
  eapply semax_pre; [ | apply (seg_pre_ok gv v_window_bits v_one v_split)].
  { unfold sm_pre0. entailer!. }
  intros w src room flush inp ins o1 o2 FA.
  apply (seg_one_ok Inv Max); auto. intros r1 z1 L1 ow1 FB.
  apply (seg_init_ok Inv Max gv v_window_bits v_one v_split w src room flush inp ins o1 o2 r1 z1 L1 ow1); auto.
  destruct FA as (Hw & Bs & Hl & Hr & Hf & Hb & Ht & Pi & Pc & P1 & P2).
  (* the split's loop reads the copy ins *)
  apply (seg_loop_ok Inv Max); auto.
  - apply sm_fr_frame.
  - apply (seg_tail_ok Inv Max gv v_window_bits v_one v_split w src room flush inp); auto. unfold sm_A_facts; auto 20.
Qed.

(* comparisons of two different ints *)
Lemma si_eq_false r c: Int.min_signed <= r <= Int.max_signed -> Int.min_signed <= c <= Int.max_signed -> r <> c ->
  Int.eq (Int.repr r) (Int.repr c) = false.
Proof. intros. apply Int.eq_false. intro E. apply repr_inj_signed in E; auto. Qed.

(* a branch of final(): impossible (a known false test) or one assignment *)
Ltac si_br := first [ solve [discriminate] | solve [contradiction] | forward; entailer! ].

Lemma si_final : semax_body (QPvarspecs p) [] f_final final_spec.
Proof.
  start_function.
  assert (Hc: r = 1 \/ r = 2 \/ r = -3 \/ (r <> 1 /\ r <> 2 /\ r <> -3)) by lia.
  destruct Hc as [E|[E|[E|(N1&N2&N3)]]]; [subst r .. | ].
  - forward_if (temp _t'1 (Vint (Int.repr 1))); [si_br | si_br | ].
    forward_if (temp _t'2 (Vint (Int.repr 1))); [si_br | si_br | ].
    forward.
  - forward_if (temp _t'1 (Vint (Int.repr 1))); [si_br | si_br | ].
    forward_if (temp _t'2 (Vint (Int.repr 1))); [si_br | si_br | ].
    forward.
  - forward_if (temp _t'1 (Vint (Int.repr 0))); [si_br | si_br | ].
    forward_if (temp _t'2 (Vint (Int.repr 1))); [si_br | si_br | ].
    forward.
  - forward_if (temp _t'1 (Vint (Int.repr 0))).
    { contradiction. }
    { forward. entailer!. rewrite si_eq_false by (auto; rep_lia). reflexivity. }
    forward_if (temp _t'2 (Vint (Int.repr 0))).
    { contradiction. }
    { forward. entailer!. rewrite si_eq_false by (auto; rep_lia). reflexivity. }
    forward. entailer!. unfold final_code.
    rewrite (proj2 (Z.eqb_neq r Z_STREAM_END)), (proj2 (Z.eqb_neq r Z_NEED_DICT)), (proj2 (Z.eqb_neq r Z_DATA_ERROR))
      by auto. reflexivity.
Qed.
