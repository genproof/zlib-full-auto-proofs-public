(* The main of harness/rj_crc32_negative.c, proved against main_core_spec (crc32.c's tables): for the
   negative length len2 = -1 - upto(PTRDIFF_MAX) and any crc1, crc2, crc32_combine and crc32_combine_gen
   return 0 (Combine.v crc32_combine_val_neg, and crc32_combine_gen_val's negative case). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Zlib.contracts.rj_crc32_negative.
Require Import Zlib.harness.rj_crc32_negative.code.
Require Import Zlib.proof.crc32.SpecCombine Zlib.proof.crc32.Combine.
Require Import Zlib.proof.adler32.MainLib Zlib.proof.crc32.Globals.
Require Import Zlib.proof.harness.laws_common.Spec.

Definition p := Zlib.contracts.rj_crc32_negative.whole_prog.
Definition comps := ltac:(let x := eval vm_compute in (prog_composites p) in exact x).
Definition cprog : Clight.program := Clightdefs.mkprogram comps nil nil 1%positive Logic.I.
#[export] Instance CS : compspecs. make_compspecs cprog. Defined.

Definition R (gv: globals) : mpred := (crc_table_at Ers gv * x2n_table_at Ers gv)%logic.

Definition Gmain : funspecs := [crc32_combine_spec; crc32_combine_gen_spec; upto_spec;
  nondet_size_spec; gp_assert_spec].

Lemma body_main: semax_body (QPvarspecs p) Gmain f_main (_main, main_core_spec R).
Proof.
  start_function.
  unfold R. Intros.
  forward_call (Int64.max_signed).
  Intros k.
  forward.
  replace (Int64.sub (Int64.repr (Int.signed (Int.neg (Int.repr 1)))) (Int64.repr k)) with (Int64.repr (-1 - k))
    by (rewrite Int64.sub_signed, !Int64.signed_repr by rep_lia; reflexivity).
  forward_call tt. Intros c1.
  forward_call tt. Intros c2.
  forward_call (c1, c2, -1 - k, gv, Ers).
  rewrite crc32_combine_val_neg by lia.
  forward_call (Int.repr 1).
  forward_call (-1 - k, gv, Ers).
  replace (crc32_combine_gen_val (-1 - k)) with 0
    by (unfold crc32_combine_gen_val; destruct (Z.ltb_spec (-1 - k) 0); lia).
  forward_call (Int.repr 1).
  ret0.
Qed.
