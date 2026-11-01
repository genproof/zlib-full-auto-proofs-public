(* The main of harness/ck_adler32_null.c, proved against main_core_spec (memory manager only: adler32.c has
   no globals): adler32_z(adler, Z_NULL, len) returns 1 for any adler and any len, the Z_NULL case of
   adler32_z_spec. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Zlib.contracts.ck_adler32_null.
Require Import Zlib.harness.ck_adler32_null.code.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.Spec Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.harness.laws_common.Spec.

Definition p := Zlib.contracts.ck_adler32_null.whole_prog.
Definition comps := ltac:(let x := eval vm_compute in (prog_composites p) in exact x).
Definition cprog : Clight.program := Clightdefs.mkprogram comps nil nil 1%positive Logic.I.
#[export] Instance CS : compspecs. make_compspecs cprog. Defined.

Definition R (gv: globals) : mpred := emp.

Definition Gmain : funspecs := [upto_spec; adler32_z_spec; nondet_size_spec; gp_assert_spec].

Lemma body_main: semax_body (QPvarspecs p) Gmain f_main (_main, main_core_spec R).
Proof.
  start_function.
  unfold R. Intros.
  forward_call tt. Intros adler.
  forward_call (Int64.max_signed). Intros len.
  forward_call (adler, nullval, len, true, Ews, nullval, 0, 0, @nil val, @nil Z, false, Ews).
  all: try (solve [cancel]).
  forward_call (Int.repr 1).
  forward.
  Exists (Int.repr 0). entailer!.
Qed.
