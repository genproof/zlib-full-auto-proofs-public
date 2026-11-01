(* The main of harness/ck_crc32_null.c, proved against main_core_spec (memory manager, crc32.c's tables):
   crc32_z with a Z_NULL buffer returns 0 for any CRC and any length (crc32_z_spec with isnull = true). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Zlib.contracts.ck_crc32_null.
Require Import Zlib.harness.ck_crc32_null.code.
Require Import Zlib.proof.crc32.Spec Zlib.proof.crc32.Globals.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.harness.laws_common.Spec.

Definition p := Zlib.contracts.ck_crc32_null.whole_prog.
Definition comps := ltac:(let x := eval vm_compute in (prog_composites p) in exact x).
Definition cprog : Clight.program := Clightdefs.mkprogram comps nil nil 1%positive Logic.I.
#[export] Instance CS : compspecs. make_compspecs cprog. Defined.
#[export] Instance CC1 : change_composite_env Zlib.units.Crc32.CS CS. make_cs_preserve Zlib.units.Crc32.CS CS. Defined.
#[export] Instance CC2 : change_composite_env Zlib.units.Adler32.CS CS. make_cs_preserve Zlib.units.Adler32.CS CS. Defined.

Definition R (gv: globals) : mpred := crc_table_at Ers gv.

Definition Gmain : funspecs := [crc32_z_spec; upto_spec; nondet_size_spec; gp_assert_spec].

Lemma body_main: semax_body (QPvarspecs p) Gmain f_main (_main, main_core_spec R).
Proof.
  start_function.
  unfold R. Intros.
  forward_call tt. Intros crc.
  forward_call (9223372036854775807).
  Intros len.
  forward_call (crc, nullval, len, true, Ews, nullval, 0, 0, @nil val, @nil Z, false, Ews, gv, Ers).
  { cancel. }
  forward_call (Int.repr 1).
  forward.
  Exists (Int.repr 0). entailer!.
Qed.
