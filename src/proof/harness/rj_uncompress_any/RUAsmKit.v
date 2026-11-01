(* Law rj_uncompress_any: the specifications of the assembly.

   [G] gives one specification to every function of the program that main reaches, in three parts that RUAsmTop.v
   and RUAsmInfl.v prove (each part is a Forall over its entries, [ru_entries]):
   - [G_top]: main (harness_safe's specification), the helpers of laws_common.h that main calls (upto,
     alloc_any_bytes, copy_of with a Z_NULL source of length 0 allowed, bytes_eq) and uncompr.c's uncompress2(_z)
     for any sizes with a destination and a source that may be Z_NULL (USpecW);
   - [G_infl]: inflate.c (Spec5's inflateInit_, inflateInit2_, the reset functions and inflateEnd; inflate()
     against SpecWSelf.inflate_specW_s; the allocator-generic port's inflateStateCheck, inflate_fast and
     updatewindow at zlib's default allocator SpecWLib.zc_alloc, as inflate()'s body takes them), inftrees.c,
     adler32.c, crc32.c, zutil.c and libc.c at the law's compspecs, as for rt_roundtrip (rt_roundtrip/WAsmKit.v);
   - [G_env]: the environment.
   The functions main does not reach (uncompress / uncompress_z, inflate.c's other entry points) get vacuous
   specifications (harness_safe_by_specs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Zlib.proof.adler32.Spec.
Require Zlib.proof.crc32.Spec.
Require Zlib.proof.zutil.Spec.
Require Zlib.proof.zutil.Libc.
Require Zlib.proof.inftrees.spec.
Require Zlib.proof.inflate.Callees.
Require Zlib.proof.inflate_api.Spec5.
Require Zlib.proof.inflate_api.SpecWLib.
Require Zlib.proof.inflate_api.SpecWSelf.
Require Zlib.proof.za.inflate_api.USpec.
Require Import Zlib.proof.uncompr.USpecW.
Require Import Zlib.proof.uncompr.UTheoryWAny.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.laws_common.CopyOfNull.
Require Import Zlib.proof.harness.rj_uncompress_any.RUCS.
Require Import Zlib.proof.harness.rj_uncompress_any.RUGlobals.
Require Import Zlib.proof.harness.rj_uncompress_any.RUMainDefs.
Require Import Zlib.harness.rj_uncompress_any.code.

Local Notation CSU := Zlib.proof.harness.rj_uncompress_any.RUCS.CS.
#[local] Existing Instance CSU.

Module S5 := Zlib.proof.inflate_api.Spec5.
Module SWL := Zlib.proof.inflate_api.SpecWLib.
Module ZU := Zlib.proof.za.inflate_api.USpec.

Definition G_top : funspecs :=
  [(_main, QPmain_spec_ext' p tt main_post_TT);
   (* laws_common.h *)
   upto_spec; any_bytes_spec; copy_of_spec_n; bytes_eq_spec;
   (* uncompr.c *)
   uncompress2_z_spec_w; uncompress2_spec_w].

Definition G_infl : funspecs :=
  [S5.inflateInit__spec; S5.inflateInit2__spec; S5.inflateReset2_spec; S5.inflateReset_spec;
   S5.inflateResetKeep_spec; S5.inflateEnd_spec;
   @ZU.inflateStateCheck_uspec globals SWL.zc_alloc; Zlib.proof.inflate_api.SpecWSelf.inflate_specW_s;
   @ZU.inflate_fast_uspec globals SWL.zc_alloc; @ZU.updatewindow_uspec globals SWL.zc_alloc;
   Zlib.proof.inflate.Callees.inflate_fixed_spec; Zlib.proof.inftrees.spec.inflate_table_spec;
   Zlib.proof.adler32.Spec.adler32_spec; Zlib.proof.adler32.Spec.adler32_z_spec;
   Zlib.proof.crc32.Spec.crc32_spec; Zlib.proof.crc32.Spec.crc32_z_spec;
   @Zlib.proof.zutil.Spec.zcalloc_spec CSU; @Zlib.proof.zutil.Spec.zcfree_spec CSU;
   @Zlib.proof.zutil.Libc.memcpy_spec CSU; @Zlib.proof.zutil.Libc.memset_spec CSU].

Definition G_env : funspecs :=
  [(_quickproof_malloc, @malloc_spec' CSU); (_quickproof_free, @free_spec' CSU);
   nondet_size_spec; @nondet_bytes_spec CSU; gp_assert_spec].

Definition G : funspecs := G_top ++ G_infl ++ G_env.

(* the obligation of the entries of a part of G (harness_safe_of_specs's ENTRIES restricted to it) *)
Definition ru_entries (Gk : funspecs) : Prop :=
  Forall (entry_of_prog (@HonestEspec CSU) CSU p (G ++ vacuous_internals p G)) Gk.

Lemma ru_entries_G : ru_entries G_top -> ru_entries G_infl -> ru_entries G_env -> ru_entries G.
Proof. unfold ru_entries, G; intros; repeat (apply Forall_app; split); assumption. Qed.

(* main against RUMainDefs.main_core_spec R is main against harness_safe's specification of main *)
Lemma main_entry :
  body_main_stmt -> uw_any_stmt ->
  semax_body (QPvarspecs p) Gmain f_main (_main, QPmain_spec_ext' p tt main_post_TT).
Proof.
  intros BM UA.
  eapply (semax_body_main_core _ _ p _ _ R).
  - exact globals_ok.
  - exact (BM UA).
  - vm_compute; reflexivity.
Qed.
