(* Law rj_uncompress_any: the assembly of harness_safe from main's body (RUMainDefs.body_main_stmt), uncompr.c
   against USpecW.v (a destination and a source that may be Z_NULL), inflate.c's bodies (WAsmInfl.infl5_bodies_stmt,
   SpecWLib.specw_lib_stmt, SpecWSelf.body_inflate_ws_stmt), the helpers of laws_common.h (laws_common_ok and
   copy_of's variant CopyOfNull.copy_of_n_stmt), adler32.c, crc32.c, zutil.c, libc.c, inftrees.c, the environment
   and the theory UTheoryWAny.uw_any_stmt.  The entries of the specifications (RUAsmKit.G) are proved part by part
   in RUAsmTop.v and RUAsmInfl.v. *)
Require Import QuickProof.Contract.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.laws_common.CopyOfNull.
Require Zlib.contracts.rj_uncompress_any.
Require Import Zlib.proof.inflate_api.SpecWSelf.
Require Import Zlib.proof.inflate_api.SpecWLib.
Require Import Zlib.proof.uncompr.USpecW.
Require Import Zlib.proof.uncompr.UTheoryWAny.
Require Zlib.proof.harness.rt_roundtrip.WAsmInfl.
Require Import Zlib.proof.harness.rj_uncompress_any.RUMainDefs.
Require Import VST.floyd.proofauto.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.harness.rj_uncompress_any.RUCS.
Require Import Zlib.proof.harness.rj_uncompress_any.RUAsmKit.
Require Import Zlib.proof.harness.rj_uncompress_any.RUAsmTop.
Require Import Zlib.proof.harness.rj_uncompress_any.RUAsmInfl.

Theorem rj_uncompress_any_core :
  laws_common_ok -> copy_of_n_stmt -> Zlib.proof.harness.rt_roundtrip.WAsmInfl.infl5_bodies_stmt ->
  specw_lib_stmt -> body_main_stmt -> body_inflate_ws_stmt -> uncompr_bodies_w_stmt -> uw_any_stmt ->
  harness_safe Zlib.contracts.rj_uncompress_any.whole_prog.
Proof.
  intros LC CN LI [ZL BR] BM BIS HU UA.
  change Zlib.contracts.rj_uncompress_any.whole_prog with p.
  harness_safe_by_specs Zlib.proof.harness.rj_uncompress_any.RUCS.CS G main_post_TT.
  - reflexivity.
  - apply ru_entries_G.
    + exact (ru_entries_top LC CN BR BM HU UA).
    + exact (ru_entries_infl LI (conj ZL BR) BIS).
    + exact ru_entries_env.
Qed.
