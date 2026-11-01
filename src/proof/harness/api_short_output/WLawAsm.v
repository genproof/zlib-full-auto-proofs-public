(* Law api_short_output (data of any length): the assembly of harness_safe from main's body
   (WMainDefs.body_main_w_stmt), inflate() against SpecWSelf.inflate_specW_s, uncompr.c against USpecW.v, the
   other shared bodies (trees.c and deflate.c: Obligations9.v; compress.c: RTCBodiesW.v; inflate.c:
   SpecWLib.specw_lib_stmt and WInflLib.inflate_lib_w, the parts of LibStmt5.inflate_lib5_stmt the program
   reaches; the helpers of laws_common.h: laws_common_ok and BytesEqNull.bytes_eq_spec_n; adler32.c, crc32.c,
   zutil.c, libc.c, inftrees.c), the environment and the model facts that main's body takes.  The bodies of
   inflate.c (inflate_lib_w, specw_lib_stmt), deflate.c and trees.c are hypotheses: the law's final proof gives
   them. *)
Require Import QuickProof.Contract.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.contracts.api_short_output.
Require Import Zlib.proof.inflate_api.SpecWSelf Zlib.proof.uncompr.USpecW.
Require Import Zlib.proof.roundtrip.RTC2W Zlib.proof.roundtrip.RTC2WFinal Zlib.proof.uncompr.UTheoryW.
Require Import Zlib.proof.harness.api_short_output.WMainDefs.
Require Import Zlib.proof.inflate_api.SpecWLib.
Require Import Zlib.proof.harness.api_short_output.WInflLib.
Require Import Zlib.proof.deflate.Obligations Zlib.proof.deflate.Obligations9.
Require Import VST.floyd.proofauto.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.harness.api_short_output.WLawCS Zlib.proof.harness.api_short_output.WAsmKit.
Require Import Zlib.proof.harness.api_short_output.WAsmTop Zlib.proof.harness.api_short_output.WAsmTrees.
Require Import Zlib.proof.harness.api_short_output.WAsmDefl Zlib.proof.harness.api_short_output.WAsmInfl.

Theorem api_short_output_w_core :
  laws_common_ok -> inflate_lib_w -> specw_lib_stmt -> trees_bodies_ok -> deflate_bodies_ok9 ->
  body_main_w_stmt -> body_inflate_ws_stmt -> uncompr_bodies_w_stmt ->
  c2w_bound_stmt -> c2w_final_stmt -> uw_theory_stmt ->
  harness_safe Zlib.contracts.api_short_output.whole_prog.
Proof.
  intros LC LI [ZL BR] TB DB BM BIS HU CB CF UT.
  change Zlib.contracts.api_short_output.whole_prog with p.
  harness_safe_by_specs Zlib.proof.harness.api_short_output.WLawCS.CS G main_post_TT.
  - reflexivity.
  - apply w_entries_G.
    + exact (w_entries_top LC BR DB BM HU CB CF UT).
    + exact (w_entries_trees BR TB).
    + exact (w_entries_defl BR DB).
    + exact (w_entries_infl LI (conj ZL BR) BIS).
    + exact w_entries_env.
Qed.
