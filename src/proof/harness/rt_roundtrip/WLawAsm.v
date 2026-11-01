(* Law rt_roundtrip (data of any length): the assembly of harness_safe from main's body
   (WMainDefs.body_main_w_stmt), inflate() against SpecWSelf.inflate_specW_s, uncompr.c against USpecW.v, the
   other shared bodies (trees.c and deflate.c: Obligations9.v; compress.c: RTCBodiesW.v; inflate.c:
   SpecWLib.specw_lib_stmt and WAsmInfl.infl5_bodies_stmt, the parts of LibStmt5.inflate_lib5_stmt it reaches; the helpers of laws_common.h: laws_common_ok;
   adler32.c, crc32.c, zutil.c, libc.c, inftrees.c), the environment and the model facts that main's body takes.
   The bodies of inflate.c (infl5_bodies_stmt, specw_lib_stmt, body_inflate_ws_stmt), deflate.c, trees.c and
   uncompr.c are hypotheses: the law's final proof gives them.  The entries of the specifications
   (WAsmKit.G) are proved part by part in WAsmTop.v, WAsmTrees.v, WAsmDefl1.v, WAsmDefl2.v and WAsmInfl.v. *)
Require Import QuickProof.Contract.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.contracts.rt_roundtrip.
Require Import Zlib.proof.inflate_api.SpecWSelf Zlib.proof.uncompr.USpecW.
Require Import Zlib.proof.roundtrip.RTC2W Zlib.proof.roundtrip.RTC2WFinal Zlib.proof.uncompr.UTheoryW.
Require Import Zlib.proof.harness.rt_roundtrip.WMainDefs.
Require Import Zlib.proof.inflate_api.LibStmt5 Zlib.proof.inflate_api.SpecWLib.
Require Import Zlib.proof.deflate.Obligations Zlib.proof.deflate.Obligations9.
Require Import VST.floyd.proofauto.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.harness.rt_roundtrip.WCS.
Require Import Zlib.proof.harness.rt_roundtrip.WAsmKit.
Require Import Zlib.proof.harness.rt_roundtrip.WAsmTop.
Require Import Zlib.proof.harness.rt_roundtrip.WAsmTrees.
Require Import Zlib.proof.harness.rt_roundtrip.WAsmDefl1.
Require Import Zlib.proof.harness.rt_roundtrip.WAsmDefl2.
Require Import Zlib.proof.harness.rt_roundtrip.WAsmInfl.

Theorem rt_roundtrip_w_core :
  laws_common_ok -> infl5_bodies_stmt -> specw_lib_stmt -> trees_bodies_ok -> deflate_bodies_ok9 ->
  body_main_w_stmt -> body_inflate_ws_stmt -> uncompr_bodies_w_stmt ->
  c2w_bound_stmt -> c2w_final_stmt -> uw_theory_stmt ->
  harness_safe Zlib.contracts.rt_roundtrip.whole_prog.
Proof.
  intros LC LI [ZL BR] TB DB BM BIS HU CB CF UT.
  change Zlib.contracts.rt_roundtrip.whole_prog with p.
  harness_safe_by_specs Zlib.proof.harness.rt_roundtrip.WCS.CS G main_post_TT.
  - reflexivity.
  - apply w_entries_G.
    + exact (w_entries_top LC BR DB BM HU CB CF UT).
    + exact (w_entries_trees BR TB).
    + exact (w_entries_defl1 BR DB).
    + exact (w_entries_defl2 BR DB).
    + exact (w_entries_infl LI (conj ZL BR) BIS).
    + exact w_entries_env.
Qed.
