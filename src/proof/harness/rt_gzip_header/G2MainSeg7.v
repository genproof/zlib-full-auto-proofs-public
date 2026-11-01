(* Law rt_gzip_header, main's body, segment 7 (G2MainKit.seg7_stmt): statements 48-54 of main, the six checks and
   the return.

   After the inflate loop, got's memory (RTH8Spec.head_mem8 with G2IFacts.g2_hdr_out) is got's struct with the
   values main checks and, for each field present in main's header, got's buffer holding exactly its bytes
   (G2MS7Kit.got_view); the copies of extra, name and comment that same_field compares them with are moved to the
   compspecs of same_field (hobjs_view).  From that state (G2MS7Kit.Q7) the statements are proved one by one in
   G2MS7A1.v, G2MS7A.v, G2MS7B1.v, G2MS7B.v .. G2MS7F.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.harness.rt_gzip_header.CS.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainDefs.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainKit.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS7Kit.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS7A.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS7B.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS7C.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS7D.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS7E.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS7F.
Require Import Zlib.harness.rt_gzip_header.code.
#[local] Existing Instance Zlib.proof.harness.rt_gzip_header.CS.CS.
Local Open Scope logic.

Lemma g2seg7_ok : seg7_stmt.
Proof.
  intros Espec gv vh vg vc vd vr g L1 Fr.
  apply semax_pre with (P' := EX vxf : val, EX vxl : val, Q7 gv vh vg vc vd vr g Fr vxf vxl (rest40 g)).
  { unfold A40, Q7, lv_locals, gp_locals, gs_locals. Intros. cbn [app].
    match goal with H : GI.g2_hdr_out _ _ _ _ |- _ => rename H into HO end.
    sep_apply (got_view g L1 vg ltac:(assumption) HO ltac:(assumption) ltac:(assumption) ltac:(assumption)
                 ltac:(assumption) ltac:(assumption) ltac:(assumption)).
    Intros vxf vxl. sep_apply (hobjs_view g ltac:(assumption)).
    Exists vxf vxl. unfold rest40, hx7, hn7, hc7. entailer!. }
  Intros vxf vxl. rewrite seg7_split.
  eapply semax_seq; [ apply s40_ok | ].
  eapply semax_seq; [ apply s41_ok | ].
  eapply semax_seq; [ apply s42_ok | ].
  eapply semax_seq; [ apply s43_ok | ].
  eapply semax_seq; [ apply s44_ok | ].
  eapply semax_seq; [ apply s45_ok | ].
  apply s46_ok.
Qed.
