(* Law rt_session (harness/rt_session.c): main's final checks (statements 74-84) with a header: the header's fields against the copies (SMKit.v, [segE_9_stmt]). *)
(* The proof is rt_gzip_header's (G2MainSeg7.v) after rt_stream_trailing's checks (TSegE.v): SME9A.v and SME9B.v
   prove statements 74-77 (asked is 0 as there is no dictionary with a header; next_in == input + compressed_len;
   next_out == out + data_len and out's bytes against expected's; !with_head is false) and move to SME9Kit.Q9,
   where got's memory is read through G2IFacts.g2_hdr_out and the other locals' memory is given back to their
   stack slots; SME9H1.v .. SME9H8.v prove the six header checks and the return, one statement (or part of one)
   per lemma. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SMKit.
Require Import Zlib.proof.harness.rt_session.SME9Kit.
Require Import Zlib.proof.harness.rt_session.SME9B.
Require Import Zlib.proof.harness.rt_session.SME9H2.
Require Import Zlib.proof.harness.rt_session.SME9H4.
Require Import Zlib.proof.harness.rt_session.SME9H5.
Require Import Zlib.proof.harness.rt_session.SME9H6.
Require Import Zlib.proof.harness.rt_session.SME9H7.
Require Import Zlib.proof.harness.rt_session.SME9H8.
Require Import Zlib.harness.rt_session.code.
#[local] Existing Instance SCS.CS.

Lemma sm_segE_9 : segE_9_stmt.
Proof.
  intros Espec gv vh vg vc va vd u O c src ip z L.
  apply (semax_unfold_Ssequence segE_parts); [ first [ exact segE_split | exact (eq_sym segE_split) ] | ].
  unfold segE_parts.
  eapply semax_seq; [ apply e74_77_ok | ].
  apply extract_exists_pre; intro vxf. apply extract_exists_pre; intro vxl.
  eapply semax_seq; [ apply e78_ok | ].
  eapply semax_seq; [ apply e79_ok | ].
  eapply semax_seq; [ apply e80_ok | ].
  eapply semax_seq; [ apply e81_ok | ].
  eapply semax_seq; [ apply e82_ok | ].
  eapply semax_seq; [ apply e83_ok | ].
  apply e84_ok.
Qed.
