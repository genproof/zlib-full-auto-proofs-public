(* Law inflate_check, main: one iteration of the loop: IKMainPre ; IKMainCall ; IKMainChk1 ; IKMainChk2 ; the three
   free()s and `if (stop == 0) break;` (seg_L4), back to the loop invariant ik_inv. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessRef Zlib.proof.adler32.MainLib.
Require Zlib.proof.crc32.HarnessRef.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib Zlib.proof.harness.inflate_common.HarnessLe32.
Require Import Zlib.proof.harness.inflate_check.IKLawCS Zlib.proof.harness.inflate_check.IKGlobals
               Zlib.proof.harness.inflate_check.IKFacts.
Require Import Zlib.harness.x_inflate_check.code.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.inflate_check.IKMainKit.
Local Open Scope logic.
Require Import Zlib.proof.harness.inflate_check.IKMainPre Zlib.proof.harness.inflate_check.IKMainCall
               Zlib.proof.harness.inflate_check.IKMainChk1 Zlib.proof.harness.inflate_check.IKMainChk2.

Lemma seg_loop_ok {Espec: OracleKind} I gv vs vosn w srcp src adler0 Fr pos out z L :
  ik_glob I w srcp src adler0 -> I w src pos out z L -> 0 <= pos <= Zlength src -> bytes_ok out ->
  (w < 0 -> zf_adler z = adler0) ->
  semax Delta_m (ik_at gv vs vosn w srcp src adler0 Fr pos out z L) seg_loop
    (ik_PL (ik_inv I gv vs vosn w srcp src adler0 Fr)).
Proof.
  intros G HI Hpos Hout Hraw.
  apply (pre_ok I); auto.
  intros ain aout flush stop ibp obp q bs BF.
  apply (call_ok I); auto.
  intros pos' out' r z' L' cont MF HI' LOK Hc.
  apply chk1_ok; auto. apply chk2_ok; auto.
  pose proof BF as BF'.
  destruct BF' as (_ & _ & _ & _ & _ & Hain & Hpa & Haout & Hbs & Hbsb & Hfl & Hst & Pib & Pob & Pq).
  pose proof MF as MF'.
  destruct MF' as (Hw & Hpos' & Hsrc & Hsb & Psrc & Had & Hout' & Hz' & Hr & Hraw' & _).
  unfold ik_mid, seg_L4, ik_PL, Delta_m, Gmain_k. simplify_func_tycontext. abbreviate_semax.
  Intros.
  forward_call (tarray tuchar ain, ibp, gv).
  { rewrite if_false by (destruct ibp; try contradiction; discriminate).
    sep_apply (data_at_data_at_ Ews (tarray tuchar ain)). cancel. }
  forward_call (tarray tuchar aout, obp, gv).
  { rewrite if_false by (destruct obp; try contradiction; discriminate).
    sep_apply (data_at_data_at_ Ews (tarray tuchar aout) cont obp). cancel. }
  forward.
  forward_call (tarray tuchar aout, q, gv).
  { rewrite if_false by (destruct q; try contradiction; discriminate).
    sep_apply (data_at_data_at_ Ews (tarray tuchar aout) (bytes_rep bs) q). cancel. }
  sep_apply (ik_istream_fold gv Tsh vs z' L'); auto.
  forward_if.
  { forward. unfold ik_inv. Exists pos' out' z' L'. entailer!. }
  { forward. unfold ik_inv. Exists pos' out' z' L'. entailer!. }
Qed.
