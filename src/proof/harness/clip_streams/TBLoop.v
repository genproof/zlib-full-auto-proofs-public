(* Law rfc_trailing_bytes, main: statement 34 of TBKit.v (the do-while of inflate() calls until Z_STREAM_END),
   gp_assert(next_in == input + compressed_len) and return 0, from the loop's invariant TBKit.tb_inv.
   The loop's body is proved in three parts (TBLoopIn.v, TBLoopOut.v, TBLoopCall.v); here: the loop's test (P
   again unless the code is Z_STREAM_END, which comes with next_in = input + |O|) and the code after the loop. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Zlib.proof.inflate.Callees.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.clip_streams.CS Zlib.proof.harness.clip_streams.Globals.
Require Import Zlib.proof.harness.clip_streams.DFacts Zlib.proof.harness.clip_streams.IFacts.
Require Import Zlib.proof.harness.clip_streams.TBFacts Zlib.proof.harness.clip_streams.MainDefs.
Require Import Zlib.proof.harness.clip_streams.TBKit Zlib.proof.harness.clip_streams.TBLoopKit.
Require Import Zlib.proof.harness.clip_streams.TBLoopIn Zlib.proof.harness.clip_streams.TBLoopOut.
Require Import Zlib.proof.harness.clip_streams.TBLoopCall.
Require Import Zlib.harness.rfc_trailing_bytes.code.
#[local] Existing Instance CS.CS.
Local Open Scope logic.

Lemma tb_loop : tb_loop_stmt.
Proof.
  intros Espec P wbits n D O src dp op ip vc vd gv PF FA.
  pose proof FA as FA0.
  destruct FA as (DF & HD & Hn & HO & Hsl & Hsb & Hw & BD & BD' & BO & Pdp & Pop & Pip).
  unfold tb_seg34, Delta_tb, POST_B, POST_tb. abbreviate_semax.
  forward_loop (tb_inv P wbits n D O src dp op ip vc vd gv)
    continue: (tbl_cont P wbits n D O src dp op ip vc vd gv)
    break: (tbl_brk O src ip vc vd gv).
  { apply ENTAIL_refl. }
  2: { unfold tbl_cont. Intros r pos out z L.
       forward_if.
       - assert (HP: P wbits D O src pos out z L) by (apply H0; exact H5).
         destruct (tl_ok P PF _ _ _ _ _ _ _ _ HP) as (Hhd & _).
         rewrite (tbl_head_emp L Hhd).
         forward. unfold tb_inv. Exists pos out z L. entailer!.
       - assert (Ep: pos = Zlength O) by (apply H1; exact H5). subst pos.
         forward. unfold tbl_brk. Exists z L. entailer!. }
  2: { unfold tbl_brk. Intros z L.
       rewrite tbl_istreamA_unfold. Intros. unfold tbl_tup. rewrite H.
       forward.
       forward_call (Int.repr 1).
       { entailer!. eapply derives_trans; [ | apply tbl_test_eq_self; auto].
         eapply derives_trans; [ | apply (tbl_weak_valid Ews (Zlength src) (bytes_rep src) ip (Zlength O));
                                   [auto | pose proof (Zlength_nonneg O); lia] ].
         cancel. }
       forward. Exists (Int.repr 0). sep_apply (data_at_data_at_ Tsh t_zsl). entailer!. }
  unfold tb_inv. Intros pos out z L.
  rewrite tbl_istreamA_unfold. Intros.
  unfold tbl_tup. rewrite H1, H2.
  eapply semax_pre; [ | apply (tbl_in Espec P wbits n D O src dp op ip vc vd gv pos out z L
                                    (Vint (Int.repr (zf_ai z))) (Vint (Int.repr (zf_ao z)))); auto ].
  { unfold tbl_st. entailer!. }
  apply tbl_out; auto.
  apply tbl_call; auto.
Qed.
