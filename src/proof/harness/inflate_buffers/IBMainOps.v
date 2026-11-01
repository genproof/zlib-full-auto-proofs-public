(* Law inflate_buffers, main: the dispatch seg_ops (`if (op < 200) ... else ...`) from its eleven branches. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_buffers.IBLawCS Zlib.proof.harness.inflate_buffers.IBGlobals
               Zlib.proof.harness.inflate_buffers.IBFacts Zlib.proof.harness.inflate_buffers.IBMainKit.
Require Import Zlib.harness.x_inflate_buffers.code.
Require Import Zlib.proof.crc32.Spec.

Require Import Zlib.proof.harness.inflate_buffers.IBMainInf Zlib.proof.harness.inflate_buffers.IBMainSync
  Zlib.proof.harness.inflate_buffers.IBMainGd Zlib.proof.harness.inflate_buffers.IBMainSd
  Zlib.proof.harness.inflate_buffers.IBMainPrime Zlib.proof.harness.inflate_buffers.IBMainReset
  Zlib.proof.harness.inflate_buffers.IBMainReset2 Zlib.proof.harness.inflate_buffers.IBMainVal
  Zlib.proof.harness.inflate_buffers.IBMainMark Zlib.proof.harness.inflate_buffers.IBMainCu
  Zlib.proof.harness.inflate_buffers.IBMainSp.

Ltac ops_br lem :=
  repeat match goal with
         | P := @abbreviate statement _ |- _ => unfold abbreviate in P; subst P
         | P := @abbreviate ret_assert _ |- _ => unfold abbreviate in P; subst P end;
  match goal with H: ops_hyps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    eapply semax_pre;
    [ idtac | eapply (lem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (normal_ret_assert FF)); [exact H | lia] ] end;
  unfold ops_pre, ops_locals; entailer!.

Lemma seg_ops_ok {Espec: OracleKind} gv vs vosn vdl srcp src pos aout flush arg op innull outnull stop ain ibp obp q bs z L
    Fr (Post: ret_assert) :
  ops_hyps srcp src pos aout flush arg op innull outnull stop ain ibp obp q bs L ->
  semax Delta_m (ops_pre gv vs vosn vdl srcp src pos aout flush arg op innull outnull stop ain ibp obp q bs z L Fr)
    seg_ops
    (overridePost (ops_post gv vs vosn vdl srcp src pos aout flush arg op innull outnull stop ain ibp obp q z Fr) Post).
Proof.
  intros H.
  pose proof H as H'.
  destruct H' as (FI & HI & Hpos & Hain & Hpa & Hsrc & Hsb & Haout & Hbsl & Hbsb & Hfl & Harg & Hopr & Hin & Hout & Hst & Psrc & Pib & Pob & Pq).
  destruct Post as [Pn Pb Pc Pr].
  unfold seg_ops, Delta_m, Gmain_k. simplify_func_tycontext.
  unfold ops_pre, ops_locals.
  forward_if; [ ops_br @seg_inf_ok | ].
  forward_if; [ ops_br @seg_sync_ok | ].
  forward_if; [ ops_br @seg_gd_ok | ].
  forward_if; [ ops_br @seg_sd_ok | ].
  forward_if; [ ops_br @seg_prime_ok | ].
  forward_if; [ ops_br @seg_reset_ok | ].
  forward_if; [ ops_br @seg_reset2_ok | ].
  forward_if; [ ops_br @seg_val_ok | ].
  forward_if; [ ops_br @seg_mark_ok | ].
  forward_if; [ ops_br @seg_cu_ok | ops_br @seg_sp_ok ].
Qed.
