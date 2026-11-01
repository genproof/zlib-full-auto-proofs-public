(* Law inflate_buffers, main: the branch inflatePrime(&s, (int) arg, flush) (230 <= op < 235) and its assert. *)
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

Lemma seg_prime_ok {Espec: OracleKind} gv vs vosn vdl srcp src pos aout flush arg op innull outnull stop ain ibp obp q bs z L
    Fr (Post: ret_assert) :
  ops_hyps srcp src pos aout flush arg op innull outnull stop ain ibp obp q bs L -> 230 <= op < 235 ->
  semax Delta_m (ops_pre gv vs vosn vdl srcp src pos aout flush arg op innull outnull stop ain ibp obp q bs z L Fr)
    seg_prime
    (overridePost (ops_post gv vs vosn vdl srcp src pos aout flush arg op innull outnull stop ain ibp obp q z Fr) Post).
Proof.
  intros H Hop.
  destruct H as (FI & HI & Hpos & Hain & Hpa & Hsrc & Hsb & Haout & Hbsl & Hbsb & Hfl & Harg & Hopr & Hin & Hout & Hst & Psrc & Pib & Pob & Pq).
  unfold ops_pre, ops_locals.
  assert_PROP (isptr vs) as Pvs by entailer!.
  unfold seg_prime, Delta_m, Gmain_k. simplify_func_tycontext. abbreviate_semax.
  forward_call (gv, Tsh, vs, ib_zcall z (ib_nin op innull) (ib_nout op outnull) ibp obp ain aout, Some L,
                Int.signed (Int.repr arg), flush).
  { entailer!. simpl. rewrite Int.repr_signed. reflexivity. }
  { rewrite ib_istream_opt by auto. cancel. }
  rewrite ib_istream_opt by auto.
  unfold on_live; rewrite ib_is_live by auto.
  unfold prime_f.
  rewrite ib_nin_ge, ib_nout_ge in * by lia.
  destruct (prime_s (Int.signed (Int.repr arg)) flush (l_s L)) as [s|] eqn:HP; unfold fst3, snd3, thd3; cbn [fst snd];
    (assert_PROP (zf_ok (ib_zcall z false false ibp obp ain aout)) as ZOK by (unfold istream; entailer!)).
  - assert (HI': ib_inv (set_l_s L s)) by (exact (fi_prime FI _ _ _ _ HI HP)).
    forward_if (temp _t'38 (Vint (Int.repr 1))).
    { forward. entailer!. }
    { exfalso. apply H. reflexivity. }
    forward_call (Int.repr 1).
    destruct Post as [Pn Pb Pc Pr]; unfold overridePost; simpl RA_normal.
    unfold ops_post, ops_post_at, ops_locals.
    Exists 0 0 (ib_zcall z false false ibp obp ain aout) (set_l_s L s) bs bs.
    rewrite ib_nin_ge, ib_nout_ge by lia.
    entailer!.
    apply ops_out_same; auto; rep_lia.
  - forward_if (temp _t'38 (Vint (Int.repr 1))).
    { discriminate. }
    { forward. entailer!. }
    forward_call (Int.repr 1).
    destruct Post as [Pn Pb Pc Pr]; unfold overridePost; simpl RA_normal.
    unfold ops_post, ops_post_at, ops_locals.
    Exists Z_STREAM_ERROR 0 (ib_zcall z false false ibp obp ain aout) L bs bs.
    rewrite ib_nin_ge, ib_nout_ge by lia.
    entailer!.
    apply ops_out_same; auto; try rep_lia; unfold Z_STREAM_ERROR; rep_lia.
Qed.
