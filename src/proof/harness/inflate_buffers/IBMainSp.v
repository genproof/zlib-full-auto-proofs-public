(* Law inflate_buffers, main: the branch inflateSyncPoint (op >= 254) and its assert. *)
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

Lemma seg_sp_ok {Espec: OracleKind} gv vs vosn vdl srcp src pos aout flush arg op innull outnull stop ain ibp obp q bs z L
    Fr (Post: ret_assert) :
  ops_hyps srcp src pos aout flush arg op innull outnull stop ain ibp obp q bs L -> 254 <= op ->
  semax Delta_m (ops_pre gv vs vosn vdl srcp src pos aout flush arg op innull outnull stop ain ibp obp q bs z L Fr)
    seg_sp
    (overridePost (ops_post gv vs vosn vdl srcp src pos aout flush arg op innull outnull stop ain ibp obp q z Fr) Post).
Proof.
  intros H Hop.
  destruct H as (FI & HI & Hpos & Hain & Hpa & Hsrc & Hsb & Haout & Hbsl & Hbsb & Hfl & Harg & Hopr & Hin & Hout & Hst & Psrc & Pib & Pob & Pq).
  unfold ops_pre, ops_locals.
  assert_PROP (isptr vs) as Pvs by entailer!.
  unfold seg_sp, Delta_m, Gmain_k. simplify_func_tycontext. abbreviate_semax.
  forward_call (gv, Tsh, vs, ib_zcall z (ib_nin op innull) (ib_nout op outnull) ibp obp ain aout, Some L).
  { rewrite ib_istream_opt by auto. cancel. }
  rewrite ib_istream_opt, ib_is_live by auto.
  set (sv := syncpoint_val (l_s L)).
  assert (Hsv: sv = 0 \/ sv = 1) by (unfold sv, syncpoint_val; destruct (_ && _)%bool; auto).
  clearbody sv.
  forward_if (PROP () LOCAL (temp _t'45 (Vint (Int.repr 1)); temp _r (Vint (Int.repr sv)); temp _reset (Vint (Int.repr 0));
     temp _tin (Vlong (Int64.repr (zf_tin z))); temp _tout (Vlong (Int64.repr (zf_tout z)));
     temp _nin (Vint (Int.repr (if ib_nin op innull then 1 else 0)));
     temp _nout (Vint (Int.repr (if ib_nout op outnull then 1 else 0)));
     temp _ib ibp; temp _ob obp; temp _ain (Vint (Int.repr ain));
     temp _aout (Vint (Int.repr (aout))); temp _flush (Vint (Int.repr flush)); temp _arg (Vint (Int.repr arg));
     temp _op (Vint (Int.repr op)); temp _in_null (Vint (Int.repr innull)); temp _out_null (Vint (Int.repr outnull));
     temp _stop (Vint (Int.repr stop));
     temp _n (Vint (Int.repr (Zlength src))); temp _src srcp; temp _pos (Vint (Int.repr pos));
     lvar _dl tuint vdl; lvar _osnap (tptr tuchar) vosn; lvar _s (Tstruct _z_stream_s noattr) vs; gvars gv)
   SEP (istream gv Tsh vs (ib_zcall z (ib_nin op innull) (ib_nout op outnull) ibp obp ain (aout)) (Some L);
        zfuncs gv; mem_mgr gv; tables_rep Ers gv;
        crc_table_at Ers gv; malloc_token Ews (tarray tuchar (Zlength src)) srcp;
        data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) srcp;
        malloc_token Ews (tarray tuchar ain) ibp;
        data_at Ews (tarray tuchar ain) (bytes_rep (sublist pos (pos + ain) src)) ibp;
        malloc_token Ews (tarray tuchar (aout)) obp;
        data_at Ews (tarray tuchar (aout)) (bytes_rep bs) obp;
        data_at Tsh (tptr tuchar) q vosn; malloc_token Ews (tarray tuchar (aout)) q;
        data_at Ews (tarray tuchar (aout)) (bytes_rep bs) q; data_at_ Tsh tuint vdl; Fr)).
  { forward. entailer!. }
  { forward. entailer!. destruct Hsv as [-> | ->]; [contradiction | reflexivity]. }
  forward_call (Int.repr 1).
  destruct Post as [Pn Pb Pc Pr]; unfold overridePost; simpl RA_normal.
  rewrite ib_nin_ge, ib_nout_ge in * by lia.
  assert_PROP (zf_ok (ib_zcall z false false ibp obp ain aout)) as ZOK by (unfold istream; entailer!).
  unfold ops_post, ops_post_at, ops_locals.
  Exists sv 0 (ib_zcall z false false ibp obp ain aout) L bs bs.
  rewrite ib_nin_ge, ib_nout_ge by lia.
  entailer!.
  apply ops_out_same; auto; destruct Hsv as [-> | ->]; rep_lia.
Qed.
