(* Law inflate_buffers, main: the branch inflateReset2(&s, (int) arg) (240 <= op < 245), its asserts, reset = (r == Z_OK). *)
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

Lemma ib_istream_rst gv shs vs z L:
  isptr vs -> istream gv shs vs z (Some L) |-- rstream_opt gv shs vs z (rst_of gv (Some L)).
Proof.
  intros P. unfold istream, rstream_opt, rstream, rst_of, state_mem.
  rewrite if_false by (intro; subst; contradiction).
  rewrite state_rep_v_eq. Intros.
  match goal with H: live_ok L |- _ => destruct H as (LP & LS & _) end.
  pose proof (sw_mode _ LS). pose proof (sw_wbits _ LS).
  entailer!.
Qed.

Lemma ib_rst_istream gv shs vs z L:
  isptr vs -> live_ok L -> rstream_opt gv shs vs z (rst_of gv (Some L)) |-- istream gv shs vs z (Some L).
Proof.
  intros P LOK. unfold istream, rstream_opt, rstream, rst_of, state_mem.
  rewrite if_false by (intro; subst; contradiction).
  rewrite state_rep_v_eq. Intros.
  entailer!.
Qed.

Lemma ib_wbits_ok_none w: wbits_ok w = true <-> reset2_wb w <> None.
Proof. unfold wbits_ok. destruct (reset2_wb w); split; congruence. Qed.

Lemma seg_reset2_ok {Espec: OracleKind} gv vs vosn vdl srcp src pos aout flush arg op innull outnull stop ain ibp obp q bs z L
    Fr (Post: ret_assert) :
  ops_hyps srcp src pos aout flush arg op innull outnull stop ain ibp obp q bs L -> 240 <= op < 245 ->
  semax Delta_m (ops_pre gv vs vosn vdl srcp src pos aout flush arg op innull outnull stop ain ibp obp q bs z L Fr)
    seg_reset2
    (overridePost (ops_post gv vs vosn vdl srcp src pos aout flush arg op innull outnull stop ain ibp obp q z Fr) Post).
Proof.
  intros H Hop.
  destruct H as (FI & HI & Hpos & Hain & Hpa & Hsrc & Hsb & Haout & Hbsl & Hbsb & Hfl & Harg & Hopr & Hin & Hout & Hst & Psrc & Pib & Pob & Pq).
  unfold ops_pre, ops_locals.
  assert_PROP (isptr vs) as Pvs by entailer!.
  rewrite ib_nin_ge, ib_nout_ge by lia.
  unfold seg_reset2, Delta_m, Gmain_k. simplify_func_tycontext. abbreviate_semax.
  set (zc := ib_zcall z false false ibp obp ain aout).
  assert_PROP (zf_ok zc /\ live_ok L) as ZL by (rewrite ib_istream_unfold; entailer!). destruct ZL as [ZOK LOK].
  set (w := Int.signed (Int.repr arg)).
  assert (Hw: Int.repr w = Int.repr arg) by apply Int.repr_signed.
  assert (Hwr: Int.min_signed <= w <= Int.max_signed) by apply Int.signed_range.
  sep_apply (ib_istream_rst gv Tsh vs zc L Pvs).
  forward_call (gv, Tsh, vs, zc, rst_of gv (Some L), w).
  { rewrite Hw. entailer!. }
  { unfold reset_pre, rs_live, rst_of. rewrite if_false by (intro; subst; contradiction).
    unfold reset2_f. destruct (reset2_wb w) as [[wr wb]|] eqn:E; [|discriminate]. intros _.
    apply (fi_reset2 FI L w wr wb LOK HI E). }
  unfold reset_ret, reset_post, rs_live, rst_of. rewrite if_false by (intro; subst; contradiction).
  forward_call w.
  { rewrite Hw. entailer!. }
  unfold reset2_f, wbits_ok.
  destruct (reset2_wb w) as [[wr wb]|] eqn:E.
  - unfold fst3, snd3, thd3; cbn [fst snd]. rewrite Z.eqb_refl.
    forward_call (Int.repr 1).
    forward_if (temp _t'42 (Vint (Int.repr 1))).
    { forward. entailer!. }
    { exfalso; apply H; reflexivity. }
    forward_call (Int.repr 1).
    forward.
    destruct (fi_reset2 FI L w wr wb LOK HI E) as [LOK2 HI2].
    set (s2 := reset2_s wr wb (l_s L)) in *.
    assert_PROP (zf_ok (reset_keep_z zc s2)) as ZOK2 by (unfold istream; entailer!).
    destruct Post as [Pn Pb Pc Pr]; unfold overridePost; simpl RA_normal.
    unfold ops_post, ops_post_at, ops_locals.
    Exists 0 1 (reset_keep_z zc s2) (set_l_s L s2) bs bs.
    rewrite ib_nin_ge, ib_nout_ge by lia.
    entailer!.
    destruct ZOK as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6).
    unfold zc, ops_out, reset_keep_z, ib_zcall in *; cbn [zf_ai zf_ao zf_tin zf_tout zf_ni zf_no] in *.
    rewrite !Z.sub_diag.
    repeat split; auto; try lia; try discriminate.
    all: destruct ibp, obp; try contradiction; simpl; rewrite ?Ptrofs.add_zero; reflexivity.
  - unfold fst3, snd3, thd3; cbn [fst snd]. change (Z_STREAM_ERROR =? Z_OK) with false. cbv iota.
    sep_apply (ib_rst_istream gv Tsh vs zc L Pvs LOK).
    forward_call (Int.repr 1).
    forward_if (temp _t'42 (Vint (Int.repr 1))).
    { exfalso. apply repr_inj_signed in H; [unfold Z_STREAM_ERROR in H; lia | unfold Z_STREAM_ERROR; rep_lia | rep_lia]. }
    { forward. entailer!. }
    forward_call (Int.repr 1).
    forward.
    destruct Post as [Pn Pb Pc Pr]; unfold overridePost; simpl RA_normal.
    unfold ops_post, ops_post_at, ops_locals.
    Exists Z_STREAM_ERROR 0 zc L bs bs.
    rewrite ib_nin_ge, ib_nout_ge by lia.
    entailer!.
    apply ops_out_same; auto; unfold Z_STREAM_ERROR; rep_lia.
Qed.