(* Law inflate_buffers, main: the branch inflateReset (235 <= op < 240), its assert, reset = 1. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.ResetKit5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_buffers.IBLawCS Zlib.proof.harness.inflate_buffers.IBGlobals
               Zlib.proof.harness.inflate_buffers.IBFacts Zlib.proof.harness.inflate_buffers.IBMainKit.
Require Import Zlib.harness.x_inflate_buffers.code.
Require Import Zlib.proof.crc32.Spec.

(* a live stream as inflateReset takes it *)
Lemma ib_istream_rst gv shs vs z L:
  isptr vs -> istream gv shs vs z (Some L) |-- rstream_opt gv shs vs z (rst_of gv (Some L)).
Proof.
  intros P. unfold rstream_opt, rstream, rst_of. rewrite if_false by (intro; subst; contradiction).
  unfold istream, state_mem. rewrite state_rep_v_eq. Intros.
  match goal with H: live_ok L |- _ => destruct H as (SP & SW & _) end.
  entailer!. split; [apply (sw_mode _ SW) | apply (sw_wbits _ SW)].
Qed.

(* inflateReset (Spec5.reset_f, patch F8) keeps the stream live and the harness invariant: without bit 3 of wrap it
   is the plain reset (fi_reset); with bit 3 it first frees the window and sets wbits = 0, which is live because
   bit 3 comes only with bit 0 or 1 (Inv.wrap_land8: a wrapped stream before its header) *)
Lemma ib_reset_full (FI: ib_facts) (L: live) : live_ok L -> ib_inv L ->
  live_ok (set_l_s L (reset_full_s (l_s L))) /\ ib_inv (set_l_s L (reset_full_s (l_s L))).
Proof.
  intros HL HI. unfold reset_full_s, reset_hdr_s.
  destruct (Z.eqb_spec (Z.land (i_wrap (l_s L)) 8) 0) as [E | H8]; [exact (fi_reset FI L HL HI) | ].
  split.
  2: { unfold ib_inv, ib_inv_s. rs_simpl. split; [reflexivity | lia]. }
  destruct L as [sp winp s h headp hsh xb nb cb].
  destruct HL as (P & W & M & HW & W3 & HS & WB0 & HD & WF).
  cbn [l_s l_sp l_h l_hsh l_xb l_nb l_cb set_l_s] in *.
  pose proof (wrap_land8 _ (sw_wrap _ W) H8) as H3.
  split; [exact P | ]. split; [ | split; [ | split; [exact HW | split; [ | split; [exact HS | ]]]]].
  - destruct W. constructor; rs_simpl; auto;
      try (unfold HEAD, SYNC, srange, urange, lrange, tref_ok, ENOUGH_CODES in *; rep_lia).
    split; [reflexivity | constructor].
  - constructor; rs_simpl; repeat split; intros; exfalso;
      try (apply head_not_decode; assumption);
      unfold HEAD, LENLENS, CODELENS, LENEXT, DISTEXT, MATCH, DIST in *; lia.
  - destruct W3. constructor; rs_simpl; auto; intros HM;
      try (exfalso; apply head_not_decode; exact HM);
      try (unfold HEAD, LENEXT, DISTEXT in *; lia).
  - rs_simpl. split; [intros _; split; [exact H3 | reflexivity] | ]. split; [intro; discriminate | ].
    intros _ _. split; [reflexivity | left; reflexivity].
Qed.

Lemma seg_reset_ok {Espec: OracleKind} gv vs vosn vdl srcp src pos aout flush arg op innull outnull stop ain ibp obp q bs z L
    Fr (Post: ret_assert) :
  ops_hyps srcp src pos aout flush arg op innull outnull stop ain ibp obp q bs L -> 235 <= op < 240 ->
  semax Delta_m (ops_pre gv vs vosn vdl srcp src pos aout flush arg op innull outnull stop ain ibp obp q bs z L Fr)
    seg_reset
    (overridePost (ops_post gv vs vosn vdl srcp src pos aout flush arg op innull outnull stop ain ibp obp q z Fr) Post).
Proof.
  intros H Hop.
  destruct H as (FI & HI & Hpos & Hain & Hpa & Hsrc & Hsb & Haout & Hbsl & Hbsb & Hfl & Harg & Hopr & Hin & Hout & Hst & Psrc & Pib & Pob & Pq).
  unfold ops_pre, ops_locals.
  assert_PROP (isptr vs) as Pvs by entailer!.
  unfold seg_reset, Delta_m, Gmain_k. simplify_func_tycontext. abbreviate_semax.
  rewrite ib_nin_ge, ib_nout_ge by lia.
  set (zc := ib_zcall z false false ibp obp ain aout).
  assert_PROP (zf_ok zc /\ live_ok L) as ZL by (unfold istream; entailer!).
  destruct ZL as (ZOK & LOK).
  forward_call (gv, Tsh, vs, zc, rst_of gv (Some L)).
  { sep_apply (ib_istream_rst gv Tsh vs zc L Pvs). cancel. }
  { unfold reset_pre, rs_live. rewrite if_false by (intro; subst; contradiction).
    intros _. apply (ib_reset_full FI L LOK HI). }
  unfold reset_post, reset_ret, rs_live. rewrite !if_false by (intro; subst; contradiction). unfold rst_of. cbv iota.
  change (fst3 (reset_f zc L)) with Z_OK. rewrite Z.eqb_refl.
  change (snd3 (reset_f zc L)) with (reset_keep_z zc (reset_full_s (l_s L))).
  change (thd3 (reset_f zc L)) with (set_l_s L (reset_full_s (l_s L))).
  change Z_OK with 0.
  forward_call (Int.repr 1).
  forward.
  destruct Post as [Pn Pb Pc Pr]; unfold overridePost; simpl RA_normal.
  destruct (ib_reset_full FI L LOK HI) as (LOK' & HI').
  unfold ops_post, ops_post_at, ops_locals.
  Exists 0 1 (reset_keep_z zc (reset_full_s (l_s L))) (set_l_s L (reset_full_s (l_s L))) bs bs.
  rewrite ib_nin_ge, ib_nout_ge by lia.
  entailer!.
  destruct ZOK as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6). unfold zc in *.
  cbn [ib_zcall zf_ai zf_ao zf_tin zf_tout zf_ni zf_no] in *.
  unfold ops_out, reset_keep_z; cbn [ib_zcall zf_ai zf_ao zf_tin zf_tout zf_ni zf_no].
  rewrite !Z.sub_diag.
  repeat split; auto; try rep_lia; try discriminate.
  all: destruct ibp, obp; try contradiction; simpl; rewrite ?Ptrofs.add_zero; reflexivity.
Qed.
