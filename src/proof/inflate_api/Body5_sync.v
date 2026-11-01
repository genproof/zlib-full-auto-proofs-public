(* Bodies of inflate.c's API functions, version 5: api_sync_stmt (Bodies5.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.Body5_sync_kit.
Require Import Zlib.proof.inflate_api.Body5_sync0.
Require Import Zlib.proof.inflate_api.Body5_sync1.
Require Import Zlib.proof.inflate_api.Body5_sync2.
Require Import Zlib.proof.inflate_api.Body5_sync3.
Require Import Zlib.proof.inflate_api.Body5_sync3b.
Require Import Zlib.proof.inflate_api.Body5_sync4.
Require Import Zlib.proof.inflate_api.Body5_sync5.
#[local] Existing Instance Zlib.units.Inflate.CS.

Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* inflateSync                                                                                    *)

Lemma body_inflateSync {E: OracleKind}: semax_body Vprog_inflate Gp_sync f_inflateSync inflateSync_spec.
Proof.
  start_function.
  unfold istream_opt.
  destruct (eq_dec strmp nullval) as [Hn | Hn].
  - subst strmp.
    forward_call (nullval, shs, default_val t_strm, nullval, 0, false, gv).
    { simpl. cancel. }
    forward_if; [forward | discriminate].
    cancel.
  - destruct st as [L | ].
    2: { unfold istream, zstrm_at, strm_rep. Intros.
    remember (gv _zcalloc) as zca eqn:Hzca. remember (gv _zcfree) as zcf eqn:Hzcf.
    forward_call (strmp, shs, (zf_ni z, (Vint (Int.repr (zf_ai z)), (lv (zf_tin z), (zf_no z,
      (Vint (Int.repr (zf_ao z)), (lv (zf_tout z), (msg_val gv (zf_msg z), (nullval, (zca, (zcf,
      (nullval, (zv (zf_dt z), (lv (zf_adler z), zf_res z))))))))))))), nullval, 0, false, gv).
    { destruct (eq_dec strmp nullval); [contradiction | ]. cancel. }
    { right. split; [auto | ]. subst zca zcf. repeat split. }
    destruct (eq_dec strmp nullval); [contradiction | ].
    forward_if.
    { forward. unfold on_live, fst3, snd3, thd3, is_live, istream_opt. rewrite !if_false by auto. cbn [fst snd]. unfold istream, zstrm_at, strm_rep. entailer!. }
    { match goal with H: Int.repr 1 = Int.zero |- _ => inversion H end. } }
    destruct L as [sp winp s h headp hsh xb nb cb].
    unfold istream, state_mem, zstrm_at, strm_rep. cbn [l_sp l_winp l_s l_h l_headp]. rewrite state_rep_sync. Intros.
    match goal with H: live_ok _ |- _ => pose proof H as LOK; destruct H as (Hsp & SW & MW & HW & SW3 & HS & WW) end.
    cbn [l_sp l_s l_h] in Hsp, SW, MW, HW, SW3, HS, WW.
    remember (gv _zcalloc) as zca eqn:Hzca. remember (gv _zcfree) as zcf eqn:Hzcf.
    forward_call (strmp, shs, (zf_ni z, (Vint (Int.repr (zf_ai z)), (lv (zf_tin z), (zf_no z,
      (Vint (Int.repr (zf_ao z)), (lv (zf_tout z), (msg_val gv (zf_msg z), (sp, (zca, (zcf,
      (nullval, (zv (zf_dt z), (lv (zf_adler z), zf_res z))))))))))))), sp, i_mode s, true, gv).
    { destruct (eq_dec strmp nullval); [contradiction | ]. cancel. }
    { pose proof (sw_mode _ SW). split; [ | unfold HEAD, SYNC in *; rep_lia].
      right. split; [auto | ]. subst zca zcf. repeat split. }
    destruct (eq_dec strmp nullval) as [Hx | Hx]; [contradiction | ].
    pose proof (sw_mode _ SW) as HMD.
    rewrite (proj2 (Z.leb_le _ _) (proj1 HMD)), (proj2 (Z.leb_le _ _) (proj2 HMD)). simpl andb. cbv iota.
    forward_if; [contradiction | ]. Intros.
    destruct ib as [ | ish ip ilo ilen ic]; [contradiction | ].
    pose proof H0 as HIN.
    destruct H0 as (ISH & IP & ILO & ILEN & IC & IMAX & ISUB & IBY).
    pose proof H3 as ZOK. destruct H3 as (ZAI & ZAO & ZTIN & ZTOUT & ZDT & ZADL).
    pose proof (sw_bits _ SW) as HBITS.
    (* the rest of the body: segments 0 to 5 *)
    assert (NI: zf_ni z = offset_val ilo ip) by (rewrite H1; simpl; f_equal; lia).
    assert (HY: sync_hyps shs strmp z ish ip ilo ilen ic inp)
      by (exact (conj HIN (conj NI (conj H2 (conj ZOK (conj H4 Hn)))))).
    drop_LOCAL 0%nat. subst zca zcf.
    exact (sync_part0 (sync_part1 (sync_part2 (sync_part3 (sync_part3b (sync_part4 sync_part5))))) _ gv shs strmp z sp winp s h
             headp hsh xb nb cb ish ip ilo ilen ic inp v_buf HY LOK HMD).
Qed.

Lemma api5_sync : api_sync_stmt.
Proof.
  intros E. split; [apply body_syncsearch | apply body_inflateSync].
Qed.
