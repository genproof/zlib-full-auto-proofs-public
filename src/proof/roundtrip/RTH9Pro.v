(* The prologue of inflate()'s body for a call of any uInt size (RTH9Parts.pro_part9_stmt).  The script is
   round 1's RTHPro6.pro_part6 (a port of inflate_api/Body5Pro.v to the headless loop state): it never uses
   the bounds avail_in, avail_out <= 2^31 - 1 of RTHCase.pro_part6_stmt (have and left are the uInt values
   themselves).  It is cut into pieces that check quickly: this file treats a Z_NULL or ended stream and calls
   inflateStateCheck; RTH9ProN (next_out = Z_NULL) and RTH9ProO (the other argument checks, with RTH9ProB,
   RTH9ProMN, RTH9ProMB) continue, RTH9ProT1, RTH9ProT2 and RTH9ProP end the prologue; RTH9ProKit holds what
   they share. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTHCase.
Require Import Zlib.proof.inflate_api.Body5Conv.
Require Import Zlib.proof.inflate_api.Body5Pro.
Require Import Zlib.proof.roundtrip.RTH9Parts.
Require Import Zlib.proof.roundtrip.RTH9ProKit.
Require Import Zlib.proof.roundtrip.RTH9ProN.
Require Import Zlib.proof.roundtrip.RTH9ProO.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.
Local Opaque denote_tc_test_eq.

Lemma pro_part9 : pro_part9_stmt.
Proof.
intros Espec gv shs strmp z st ib inp ob flush gsh tsh itok otok vh vl vb Hd R
  HF HG HT HIT HOT HNI HIB HOB HBAD.
destruct R as [Rn Rb Rc Rr]. simpl RA_return in HBAD.
unfold pro_pre6.
cbv beta iota zeta delta [inflate_pre inflate_leave0 f_inflate fn_body].
forward.
destruct (eq_dec strmp nullval) as [EN|NN].
{ (* Z_NULL stream *)
  subst strmp.
  replace (is_live nullval st) with (@None live) by reflexivity.
  forward_call (nullval, shs, default_val t_strm, nullval, 0, false, gv).
  { rewrite if_true by auto. cancel. }
  rewrite !if_true by auto.
  forward_if (temp _t'2 (Vint (Int.repr 1))).
  { forward. entailer!. }
  { exfalso. inv H. }
  forward_if (temp _t'3 (Vint (Int.repr 1))).
  { forward. entailer!. }
  { exfalso. inv H. }
  forward_if (PROP (False) LOCAL () SEP ()).
  2:{ exfalso. inv H. }
  eapply semax_pre; [ | apply semax_return].
  apply andp_right. { entailer!. }
  eapply derives_trans; [ | apply (HBAD (or_introl eq_refl))].
  apply andp_right; [apply andp_left1; apply derives_refl | ].
  unfold istream_opt. rewrite if_true by auto. unfold htok6. simpl bufs_opt.
  entailer!. }
assert (ISL: is_live strmp st = st) by (unfold is_live; rewrite if_false by auto; reflexivity).
rewrite ISL in HBAD |- *.
unfold istream_opt at 1. rewrite if_false by auto. unfold istream at 1.
destruct st as [L|].
2:{ (* ended stream *)
  rewrite zstrm_at_eq. Intros.
  forward_call (strmp, shs, zsv gv z nullval, nullval, 0, false, gv).
  { rewrite if_false by auto. cancel. }
  { right. split; [auto | unfold stream_ok_val, zsv; simpl; auto]. }
  rewrite !if_false by auto. Intros.
  forward_if (temp _t'2 (Vint (Int.repr 1))).
  { forward. entailer!. }
  { exfalso. inv H1. }
  forward_if (temp _t'3 (Vint (Int.repr 1))).
  { forward. entailer!. }
  { exfalso. inv H1. }
  forward_if (PROP (False) LOCAL () SEP ()).
  2:{ exfalso. inv H1. }
  eapply semax_pre; [ | apply semax_return].
  apply andp_right. { entailer!. }
  eapply derives_trans; [ | apply (HBAD (or_introl ISL))].
  apply andp_right; [apply andp_left1; apply derives_refl | ].
  unfold istream_opt. rewrite if_false by auto. unfold istream. rewrite zstrm_at_eq.
  unfold htok6. simpl bufs_opt.
  entailer!. }
Intros. rename H into ZOK, H0 into WS, H1 into LOK.
pose proof LOK as (LP & LS & LM & LH & LS3 & LW & LW0 & LHD & LWIN).
assert (MC: ((HEAD <=? i_mode (l_s L)) && (i_mode (l_s L) <=? SYNC))%bool = true).
{ pose proof (sw_mode _ LS). apply andb_true_intro; split; apply Z.leb_le; lia. }
unfold state_mem. rewrite zstrm_at_eq, state_rep_split. Intros.
forward_call (strmp, shs, zsv gv z (l_sp L), l_sp L, i_mode (l_s L), true, gv).
{ rewrite if_false by auto. cancel. }
{ pose proof (sw_mode _ LS). unfold HEAD, SYNC in *.
  split3; [right; split; [auto | unfold stream_ok_val, zsv; simpl; auto] | | ]; rep_lia. }
rewrite !if_false by auto. rewrite MC. Intros. unfold zsv.
remember (gv _zcalloc) as zca eqn:Hzca. remember (gv _zcfree) as zcf eqn:Hzcf.
destruct ob as [o|].
2:{ (* next_out = Z_NULL *)
  subst zca zcf. eapply pro9_outnull; pro9_ctx_ok. }
destruct o as [osh op olo on oc].
subst zca zcf. eapply pro9_outbuf; pro9_ctx_ok.
Qed.
