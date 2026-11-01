(** * deflate_rle with up to 2^32 - 1 bytes of output space

    LTCRleGlue.rle_from_parts, LTCRle2.rle_ok2 and LTCStillRle.still_rle_ok for [compress_prew]
    (DetCoreKit.v).  Their proofs use [zin_ok] only through [zall]; the proofs are the originals with
    [zwide_zall] for [zin_ok_zall]. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.DetCoreKit.
Require Import Zlib.proof.deflate.LTCRleGlue Zlib.proof.deflate.LTCRleRefill Zlib.proof.deflate.LTCRleScan Zlib.proof.deflate.LTCRleLit Zlib.proof.deflate.LTCRleDist Zlib.proof.deflate.LTCRleFbw Zlib.proof.deflate.LTCRleBflush Zlib.proof.deflate.LTCRleTail Zlib.proof.deflate.LTCStillRleKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** The kernel must never compute [loop FUEL]. *)
Local Strategy opaque [loop loop2].

(** LTCRleGlue.rle_from_parts. *)
Theorem rle_from_partsw :
  rrefill_stmt -> rscan_stmt -> rlit_stmt -> rdist_stmt -> rbflush_stmt -> rtail_stmt -> rle_specw.
Proof.
  intros Hre Hsc Hli Hdi Hbf Hta s z flush (HW & Ho & Hq & Hfl & Hzi & Hwr & Ha) Hfn.
  pose proof (zwide_zall z Hzi) as Hz.
  destruct (rloop_ok Hre Hsc Hli Hdi Hbf s z flush HW Ho Hq Hz Ha Hfn Hfl) as ([[s1 z1] o] & E & H).
  unfold c_deflate_rle. rewrite E. cbn [bind].
  destruct o as [bs|].
  - destruct H as (evs & Hc & Hb). exists s1, z1, bs, evs. split; [reflexivity|].
    apply cpost_of; assumption.
  - destruct H as (evs & HFI & Hl & Hai & Hf & Hss).
    destruct (rFI_parts _ _ _ _ _ _ HFI Hfn) as (HW1 & Ho1 & Hq1 & Hz1 & Ha1 & Hfn1).
    destruct (Hta s1 z1 flush HW1 Ho1 Hq1 Hz1 Ha1 Hfn1 Hfl Hf Hl Hai Hss) as (s2 & z2 & bs & evs2 & E2 & Hc2 & Hb2).
    exists s2, z2, bs, (evs ++ evs2). split; [exact E2|].
    apply cpost_of.
    + eapply rg_crel_trans; [exact Hz|exact Ha|apply rFI_crel; exact HFI|exact Hc2].
    + destruct (rFI_sp _ _ _ _ _ _ HFI) as (P1 & A1).
      eapply rg_bpost_start; [exact P1|exact A1|apply (rFI_last _ _ _ _ _ _ HFI)|exact Hb2].
Qed.

(** LTCRle2.rle_ok2. *)
Theorem rle_ok2w : fill_spec -> tally_spec2 -> fbo_spec -> fpend_spec2 -> rle_specw.
Proof.
  intros Hfill Htal Hfbo _.
  pose proof (rfbw_ok Hfbo) as Hfbw.
  apply rle_from_partsw.
  - exact (rrefill_ok Hfill).
  - exact rscan_ok.
  - exact (rlit_ok Htal).
  - exact (rdist_ok Htal).
  - exact (rbflush_ok Hfbw).
  - exact (rtail_ok Hfbw).
Qed.

(** LTCStillRle.still_rle_ok. *)
Theorem still_rle_okw : fill_idem_spec -> fill_spec -> tally_spec2 -> fbo_spec -> fpend_spec2 -> rle_specw ->
  forall s z flush, compress_prew s z flush -> still_at s -> fn_of s = 4 -> still_concl c_deflate_rle s z flush.
Proof.
  intros Hidem Hfill Hta Hfb _ _ s z flush Hpre (Hst & Hbs & Hla) Hfn s' z' bs Hrun Hni.
  destruct Hpre as (HW & Ho & Hq & Hfl & Hzi & Hwr & Ha).
  pose proof (zwide_zall z Hzi) as Hz.
  assert (Hfp : fill_pre s).
  { destruct HW as (Hp & Hs & Hpos & Hw & Hh & _).
    assert (Hlev := fn_of_rle s Hp Hfn).
    unfold whash in Hh. destruct (Z.eqb_spec (d_level s) 0) as [E|N]; [lia|].
    destruct Hh as (_ & Hc).
    split; [exact Hp|]. split; [exact Hs|]. split; [exact Hpos|]. split; [exact Hw|exact Hc]. }
  assert (Hws : 512 <= d_w_size s).
  { destruct HW as ((Hb & Hs & _) & _). rewrite Hs. change 512 with (2 ^ 9).
    apply Z.pow_le_mono_r; lia. }
  destruct (Hfill s z Hfp Hz Ha) as (s1 & z1 & k1 & d & Hfw & Hfp1 & Hk & Hzs & Hd & Es & Eb & _ & _ &
    El & Hss & Hor & Hhw).
  assert (Hd0 : d = 0).
  { destruct Hd as [Hd|(_ & Hd)]; [exact Hd|]. unfold MAX_DIST in Hd.
    replace MIN_LOOKAHEAD with 262 in Hd by reflexivity. lia. }
  subst d.
  assert (Hs1 : d_strstart s1 = 0) by lia.
  assert (Hn0 : need_rle s = true).
  { unfold need_rle. rewrite Hla. reflexivity. }
  assert (Hk0 : 0 <= k1) by (destruct Hzs as (_ & Hk1 & _); lia).
  destruct (Z.eq_dec k1 0) as [Ek|Nk].
  - (* nothing read: the first iteration leaves at once *)
    subst k1.
    assert (Hn1 : need_rle s1 = true).
    { unfold need_rle. rewrite El, Hla. reflexivity. }
    rewrite (rle_k0 s z flush s1 z1 s' z' bs Hn0 Hfw Hn1 ltac:(lia) Hrun). exact Hs1.
  - (* RESTART: the run is the run from the state after the fill, which reads more *)
    destruct (rrefill_fill_FI s z flush s1 z1 k1 0 HW Ho Hq Hz Ha Hfn Hfp1 Hk Hzs Es Eb El)
      as (HFI & Ews & Ewz & Eai).
    destruct (rFI_parts _ _ _ _ _ _ HFI Hfn) as (HW1 & Ho1 & Hq1 & Hz1 & Ha1 & Hfn1).
    assert (Hid : need_rle s1 = true -> c_fill_window s1 z1 = Some (s1, z1)).
    { intros Hn1.
      assert (Hai1 : z_avail_in z1 = 0).
      { destruct Hor as [Hor|Hor]; [|exact Hor].
        unfold need_rle in Hn1. apply Z.leb_le in Hn1.
        replace MIN_LOOKAHEAD with 262 in Hor by reflexivity. unfold MAX_MATCH in Hn1. lia. }
      apply Hidem; [exact Hfp1|exact Hz1|exact Ha1|exact Hai1| |].
      - rewrite Ews. unfold MAX_DIST in *. rewrite Ews. exact Hss.
      - rewrite Ewz. exact Hhw. }
    rewrite (rle_restart s z flush s1 z1 Hn0 Hfw ltac:(lia) Hid) in Hrun.
    destruct (rle_run_zall Hfill Hta Hfb s1 z1 flush HW1 Ho1 Hq1 Hz1 Ha1 Hfn1 Hfl)
      as (s2 & z2 & bs2 & k & x & Er & Hzs2).
    rewrite Er in Hrun. inversion Hrun; subst s2 z2 bs2.
    destruct Hzs2 as (_ & Hk2 & En2 & _). destruct Hzs as (_ & _ & En1 & _).
    lia.
Qed.
