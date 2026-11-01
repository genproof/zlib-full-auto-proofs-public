(** * deflate_fast with up to 2^32 - 1 bytes of output space

    LTCFastGlue.fast_from_parts, LTCFast2.fast_ok2 and LTCStillFast.still_fast_ok for [compress_prew]
    (DetCoreKit.v).  Their proofs use [zin_ok] only through [zall]; the proofs are the originals with
    [zwide_zall] for [zin_ok_zall]. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.DetCoreKit.
Require Import Zlib.proof.deflate.LTCFastGlue Zlib.proof.deflate.LTCFastRefill Zlib.proof.deflate.LTCFastSearch Zlib.proof.deflate.LTCFastLit2 Zlib.proof.deflate.LTCFastMatch2 Zlib.proof.deflate.LTCFastInsLoop Zlib.proof.deflate.LTCFastFbw Zlib.proof.deflate.LTCFastBflush Zlib.proof.deflate.LTCFastTail Zlib.proof.deflate.LTCStillFastKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** The kernel must never compute [loop FUEL]. *)
Local Strategy opaque [loop loop2].

(** LTCFastGlue.fast_from_parts. *)
Theorem fast_from_partsw :
  refill_stmt -> search_stmt -> lit_stmt -> match_stmt -> bflush_stmt -> tail_stmt -> fast_specw.
Proof.
  intros Hre Hse Hli Hma Hbf Hta s z flush (HW & Ho & Hq & Hfl & Hzi & Hwr & Ha) Hfn.
  pose proof (zwide_zall z Hzi) as Hz.
  destruct (loop_ok Hre Hse Hli Hma Hbf s z flush HW Ho Hq Hz Ha Hfn Hfl) as (r & Er & Hr).
  unfold c_deflate_fast. rewrite Er. cbn [bind].
  destruct r as [[s1 z1] [bs|]]; cbv beta iota delta [loop_res] in Hr.
  - destruct Hr as (evs & Hc & Hb). exists s1, z1, bs, evs. split; [reflexivity|].
    apply cpost_of; assumption.
  - destruct Hr as (evs & HFI & Hla & Hai & Hnf & Hss).
    destruct (FI_parts _ _ _ _ _ _ HFI Hfn) as (HW1 & Ho1 & Hq1 & Hz1 & Ha1 & Hfn1).
    destruct (Hta s1 z1 flush HW1 Ho1 Hq1 Hz1 Ha1 Hfn1 Hfl Hnf Hla Hai Hss)
      as (s' & z' & bs & evs2 & Et & Hc & Hb).
    exists s', z', bs, (evs ++ evs2). split; [exact Et|].
    apply cpost_of.
    + eapply crel_trans; [exact Hz|exact Ha|apply FI_crel; exact HFI|exact Hc].
    + destruct (FI_sp _ _ _ _ _ _ HFI) as (P1 & A1).
      eapply (bpost_start s s1 z z1); [exact P1|exact A1|apply (FI_last _ _ _ _ _ _ HFI)|exact Hb].
Qed.

(** LTCFast2.fast_ok2. *)
Theorem fast_ok2w : fill_spec -> ins_spec -> lm_spec -> tally_spec2 -> fbo_spec -> fpend_spec2 -> fast_specw.
Proof.
  intros Hfi Hin Hlm Hta Hfb _. apply fast_from_partsw.
  - exact (refill_ok Hfi).
  - exact (search_ok Hin Hlm).
  - exact (lit_ok2 Hta).
  - exact (match_ok2 Hta (insloop_ok Hin)).
  - exact (bflush_ok (fbw_ok Hfb)).
  - exact (tail_ok (fbw_ok Hfb)).
Qed.

(** LTCStillFast.still_fast_ok. *)
Theorem still_fast_okw : fill_idem_spec -> fill_spec -> ins_spec -> lm_spec -> tally_spec2 -> fbo_spec ->
  fpend_spec2 -> fast_specw ->
  forall s z flush, compress_prew s z flush -> still_at s -> fn_of s = 1 -> still_concl c_deflate_fast s z flush.
Proof.
  intros Hidem Hfill Hin Hlm Hta Hfb _ _ s z flush Hpre (Hst & Hbs & Hla) Hfn s' z' bs Hrun Hni.
  destruct Hpre as (HW & Ho & Hq & Hfl & Hzi & Hwr & Ha).
  pose proof (zwide_zall z Hzi) as Hz.
  assert (Hfp : fill_pre s).
  { destruct HW as (Hp & Hs & Hpos & Hw & Hh & _).
    assert (Hlev := fn_of_fast s Hp Hfn).
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
  assert (Hn0 : need_min_lookahead s = true).
  { unfold need_min_lookahead. rewrite Hla. reflexivity. }
  assert (Hk0 : 0 <= k1) by (destruct Hzs as (_ & Hk1 & _); lia).
  destruct (Z.eq_dec k1 0) as [Ek|Nk].
  - (* nothing read: the first iteration leaves at once *)
    subst k1.
    assert (Hn1 : need_min_lookahead s1 = true).
    { unfold need_min_lookahead. rewrite El, Hla. reflexivity. }
    destruct (Z.eqb_spec flush Z_NO_FLUSH) as [Ef|Nf].
    + assert (Eb1 : df_body flush (s, z) = Some (inr (s1, z1, Some need_more))).
      { rewrite (fast_body_fill s z flush s1 z1 Hn0 Hfw), Hn1, Ef. reflexivity. }
      rewrite (fast_exit_some s z flush s1 z1 s' z' bs Eb1 Hrun). exact Hs1.
    + assert (Eb1 : df_body flush (s, z) = Some (inr (s1, z1, None))).
      { rewrite (fast_body_fill s z flush s1 z1 Hn0 Hfw), Hn1.
        destruct (Z.eqb_spec flush Z_NO_FLUSH) as [E|_]; [contradiction|].
        rewrite El, Hla. reflexivity. }
      rewrite (fast_exit_none s z flush s1 z1 s' z' bs Eb1 Hrun). exact Hs1.
  - (* RESTART: the run is the run from the state after the fill, which reads more *)
    destruct (refill_fill_FI s z flush s1 z1 k1 0 HW Ho Hq Hz Ha Hfn Hfp1 Hk Hzs Es Eb El)
      as (HFI & Ews & Ewz & Eai).
    destruct (FI_parts _ _ _ _ _ _ HFI Hfn) as (HW1 & Ho1 & Hq1 & Hz1 & Ha1 & Hfn1).
    assert (Ebody : df_body flush (s, z) = df_body flush (s1, z1)).
    { rewrite (fast_body_fill s z flush s1 z1 Hn0 Hfw).
      destruct (need_min_lookahead s1) eqn:Hn1.
      - assert (Hai1 : z_avail_in z1 = 0).
        { destruct Hor as [Hor|Hor]; [|exact Hor].
          unfold need_min_lookahead in Hn1. apply Z.ltb_lt in Hn1. lia. }
        assert (Hid : c_fill_window s1 z1 = Some (s1, z1)).
        { apply Hidem; [exact Hfp1|exact Hz1|exact Ha1|exact Hai1| |].
          - rewrite Ews. unfold MAX_DIST in *. rewrite Ews. exact Hss.
          - rewrite Ewz. exact Hhw. }
        rewrite (fast_body_fill s1 z1 flush s1 z1 Hn1 Hid), Hn1. reflexivity.
      - rewrite (fast_body_nofill s1 z1 flush Hn1). cbn [andb]. rewrite El, Hla.
        destruct (Z.eqb_spec (0 + k1) 0) as [E|_]; [lia|]. reflexivity. }
    rewrite (fast_restart s z flush s1 z1 Ebody) in Hrun.
    destruct (fast_run_zall Hfill Hin Hlm Hta Hfb s1 z1 flush HW1 Ho1 Hq1 Hz1 Ha1 Hfn1 Hfl)
      as (s2 & z2 & bs2 & k & x & Er & Hzs2).
    rewrite Er in Hrun. inversion Hrun; subst s2 z2 bs2.
    destruct Hzs2 as (_ & Hk2 & En2 & _). destruct Hzs as (_ & _ & En1 & _).
    lia.
Qed.
