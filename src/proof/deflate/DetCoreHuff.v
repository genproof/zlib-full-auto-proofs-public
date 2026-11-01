(** * deflate_huff with up to 2^32 - 1 bytes of output space

    LTCHuffLoop.huff_assembly, LTCHuff2.huff_okX and LTCStillHuff.still_huff_ok for [compress_prew]
    (DetCoreKit.v).  Their proofs use [zin_ok] only through [zall] and the avail_in bound of the loop measure,
    which [zwide] keeps; the proofs are the originals with [zwide_zall] for [zin_ok_zall]. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.DetCoreKit.
Require Import Zlib.proof.deflate.LTCHuffGlue Zlib.proof.deflate.LTCHuffLoop Zlib.proof.deflate.LTCHuffFbw Zlib.proof.deflate.LTCHuffLit Zlib.proof.deflate.LTCHuffRefill Zlib.proof.deflate.LTCHuffBflush Zlib.proof.deflate.LTCHuffTail Zlib.proof.deflate.LTCStillHuffKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** LTCHuffLoop.huff_assembly. *)
Theorem huff_assemblyw : hlit_stmt -> hrefill_stmt -> hbflush_stmt -> htail_stmt -> huff_specXw.
Proof.
  intros Hlit Href Hbfl Htail s z flush Hpre He Hfn.
  destruct Hpre as (HW & Ho & Hq & Hfl & Hzi & Hwr & Had).
  assert (Hz := zwide_zall z Hzi).
  assert (HI : HFI s z flush s z []).
  { unfold HFI. split; [exact Hz|]. split; [exact Had|]. split; [exact (hcrel_refl s z flush HW He Ho Hz Had)|].
    split; [exact Hq|]. split; [exact Hz|]. split; [exact Had|constructor]. }
  assert (Hm0 : hm (s, z) < 2 ^ Z.of_nat FUEL).
  { unfold hm; cbn [fst snd]. destruct Hzi as (_ & _ & Hai & _).
    pose proof (W_la_bound s HW). change (2 ^ Z.of_nat FUEL) with (2 ^ 40). lia. }
  destruct (hloop_measure (huff_body flush) (HP s z flush) (HQ s z flush) hm
              (huff_step Hlit Href Hbfl s z flush Hfl Hfn) FUEL (s, z) (ex_intro _ [] HI) Hm0)
    as (r & Er & Hr).
  unfold c_deflate_huff. rewrite Er. cbn [bind].
  destruct r as [[s' z'] [bs|]].
  - destruct Hr as (evs & Hc & Hb). destruct (cpost_of_h _ _ _ _ _ _ _ Hc Hb) as [Hp He'].
    exists s', z', bs, evs. split; [reflexivity|]. split; [exact Hp|exact He'].
  - destruct Hr as (evs & HI' & Hla & Hai & Hnf).
    destruct (Htail s z flush s' z' evs HI' Hfl Hfn Hnf Hla Hai) as (s2 & z2 & bs & evs' & E & Hc & Hb).
    destruct (cpost_of_h _ _ _ _ _ _ _ Hc Hb) as [Hp He'].
    exists s2, z2, bs, evs'. split; [exact E|]. split; [exact Hp|exact He'].
Qed.

(** LTCHuff2.huff_okX. *)
Theorem huff_okXw : fill_spec -> tally_spec2 -> fbo_spec -> huff_specXw.
Proof.
  intros Hfill Htally Hfbo.
  assert (Hfbw := LTCHuffFbw.hfbw_ok Hfbo).
  exact (huff_assemblyw (LTCHuffLit.hlit_ok Htally) (LTCHuffRefill.hrefill_ok Hfill)
           (LTCHuffBflush.hbflush_ok Hfbw) (LTCHuffTail.htail_ok Hfbw)).
Qed.

(** The kernel must never compute [loop FUEL]. *)
Local Strategy opaque [loop loop2].

(** LTCStillHuff.still_huff_ok. *)
Theorem still_huff_okw : fill_idem_spec -> fill_spec -> tally_spec2 -> fbo_spec -> fpend_spec2 -> huff_specXw ->
  forall s z flush, compress_prew s z flush -> huff_extra s -> still_at s -> fn_of s = 3 ->
    still_concl c_deflate_huff s z flush.
Proof.
  intros _ Hfill Htally Hfbo _ _ s z flush Hpre He Hst Hfn s' z' bs E Enext.
  destruct Hpre as (HW & Ho & Hq & Hfl & Hzi & Hwr & Had).
  assert (Hz := zwide_zall z Hzi).
  assert (HI : HFI s z flush s z []).
  { unfold HFI. split; [exact Hz|]. split; [exact Had|].
    split; [exact (LTCHuffGlue.hcrel_refl s z flush HW He Ho Hz Had)|].
    split; [exact Hq|]. split; [exact Hz|]. split; [exact Had|constructor]. }
  destruct Hst as (Hss & Hbs & Hla).
  destruct (LTCHuffRefill.hrefill_ok Hfill s z flush s z [] HI Hfn Hla) as (s1 & z1 & Ef & HI1 & Hsum & Hz1).
  assert (HW0 := HW).
  destruct HW0 as (Hp & Hs & Hpos & Hw & Hh & Hm & H0 & syms & Ht).
  assert (Hlev := fn_of_huff s Hp Hfn).
  assert (Hfp : fill_pre s).
  { unfold whash in Hh. destruct (Z.eqb_spec (d_level s) 0) as [E0|N]; [lia|].
    destruct Hh as (_ & Hc).
    split; [exact Hp|]. split; [exact Hs|]. split; [exact Hpos|]. split; [exact Hw|exact Hc]. }
  destruct (Hfill s z Hfp Hz Had) as (s1' & z1' & k & d & Ef' & _ & _ & Hzs & Hd & Es1 & Eb1 & _ & _ &
    El1 & _).
  rewrite Ef in Ef'. injection Ef' as <- <-.
  assert (Hd0 : d = 0).
  { destruct Hd as [Hd|(_ & Hd)]; [exact Hd|]. exfalso.
    destruct Hp as (Hwb & Hws & _).
    assert (2 ^ 9 <= 2 ^ d_w_bits s) by (apply Z.pow_le_mono_r; lia).
    unfold MAX_DIST in Hd. replace MIN_LOOKAHEAD with 262 in Hd by reflexivity. lia. }
  subst d. rewrite Hss in Es1. rewrite Hla in El1.
  destruct (Z.eqb_spec (d_lookahead s1) 0) as [L0|L0].
  - rewrite (sh_huff_exit flush s z s1 z1 _ s' z' bs (sh_body_exit flush s z s1 z1 Hla Ef L0) E). lia.
  - assert (E1 : c_deflate_huff s1 z1 flush = Some (s', z', bs)).
    { rewrite <- (sh_huff_same flush s z s1 z1 (sh_body_same flush s z s1 z1 Hla Ef L0)). exact E. }
    destruct HI1 as (_ & _ & Hc1 & Hq1 & Hz1' & Ha1 & _).
    assert (Hfn1 : fn_of s1 = 3) by (rewrite (LTCHuffGlue.fn_of_hcrel _ _ _ _ _ _ Hc1); exact Hfn).
    destruct Hc1 as (HW1 & He1 & Ho1 & _).
    assert (HI1 : HFI s1 z1 flush s1 z1 []).
    { unfold HFI. split; [exact Hz1'|]. split; [exact Ha1|].
      split; [exact (LTCHuffGlue.hcrel_refl s1 z1 flush HW1 He1 Ho1 Hz1' Ha1)|].
      split; [exact Hq1|]. split; [exact Hz1'|]. split; [exact Ha1|constructor]. }
    assert (Hbd : z_avail_in z1 + d_lookahead s1 < 2 ^ 40).
    { destruct Hzi as (_ & _ & Hai & _). rewrite Hsum, Hla. lia. }
    destruct (sh_huff_run Hfill Htally Hfbo s1 z1 flush HI1 Hfl Hfn1 Hbd) as (s2 & z2 & bs2 & evs & E2 & Hc2).
    rewrite E1 in E2. injection E2 as <- <- <-.
    destruct Hc2 as (_ & _ & _ & _ & _ & (k2 & x & Hzs2 & _) & _).
    destruct Hzs as (_ & Hk & Hn1 & _). destruct Hzs2 as (_ & Hk2 & Hn2 & _). lia.
Qed.
