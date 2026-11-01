(* Round-trip part RT-B: rt_init_facts and rt_bound_once (RTDIface) from the deflate laws' theory.
   rt_init_facts: LawFacts.af_init without the invariant.  rt_bound_once: with windowBits 15, memLevel 8 and
   the default strategy deflateBound's tight class applies at every level, and the zlib header without a
   dictionary is 2 bytes, so deflateBound(n) = compressBound(n); then RTBWalk.rtb_deflate_walk (one
   deflate(Z_FINISH) with that much space ends the stream, with the caller's fields). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.deflate.LTBWalk Zlib.proof.deflate.LTBInit Zlib.proof.deflate.LTBDBound.
Require Import Zlib.proof.deflate.LTBound.
Require Zlib.proof.deflate.LTCore Zlib.proof.deflate.LTHdr Zlib.proof.deflate.LawTheory.
Require Import Zlib.proof.roundtrip.RTBWalk.
Require Import Zlib.proof.roundtrip.RTDIface.
Import ListNotations.
Local Open Scope Z_scope.

Lemma rtb_params : forall level, -1 <= level <= 9 -> params_ok level 8 15 8 0 = true.
Proof.
  intros level Hl.
  assert (level = -1 \/ level = 0 \/ level = 1 \/ level = 2 \/ level = 3 \/ level = 4 \/ level = 5 \/
          level = 6 \/ level = 7 \/ level = 8 \/ level = 9) by lia.
  repeat match goal with H : _ \/ _ |- _ => destruct H as [->|H] end; subst; reflexivity.
Qed.

Theorem rtb_facts :
  Zlib.proof.huffman.Overlay.overlay_statement -> Zlib.proof.huffman.BlockBound.block_bound_statement ->
  rt_init_facts /\ rt_bound_once.
Proof.
  intros Hov Hbb.
  destruct (Zlib.proof.deflate.LawTheory.law_theory Hov Hbb) as [(I & Iend & AF) _].
  split.
  - intros level method wbits mem strategy a1 a2 a3 a4 a5 z H1 H2 H3 H4 H5.
    destruct (af_init I Iend AF level method wbits mem strategy a1 a2 a3 a4 a5 z H1 H2 H3 H4 H5) as [A B].
    split; [exact A|]. intros os z' code E. destruct (B os z' code E) as (B1 & B2 & B3).
    split; [exact B1|]. split; [exact B2|]. intros Hc. destruct (B3 Hc) as (s & Hs & Hg & _). eauto.
  - intros level a1 a2 a3 a4 a5 z s z1 src msg Hl Hsrc Hn Hinit.
    destruct (Zlib.proof.deflate.LTCore.core_theory Hov) as [W CF].
    destruct Zlib.proof.deflate.LTHdr.hdr_theory as [HI HF].
    destruct (bpre_init W CF level 15 8 0 a1 a2 a3 a4 a5 z (rtb_params level Hl)) as [_ B].
    destruct (B _ _ _ Hinit eq_refl) as (s0 & Hs0 & Hg0 & HB). injection Hs0 as <-.
    assert (Hn' : 0 <= Zlength src <= 1048576) by (pose proof (Zlength_nonneg src); lia).
    destruct (bound_of_bpre W HI CF level 15 8 0 false s _ _ _ (Zlength src) HB Hn') as (b & Eb & Hb & _ & HR).
    assert (Hbv : b = c_compressBound (Zlength src)).
    { destruct HB as (HW & Ho & Hpo & Hst & Hwr & Hpd & Hpo0 & Hbi & Hsym & Hla & Hss & Hds & Hlv & Hsg & Hwb &
                      Hhb & Hgz & Hlf & Ht & Hti & Had).
      assert (Hw1 : d_wrap s = 1) by (rewrite Hwr; reflexivity).
      assert (Hso : status_ok (d_status s) = true) by (rewrite Hst; reflexivity).
      rewrite (deflateBound_val s (Zlength src) (z_adler z1) (cf_prm W CF s HW) Hso ltac:(lia) Hgz Hn') in Eb.
      injection Eb as <-. destruct (Hds eq_refl) as [Hs0 _].
      rewrite (hdr_bytes_zlib_nodict s (z_adler z1) Hw1 Hs0), Hw1, compressBound_val by exact Hn'.
      assert (Hc : bcls_of s = BTight).
      { unfold bcls_of, tight_b. rewrite Hwb, Hhb, Hsg. reflexivity. }
      rewrite Hc. unfold tlen. cbn. lia. }
    subst b.
    assert (Hto : z_total_out z1 = 0) by (destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                                                       _ & _ & _ & _ & Ht & _); exact Ht).
    pose proof (tbo_body_range BTight (Zlength src) Hn') as Hbr.
    pose proof (compressBound_val (Zlength src) Hn') as Hcb.
    destruct (rtb_deflate_walk W HI CF HF Hbb (cpost_extra_ok W CF) (Zlength src) (c_compressBound (Zlength src))
                0 false s (z_total_in z1) (z_total_out z1) (z_adler z1) src (c_compressBound (Zlength src))
                Z_FINISH msg HR ltac:(right; reflexivity) ltac:(intros H; discriminate) Hsrc ltac:(lia)
                ltac:(intros _; lia) ltac:(lia))
      as (s' & z' & code & E & G & _ & _ & _ & R & CFr).
    destruct (R eq_refl eq_refl eq_refl ltac:(lia)) as [-> Ea].
    exists s', z'. split; [exact E|]. split; [exact G|]. split; [exact Ea|].
    destruct CFr as (Zi & Zn & Zs & Zt & Zao & Zl & Ztt & Zb).
    pose proof (Zlength_nonneg (z_out z')).
    unfold rcall_ok. split; [exact Zi|]. rewrite Ea.
    repeat split; try lia. exact Zb.
Qed.
