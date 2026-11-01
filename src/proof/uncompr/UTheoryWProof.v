(* The proof of UTheoryW.uw_theory_stmt from the wide decode theory: the decode context of the stream O read
   from a source that starts with O (clip_streams/DCtx.clip_dctx, as rfc_trailing_bytes takes it), then the loop
   of inflate() calls (UWLoop.uw_loop). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.uncompr.UTheoryW.
Import ListNotations.
Local Open Scope Z_scope.

Require Import VST.floyd.proofauto.
Require Import Zlib.proof.rfc1951.Decode7.
Require Import Zlib.proof.uncompr.UWLive Zlib.proof.uncompr.UWLoop.
Require Zlib.proof.wide.Decode7.
Require Zlib.proof.roundtrip.RTUTheory.
Require Zlib.proof.harness.clip_streams.DCtx Zlib.proof.harness.clip_streams.PfxTheory.

(* the stream after inflateInit_ (UModel.m_first) is the start of the loop: a live stream, the decoder at the
   start of the stream (decode_init7_stmt), nothing offered yet *)
Lemma uw_first (DI: decode_init7_stmt) (G: dctx) (cap: Z) :
  dctx_ok7 G -> dc_hist G = [] -> dc_iw G = 15 -> (forall wb fl did, dc_w G = WZlib wb fl did -> did = None) ->
  0 <= cap -> uw_RI G cap m_first 0 [] 0 0.
Proof.
  intros OK HI IW ND CAP.
  set (sp := Vptr xH Ptrofs.zero).
  pose proof (DI G sp OK HI ND) as D0. rewrite IW in D0.
  split.
  - split; [exists (init_live sp 15); split; [apply Zlib.proof.roundtrip.RTUTheory.rtu_init_live_ok; exact I|];
            split; reflexivity|].
    split; [unfold Zlib.proof.inflate.InvW.swfW; split; intros E; vm_compute in E; discriminate|].
    split; [vm_compute; reflexivity|].
    unfold lrange; cbn; rep_lia.
  - split; [exact D0|]. unfold uw_max. rewrite Zlength_nil. rep_lia.
Qed.

Theorem uw_theory : uw_theory_stmt.
Proof.
  intros D O src cap r slen0 dlen out DF RB LD PO LOS BS LS CAP REL.
  destruct REL as [(-> & _)|(err & UL & -> & ->)]; [left; reflexivity|].
  destruct Zlib.proof.wide.Decode7.decode7 as [DI DK].
  assert (DF': Zlib.proof.harness.clip_streams.IFacts.dfinal_of 15 D O) by (split; [reflexivity|exact DF]).
  destruct (Zlib.proof.harness.clip_streams.DCtx.clip_dctx 15 D O src DF' ltac:(lia) PO BS)
    as (G & OK & SRC & SL & FU & HI & IW & ND & TL).
  assert (WZ: exists wb fl did, dc_w G = WZlib wb fl did).
  { destruct (dc_w G) as [|wb fl did|h]; cbn in TL; try discriminate. eauto. }
  destruct WZ as (wb & fl & did & W).
  rewrite <- SRC in UL.
  destruct (uw_loop DK G wb fl did cap OK W _ _ _ _ _ _ _ _ UL (uw_first DI G cap OK HI IW ND ltac:(lia)))
    as [->|[(-> & -> & -> & LC)|(-> & C & LT & UL' & rest & PR)]].
  - left. reflexivity.
  - right; left. rewrite FU, SL in *. auto.
  - right; right. rewrite FU, SL in *.
    split; [apply Zlib.proof.roundtrip.RTUTheory.rtu_unc_buf; lia|].
    split; [exact LT|]. split; [exact C|].
    split; [|exact UL'].
    rewrite PR, <- C, sublist_app1 by (pose proof (Zlength_nonneg out); lia).
    rewrite sublist_same; reflexivity.
Qed.
