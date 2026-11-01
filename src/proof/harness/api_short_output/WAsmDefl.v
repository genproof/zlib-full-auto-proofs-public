(* Law api_short_output (data of any length): the entries of WAsmKit.G_defl, from the bodies of deflate.c
   (Obligations9.deflate_bodies_ok9; deflate and its input-carrying callees from the dnull port, DSpecNBody). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Assembly.
Require Import Zlib.proof.deflate.Obligations Zlib.proof.deflate.Obligations9.
Require Zlib.proof.inflate_api.SpecWLib.
Require Zlib.proof.deflate.DSpecNBody.
Module ON := Zlib.proof.dnull.deflate.Obligations_N.
Require Import Zlib.proof.harness.api_short_output.WLawCS Zlib.proof.harness.api_short_output.WAsmKit.
#[local] Existing Instance Zlib.proof.harness.api_short_output.WLawCS.CS.

Lemma w_entries_defl : Zlib.proof.inflate_api.SpecWLib.specw_bridge_stmt -> deflate_bodies_ok9 ->
  w_entries G_defl.
Proof.
  intros BR DB. unfold w_entries, G_defl.
  destruct DB as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D16 &
                  D17 & D18 & D19 & D20 & D21 & D22 & D23 & D24 & D25 & _).
  unfold ob_read_buf, ob_putShortMSB, ob_flush_pending, ob_slide_hash, ob_longest_match, ob_lm_init,
    ob_fill_window, ob_deflate_stored, ob_deflate_fast, ob_deflate_slow, ob_deflate_rle, ob_deflate_huff,
    ob_deflateStateCheck, ob_deflateResetKeep9, ob_deflateReset9, ob_deflateSetHeader, ob_deflateTune,
    ob_deflatePrime, ob_deflateBound_z, ob_deflateBound, ob_deflateSetDictionary, ob_deflateEnd,
    ob_deflateInit2_9, ob_deflate, ob_deflateParams in *.
  pose proof Zlib.proof.dnull.deflate.Body_read_buf_N.body_read_buf_N as N1.
  pose proof Zlib.proof.dnull.deflate.Body_flush_pending_N.body_flush_pending_N as N3.
  pose proof Zlib.proof.dnull.PartFillWindow.dn_fill_window as N7.
  pose proof Zlib.proof.dnull.PartStored.dn_deflate_stored as N8.
  pose proof Zlib.proof.dnull.PartFast.dn_deflate_fast as N9.
  pose proof Zlib.proof.dnull.PartSlow.dn_deflate_slow as N10.
  pose proof Zlib.proof.dnull.PartRle.dn_deflate_rle as N11.
  pose proof Zlib.proof.dnull.PartHuff.dn_deflate_huff as N12.
  pose proof Zlib.proof.dnull.PartDeflate.dn_deflate as N24.
  unfold ON.ob_read_buf_N, ON.ob_flush_pending_N, ON.ob_fill_window_N, ON.ob_deflate_stored_N,
    ON.ob_deflate_fast_N, ON.ob_deflate_slow_N, ON.ob_deflate_rle_N, ON.ob_deflate_huff_N, ON.ob_deflate_N in *.
  w_entry N1 BR. w_entry D2 BR. w_entry N3 BR. w_entry D4 BR. w_entry D5 BR. w_entry D6 BR.
  w_entry N7 BR. w_entry N8 BR. w_entry N9 BR. w_entry N10 BR. w_entry N11 BR. w_entry N12 BR.
  w_entry D13 BR. w_entry D14 BR. w_entry D15 BR. w_entry D16 BR. w_entry D17 BR. w_entry D18 BR.
  w_entry D19 BR. w_entry D20 BR. w_entry D22 BR. w_entry D23 BR. w_entry N24 BR.
  apply Forall_nil.
Qed.
