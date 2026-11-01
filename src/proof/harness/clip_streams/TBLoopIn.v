(* Law rfc_trailing_bytes, main: the first part of the inflate loop's body (TBLoopKit.tbl_in_stmt),
   decompressor.avail_in = clip(compressed_len + after - (next_in - input)). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Zlib.proof.inflate.Callees.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.clip_streams.CS Zlib.proof.harness.clip_streams.Globals.
Require Import Zlib.proof.harness.clip_streams.DFacts Zlib.proof.harness.clip_streams.IFacts.
Require Import Zlib.proof.harness.clip_streams.TBFacts Zlib.proof.harness.clip_streams.MainDefs.
Require Import Zlib.proof.harness.clip_streams.TBKit Zlib.proof.harness.clip_streams.TBLoopKit.
Require Import Zlib.harness.rfc_trailing_bytes.code.
#[local] Existing Instance CS.CS.
Local Open Scope logic.

Lemma tbl_in : tbl_in_stmt.
Proof.
  intros Espec P wbits n D O src dp op ip vc vd gv pos out z L vai vao Y R PF FA HY.
  destruct FA as (DF & HD & Hn & HO & Hsl & Hsb & Hw & BD & BD' & BO & Pdp & Pop & Pip).
  unfold tbl_st. Intros.
  destruct (tl_ok P PF _ _ _ _ _ _ _ _ H) as (Hhd & Hpos & rest & Erest).
  unfold tbl_x1, Delta_tb. abbreviate_semax.
  forward.
  forward_call (Zlength src - pos).
  { apply prop_right. apply tbl_sameblock; auto. }
  { entailer!. replace (Zlength O + (Zlength src - Zlength O)) with (Zlength src) by lia.
    rewrite tbl_ptr_sub by (auto; rep_lia). reflexivity. }
  forward.
  eapply semax_pre; [ | exact HY ].
  unfold tbl_st. entailer!.
Qed.
