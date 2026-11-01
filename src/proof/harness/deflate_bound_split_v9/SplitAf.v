(* Law deflate_bound_split: api_fields split at next_in (v5 specs take strm->next_in separately). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.harness.x_deflate_bound_split.code.
Require Import Zlib.proof.harness.deflate_bound_split_v9.SplitMain Zlib.proof.harness.deflate_bound_split_v9.SplitKit.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

Definition af_rest (sp : val) (ain tin : Z) (nout : val) (aout tout : Z) (msgv : val) (adler : Z) : mpred :=
  !! (u32_ok ain /\ u64_ok tin /\ u32_ok aout /\ u64_ok tout /\ u64_ok adler) &&
  (@field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._avail_in) (vi ain) sp *
   @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._total_in) (vl tin) sp *
   @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._next_out) nout sp *
   @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._avail_out) (vi aout) sp *
   @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._total_out) (vl tout) sp *
   @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._msg) msgv sp *
   @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._adler) (vl adler) sp).

Lemma af_split (sp nin : val) (ain tin : Z) (nout : val) (aout tout : Z) (msgv : val) (adler : Z) :
  api_fields sp nin ain tin nout aout tout msgv adler =
  @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._next_in) nin sp * af_rest sp ain tin nout aout tout msgv adler.
Proof.
  unfold api_fields, af_rest. apply pred_ext; entailer!.
Qed.

Lemma af_join (sp nin : val) (ain tin : Z) (nout : val) (aout tout : Z) (msgv : val) (adler : Z) :
  @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._next_in) nin sp * af_rest sp ain tin nout aout tout msgv adler
  |-- api_fields sp nin ain tin nout aout tout msgv adler.
Proof. rewrite af_split. apply derives_refl. Qed.

Lemma sf_split (sp : val) (f : sfields) :
  sf_at sp f = @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._next_in) (sf_nin f) sp *
    af_rest sp (sf_ain f) (sf_tin f) (sf_nout f) (sf_aout f) (sf_tout f) (sf_msgv f) (sf_adler f).
Proof. unfold sf_at. apply af_split. Qed.
