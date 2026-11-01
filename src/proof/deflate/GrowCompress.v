(** * The compression functions of deflate.c (DModel2: deflate_stored, deflate_fast, deflate_slow, deflate_rle,
    deflate_huff) only append to the output ([out_grow z z'], DeflateKit) and keep the gz_header and the sizes
    of the allocations ([dkeep s s'], DeflateKit).  The statements only: GrowCompressR.v proves (Qed)
    grow_deflate_fast/slow/rle/huff and, in the ranged form compress_facts_r, all five (grow_compress_proved_r). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.DeflateKit.
#[export] Existing Instance DCS.CS.
Open Scope cmodel_scope.

Definition compress_facts (c : dstate -> strm -> Z -> option (dstate * strm * bstate)) : Prop :=
  forall s z f r, c s z f = Some r -> out_grow z (snd (fst r)) /\ dkeep s (fst (fst r)).

Definition grow_compress_all : Prop :=
  compress_facts c_deflate_stored /\ compress_facts c_deflate_fast /\ compress_facts c_deflate_slow /\
  compress_facts c_deflate_rle /\ compress_facts c_deflate_huff.
