(** * deflate_stored's first-phase loop for any [left + avail_in] ([LTWClipKit.dsloop_clip_stmt])

    Since fix F9, deflate_stored compares a block length with [left + strm->avail_in] in 64 bits: the wide loop
    (src/proof/wide/deflate/LTCStoredLoop.v, [dsloop_ok''_w]) holds for every call, whatever the sum, and gives
    the blocks written without [clip_ok]. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.deflate.LTWClipKit.
Require Import Zlib.proof.wide.deflate.LTCStoredLoop.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Theorem dsloop_clip_ok : sblk_stmt -> dsloop_clip_stmt.
Proof.
  intros Hsb s z flush HW Ho Hq Hlev Hz Ha Hf Hao.
  destruct (dsloop_ok''_w Hsb s z flush HW Ho Hq Hlev Hz Ha Hf Hao)
    as (s1 & z1 & last & evs & k & x & E & K & B & O & Q & G & Z & X & A & S & P & C & F & L).
  exists s1, z1, last, k, x.
  do 10 (split; [assumption|]).
  split; [destruct L as [(L & _)|(L & _)]; [left|right]; exact L|].
  split.
  - intros L0 Hfin. destruct L as [(_ & _ & L)|(L & _)]; [exact (L Hfin)|lia].
  - intros _. exists evs. split; [exact S|]. split; [exact C|]. split; [exact F|].
    destruct L as [(L1 & L2 & _)|(L1 & L2 & L3 & L4 & L5 & L6)]; [left; auto|right; auto 7].
Qed.
