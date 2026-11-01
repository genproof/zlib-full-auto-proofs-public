(* From the invariant of the deflate laws to the wide one: a stream in Krt3 (RTDV3.v, sizes of
   deflate_roundtrip) is in K7 (RTK7Defs.v).  The header limits of RTDLawFacts.hdr_ok are within those of
   RTK7.rhdr_ok7, the dictionary of at most 32768 bytes within 2^32 - 1, and total_in, which Iapi bounds by the
   data plus the dictionary, is its own value modulo 2^64 while that sum is below 2^64. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTK7Defs.
Import ListNotations.
Local Open Scope Z_scope.

(* the headers of the deflate laws are headers of the short laws *)
Lemma hdr_ok_rhdr_ok7 : forall h, hdr_ok h -> rhdr_ok7 h.
Proof.
  intros h (Ht & Hc & Ho & Hti & Hx & Hex & Hn & Hcm).
  unfold rhdr_ok7, rs32, u32r in *.
  split; [destruct Ht; lia|]. split; [destruct Hc; lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [exact Hex|].
  split; intros l E.
  - destruct (Hn l E) as (l0 & -> & Hl & Hf). exists l0. repeat split; auto; lia.
  - destruct (Hcm l E) as (l0 & -> & Hl & Hf). exists l0. repeat split; auto; lia.
Qed.

Lemma hinv_hinv7 : forall s a H k, hinv s a H k -> hinv7 s a H k.
Proof.
  intros s a H k (Hw & h & xfl & Hg & Hok & HH & Hst & Hidx & Hk & Ha).
  split; [exact Hw|]. exists h, xfl. split; [exact Hg|]. split; [exact (hdr_ok_rhdr_ok7 h Hok)|].
  auto.
Qed.

(* Iapi -> Iapi7 for the same invariant of the state, while the data and the dictionary fit in 64 bits *)
Lemma Iapi_Iapi7 : forall W dict wrap D O fin s tin tout adler,
  Iapi W hinv dict wrap D O fin s tin tout adler -> Zlength D + Zlength dict < 18446744073709551616 ->
  Iapi7 W hinv7 dict wrap D O fin s tin tout adler.
Proof.
  intros W dict wrap D O fin s tin tout adler
    (HW & Ho & Hwr & Hw2 & Hbd & Hld & Hlf & Hgz & Htout & HbO & HbD & Htin & Hfin & HD0 & Hph) Hlt.
  unfold Iapi7.
  do 5 (split; [assumption|]). split; [lia|]. split; [assumption|].
  split; [intros h E; exact (hdr_ok_rhdr_ok7 h (Hgz h E))|].
  do 3 (split; [assumption|]).
  split; [lia|].
  split.
  { exists (tin - Zlength D). split; [lia|]. unfold u64.
    replace (Zlength D + (tin - Zlength D)) with tin by lia.
    pose proof (Zlength_nonneg D). rewrite Z.mod_small; lia. }
  split; [exact Hfin|]. split; [exact HD0|].
  destruct Hph as [Hp | (Hlf2 & [Hp | [Hp | Hp]])]; [left; exact Hp|right; split; [exact Hlf2|]..].
  - left. destruct Hp as (Hw' & HD & HO & Hbv & Hsn & H & k & Hh & HE).
    repeat split; auto. exists H, k. split; [exact (hinv_hinv7 _ _ _ _ Hh)|exact HE].
  - right; left; exact Hp.
  - right; right; exact Hp.
Qed.

(* Krt3 -> K7 under the same bound *)
Lemma Krt3_K7 : forall dict wrap D O fin s tin tout adler,
  Krt3 dict wrap D O fin s tin tout adler -> Zlength D + Zlength dict < 18446744073709551616 ->
  K7 dict wrap D O fin s tin tout adler.
Proof.
  intros dict wrap D O fin s tin tout adler (HI & HK) Hlt. left. split; [|exact HK].
  exact (Iapi_Iapi7 _ _ _ _ _ _ _ _ _ _ HI Hlt).
Qed.
