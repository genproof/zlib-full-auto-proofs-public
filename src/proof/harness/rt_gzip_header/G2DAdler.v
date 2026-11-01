(* Law rt_gzip_header on the round-2 harness: deflate() keeps strm->adler a 64-bit value with a gzip header.

   AdlerKeep.c_deflate_adler_range proves this for a Z_NULL gz_header only.  With a header the stages EXTRA ..
   HCRC compute CRC-32s of pending_buf bytes (HCRC_UPDATE): below 2^32 when the pending buffer holds bytes and
   strm->adler is below 2^32 on entry (DetApiHdrSt.hdr_stages_adq).  The GZIP stage first sets strm->adler to 0,
   so its value on entry does not matter; in the other states the header stages do nothing.  Hence
   [g2_deflate_adler]: with the pending buffer's bytes ([pbq]) and strm->adler below 2^32 whenever deflate() may
   start in a header state that reads it (INIT, EXTRA, NAME, COMMENT, HCRC), the call leaves strm->adler a
   64-bit value (the compression stage and the trailer as in AdlerKeep). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.deflate.DModel4.
Require Import Zlib.proof.deflate.AdlerKeep.
Require Zlib.proof.deflate.InFacts.
Require Zlib.proof.deflate.DetApiHdrSt.
Require Zlib.proof.deflate.LTDefs.
Require Zlib.proof.deflate.LTHdrStages.
Require Zlib.proof.deflate.DeflateKit.
Import ListNotations.
Local Open Scope Z_scope.

Module HQ := Zlib.proof.deflate.DetApiHdrSt.
Module IF := Zlib.proof.deflate.InFacts.
Module HS := Zlib.proof.deflate.LTHdrStages.

Local Strategy opaque [loop loop2].

(* the states in which the header stages read strm->adler *)
Definition hstat (st : Z) : Prop :=
  st = INIT_STATE \/ st = EXTRA_STATE \/ st = NAME_STATE \/ st = COMMENT_STATE \/ st = HCRC_STATE.

Lemma g2_flush_status s z s' z' : c_flush_pending s z = Some (s', z') -> d_status s' = d_status s.
Proof.
  unfold c_flush_pending. intros H. adec.
  all: repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity.
Qed.

(** The entry stage keeps the status, strm->adler, the input object and the pending buffer's bytes. *)
Lemma g2_entry s z f s1 z1 o : c_deflate_entry s z f = Some (s1, z1, o) -> HQ.pbq s ->
  d_status s1 = d_status s /\ z_adler z1 = z_adler z /\ z_in z1 = z_in z /\ HQ.pbq s1.
Proof.
  unfold c_deflate_entry, then_stage. intros H P. adec.
  all: try match goal with E : c_flush_pending ?a _ = Some _ |- _ =>
    assert (Pa : HQ.pbq a) by (eapply HQ.pbq_ext; [exact P|reflexivity|reflexivity]);
    pose proof (g2_flush_status _ _ _ _ E); pose proof (IF.zin_flush_pending _ _ _ _ E);
    destruct (HQ.pbq_flush _ _ _ _ E Pa) end.
  all: cbn [d_status set_d_last_flush z_adler z_in set_z_msg] in *.
  all: refine (conj _ (conj _ (conj _ _))); try congruence;
    try (eapply HQ.pbq_ext; [eassumption|reflexivity|reflexivity]).
Qed.

Lemma classic_hstat st : hstat st \/ ~ hstat st.
Proof.
  unfold hstat.
  destruct (Z.eq_dec st INIT_STATE); [tauto|]. destruct (Z.eq_dec st EXTRA_STATE); [tauto|].
  destruct (Z.eq_dec st NAME_STATE); [tauto|]. destruct (Z.eq_dec st COMMENT_STATE); [tauto|].
  destruct (Z.eq_dec st HCRC_STATE); [tauto|]. right. intros [?|[?|[?|[?|?]]]]; contradiction.
Qed.

Lemma then_zin r k s' z' o z :
  (forall s1 z1 o1, r = Some (s1, z1, o1) -> z_in z1 = z_in z) ->
  (forall s1 z1 s2 z2 o2, k s1 z1 = Some (s2, z2, o2) -> z_in z2 = z_in z1) ->
  then_stage r k = Some (s', z', o) -> z_in z' = z_in z.
Proof.
  intros H1 H2 H. apply IF.then_stage_inv' in H as (s1 & z1 & o1 & E & [(_ & -> & ->) | (_ & E2)]).
  - exact (H1 _ _ _ E).
  - rewrite (H2 _ _ _ _ _ E2). exact (H1 _ _ _ E).
Qed.

(** The header stages keep the input object. *)
Lemma g2_hdr_zin s z s' z' o : Zlib.proof.deflate.LTDefs.hdr_stages s z = Some (s', z', o) -> z_in z' = z_in z.
Proof.
  unfold Zlib.proof.deflate.LTDefs.hdr_stages. intros H.
  refine (then_zin _ _ _ _ _ _ _ _ H).
  { intros s1 z1 o1 E. rewrite Zlib.proof.deflate.DeflateKit.c_deflate_zlib_header_eq in E.
    exact (IF.in_zlib 0 _ _ _ _ _ E). }
  intros s1 z1 s2 z2 o2 E2. refine (then_zin _ _ _ _ _ _ _ _ E2).
  { intros s3 z3 o3 E. exact (IF.in_gzip 0 _ _ _ _ _ E). }
  intros s3 z3 s4 z4 o4 E4. refine (then_zin _ _ _ _ _ _ _ _ E4).
  { intros s5 z5 o5 E. exact (IF.in_extra 0 _ _ _ _ _ E). }
  intros s5 z5 s6 z6 o6 E6. refine (then_zin _ _ _ _ _ _ _ _ E6).
  { intros s7 z7 o7 E. exact (IF.in_name 0 _ _ _ _ _ E). }
  intros s7 z7 s8 z8 o8 E8. refine (then_zin _ _ _ _ _ _ _ _ E8).
  { intros s9 z9 o9 E. exact (IF.in_comment 0 _ _ _ _ _ E). }
  intros s9 z9 s10 z10 o10 E10. exact (IF.in_hcrc 0 _ _ _ _ _ E10).
Qed.

(** In GZIP_STATE the header stages start by setting strm->adler to 0. *)
Lemma g2_hdr_gzip s z : d_status s = GZIP_STATE ->
  Zlib.proof.deflate.LTDefs.hdr_stages s z = Zlib.proof.deflate.LTDefs.hdr_stages s (set_z_adler z 0).
Proof.
  intros Hs. unfold Zlib.proof.deflate.LTDefs.hdr_stages.
  rewrite !HS.zlib_id by (rewrite Hs; discriminate). cbn [then_stage bind].
  f_equal. unfold c_deflate_gzip_header. rewrite Hs. cbn [Z.eqb].
  replace (set_z_adler (set_z_adler z 0) 0) with (set_z_adler z 0) by (destruct z; reflexivity).
  reflexivity.
Qed.

(** In the other states outside the header the header stages do nothing. *)
Lemma g2_hdr_id s z : ~ hstat (d_status s) -> d_status s <> GZIP_STATE ->
  Zlib.proof.deflate.LTDefs.hdr_stages s z = Some (s, z, None).
Proof.
  intros Hh Hg. unfold hstat in Hh. unfold Zlib.proof.deflate.LTDefs.hdr_stages.
  rewrite HS.zlib_id by tauto. cbn [then_stage bind].
  rewrite HS.gzip_id by tauto. cbn [then_stage bind].
  rewrite HS.extra_id by tauto. cbn [then_stage bind].
  rewrite HS.name_id by tauto. cbn [then_stage bind].
  rewrite HS.comment_id by tauto. cbn [then_stage bind].
  rewrite HS.hcrc_id by tauto. reflexivity.
Qed.

Lemma g2_hdr s z s' z' o : Zlib.proof.deflate.LTDefs.hdr_stages s z = Some (s', z', o) -> HQ.pbq s ->
  0 <= z_adler z <= 18446744073709551615 -> (hstat (d_status s) -> HQ.adq z) ->
  0 <= z_adler z' <= 18446744073709551615.
Proof.
  intros H P A Q.
  destruct (classic_hstat (d_status s)) as [Hh|Hh].
  - destruct (HQ.hdr_stages_adq _ _ _ _ _ H P (Q Hh)) as [_ A']. unfold HQ.adq in A'. lia.
  - destruct (Z.eq_dec (d_status s) GZIP_STATE) as [Hg|Hg].
    + rewrite (g2_hdr_gzip s z Hg) in H.
      destruct (HQ.hdr_stages_adq _ _ _ _ _ H P) as [_ A']; [unfold HQ.adq; cbn [z_adler set_z_adler]; lia|].
      unfold HQ.adq in A'. lia.
    + rewrite (g2_hdr_id s z Hh Hg) in H. injection H as <- <- <-. exact A.
Qed.

(** deflate() keeps strm->adler a 64-bit value, with or without a gz_header. *)
Lemma g2_deflate_adler s z flush s' z' code :
  HQ.pbq s -> Forall (fun b => 0 <= b < 256) (z_in z) -> 0 <= z_adler z <= 18446744073709551615 ->
  (hstat (d_status s) -> HQ.adq z) -> c_deflate s z flush = Some (s', z', code) ->
  0 <= z_adler z' <= 18446744073709551615.
Proof.
  intros P B A Q H. set (inp := z_in z) in B.
  enough (Zf : zok inp z') by apply Zf.
  rewrite Zlib.proof.deflate.LTDefs.c_deflate_stages in H.
  destruct (bad_state s || (flush >? Z_BLOCK) || (flush <? 0)).
  { injection H as <- <- <-. split; [reflexivity|exact A]. }
  destruct (then_stage (then_stage (c_deflate_entry s z flush) Zlib.proof.deflate.LTDefs.hdr_stages)
              (fun s0 z0 => c_deflate_compress s0 z0 flush)) as [[[s3 z3] o]|] eqn:R; [|discriminate].
  cbn [bind] in H.
  assert (Z3 : zok inp z3).
  { refine (then_stage_ok (fun y => zok inp (snd (fst y))) (fun y => zok inp (snd (fst y))) _ _ _ R _
              (fun y H => H) _).
    - intros [[s2 z2] o2] Ey. cbn [fst snd].
      apply IF.then_stage_inv' in Ey as (s1 & z1 & o1 & E1 & [(_ & -> & ->) | (_ & E2)]);
        destruct (g2_entry _ _ _ _ _ _ E1 P) as (St & Ad & Zi & P1).
      + split; [exact Zi|]. rewrite Ad. exact A.
      + split; [rewrite (g2_hdr_zin _ _ _ _ _ E2); exact Zi|].
        refine (g2_hdr _ _ _ _ _ E2 P1 _ _); [rewrite Ad; exact A|].
        rewrite St. intros Hh. unfold HQ.adq. rewrite Ad. exact (Q Hh).
    - intros s2 z2 [[s3' z3'] o3'] Z2 E. exact (ak_deflate_compress inp B _ _ _ _ _ _ E Z2). }
  destruct o as [c|].
  - injection H as <- <- <-. exact Z3.
  - exact (ak_deflate_trailer inp _ _ _ _ _ _ H Z3).
Qed.
