(* deflate() on the round trips' wide invariant: every call is defined, its return codes, and the invariant kept.

   RTK7.kfacts7 (RTK7Deflate.rtk7_deflate_ok) says what a deflate() call does to the round trip's invariant K7
   GIVEN the call's model run and its return codes.  The laws that make deflate() calls of their own choosing
   (rt_stream: any pieces of data of any length, any output space below 2^32, any flush; api_deterministic: the
   same, next_in anywhere in the input object after a deflateParams) need the converse: on the wide deflate_api
   invariant RTK7Defs.Iapi7 (W3, hinv7), every call with the sizes of the C types is defined, returns Z_OK,
   Z_BUF_ERROR (no progress at all) or Z_STREAM_END (only for Z_FINISH, all the input consumed), and keeps Iapi7
   unless it returned Z_STREAM_END.

   This is DetWide.api_deflate_wide / round 1's DetCodes.api_codes_wide without their size limits (data at most 2^20 bytes,
   avail_in at most 2^30, total_in / total_out at most 2^40), over Iapi7 instead of LTApiDefs.Iapi.  The Z_STREAM_END
   clause needs deflate_stored with the 64-bit sums of fix F9: with the old 32-bit `left + avail_in` a level-0
   Z_FINISH call could end in RTK7Defs.stored_cut (a last block with input left).  [comp_nocut7_stmt] is that
   fact: the compression functions always end as LTDefs.cpost says (LTWIface.cw_compress for the streams of the C
   types, without the 32-bit guard at level 0). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTK7Defs.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** The compression stage of a call on the streams of the C types: defined, and it ends as [cpost] says (never
    in [stored_cut]). *)
Definition comp_nocut7_stmt : Prop :=
  forall s z flush,
    W3 s -> outok s -> quiet s -> 0 <= flush <= 5 -> zin_ok7 z ->
    0 <= d_wrap s <= 2 -> adler_pre (d_wrap s) (z_adler z) ->
    exists s' z' bs evs, c_compress_func s z flush = Some (s', z', bs) /\ cpost W3 s z flush s' z' bs evs.

(** The stream after a call given the input object [inb] with next_in at [nin] (avail_in the rest of it),
    [aout] bytes of output space, total_in [tin], total_out [tout]: next_in moved on by the bytes consumed
    (total_in by as many, modulo 2^64), the bytes written. *)
Definition call_ok7 (inb : list Z) (nin aout tin tout : Z) (z' : strm) : Prop :=
  z_in z' = inb /\ nin <= z_next_in z' <= Zlength inb /\ z_avail_in z' = Zlength inb - z_next_in z' /\
  z_total_in z' = u64 (tin + (z_next_in z' - nin)) /\
  0 <= z_avail_out z' <= aout /\ Zlength (z_out z') = aout - z_avail_out z' /\
  z_total_out z' = tout + (aout - z_avail_out z') /\ rbytes (z_out z').

(** deflate(strm, flush) on Iapi7: any flush of zlib.h, the input object [inb] with next_in at [nin] and the
    rest of it offered (at most 2^32 - 1 bytes), [aout] < 2^32 bytes of output space, the data and the output
    below 2^64 bytes in all; once Z_FINISH was given, only Z_FINISH with the rest of the data. *)
Definition api7_deflate_stmt : Prop :=
  forall dict wrap D O fin s tin tout adler inb nin aout flush msg,
    Iapi7 W3 hinv7 dict wrap D O fin s tin tout adler ->
    0 <= flush <= 5 -> rbytes inb -> 0 <= nin <= Zlength inb -> Zlength inb - nin <= 4294967295 ->
    Zlength D + (Zlength inb - nin) <= 18446744073709551615 ->
    0 <= aout <= 4294967295 -> Zlength O + aout <= 18446744073709551615 ->
    (forall R, fin = Some R -> flush = Z_FINISH /\ R = sublist nin (Zlength inb) inb) ->
    exists s' z' code,
      c_deflate s (rzcall inb nin (Zlength inb - nin) tin aout tout adler msg) flush = Some (s', z', code) /\
      d_gzhead s' = d_gzhead s /\ d_w_bits s' = d_w_bits s /\ call_ok7 inb nin aout tin tout z' /\
      (0 <= adler < 4294967296 -> 0 <= z_adler z' < 4294967296) /\
      (code = Z_OK \/ code = Z_STREAM_END \/ code = Z_BUF_ERROR) /\
      (code = Z_STREAM_END -> flush = Z_FINISH /\ z_avail_in z' = 0) /\
      (code = Z_BUF_ERROR -> z_next_in z' = nin /\ z_avail_out z' = aout) /\
      (code <> Z_STREAM_END ->
       Iapi7 W3 hinv7 dict wrap (D ++ sublist nin (z_next_in z') inb) (O ++ z_out z')
         (if flush =? Z_FINISH then Some (sublist (z_next_in z') (Zlength inb) inb) else None)
         s' (z_total_in z') (z_total_out z') (z_adler z')).

(** ** The proof

    deflate_w (deflate/DetApiWide.v) for Iapi7: a call offered the input object from next_in 0 runs its four
    stages under RTK7DMid.Mid7 (RTK7DEntry, RTK7AStages, RTK7AComp; their invariant facts from RTK7DHdrSt and
    RTK7DTrail); a call with next_in at [nin] is the call on the rest of the object from next_in 0 with the bytes
    before [nin] put in front (DetShiftIn.deflate_pre).  The core facts come from comp_nocut7_stmt
    (RTK7ACore), the header facts from RTK7Hdr. *)
Require Zlib.proof.roundtrip.RTK7AStages.
Require Zlib.proof.roundtrip.RTK7AComp.
Require Zlib.proof.roundtrip.RTK7ACore.
Require Zlib.proof.roundtrip.RTK7Hdr.
Require Zlib.proof.deflate.DetShiftIn.
Require Zlib.proof.huffman.Lemmas.

Module ApiProof.
Import Zlib.proof.roundtrip.RTK7AStages Zlib.proof.roundtrip.RTK7AComp.

(* the call offered the whole object from next_in 0: it runs, and ends in Mid7 unless it returned Z_STREAM_END *)
Lemma api7_deflate0 : core_facts7 W3 -> hdr_facts7 hinv7 -> comp_nocut7_stmt ->
  forall dict wrap D O fin s tin tout adler inb aout flush msg,
    Iapi7 W3 hinv7 dict wrap D O fin s tin tout adler ->
    0 <= flush <= 5 -> rbytes inb -> Zlength inb <= 4294967295 ->
    Zlength D + Zlength inb <= 18446744073709551615 ->
    0 <= aout <= 4294967295 -> Zlength O + aout <= 18446744073709551615 ->
    (forall R, fin = Some R -> flush = Z_FINISH /\ inb = R) ->
    exists s' z' code,
      c_deflate s (rzcall inb 0 (Zlength inb) tin aout tout adler msg) flush = Some (s', z', code) /\
      d_gzhead s' = d_gzhead s /\ d_w_bits s' = d_w_bits s /\ zrun7 inb aout tin tout z' /\
      (0 <= adler < 4294967296 -> 0 <= z_adler z' < 4294967296) /\
      (code = Z_OK \/ code = Z_STREAM_END \/ code = Z_BUF_ERROR) /\
      (code = Z_STREAM_END -> flush = Z_FINISH /\ z_avail_in z' = 0) /\
      (code = Z_BUF_ERROR -> z_next_in z' = 0 /\ z_avail_out z' = aout) /\
      (code <> Z_STREAM_END -> Mid7 W3 hinv7 dict wrap D O inb aout tin tout flush s' z').
Proof.
  intros CF HF CN dict wrap D O fin s tin tout adler inb aout flush msg HIa Hfl Hb Hl Hd Ha Ho Hfin.
  change (rzcall inb 0 (Zlength inb) tin aout tout adler msg) with (zcall inb 0 (Zlength inb) tin aout tout adler msg).
  change (rbytes inb) with (bytes inb) in Hb.
  pose proof (mid7_start W3 hinv7 dict wrap D O fin s tin tout adler inb aout flush msg HIa Hb Hl Hd Ha Ho Hfin)
    as M0.
  set (z0 := zcall inb 0 (Zlength inb) tin aout tout adler msg) in *.
  assert (Ad0 : z_adler z0 = adler) by reflexivity.
  rewrite c_deflate_stages.
  rewrite (Iapi7_bad_state W3 hinv7 dict wrap D O fin s tin tout adler HF HIa).
  replace (flush >? Z_BLOCK) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; unfold Z_BLOCK; lia).
  replace (flush <? 0) with false by (symmetry; apply Z.ltb_ge; lia). cbn [orb].
  (* entry *)
  destruct (entry_ex7 W3 hinv7 dict wrap D O inb aout tin tout flush s z0 CF HF M0 eq_refl eq_refl eq_refl Hfl)
    as (s1 & z1 & o1 & E1 & G1 & M1 & P1).
  destruct (entry_keep _ _ _ _ _ _ E1) as [Wb1 A1].
  rewrite E1. destruct o1 as [c|].
  { cbn [then_stage bind]. exists s1, z1, c. split; [reflexivity|]. split; [exact G1|]. split; [exact Wb1|].
    split; [exact (proj1 M1)|]. split; [rewrite A1, Ad0; auto|].
    split; [destruct P1 as [->|(->&_)]; auto|].
    split; [intros E; exfalso; destruct P1 as [->|(->&_)]; discriminate|].
    split; [|intros _; exact M1].
    intros E. destruct P1 as [->|(_ & Hn & Hz)]; [discriminate|]. split; [exact Hn|].
    destruct M1 as ((_ & _ & _ & _ & _ & Hzl & _) & _). rewrite Hz, Zlength_nil in Hzl. lia. }
  cbn [then_stage bind]. destruct P1 as (Q1 & Q2 & Q3 & Q4 & Q5).
  (* the headers *)
  destruct (hdr_ex7 W3 hinv7 dict wrap D O inb aout tin tout flush s1 z1 CF HF M1 Q1 Q2 Hfl Q3 Q5)
    as (s2 & z2 & r2 & E2 & Wb2 & A2).
  destruct (hdr_stage_ok7 W3 hinv7 dict wrap D O inb aout tin tout flush s1 z1 s2 z2 r2 CF HF M1 Q1 Q2 Hfl Q3 Q5
              E2) as (G2 & M2 & N2 & P2).
  rewrite E2. destruct r2 as [c|].
  { cbn [then_stage bind]. exists s2, z2, c. split; [reflexivity|]. split; [congruence|]. split; [congruence|].
    split; [exact (proj1 M2)|]. split; [intros Hr; apply A2; rewrite A1, Ad0; exact Hr|].
    subst c. split; [left; reflexivity|]. split; [discriminate|]. split; [discriminate|]. intros _; exact M2. }
  cbn [then_stage bind]. destruct P2 as (R1 & R2).
  (* the compression *)
  destruct (comp_stage_ex7n W3 hinv7 dict wrap D O inb aout tin tout flush s2 z2 CF HF Hb CN M2 R1 Hfl R2)
    as (s3 & z3 & o3 & E3 & G3 & Wb3 & M3 & A3 & P3).
  rewrite E3. destruct o3 as [c|].
  { cbn [bind]. exists s3, z3, c. split; [reflexivity|]. split; [congruence|]. split; [congruence|].
    split; [exact (proj1 M3)|]. split; [intros Hr; apply A3, A2; rewrite A1, Ad0; exact Hr|].
    subst c. split; [left; reflexivity|]. split; [discriminate|]. split; [discriminate|]. intros _; exact M3. }
  cbn [bind]. destruct P3 as (T1 & T2 & T3).
  (* the trailer *)
  destruct (trailer_ex7 W3 hinv7 dict wrap D O inb aout tin tout flush s3 z3 CF HF M3 T1 Hfl T2 T3)
    as (s4 & z4 & c & E4 & Wb4 & A4 & End4).
  destruct (trailer_ok7 W3 hinv7 dict wrap D O inb aout tin tout flush s3 z3 s4 z4 c CF HF M3 T1 Hfl T2 T3 E4)
    as (G4 & P4).
  exists s4, z4, c. split; [exact E4|]. split; [congruence|]. split; [congruence|].
  assert (Hadl : 0 <= adler < 4294967296 -> 0 <= z_adler z4 < 4294967296)
    by (intros Hr; rewrite A4; apply A3, A2; rewrite A1, Ad0; exact Hr).
  destruct P4 as [(-> & M4) | ->].
  - split; [exact (proj1 M4)|]. split; [exact Hadl|]. split; [left; reflexivity|].
    split; [discriminate|]. split; [discriminate|]. intros _; exact M4.
  - destruct (End4 eq_refl) as (Hf & Hai & Zr).
    split; [exact Zr|]. split; [exact Hadl|]. split; [right; left; reflexivity|].
    split; [intros _; split; assumption|]. split; [discriminate|]. intros E; contradiction.
Qed.

(* the call with next_in at nin: the call on the rest of the object, shifted *)
Lemma api7_deflate_ok : comp_nocut7_stmt -> api7_deflate_stmt.
Proof.
  intros CN dict wrap D O fin s tin tout adler inb nin aout flush msg HIa Hfl Hb Hn Hl Hd Ha Ho Hfin.
  pose proof (proj1 Zlib.proof.huffman.Lemmas.huffman_lemmas) as Hov.
  pose proof (Zlib.proof.roundtrip.RTK7ACore.rtk7_core_nocut Hov CN) as CF.
  pose proof Zlib.proof.roundtrip.RTK7Hdr.rtk7_hdr_ok as HF.
  set (p := sublist 0 nin inb). set (inb' := sublist nin (Zlength inb) inb).
  assert (Hp : Zlength p = nin) by (subst p; rewrite Zlength_sublist; lia).
  assert (Hl' : Zlength inb' = Zlength inb - nin) by (subst inb'; rewrite Zlength_sublist; lia).
  assert (Hpi : p ++ inb' = inb) by (subst p inb'; rewrite <- sublist_split, sublist_same by lia; reflexivity).
  assert (Hb' : rbytes inb') by (apply Forall_sublist; exact Hb).
  destruct (api7_deflate0 CF HF CN dict wrap D O fin s tin tout adler inb' aout flush msg HIa Hfl Hb'
              ltac:(lia) ltac:(lia) Ha Ho ltac:(intros R HR; destruct (Hfin R HR) as [Hf HR']; split; [exact Hf|rewrite HR'; reflexivity]))
    as (s' & z0 & code & E & G & Wb & Zr & Ad & Hc & Hend & Hbuf & Hm).
  pose proof (Zlib.proof.deflate.DetShiftIn.deflate_pre p _ _ _ _ _ _ E) as E'.
  assert (Ez : Zlib.proof.deflate.DetShiftIn.zpre p (rzcall inb' 0 (Zlength inb') tin aout tout adler msg) =
               rzcall inb nin (Zlength inb - nin) tin aout tout adler msg).
  { unfold Zlib.proof.deflate.DetShiftIn.zpre, rzcall.
    cbn [z_in z_next_in z_avail_in z_total_in z_out z_avail_out z_total_out z_adler z_msg]. rewrite Hpi, Hp, Hl', Z.add_0_r. reflexivity. }
  rewrite Ez in E'.
  set (z' := Zlib.proof.deflate.DetShiftIn.zpre p z0) in *.
  destruct Zr as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8).
  assert (Hni : z_next_in z' = nin + z_next_in z0) 
    by (subst z'; unfold Zlib.proof.deflate.DetShiftIn.zpre; cbn [z_next_in]; rewrite Hp; reflexivity).
  assert (Hsub : forall k, 0 <= k <= Zlength inb' -> sublist nin (nin + k) inb = sublist 0 k inb').
  { intros k Hk. subst inb'. rewrite sublist_sublist by lia. f_equal; lia. }
  assert (Hrest : sublist (z_next_in z') (Zlength inb) inb = sublist (z_next_in z0) (Zlength inb') inb').
  { rewrite Hni. subst inb'. rewrite sublist_sublist by lia. f_equal; lia. }
  exists s', z', code. split; [exact E'|]. split; [exact G|]. split; [exact Wb|].
  split.
  { unfold call_ok7. subst z'; cbn [Zlib.proof.deflate.DetShiftIn.zpre z_in z_next_in z_avail_in z_total_in
      z_avail_out z_out z_total_out].
    rewrite Z1, Hpi, Hp. pose proof (Zlength_nonneg (z_out z0)).
    repeat split; try lia; [rewrite Z4; f_equal; lia|exact Z8]. }
  split; [exact Ad|]. split; [exact Hc|].
  split; [intros Ec; destruct (Hend Ec) as [Hf Hai]; split; [exact Hf|exact Hai]|].
  split; [intros Ec; destruct (Hbuf Ec) as [Hn0 Hao]; split; [lia|exact Hao]|].
  intros Hne. destruct (Hm Hne) as (_ & _ & _ & _ & _ & Hi).
  rewrite Hrest, Hni, Hsub by lia.
  unfold fin_of in Hi. exact Hi.
Qed.

End ApiProof.

Theorem rtk7_api_deflate : comp_nocut7_stmt -> api7_deflate_stmt.
Proof. exact ApiProof.api7_deflate_ok. Qed.
