(* The header stages of deflate() keep KMid (the functional half): RTDDgHdr.kf_hdr_ok for Mid7. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTK7DMid.
Require Import Zlib.proof.roundtrip.RTDDfHdrBytes Zlib.proof.roundtrip.RTDDgHdr.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** The header bytes for the headers of the short laws *)

(* RTDDfHdrBytes.hb_cstr for the strings of rcstr_ok7 *)
Lemma hb7_cstr : forall o, rcstr_ok7 o ->
  cstr_bytes o = match option_map (@removelast Z) o with Some n => n ++ [0] | None => [] end.
Proof.
  intros [l|] Hc; [|reflexivity]. destruct (Hc l eq_refl) as [l0 [-> _]].
  simpl. rewrite removelast_last. reflexivity.
Qed.

(* RTDDfHdrBytes.hb_body for rhdr_ok7: the text, hcrc and os fields enter the header only through their tests
   and their low byte *)
Lemma hb7_body : forall h xfl, rhdr_ok7 h -> 0 <= xfl < 256 ->
  gz_body h xfl = F.gz_bytes0 (fhdr_of (Some h) xfl).
Proof.
  intros h xfl (Ht & Hh & Hos & Htm & Hel & Hx & Hn & Hc) Hxfl.
  unfold gz_body, gz_pre, gz_extra_bytes, F.gz_bytes0, F.gz_flg, fhdr_of, gz_flags. cbn [F.gz_text F.gz_hcrc F.gz_extra
    F.gz_name F.gz_comment F.gz_mtime F.gz_xfl F.gz_os].
  rewrite (hb7_cstr _ Hn), (hb7_cstr _ Hc), hb_le4, !hb_land255.
  destruct (gz_text h =? 0), (gz_hcrc h =? 0); cbn [negb];
  destruct (gz_extra h) as [x|] eqn:Ex; cbn [option_map];
  destruct (gz_name h), (gz_comment h); cbn [option_map];
  unfold u8; cbn [map app]; rewrite ?Zmod_mod, (Z.mod_small xfl) by lia;
  try reflexivity;
  (destruct (Hx x eq_refl) as [Lx _];
   change 65535 with (Z.ones 16); rewrite Z.land_ones by lia;
   rewrite (Z.mod_small (gz_extra_len h) (2 ^ 16)) by lia;
   rewrite hb_le2, Zlength_sublist by lia; rewrite Z.sub_0_r; reflexivity).
Qed.

(* RTDDfHdrBytes.hb_gz_some for rhdr_ok7 *)
Lemma hb7_gz_some : forall h xfl, rhdr_ok7 h -> 0 <= xfl < 256 ->
  gz_hdr_bytes (Some h) xfl = F.gz_bytes (fhdr_of (Some h) xfl).
Proof.
  intros h xfl Hok Hxfl. unfold gz_hdr_bytes, F.gz_bytes.
  rewrite (hb7_body h xfl Hok Hxfl).
  replace (F.gz_hcrc (fhdr_of (Some h) xfl)) with (negb (gz_hcrc h =? 0)) by reflexivity.
  destruct (gz_hcrc h =? 0); cbn [negb]; [apply app_nil_r|].
  f_equal. rewrite hb_le2, !hb_land255. reflexivity.
Qed.

(** ** Helpers *)

(* RTDDgHdr.kh_fresh for rhdr_ok7: the header in Format's terms, from a fresh stream *)
Lemma kh7_fresh : forall dict wrap s a,
  prm s -> d_wrap s = wrap -> 0 <= wrap <= 2 -> (forall h, d_gzhead s = Some h -> rhdr_ok7 h) ->
  (d_strstart s = 0 <-> dict = []) -> (wrap = 1 -> a = radler 1 dict) ->
  khdr dict wrap s (hdr_bytes s a).
Proof.
  intros dict wrap s a Hp Hw Hr Hg Hss Ha. unfold hdr_bytes. rewrite Hw.
  assert (wrap = 0 \/ wrap = 1 \/ wrap = 2) as [->|[->| ->]] by lia.
  - reflexivity.
  - apply hb_zlib; [exact Hp|exact Hss|intros _; apply Ha; reflexivity].
  - unfold khdr. cbn [Z.eqb Pos.eqb]. exists (xfl_byte s). split; [apply kh_xfl|].
    destruct (d_gzhead s) as [h|] eqn:E.
    + apply hb7_gz_some; [exact (Hg h eq_refl)|].
      destruct (kh_xfl s) as [->|[->| ->]]; lia.
    + apply hb_gz_none.
Qed.

(* RTDDgHdr.kf_tail for hinv7: after hdr_post, KMid at the end *)
Lemma kf7_tail : hdr_facts7 hinv7 -> forall dict wrap D O inb s z H k s' z' r,
  KMid dict wrap D O inb s z ->
  d_status s <> BUSY_STATE -> d_status s <> FINISH_STATE -> 0 <= k ->
  O ++ z_out z = sublist 0 k H -> khdr dict wrap s H ->
  hdr_post hinv7 s z H k s' z' r ->
  d_w_bits s' = d_w_bits s /\ KMid dict wrap D O inb s' z'.
Proof.
  intros HF dict wrap D O inb s z H k s' z' r HK Hn1 Hn2 Hk0 HO HH HP.
  destruct HK as [[Hgz [BS [syms [Hkc Hcase]]]] _].
  destruct Hcase as [(_ & _ & -> & Hbv) | [(A & _) | (A & _)]]; [| congruence | congruence].
  destruct HP as (Hce & Hout' & Hwr' & Hgz' & Hbv' & x & k' & Hk & Hx & ZS & Hr).
  destruct ZS as (Zin' & Zni' & Zai' & Zti' & Zo' & _).
  pose proof (kh_wbits _ _ Hce) as Hw.
  assert (HH' : khdr dict wrap s' H) by exact (kh_frame _ _ _ _ _ Hw Hgz' HH).
  assert (HO' : (O ++ z_out z') ++ pend s' = sublist 0 k' H).
  { rewrite Zo', !app_assoc, HO, <- app_assoc, Hx. apply sublist_rejoin; lia. }
  assert (Hbi : bibits s' = []) by (unfold bibits; rewrite Hbv', Hbv; reflexivity).
  assert (Hbusy : d_status s' = BUSY_STATE -> k' = Zlength H ->
                  allbits (O ++ z_out z') s' = F.bytes_bits H ++ enc_from 0 [] false).
  { intros _ E. unfold allbits. rewrite HO', Hbi, E, sublist_same by reflexivity. cbn [enc_from].
    rewrite !app_nil_r. reflexivity. }
  split; [exact Hw|].
  unfold KMid, KFd, KF2g. rewrite Zni'.
  split.
  2:{ intros _ _. exists H. split; [exact HH'|]. rewrite HO', Zlength_sublist by lia.
      f_equal; lia. }
  split; [rewrite Hgz'; exact Hgz|].
  exists [], syms. split; [exact (kcore3_frame _ _ _ _ _ _ Hce Hkc)|].
  destruct r as [c|].
  - destruct Hr as (_ & _ & _ & _ & [(Hb & Hk' & _)|HI']).
    + right; left. split; [exact Hb|]. exists H. split; [exact HH'|]. exact (Hbusy Hb Hk').
    + left. destruct (hf7_status _ HF _ _ _ _ HI') as (_ & _ & Hst & _).
      split; [destruct Hst as [S|[S|[S|S]]]; rewrite S; discriminate|].
      split; [destruct Hst as [S|[S|[S|S]]]; rewrite S; discriminate|].
      split; [reflexivity|]. rewrite Hbv'; exact Hbv.
  - destruct Hr as (Hk' & Hb & _).
    right; left. split; [exact Hb|]. exists H. split; [exact HH'|]. exact (Hbusy Hb Hk').
Qed.

Lemma kf_hdr_ok7 : core_facts7 W3 -> hdr_facts7 hinv7 ->
  forall dict wrap D O inb aout tin tout flush s z s2 z2 r,
  Mid7 W3 hinv7 dict wrap D O inb aout tin tout flush s z ->
  KMid dict wrap D O inb s z ->
  d_pending s = 0 -> d_last_flush s = flush -> 0 <= flush <= 5 -> 0 < z_avail_out z ->
  (d_status s = FINISH_STATE -> z_avail_in z = 0) ->
  hdr_stages s z = Some (s2, z2, r) ->
  d_w_bits s2 = d_w_bits s /\ KMid dict wrap D O inb s2 z2.
Proof.
  intros CF HF dict wrap D O inb aout tin tout flush s z s2 z2 r M HK Hpend Hlf Hfl Hao Hfin HS2.
  destruct M as (ZR & Hsz1 & Hsz2 & Hsz3 & Hsz4 & IA).
  destruct IA as (HW & Hout & Hwr0 & Hw2 & Hbd & Hld & Hlfr & Hgz & Hto & HbO & HbD & HDl & Htin & HF6 & _ & Hph).
  pose proof ZR as (Zin & Zni & Zai & Zti & Zao & Zol & Zto & Zbo).
  assert (Hzao : 0 <= z_avail_out z <= 4294967295) by (pose proof (Zlength_nonneg (z_out z)); lia).
  assert (Hzto : 0 <= z_total_out z /\ z_total_out z + z_avail_out z <= 18446744073709551615).
  { rewrite Hto, Zlength_app. pose proof (Zlength_nonneg O). pose proof (Zlength_nonneg (z_out z)). lia. }
  pose proof (W3_prm _ HW) as Hprm.
  assert (Hp0 : pend s = []) by (unfold pend; rewrite Hpend, Z.add_0_r; apply sublist_nil).
  destruct Hph as [P0 | [Hlf2 [P1 | [P2 | P3]]]].
  - destruct P0 as (Hst & Hw & HD & HO & _ & Hbv & Hsym & _ & _ & Hss & Had).
    set (H := hdr_bytes s (z_adler z)).
    assert (HH : khdr dict wrap s H).
    { apply kh7_fresh; auto. }
    assert (Hpre : hdr_pre7 hinv7 s z H 0).
    { unfold hdr_pre7. split; [exact Hprm|]. split; [exact Hout|]. split; [exact Hpend|].
      split; [exact Hsym|]. split; [exact Hbv|]. split; [exact Hzao|]. split; [exact (proj1 Hzto)|].
      split; [exact (proj2 Hzto)|]. split; [exact Hgz|].
      destruct Hst as [[Hst Hwl]|[Hst Hw2']]; [left|right; left]; repeat split; auto; lia. }
    destruct (hf7_run _ HF _ _ _ _ Hpre) as (s' & z' & r' & HS & HP).
    rewrite HS2 in HS. injection HS as <- <- <-.
    assert (N : d_status s <> BUSY_STATE /\ d_status s <> FINISH_STATE)
      by (destruct Hst as [[S _]|[S _]]; rewrite S; split; discriminate).
    refine (kf7_tail HF dict wrap D O inb s z H 0 s2 z2 r HK (proj1 N) (proj2 N) ltac:(lia) _ HH HP).
    rewrite HO. symmetry. apply sublist_nil.
  - destruct P1 as (Hw & HD & HOne & Hbv & Hsym & H & k & HIk & HOk).
    destruct (hf7_status _ HF _ _ _ _ HIk) as (Hw' & [h Hh] & Hst & [xfl HX] & Hk).
    assert (N : d_status s <> BUSY_STATE /\ d_status s <> FINISH_STATE)
      by (destruct Hst as [S|[S|[S|S]]]; rewrite S; split; discriminate).
    rewrite Hp0, app_nil_r in HOk.
    assert (HH : khdr dict wrap s H).
    { destruct HK as [_ HK]. destruct (HK (proj1 N) (proj2 N)) as (HDR & HHD & HE).
      rewrite Hp0, app_nil_r, HOk in HE.
      assert (Hok : rhdr_ok7 h) by exact (Hgz h Hh).
      subst wrap. pose proof HHD as HHD'. unfold khdr in HHD'. cbn [Z.eqb Pos.eqb] in HHD'.
      destruct HHD' as (x' & Hx' & EHDR).
      rewrite Hh in HX, EHDR. rewrite <- hb7_gz_some in EHDR by (exact Hok || lia).
      assert (E8 : u8 xfl = x').
      { rewrite Zlength_sublist in HE by lia. rewrite Z.sub_0_r in HE.
        assert (Z8 : Znth 8 (sublist 0 k H) = Znth 8 (sublist 0 k HDR)) by (rewrite <- HE; reflexivity).
        rewrite !Znth_sublist in Z8 by lia. rewrite Z.add_0_r in Z8.
        rewrite HX, EHDR, !kh_gz_8 in Z8. rewrite Z8. unfold u8. apply Z.mod_small. lia. }
      replace H with HDR; [exact HHD|]. rewrite HX, EHDR, <- E8. apply kh_gz_u8. }
    assert (Hpre : hdr_pre7 hinv7 s z H k).
    { unfold hdr_pre7. split; [exact Hprm|]. split; [exact Hout|]. split; [exact Hpend|].
      split; [exact Hsym|]. split; [exact Hbv|]. split; [exact Hzao|]. split; [exact (proj1 Hzto)|].
      split; [exact (proj2 Hzto)|]. split; [exact Hgz|]. right; right; exact HIk. }
    destruct (hf7_run _ HF _ _ _ _ Hpre) as (s' & z' & r' & HS & HP).
    rewrite HS2 in HS. injection HS as <- <- <-.
    exact (kf7_tail HF dict wrap D O inb s z H k s2 z2 r HK (proj1 N) (proj2 N) ltac:(lia) HOk HH HP).
  - rewrite hdr_stages_busy in HS2 by (left; apply P2). injection HS2 as <- <- <-. auto.
  - rewrite hdr_stages_busy in HS2 by (right; apply P3). injection HS2 as <- <- <-. auto.
Qed.
