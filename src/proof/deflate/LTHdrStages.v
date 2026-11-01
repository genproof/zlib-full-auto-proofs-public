(** * The header part of the deflate laws' theory: the stages of deflate()'s header

    From the kit (LTHdrKit.v) and the two loop stages (LTHdrExtra.v, LTHdrStr.v): the HCRC, NAME, COMMENT,
    GZIP and zlib header stages, each from its entry to [hdr_post hinv] or the entry of the next stage.
 *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTHdrKit.
Require Import Zlib.proof.deflate.LTHdrExtra Zlib.proof.deflate.LTHdrStr.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** From the kit's states to [hdr_post] *)

Lemma post_none : forall s0 z0 H k0 s z,
  hmid s0 z0 H k0 s z (Zlength H) -> d_status s = BUSY_STATE -> d_pending s = 0 ->
  z_adler z = hdr_adler (d_wrap s0) (z_adler z0) -> hdr_post hinv s0 z0 H k0 s z None.
Proof.
  intros s0 z0 H k0 s z [[Hc [Hp [Ho [Hb0 [Hbv [Hs [Hw [Hg [Hpb [Hk0 [Hk [x [Hx Hz]]]]]]]]]]]]] [Hpo [Hlf Hav]]] Hst P0 Ha.
  split; [exact Hc|]. split; [exact Ho|]. split; [exact Hw|]. split; [exact Hg|]. split; [congruence|].
  exists x, (Zlength H). split; [lia|]. split; [exact Hx|]. split; [exact Hz|].
  repeat split; assumption.
Qed.

Lemma post_ret_busy : forall s0 z0 H k0 s z,
  hret s0 z0 H k0 s z (Zlength H) -> d_status s = BUSY_STATE ->
  z_adler z = hdr_adler (d_wrap s0) (z_adler z0) -> hdr_post hinv s0 z0 H k0 s z (Some Z_OK).
Proof.
  intros s0 z0 H k0 s z [[Hc [Hp [Ho [Hb0 [Hbv [Hs [Hw [Hg [Hpb [Hk0 [Hk [x [Hx Hz]]]]]]]]]]]]] [Hlf [Hav P0]]] Hst Ha.
  split; [exact Hc|]. split; [exact Ho|]. split; [exact Hw|]. split; [exact Hg|]. split; [congruence|].
  exists x, (Zlength H). split; [lia|]. split; [exact Hx|]. split; [exact Hz|].
  split; [reflexivity|]. split; [exact Hav|]. split; [exact P0|]. split; [exact Hlf|].
  left. auto.
Qed.

Lemma post_stop : forall s0 z0 H k0 s z,
  hstop s0 z0 H k0 s z -> hdr_post hinv s0 z0 H k0 s z (Some Z_OK).
Proof.
  intros s0 z0 H k0 s z [kk [[[Hc [Hp [Ho [Hb0 [Hbv [Hs [Hw [Hg [Hpb [Hk0 [Hk [x [Hx Hz]]]]]]]]]]]]] [Hlf [Hav P0]]] Hi]].
  split; [exact Hc|]. split; [exact Ho|]. split; [exact Hw|]. split; [exact Hg|]. split; [congruence|].
  exists x, kk. split; [lia|]. split; [exact Hx|]. split; [exact Hz|].
  split; [reflexivity|]. split; [exact Hav|]. split; [exact P0|]. split; [exact Hlf|].
  right. exact Hi.
Qed.

(** ** The layout of the gzip header *)

Lemma sublist_mid : forall (A B C : list Z),
  sublist (Zlength A) (Zlength A + Zlength B) (A ++ B ++ C) = B.
Proof.
  intros A B C. pose proof (Zlength_nonneg A). pose proof (Zlength_nonneg B).
  rewrite sublist_app2 by lia. replace (Zlength A - Zlength A) with 0 by lia.
  replace (Zlength A + Zlength B - Zlength A) with (Zlength B) by lia.
  rewrite sublist0_app1 by lia. apply sublist_same; lia.
Qed.

Lemma gz_pre_len : forall h xfl, Zlength (gz_pre h xfl) = 10.
Proof. intros. unfold gz_pre. rewrite Zlength_map. reflexivity. Qed.

Lemma gz_extra_len_eq : forall h, hdr_ok h ->
  Zlength (gz_extra_bytes h) = match gz_extra h with Some _ => 2 + gz_extra_len h | None => 0 end.
Proof.
  intros h [_ [_ [_ [_ [Hl [Hx _]]]]]]. unfold gz_extra_bytes.
  destruct (gz_extra h) as [x|] eqn:E; [|reflexivity].
  destruct (Hx x eq_refl) as [Lx _].
  assert (E2 : Z.land (gz_extra_len h) 65535 = gz_extra_len h).
  { change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
  rewrite Zlength_app, E2, Zlength_sublist by lia. rewrite Zlength_map. cbn. lia.
Qed.

Lemma gz_body_len : forall h xfl,
  Zlength (gz_body h xfl) =
  10 + Zlength (gz_extra_bytes h) + Zlength (cstr_bytes (gz_name h)) + Zlength (cstr_bytes (gz_comment h)).
Proof. intros. unfold gz_body. rewrite !Zlength_app, gz_pre_len. lia. Qed.

Definition gz_crc_bytes (h : gzh) (xfl : Z) : list Z :=
  if gz_hcrc h =? 0 then []
  else let c := Zlib.proof.crc32.Model.ref_crc32 0 (gz_body h xfl) in [Z.land c 255; Z.land (Z.shiftr c 8) 255].

Lemma gz_hdr_split : forall h xfl,
  gz_hdr_bytes (Some h) xfl =
  gz_pre h xfl ++ gz_extra_bytes h ++ cstr_bytes (gz_name h) ++ cstr_bytes (gz_comment h) ++ gz_crc_bytes h xfl.
Proof. intros. unfold gz_hdr_bytes, gz_crc_bytes. unfold gz_body at 1. rewrite !app_assoc. reflexivity. Qed.

Lemma cstr_len : forall o, cstr_ok o -> match o with Some l => 0 < Zlength l | None => True end.
Proof.
  intros [l|] Ho; [|exact I]. destruct (Ho l eq_refl) as [l0 [-> _]].
  rewrite Zlength_app. pose proof (Zlength_nonneg l0). cbn. lia.
Qed.

Lemma u8_land255 : forall y, u8 (Z.land y 255) = Z.land y 255.
Proof.
  intros y. unfold u8. apply Z.mod_small. change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
  apply Z.mod_pos_bound. lia.
Qed.

Lemma gent_facts : forall s0 z0 H k0 st s z,
  gent s0 z0 H k0 st s z -> d_wrap s0 = 2 /\ bytes H.
Proof.
  intros s0 z0 H k0 st s z [_ [Hw [h [xfl [_ [Hok [EH [_ [Hm _]]]]]]]]].
  split.
  - destruct Hm as [[_ [_ [_ [_ [_ [_ [Hw0 _]]]]]]] _]. congruence.
  - subst H. apply gz_hdr_bytes_bytes. exact Hok.
Qed.

Lemma prm_pbs : forall s, prm s -> 512 <= d_pending_buf_size s <= 131072.
Proof.
  intros s Hp. destruct Hp as [_ [_ [_ [[Hh1 Hh2] [_ [_ [_ [HL [P1 _]]]]]]]]].
  assert (2 ^ 7 <= 2 ^ (d_hash_bits s - 1)) by (apply Z.pow_le_mono_r; lia).
  assert (2 ^ (d_hash_bits s - 1) <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Lemma hmid_pbs : forall s0 z0 H k0 s z kk, hmid s0 z0 H k0 s z kk -> 512 <= d_pending_buf_size s <= 131072.
Proof. intros s0 z0 H k0 s z kk [[_ [Hp _]] _]. exact (prm_pbs s Hp). Qed.

(** ** HCRC_STATE *)
Lemma hcrc_stage : forall s0 z0 H k0 s z,
  gent s0 z0 H k0 HCRC_STATE s z ->
  exists s' z' r, c_deflate_hcrc s z = Some (s', z', r) /\ hdr_post hinv s0 z0 H k0 s' z' r.
Proof.
  intros s0 z0 H k0 s z Hge.
  destruct (gent_facts _ _ _ _ _ _ _ Hge) as [Hw0 Hb].
  destruct Hge as [Hst [Hw [h [xfl [Eh [Hok [EH [Hidx [Hm Ha]]]]]]]]].
  assert (Ek : gpos h HCRC_STATE (d_gzindex s) = Zlength (gz_body h xfl)).
  { change (gpos h HCRC_STATE (d_gzindex s)) with (Zlength (gz_body h 0)). rewrite !gz_body_len. reflexivity. }
  rewrite Ek in Hm, Ha.
  assert (Hadl : hdr_adler (d_wrap s0) (z_adler z0) = 0) by (rewrite Hw0; reflexivity).
  unfold c_deflate_hcrc. rewrite Hst. cbn [Z.eqb Pos.eqb HCRC_STATE]. unfold c_gzhead. rewrite Eh. cbn [bind].
  destruct (gz_hcrc h =? 0) eqn:Ehc.
  - assert (EH' : H = gz_body h xfl) by (rewrite EH; unfold gz_hdr_bytes; rewrite Ehc, app_nil_r; reflexivity).
    rewrite <- EH' in Hm.
    cbn [then_stage bind].
    destruct (flush_or_return_mid _ _ _ _ _ _ _ (hmid_status _ _ _ _ _ _ _ BUSY_STATE Hm))
      as [s' [z' [r [E [Es [_ [Eadl Hr]]]]]]].
    rewrite E. exists s', z', r. split; [reflexivity|].
    assert (Ha' : z_adler z' = hdr_adler (d_wrap s0) (z_adler z0))
      by (rewrite Eadl, Ha, Hadl; unfold hadler; rewrite Ehc; reflexivity).
    destruct r as [c|].
    + destruct Hr as [-> Hr]. apply post_ret_busy; auto.
    + destruct Hr as [Hr P0]. apply post_none; auto.
  - set (B := gz_body h xfl) in *.
    set (c := Zlib.proof.crc32.Model.ref_crc32 0 B).
    pose proof (Zlength_nonneg B) as HBn.
    assert (EH' : H = B ++ [Z.land c 255; Z.land (Z.shiftr c 8) 255])
      by (rewrite EH; unfold gz_hdr_bytes; rewrite Ehc; reflexivity).
    assert (LH : Zlength H = Zlength B + 2) by (rewrite EH', Zlength_app; reflexivity).
    assert (Hac : z_adler z = c).
    { rewrite Ha. unfold hadler. rewrite Ehc. unfold c. f_equal. rewrite EH', sublist0_app1 by lia.
      apply sublist_same; lia. }
    assert (Pre : exists s1 z1 r1,
      (if u64 (d_pending s + 2) >? d_pending_buf_size s then c_flush_or_return s z else Some (s, z, None)) =
        Some (s1, z1, r1) /\ d_status s1 = HCRC_STATE /\ d_gzindex s1 = d_gzindex s /\ z_adler z1 = c /\
      match r1 with
      | None => hmid s0 z0 H k0 s1 z1 (Zlength B) /\ d_pending s1 + 2 <= d_pending_buf_size s1
      | Some c => c = Z_OK /\ hret s0 z0 H k0 s1 z1 (Zlength B)
      end).
    { destruct (hmid_buf_len _ _ _ _ _ _ _ Hm) as [Lb [Lm [Hp0 Hp1]]].
      destruct (u64 (d_pending s + 2) >? d_pending_buf_size s) eqn:Eu.
      - destruct (flush_or_return_mid _ _ _ _ _ _ _ Hm) as [s1 [z1 [r1 [E [Es [Eg [Eadl Hr]]]]]]].
        exists s1, z1, r1. split; [exact E|]. split; [congruence|]. split; [exact Eg|]. split; [congruence|].
        destruct r1 as [c1|]; [exact Hr|]. destruct Hr as [Hr P0]. split; [exact Hr|].
        rewrite P0. pose proof (hmid_pbs _ _ _ _ _ _ _ Hr). lia.
      - exists s, z, None. split; [reflexivity|]. split; [exact Hst|]. split; [reflexivity|].
        split; [exact Hac|]. split; [exact Hm|].
        pose proof (hmid_pbs _ _ _ _ _ _ _ Hm).
        rewrite Z.gtb_ltb, Z.ltb_ge in Eu. unfold u64 in Eu. rewrite Z.mod_small in Eu; lia. }
    destruct Pre as [s1 [z1 [r1 [E1 [Es1 [Eg1 [Ea1 Hr1]]]]]]].
    rewrite E1. destruct r1 as [c1|].
    + destruct Hr1 as [-> Hr1]. cbn [then_stage bind].
      exists s1, z1, (Some Z_OK). split; [reflexivity|]. apply post_stop. exists (Zlength B).
      split; [exact Hr1|].
      destruct Hr1 as [[_ [_ [_ [_ [_ [_ [Hw1 [Hg1 _]]]]]]]] _].
      assert (Hgs : d_gzhead s0 = Some h) by (destruct Hm as [[_ [_ [_ [_ [_ [_ [_ [Hg0 _]]]]]]]] _]; congruence).
      split; [congruence|]. exists h, xfl. split; [congruence|]. split; [exact Hok|]. split; [exact EH|].
      split; [right; right; right; split; [exact Es1|]; apply Z.eqb_neq; exact Ehc|].
      rewrite Es1. split; [exact I|]. split.
      * change (gpos h HCRC_STATE (d_gzindex s1)) with (Zlength (gz_body h 0)). unfold B. rewrite !gz_body_len. reflexivity.
      * rewrite Ea1, <- Hac, Ha. reflexivity.
    + destruct Hr1 as [Hm1 Hroom]. cbn [then_stage bind].
      destruct (dput_bytes_mid [Z.land (z_adler z1) 255; Z.land (Z.shiftr (z_adler z1) 8) 255]
                  s0 z0 H k0 s1 z1 (Zlength B) Hm1) as [o [E2 [Hm2 Hp2]]].
      * exact Hroom.
      * assert (L2 : Zlength [Z.land (z_adler z1) 255; Z.land (Z.shiftr (z_adler z1) 8) 255] = 2) by reflexivity.
        rewrite L2, LH. lia.
      * rewrite Ea1. cbn [map]. rewrite !u8_land255. rewrite EH'.
        change (Zlength [Z.land c 255; Z.land (Z.shiftr c 8) 255]) with 2.
        rewrite sublist_app2 by (pose proof (Zlength_nonneg B); lia). rewrite Z.sub_diag.
        replace (Zlength B + 2 - Zlength B) with 2 by lia. reflexivity.
      * rewrite E2. cbn [bind then_stage].
        change (Zlength [Z.land (z_adler z1) 255; Z.land (Z.shiftr (z_adler z1) 8) 255]) with 2 in Hm2.
        rewrite <- LH in Hm2.
        destruct (flush_or_return_mid _ _ _ _ _ _ _
                    (hmid_status _ _ _ _ _ _ _ BUSY_STATE (hmid_adler _ _ _ _ _ _ _ 0 Hm2)))
          as [s' [z' [r [E [Es [_ [Eadl Hr]]]]]]].
        rewrite E. exists s', z', r. split; [reflexivity|].
        assert (Ha' : z_adler z' = hdr_adler (d_wrap s0) (z_adler z0)) by (rewrite Eadl, Hadl; reflexivity).
        destruct r as [c2|].
        -- destruct Hr as [-> Hr]. apply post_ret_busy; auto.
        -- destruct Hr as [Hr P0]. apply post_none; auto.
Qed.

(** ** NAME_STATE and COMMENT_STATE *)

Lemma hdr_ok_cstr : forall h, hdr_ok h -> cstr_ok (gz_name h) /\ cstr_ok (gz_comment h).
Proof. intros h [_ [_ [_ [_ [_ [_ [Hn Hc]]]]]]]. auto. Qed.

Lemma name_stage : forall s0 z0 H k0 s z,
  gent s0 z0 H k0 NAME_STATE s z ->
  exists s' z' r, c_deflate_name s z = Some (s', z', r) /\
    match r with
    | None => gent s0 z0 H k0 COMMENT_STATE s' z'
    | Some c => c = Z_OK /\ hstop s0 z0 H k0 s' z'
    end.
Proof.
  intros s0 z0 H k0 s z Hge.
  destruct (gent_facts _ _ _ _ _ _ _ Hge) as [Hw0 Hb].
  destruct Hge as [Hst [Hw [h [xfl [Eh [Hok [EH [Hidx [Hm Ha]]]]]]]]].
  destruct (hdr_ok_cstr h Hok) as [Cn Cc].
  set (base := 10 + Zlength (gz_extra_bytes h)).
  change (gpos h NAME_STATE (d_gzindex s)) with (10 + Zlength (gz_extra_bytes h) + d_gzindex s) in Hm, Ha.
  fold base in Hm, Ha.
  change (gidx_ok h NAME_STATE (d_gzindex s))
    with (match gz_name h with Some l => 0 <= d_gzindex s < Zlength l | None => d_gzindex s = 0 end) in Hidx.
  assert (Hsplit : H = (gz_pre h xfl ++ gz_extra_bytes h) ++ cstr_bytes (gz_name h) ++
                       (cstr_bytes (gz_comment h) ++ gz_crc_bytes h xfl))
    by (rewrite EH, gz_hdr_split, !app_assoc; reflexivity).
  assert (Lbase : Zlength (gz_pre h xfl ++ gz_extra_bytes h) = base)
    by (rewrite Zlength_app, gz_pre_len; reflexivity).
  destruct (str_stage s0 z0 H k0 s z h (gz_name h) true base Hm Eh Hb Cn ltac:(unfold base; pose proof (Zlength_nonneg (gz_extra_bytes h)); lia) Hidx)
    as [s' [z' [r [E [Es [Eg [Ew Hr]]]]]]].
  - rewrite Hsplit, Zlength_app, Lbase, !Zlength_app. pose proof (Zlength_nonneg (cstr_bytes (gz_comment h))).
    pose proof (Zlength_nonneg (gz_crc_bytes h xfl)). lia.
  - rewrite Hsplit, <- Lbase. apply sublist_mid.
  - exact Ha.
  - unfold c_deflate_name. rewrite Hst. cbn [Z.eqb Pos.eqb NAME_STATE]. unfold c_gzhead. rewrite Eh.
    cbn [bind]. rewrite E. cbn [then_stage bind].
    destruct r as [c|].
    + exists s', z', (Some c). split; [reflexivity|].
      destruct Hr as [-> [Hne [Hg' [Hr Ha']]]]. split; [reflexivity|].
      exists (base + d_gzindex s'). split; [exact Hr|].
      split; [congruence|]. exists h, xfl. split; [congruence|]. split; [exact Hok|]. split; [exact EH|].
      rewrite Es, Hst. split; [right; left; auto|].
      split.
      * change (gidx_ok h NAME_STATE (d_gzindex s'))
          with (match gz_name h with Some l => 0 <= d_gzindex s' < Zlength l | None => d_gzindex s' = 0 end).
        destruct (gz_name h); [exact Hg'|contradiction].
      * split; [reflexivity|exact Ha'].
    + exists (set_d_status s' COMMENT_STATE), z', None. split; [reflexivity|].
      destruct Hr as [Hm' [Hg0 Ha']].
      split; [reflexivity|]. split; [change (d_wrap s' = 2); congruence|]. exists h, xfl.
      split; [change (d_gzhead s' = Some h); congruence|]. split; [exact Hok|].
      split; [exact EH|].
      cbn [d_gzindex set_d_status]. rewrite (Hg0 eq_refl).
      assert (Ep : gpos h COMMENT_STATE 0 = base + Zlength (cstr_bytes (gz_name h))).
      { change (gpos h COMMENT_STATE 0)
          with (10 + Zlength (gz_extra_bytes h) + Zlength (cstr_bytes (gz_name h)) + 0). unfold base. lia. }
      split.
      * change (gidx_ok h COMMENT_STATE 0)
          with (match gz_comment h with Some l => 0 <= 0 < Zlength l | None => 0 = 0 end).
        pose proof (cstr_len _ Cc). destruct (gz_comment h); [lia|reflexivity].
      * rewrite Ep. split; [apply hmid_status; exact Hm'|exact Ha'].
Qed.

Lemma comment_stage : forall s0 z0 H k0 s z,
  gent s0 z0 H k0 COMMENT_STATE s z ->
  exists s' z' r, c_deflate_comment s z = Some (s', z', r) /\
    match r with
    | None => gent s0 z0 H k0 HCRC_STATE s' z'
    | Some c => c = Z_OK /\ hstop s0 z0 H k0 s' z'
    end.
Proof.
  intros s0 z0 H k0 s z Hge.
  destruct (gent_facts _ _ _ _ _ _ _ Hge) as [Hw0 Hb].
  destruct Hge as [Hst [Hw [h [xfl [Eh [Hok [EH [Hidx [Hm Ha]]]]]]]]].
  destruct (hdr_ok_cstr h Hok) as [Cn Cc].
  set (base := 10 + Zlength (gz_extra_bytes h) + Zlength (cstr_bytes (gz_name h))).
  change (gpos h COMMENT_STATE (d_gzindex s))
    with (10 + Zlength (gz_extra_bytes h) + Zlength (cstr_bytes (gz_name h)) + d_gzindex s) in Hm, Ha.
  fold base in Hm, Ha.
  change (gidx_ok h COMMENT_STATE (d_gzindex s))
    with (match gz_comment h with Some l => 0 <= d_gzindex s < Zlength l | None => d_gzindex s = 0 end) in Hidx.
  assert (Hsplit : H = (gz_pre h xfl ++ gz_extra_bytes h ++ cstr_bytes (gz_name h)) ++
                       cstr_bytes (gz_comment h) ++ gz_crc_bytes h xfl)
    by (rewrite EH, gz_hdr_split, !app_assoc; reflexivity).
  assert (Lbase : Zlength (gz_pre h xfl ++ gz_extra_bytes h ++ cstr_bytes (gz_name h)) = base)
    by (rewrite !Zlength_app, gz_pre_len; unfold base; lia).
  destruct (str_stage s0 z0 H k0 s z h (gz_comment h) false base Hm Eh Hb Cc ltac:(unfold base; pose proof (Zlength_nonneg (gz_extra_bytes h)); pose proof (Zlength_nonneg (cstr_bytes (gz_name h))); lia) Hidx)
    as [s' [z' [r [E [Es [Eg [Ew Hr]]]]]]].
  - rewrite Hsplit, Zlength_app, Lbase, !Zlength_app.
    pose proof (Zlength_nonneg (gz_crc_bytes h xfl)). lia.
  - rewrite Hsplit, <- Lbase. apply sublist_mid.
  - exact Ha.
  - unfold c_deflate_comment. rewrite Hst. cbn [Z.eqb Pos.eqb COMMENT_STATE]. unfold c_gzhead. rewrite Eh.
    cbn [bind]. rewrite E. cbn [then_stage bind].
    destruct r as [c|].
    + exists s', z', (Some c). split; [reflexivity|].
      destruct Hr as [-> [Hne [Hg' [Hr Ha']]]]. split; [reflexivity|].
      exists (base + d_gzindex s'). split; [exact Hr|].
      split; [congruence|]. exists h, xfl. split; [congruence|]. split; [exact Hok|]. split; [exact EH|].
      rewrite Es, Hst. split; [right; right; left; auto|].
      split.
      * change (gidx_ok h COMMENT_STATE (d_gzindex s'))
          with (match gz_comment h with Some l => 0 <= d_gzindex s' < Zlength l | None => d_gzindex s' = 0 end).
        destruct (gz_comment h); [exact Hg'|contradiction].
      * split; [reflexivity|exact Ha'].
    + exists (set_d_status s' HCRC_STATE), z', None. split; [reflexivity|].
      destruct Hr as [Hm' [_ Ha']].
      split; [reflexivity|]. split; [change (d_wrap s' = 2); congruence|]. exists h, xfl.
      split; [change (d_gzhead s' = Some h); congruence|]. split; [exact Hok|].
      split; [exact EH|].
      assert (Ep : gpos h HCRC_STATE (d_gzindex (set_d_status s' HCRC_STATE)) =
                   base + Zlength (cstr_bytes (gz_comment h))).
      { change (gpos h HCRC_STATE (d_gzindex (set_d_status s' HCRC_STATE))) with (Zlength (gz_body h 0)).
        rewrite gz_body_len. unfold base. lia. }
      split; [exact I|].
      rewrite Ep. split; [apply hmid_status; exact Hm'|exact Ha'].
Qed.

(** ** The start of the header stages *)

Lemma hmid_init : forall s z H,
  prm s -> outok s -> d_pending s = 0 -> d_sym_next s = 0 -> d_bi_valid s = 0 ->
  0 <= z_avail_out z -> 0 <= z_total_out z <= 1099511627776 -> hmid s z H 0 s z 0.
Proof.
  intros s z H Hp Ho P0 Hs Hbv Hav Ht.
  assert (Hpo : d_po s = 0) by (destruct Ho as [_ [_ [_ [_ [_ O]]]]]; auto).
  split; [|split; [exact Hpo|split; [reflexivity|exact Hav]]].
  split; [split; [reflexivity|split; [reflexivity|split; reflexivity]]|].
  split; [exact Hp|]. split; [exact Ho|]. split; [exact Hbv|]. split; [exact Hbv|]. split; [exact Hs|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [pose proof (Zlength_nonneg H); lia|].
  exists []. split.
  - unfold pend. rewrite P0, Z.add_0_r, !sublist_nil. reflexivity.
  - unfold zout_step. rewrite app_nil_r. cbn [Zlength Zlength_aux]. rewrite Z.add_0_r, Z.sub_0_r.
    unfold u64. rewrite Z.mod_small by lia. repeat split; reflexivity.
Qed.

Lemma sublist_at : forall A l C kk, kk = Zlength A -> sublist kk (kk + Zlength l) (A ++ map u8 l ++ C) = map u8 l.
Proof. intros A l C kk ->. rewrite <- (Zlength_map _ _ u8 l). apply sublist_mid. Qed.

Lemma hmid_kk_le : forall s0 z0 H k0 s z kk, hmid s0 z0 H k0 s z kk -> 0 <= kk <= Zlength H.
Proof. intros s0 z0 H k0 s z kk [[_ [_ [_ [_ [_ [_ [_ [_ [_ [Hk0 [Hk _]]]]]]]]]]] _]. lia. Qed.

(** ** GZIP_STATE *)

Lemma xfl_byte_range : forall s, u8 (xfl_byte s) = xfl_byte s.
Proof.
  intros s. unfold xfl_byte.
  destruct (d_level s =? 9); [reflexivity|]. destruct (_ || _); reflexivity.
Qed.

Lemma gzip_stage : forall s z,
  prm s -> outok s -> d_pending s = 0 -> d_sym_next s = 0 -> d_bi_valid s = 0 ->
  0 <= z_avail_out z -> 0 <= z_total_out z <= 1099511627776 ->
  d_status s = GZIP_STATE -> d_wrap s = 2 -> (forall h, d_gzhead s = Some h -> hdr_ok h) ->
  exists s' z' r, c_deflate_gzip_header s z = Some (s', z', r) /\
    ((r = None /\ gent s z (gz_hdr_bytes (d_gzhead s) (xfl_byte s)) 0 EXTRA_STATE s' z') \/
     (d_status s' = BUSY_STATE /\ hdr_post hinv s z (gz_hdr_bytes (d_gzhead s) (xfl_byte s)) 0 s' z' r)).
Proof.
  intros s z Hp Ho P0 Hs Hbv Hav Ht Hst Hw Hok.
  set (H := gz_hdr_bytes (d_gzhead s) (xfl_byte s)).
  pose proof (hmid_init s z H Hp Ho P0 Hs Hbv Hav Ht) as Hm0.
  pose proof (hmid_adler _ _ _ _ _ _ _ 0 Hm0) as Hm1.
  pose proof (prm_pbs s Hp) as Hpbs.
  unfold c_deflate_gzip_header. rewrite Hst. cbn [Z.eqb Pos.eqb GZIP_STATE].
  destruct (d_gzhead s) as [h|] eqn:Eh.
  - (* a user header *)
    specialize (Hok h eq_refl).
    set (t := gz_time h).
    set (l2 := [gz_flags h; Z.land t 255; Z.land (Z.shiftr t 8) 255; Z.land (Z.shiftr t 16) 255;
                Z.land (Z.shiftr t 24) 255; xfl_byte s; Z.land (gz_os h) 255]).
    set (R := gz_extra_bytes h ++ cstr_bytes (gz_name h) ++ cstr_bytes (gz_comment h) ++ gz_crc_bytes h (xfl_byte s)).
    assert (EH : H = map u8 [31; 139; 8] ++ map u8 l2 ++ R)
      by (unfold H; rewrite gz_hdr_split; reflexivity).
    assert (LR : 0 <= Zlength R) by apply Zlength_nonneg.
    destruct (dput_bytes_mid [31; 139; 8] s z H 0 s (set_z_adler z 0) 0 Hm1) as [o1 [E1 [Hm2 Hp2]]].
    { rewrite P0. cbn. lia. }
    { rewrite EH, !Zlength_app, !Zlength_map. cbn. lia. }
    { rewrite EH. apply (sublist_at []). reflexivity. }
    rewrite E1. cbn [bind].
    change (d_gzhead (set_d_out s o1)) with (d_gzhead s). rewrite Eh.
    change (xfl_byte (set_d_out s o1)) with (xfl_byte s). change (gz_time h) with t. fold l2.
    destruct (dput_bytes_mid l2 s z H 0 (set_d_out s o1) (set_z_adler z 0) (0 + Zlength [31; 139; 8]) Hm2)
      as [o2 [E2 [Hm3 Hp3]]].
    { rewrite Hp2, P0. change (d_pending_buf_size (set_d_out s o1)) with (d_pending_buf_size s). cbn. lia. }
    { rewrite EH, !Zlength_app, !Zlength_map. cbn. lia. }
    { rewrite EH. apply sublist_at. reflexivity. }
    rewrite E2. cbn [bind]. rewrite set_d_out_twice in Hm3, Hp3 |- *.
    change (0 + Zlength [31; 139; 8] + Zlength l2) with 10 in Hm3.
    change (Zlength [31; 139; 8]) with 3 in Hp2. change (Zlength l2) with 7 in Hp3.
    assert (Hel : 0 <= gz_extra_len h <= 4096) by (destruct Hok as [_ [_ [_ [_ [Hel _]]]]]; exact Hel).
    assert (X : exists s4,
      (match gz_extra h with
       | Some _ => c_dput_bytes (set_d_out s o2)
                     [Z.land (gz_extra_len h) 255; Z.land (Z.shiftr (gz_extra_len h) 8) 255]
       | None => Some (set_d_out s o2) end) = Some s4 /\
      hmid s z H 0 s4 (set_z_adler z 0) (gpos h EXTRA_STATE 0) /\ d_pending s4 = gpos h EXTRA_STATE 0 /\
      d_wrap s4 = 2 /\ d_gzhead s4 = Some h).
    { change (gpos h EXTRA_STATE 0) with (10 + match gz_extra h with Some _ => 2 + 0 | None => 0 end).
      destruct (gz_extra h) as [x|] eqn:Ex.
      - set (l3 := [Z.land (gz_extra_len h) 255; Z.land (Z.shiftr (gz_extra_len h) 8) 255]).
        assert (EH3 : H = (map u8 [31; 139; 8] ++ map u8 l2) ++ map u8 l3 ++
                          (sublist 0 (Z.land (gz_extra_len h) 65535) x ++ cstr_bytes (gz_name h) ++
                           cstr_bytes (gz_comment h) ++ gz_crc_bytes h (xfl_byte s))).
        { rewrite EH. unfold R, gz_extra_bytes. rewrite Ex. rewrite !app_assoc. reflexivity. }
        destruct (dput_bytes_mid l3 s z H 0 (set_d_out s o2) (set_z_adler z 0) 10 Hm3) as [o3 [E3 [Hm4 Hp4]]].
        + rewrite Hp3, Hp2, P0. change (d_pending_buf_size (set_d_out s o2)) with (d_pending_buf_size s). cbn. lia.
        + rewrite EH3, !Zlength_app, !Zlength_map. change (Zlength [31; 139; 8]) with 3.
          change (Zlength l2) with 7. change (Zlength l3) with 2.
          pose proof (Zlength_nonneg (sublist 0 (Z.land (gz_extra_len h) 65535) x)).
          pose proof (Zlength_nonneg (cstr_bytes (gz_name h))). pose proof (Zlength_nonneg (cstr_bytes (gz_comment h))).
          pose proof (Zlength_nonneg (gz_crc_bytes h (xfl_byte s))). lia.
        + rewrite EH3. apply sublist_at. reflexivity.
        + exists (set_d_out (set_d_out s o2) o3). rewrite set_d_out_twice in *.
          split; [exact E3|]. split; [exact Hm4|]. split.
          * rewrite Hp4, Hp3, Hp2, P0. reflexivity.
          * split; [exact Hw|exact Eh].
      - exists (set_d_out s o2). split; [reflexivity|]. split; [exact Hm3|]. split.
        + rewrite Hp3, Hp2, P0. reflexivity.
        + split; [exact Hw|exact Eh]. }
    destruct X as [s4 [E4 [Hm4 [Hp4 [Hw4 Hg4]]]]].
    rewrite E4. cbn [bind].
    assert (HbH : bytes H) by (unfold H; apply gz_hdr_bytes_bytes; exact Hok).
    assert (Hz : exists z4, (if gz_hcrc h =? 0 then Some (set_z_adler z 0) else
                 let* bytes := mb_read (d_pb s4) 0 (d_pending s4) in
                 Some (set_z_adler (set_z_adler z 0)
                   (Zlib.proof.crc32.Model.ref_crc32 (z_adler (set_z_adler z 0)) bytes))) = Some z4 /\
                 z4 = set_z_adler z (hadler h H (gpos h EXTRA_STATE 0))).
    { unfold hadler. destruct (gz_hcrc h =? 0).
      - exists (set_z_adler z 0). split; reflexivity.
      - pose proof (mid_read s z H 0 s4 (set_z_adler z 0) (gpos h EXTRA_STATE 0) 0 Hm4) as Hr.
        rewrite Z.sub_0_r, Hp4, Z.sub_diag, Z.add_0_r in Hr. rewrite Hp4, Hr by (change (gpos h EXTRA_STATE 0) with (10 + match gz_extra h with Some _ => 2 + 0 | None => 0 end); destruct (gz_extra h); lia). cbn [bind].
        eexists. split; [reflexivity|]. reflexivity. }
    destruct Hz as [z4 [Ez4 ->]]. rewrite Ez4.
    exists (set_d_status (set_d_gzindex s4 0) EXTRA_STATE), (set_z_adler z (hadler h H (gpos h EXTRA_STATE 0))), None.
    split; [reflexivity|]. left. split; [reflexivity|].
    split; [reflexivity|]. split; [exact Hw4|]. exists h, (xfl_byte s).
    split; [exact Hg4|]. split; [exact Hok|]. split; [reflexivity|].
    change (d_gzindex (set_d_status (set_d_gzindex s4 0) EXTRA_STATE)) with 0.
    split.
    + change (gidx_ok h EXTRA_STATE 0)
        with (match gz_extra h with Some _ => 0 <= 0 <= gz_extra_len h | None => 0 = 0 end).
      destruct (gz_extra h); [lia|reflexivity].
    + split; [|reflexivity].
      apply hmid_status, hmid_gzindex. 
      destruct Hm4 as [[Hc [Hpr [Hou [Hb0 [Hbv4 [Hs4 [Hw' [Hg' [Hpb [Hk0 [Hk [x [Hx Hzs]]]]]]]]]]]]] Hrest].
      split; [|exact Hrest].
      repeat (split; [assumption|]). exists x. split; [exact Hx|].
      unfold zout_step in *. cbn [z_in z_next_in z_avail_in z_total_in z_out z_avail_out z_total_out z_adler z_msg set_z_adler] in *.
      intuition.
  - set (l2 := [0; 0; 0; 0; 0; xfl_byte s; OS_CODE]).
    assert (EH : H = map u8 [31; 139; 8] ++ map u8 l2 ++ []).
    { unfold H, l2, gz_hdr_bytes. cbn [map app]. rewrite xfl_byte_range. reflexivity. }
    destruct (dput_bytes_mid [31; 139; 8] s z H 0 s (set_z_adler z 0) 0 Hm1) as [o1 [E1 [Hm2 Hp2]]].
    { rewrite P0. cbn. lia. }
    { rewrite EH, !Zlength_app, !Zlength_map. cbn. lia. }
    { rewrite EH. apply (sublist_at []). reflexivity. }
    rewrite E1. cbn [bind].
    change (d_gzhead (set_d_out s o1)) with (d_gzhead s). rewrite Eh.
    change (xfl_byte (set_d_out s o1)) with (xfl_byte s). fold l2.
    destruct (dput_bytes_mid l2 s z H 0 (set_d_out s o1) (set_z_adler z 0) (0 + Zlength [31; 139; 8]) Hm2)
      as [o2 [E2 [Hm3 Hp3]]].
    { rewrite Hp2, P0. change (d_pending_buf_size (set_d_out s o1)) with (d_pending_buf_size s). cbn. lia. }
    { rewrite EH, !Zlength_app, !Zlength_map. cbn. lia. }
    { rewrite EH. apply sublist_at. reflexivity. }
    rewrite E2. cbn [bind]. rewrite set_d_out_twice in Hm3 |- *.
    change (0 + Zlength [31; 139; 8] + Zlength l2) with (Zlength H) in Hm3.
    destruct (flush_or_return_mid _ _ _ _ _ _ _ (hmid_status _ _ _ _ _ _ _ BUSY_STATE Hm3))
      as [s' [z' [r [E [Es [_ [Eadl Hr]]]]]]].
    rewrite E. exists s', z', r. split; [reflexivity|]. right. split; [exact Es|].
    assert (Ha' : z_adler z' = hdr_adler (d_wrap s) (z_adler z)) by (rewrite Eadl, Hw; reflexivity).
    destruct r as [c|].
    + destruct Hr as [-> Hr]. apply post_ret_busy; auto.
    + destruct Hr as [Hr P1]. apply post_none; auto.
Qed.

(** ** INIT_STATE: the zlib header (or none for a raw stream) *)

Lemma putShortMSB_bytes : forall s b, c_putShortMSB s b = c_dput_bytes s [Z.shiftr b 8; Z.land b 255].
Proof.
  intros s b. unfold c_putShortMSB. cbn [c_dput_bytes].
  destruct (c_dput_byte s (Z.shiftr b 8)) as [s1|]; cbn [bind]; [|reflexivity].
  destruct (c_dput_byte s1 (Z.land b 255)); reflexivity.
Qed.

Lemma zlib_stage : forall s z,
  prm s -> outok s -> d_pending s = 0 -> d_sym_next s = 0 -> d_bi_valid s = 0 ->
  0 <= z_avail_out z -> 0 <= z_total_out z <= 1099511627776 ->
  d_status s = INIT_STATE -> 0 <= d_wrap s <= 1 ->
  exists s' z' r, c_deflate_zlib_header s z = Some (s', z', r) /\ d_status s' = BUSY_STATE /\
    hdr_post hinv s z (hdr_bytes s (z_adler z)) 0 s' z' r.
Proof.
  intros s z Hp Ho P0 Hs Hbv Hav Ht Hst Hw.
  set (H := hdr_bytes s (z_adler z)).
  pose proof (hmid_init s z H Hp Ho P0 Hs Hbv Hav Ht) as Hm0.
  pose proof (prm_pbs s Hp) as Hpbs.
  unfold c_deflate_zlib_header. rewrite Hst. cbn [Z.eqb Pos.eqb INIT_STATE andb].
  destruct (Z.eq_dec (d_wrap s) 0) as [W0|W0].
  - rewrite W0. cbn [Z.eqb]. cbn [d_status set_d_status Z.eqb Pos.eqb BUSY_STATE INIT_STATE].
    exists (set_d_status s BUSY_STATE), z, None. split; [reflexivity|]. split; [reflexivity|].
    assert (EH : H = []) by (unfold H, hdr_bytes; rewrite W0; reflexivity).
    apply post_none.
    + rewrite EH. rewrite EH in Hm0. apply hmid_status. exact Hm0.
    + reflexivity.
    + exact P0.
    + rewrite W0. reflexivity.
  - assert (W1 : d_wrap s = 1) by lia. rewrite W1. cbn [Z.eqb Pos.eqb].
    rewrite Hst. cbn [Z.eqb Pos.eqb INIT_STATE].
    set (a := z_adler z).
    set (l1 := [Z.shiftr (zlib_header s) 8; Z.land (zlib_header s) 255]).
    set (D := if d_strstart s =? 0 then [] else msb2 (u32 (Z.shiftr a 16)) ++ msb2 (u32 (Z.land a 65535))).
    assert (EH : H = [] ++ map u8 l1 ++ D) by (unfold H, hdr_bytes; rewrite W1; reflexivity).
    rewrite putShortMSB_bytes. fold l1.
    destruct (dput_bytes_mid l1 s z H 0 s z 0 Hm0) as [o1 [E1 [Hm1 Hp1]]].
    { rewrite P0. cbn. lia. }
    { rewrite EH, !Zlength_app, Zlength_map. pose proof (Zlength_nonneg D). cbn. lia. }
    { rewrite EH. apply sublist_at. reflexivity. }
    rewrite E1. cbn [bind]. change (d_strstart (set_d_out s o1)) with (d_strstart s).
    change (0 + Zlength l1) with 2 in Hm1. change (Zlength l1) with 2 in Hp1.
    assert (X : exists s2, (if d_strstart s =? 0 then Some (set_d_out s o1) else
                 let* s1 := c_putShortMSB (set_d_out s o1) (u32 (Z.shiftr a 16)) in
                 c_putShortMSB s1 (u32 (Z.land a 65535))) = Some s2 /\ hmid s z H 0 s2 z (Zlength H)).
    { destruct (d_strstart s =? 0) eqn:Ess.
      - exists (set_d_out s o1). split; [reflexivity|].
        replace (Zlength H) with 2 by (rewrite EH; unfold D; try rewrite Ess; reflexivity). exact Hm1.
      - set (l2 := [Z.shiftr (u32 (Z.shiftr a 16)) 8; Z.land (u32 (Z.shiftr a 16)) 255]).
        set (l3 := [Z.shiftr (u32 (Z.land a 65535)) 8; Z.land (u32 (Z.land a 65535)) 255]).
        assert (EH2 : H = map u8 l1 ++ map u8 l2 ++ map u8 l3)
          by (rewrite EH; unfold D; try rewrite Ess; reflexivity).
        rewrite putShortMSB_bytes. fold l2.
        destruct (dput_bytes_mid l2 s z H 0 (set_d_out s o1) z 2 Hm1) as [o2 [E2 [Hm2 Hp2]]].
        { rewrite Hp1, P0. change (d_pending_buf_size (set_d_out s o1)) with (d_pending_buf_size s). cbn. lia. }
        { rewrite EH2, !Zlength_app, !Zlength_map. cbn. lia. }
        { rewrite EH2. apply sublist_at. reflexivity. }
        rewrite E2. cbn [bind]. rewrite set_d_out_twice in Hm2, Hp2 |- *. rewrite putShortMSB_bytes. fold l3.
        destruct (dput_bytes_mid l3 s z H 0 (set_d_out s o2) z (2 + Zlength l2) Hm2) as [o3 [E3 [Hm3 Hp3]]].
        { rewrite Hp2, Hp1, P0. change (d_pending_buf_size (set_d_out s o2)) with (d_pending_buf_size s). cbn. lia. }
        { rewrite EH2, !Zlength_app, !Zlength_map. cbn. lia. }
        { rewrite EH2, app_assoc, <- (app_nil_r (map u8 l3)). apply sublist_at. reflexivity. }
        rewrite E3. exists (set_d_out (set_d_out s o2) o3). split; [reflexivity|].
        rewrite set_d_out_twice. replace (Zlength H) with (2 + Zlength l2 + Zlength l3)
          by (rewrite EH2; reflexivity). exact Hm3. }
    destruct X as [s2 [E2 Hm2]]. rewrite E2. cbn [bind].
    destruct (flush_or_return_mid _ _ _ _ _ _ _
                (hmid_status _ _ _ _ _ _ _ BUSY_STATE (hmid_adler _ _ _ _ _ _ _ 1 Hm2)))
      as [s' [z' [r [E [Es [_ [Eadl Hr]]]]]]].
    rewrite E. exists s', z', r. split; [reflexivity|]. split; [exact Es|].
    assert (Ha' : z_adler z' = hdr_adler (d_wrap s) (z_adler z)) by (rewrite Eadl, W1; reflexivity).
    destruct r as [c|].
    + destruct Hr as [-> Hr]. apply post_ret_busy; auto.
    + destruct Hr as [Hr P1]. apply post_none; auto.
Qed.

Lemma hmid_init_k : forall s z H k,
  prm s -> outok s -> d_pending s = 0 -> d_sym_next s = 0 -> d_bi_valid s = 0 ->
  0 <= z_avail_out z -> 0 <= z_total_out z <= 1099511627776 -> 0 <= k <= Zlength H -> hmid s z H k s z k.
Proof.
  intros s z H k Hp Ho P0 Hs Hbv Hav Ht Hk.
  assert (Hpo : d_po s = 0) by (destruct Ho as [_ [_ [_ [_ [_ O]]]]]; auto).
  split; [|split; [exact Hpo|split; [reflexivity|exact Hav]]].
  split; [split; [reflexivity|split; [reflexivity|split; reflexivity]]|].
  split; [exact Hp|]. split; [exact Ho|]. split; [exact Hbv|]. split; [exact Hbv|]. split; [exact Hs|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [lia|].
  exists []. split.
  - unfold pend. rewrite P0, Z.add_0_r, !sublist_nil. reflexivity.
  - unfold zout_step. rewrite app_nil_r. cbn [Zlength Zlength_aux]. rewrite Z.add_0_r, Z.sub_0_r.
    unfold u64. rewrite Z.mod_small by lia. repeat split; reflexivity.
Qed.

(** ** The stages that do nothing in other states *)
Lemma zlib_id : forall s z, d_status s <> INIT_STATE -> c_deflate_zlib_header s z = Some (s, z, None).
Proof.
  intros s z H. unfold c_deflate_zlib_header. apply Z.eqb_neq in H. rewrite H. cbn [andb]. rewrite H. reflexivity.
Qed.
Lemma gzip_id : forall s z, d_status s <> GZIP_STATE -> c_deflate_gzip_header s z = Some (s, z, None).
Proof. intros s z H. unfold c_deflate_gzip_header. apply Z.eqb_neq in H. rewrite H. reflexivity. Qed.
Lemma extra_id : forall s z, d_status s <> EXTRA_STATE -> c_deflate_extra s z = Some (s, z, None).
Proof. intros s z H. unfold c_deflate_extra. apply Z.eqb_neq in H. rewrite H. reflexivity. Qed.
Lemma name_id : forall s z, d_status s <> NAME_STATE -> c_deflate_name s z = Some (s, z, None).
Proof. intros s z H. unfold c_deflate_name. apply Z.eqb_neq in H. rewrite H. reflexivity. Qed.
Lemma comment_id : forall s z, d_status s <> COMMENT_STATE -> c_deflate_comment s z = Some (s, z, None).
Proof. intros s z H. unfold c_deflate_comment. apply Z.eqb_neq in H. rewrite H. reflexivity. Qed.
Lemma hcrc_id : forall s z, d_status s <> HCRC_STATE -> c_deflate_hcrc s z = Some (s, z, None).
Proof. intros s z H. unfold c_deflate_hcrc. apply Z.eqb_neq in H. rewrite H. reflexivity. Qed.

(** ** Chains of stages *)
Definition from_comment (s : dstate) (z : strm) : option dres :=
  then_stage (c_deflate_comment s z) c_deflate_hcrc.
Definition from_name (s : dstate) (z : strm) : option dres :=
  then_stage (c_deflate_name s z) from_comment.
Definition from_extra (s : dstate) (z : strm) : option dres :=
  then_stage (c_deflate_extra s z) from_name.

Lemma hdr_stages_eq : forall s z,
  hdr_stages s z = then_stage (c_deflate_zlib_header s z) (fun s z =>
                   then_stage (c_deflate_gzip_header s z) from_extra).
Proof. reflexivity. Qed.

Lemma busy_rest : forall s z, d_status s = BUSY_STATE ->
  then_stage (c_deflate_gzip_header s z) from_extra = Some (s, z, None) /\ from_extra s z = Some (s, z, None).
Proof.
  intros s z H.
  assert (A : from_extra s z = Some (s, z, None)).
  { unfold from_extra. rewrite extra_id by (rewrite H; discriminate). cbn [then_stage bind].
    unfold from_name. rewrite name_id by (rewrite H; discriminate). cbn [then_stage bind].
    unfold from_comment. rewrite comment_id by (rewrite H; discriminate). cbn [then_stage bind].
    rewrite hcrc_id by (rewrite H; discriminate). reflexivity. }
  split; [|exact A]. rewrite gzip_id by (rewrite H; discriminate). cbn [then_stage bind]. exact A.
Qed.

Lemma chain_comment : forall s0 z0 H k0 s z, gent s0 z0 H k0 COMMENT_STATE s z ->
  exists s' z' r, from_comment s z = Some (s', z', r) /\ hdr_post hinv s0 z0 H k0 s' z' r.
Proof.
  intros s0 z0 H k0 s z Hg. destruct (comment_stage _ _ _ _ _ _ Hg) as [s1 [z1 [r1 [E Hr]]]].
  unfold from_comment. rewrite E. destruct r1 as [c|].
  - destruct Hr as [-> Hr]. exists s1, z1, (Some Z_OK). split; [reflexivity|]. apply post_stop. exact Hr.
  - cbn [then_stage bind]. apply hcrc_stage. exact Hr.
Qed.

Lemma chain_name : forall s0 z0 H k0 s z, gent s0 z0 H k0 NAME_STATE s z ->
  exists s' z' r, from_name s z = Some (s', z', r) /\ hdr_post hinv s0 z0 H k0 s' z' r.
Proof.
  intros s0 z0 H k0 s z Hg. destruct (name_stage _ _ _ _ _ _ Hg) as [s1 [z1 [r1 [E Hr]]]].
  unfold from_name. rewrite E. destruct r1 as [c|].
  - destruct Hr as [-> Hr]. exists s1, z1, (Some Z_OK). split; [reflexivity|]. apply post_stop. exact Hr.
  - cbn [then_stage bind]. apply chain_comment. exact Hr.
Qed.

Lemma chain_extra : forall s0 z0 H k0 s z, gent s0 z0 H k0 EXTRA_STATE s z ->
  exists s' z' r, from_extra s z = Some (s', z', r) /\ hdr_post hinv s0 z0 H k0 s' z' r.
Proof.
  intros s0 z0 H k0 s z Hg. destruct (extra_stage _ _ _ _ _ _ Hg) as [s1 [z1 [r1 [E Hr]]]].
  unfold from_extra. rewrite E. destruct r1 as [c|].
  - destruct Hr as [-> Hr]. exists s1, z1, (Some Z_OK). split; [reflexivity|]. apply post_stop. exact Hr.
  - cbn [then_stage bind]. apply chain_name. exact Hr.
Qed.
