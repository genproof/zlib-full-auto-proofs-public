(* The header stages of deflate() (hdr_stages) keep Mid7: RTDDfXHdrSt.hdr_stage_ok for the streams of RTK7Defs,
   from core_facts7 and hdr_facts7. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTK7DMid.
Require Import Zlib.proof.roundtrip.RTDDfXHdrSt.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** The gzip header bytes of the headers rhdr_ok7 (RTDDfXHdrSt.hs_gz_good for these headers) *)
Lemma hs_cstr_bytes7 : forall o, rcstr_ok7 o -> bytes (cstr_bytes o).
Proof.
  intros [l|] H; simpl; [|constructor].
  destruct (H l eq_refl) as (l0 & -> & _ & F). apply Forall_app. split; [|constructor; [lia|constructor]].
  eapply Forall_impl; [|exact F]. intros b Hb; cbv beta in *; lia.
Qed.

Lemma hs_gz_good7 : forall o xfl,
  (forall h, o = Some h -> rhdr_ok7 h) -> (o = None -> 0 <= xfl < 256) ->
  hdr_good [] 2 (gz_hdr_bytes o xfl).
Proof.
  intros o xfl Hh Hx. unfold hdr_good.
  split; [|split; [intros; lia|split; [intros; lia|intros _]]].
  - destruct o as [h|].
    + destruct (Hh h eq_refl) as (_ & _ & _ & _ & _ & Hex & Hn & Hc).
      unfold gz_hdr_bytes.
      set (c := Zlib.proof.crc32.Model.ref_crc32 0 (gz_body h xfl)).
      apply Forall_app; split.
      * unfold gz_body. apply Forall_app; split; [apply hs_bytes_map_u8|].
        apply Forall_app; split; [|apply Forall_app; split; apply hs_cstr_bytes7; assumption].
        unfold gz_extra_bytes. destruct (gz_extra h) as [x|] eqn:E; [|constructor].
        apply Forall_app; split; [apply hs_bytes_map_u8|]. apply Forall_sublist. apply (Hex x eq_refl).
      * destruct (gz_hcrc h =? 0); [constructor|].
        constructor; [apply hs_land255|constructor; [apply hs_land255|constructor]].
    + specialize (Hx eq_refl). unfold gz_hdr_bytes, OS_CODE.
      repeat (constructor; [lia|]). constructor.
  - destruct o as [h|].
    + unfold gz_hdr_bytes.
      set (c := Zlib.proof.crc32.Model.ref_crc32 0 (gz_body h xfl)).
      set (tl := if gz_hcrc h =? 0 then [] else [Z.land c 255; Z.land (Z.shiftr c 8) 255]).
      unfold gz_body, gz_pre.
      set (X := gz_extra_bytes h ++ cstr_bytes (gz_name h) ++ cstr_bytes (gz_comment h)).
      cbn [map app].
      change (u8 31) with 31. change (u8 139) with 139. change (u8 8) with 8.
      split; [|reflexivity].
      rewrite !Zlength_cons. pose proof (Zlength_nonneg ((X ++ tl))). rewrite Zlength_app in *. lia.
    + split; reflexivity.
Qed.

(** ** From hdr_post back to Mid7 (RTDDfXHdrSt.hdr_tail for Mid7, given the run of the stages) *)
Lemma hdr_tail7 : forall W HI dict wrap D O inb aout tin tout flush s z H k s' z' r,
  core_facts7 W -> hdr_facts7 HI -> Mid7 W HI dict wrap D O inb aout tin tout flush s z ->
  d_pending s = 0 -> d_last_flush s = flush -> 0 <= flush <= 5 -> 0 < z_avail_out z ->
  d_wrap s = wrap -> d_bi_valid s = 0 -> d_sym_next s = 0 -> hdr_good dict wrap H -> 0 <= k ->
  D ++ sublist 0 (z_next_in z) inb = [] -> O ++ z_out z = sublist 0 k H ->
  hdr_stages s z = Some (s', z', r) -> hdr_post HI s z H k s' z' r ->
  d_gzhead s' = d_gzhead s /\ Mid7 W HI dict wrap D O inb aout tin tout flush s' z' /\
  z_next_in z' = z_next_in z /\
  match r with
  | Some c => c = Z_OK
  | None => d_pending s' = 0 /\ (d_status s' = BUSY_STATE \/ (d_status s' = FINISH_STATE /\ z_avail_in z' = 0))
  end.
Proof.
  intros W HI dict wrap D O inb aout tin tout flush s z H k s' z' r CF HF M Hpend Hlf Hfl Hao
    Hwr Hbv Hsym HG Hk0 HD HO HS HP.
  destruct M as (ZR & Hsz1 & Hsz2 & Hsz3 & Hsz4 & IA).
  destruct IA as (HW & Hout & Hwr0 & Hw2 & Hbd & Hld & Hlfr & Hgz & Hto & HbO & HbD & HlD & Htin & HF6 & Hdz & Hph).
  destruct ZR as (Zin & Zni & Zai & Zti & Zao & Zol & Zto & Zbo).
  destruct HP as (Hce & Hout' & Hwr' & Hgz' & Hbv' & x & k' & Hk & Hx & ZS & Hr).
  destruct ZS as (Zin' & Zni' & Zai' & Zti' & Zo' & Zao' & Zto' & Zad' & Zmsg').
  pose proof (hdr_stages_ao _ _ _ _ _ HS ltac:(lia)) as Hao2.
  pose proof (hs_sym _ _ Hce) as CEF.
  assert (HbH : bytes H) by apply HG.
  assert (Hbx : bytes x).
  { assert (B : bytes (x ++ pend s')) by (rewrite Hx; apply Forall_sublist; exact HbH).
    apply Forall_app in B. apply B. }
  assert (Hlx : Zlength x <= z_avail_out z) by lia.
  assert (Hto' : z_total_out z' = z_total_out z + Zlength x).
  { rewrite Zto'. unfold u64. apply Z.mod_small. rewrite Hto, Zlength_app.
    pose proof (Zlength_nonneg O). pose proof (Zlength_nonneg (z_out z)). pose proof (Zlength_nonneg x). lia. }
  assert (HO2 : O ++ z_out z' = sublist 0 k H ++ x) by (rewrite Zo', app_assoc, HO; reflexivity).
  assert (Hfin : fin_of flush inb z' = fin_of flush inb z) by (unfold fin_of; rewrite Zni'; reflexivity).
  assert (HJ : sublist 0 k H ++ x ++ pend s' = sublist 0 k' H) by (rewrite Hx; apply sublist_rejoin; lia).
  assert (Hst : d_status s' = BUSY_STATE \/ (exists H1 k1, HI s' (z_adler z') H1 k1)).
  { destruct r as [c|]; [|left; apply Hr]. destruct Hr as (_ & _ & _ & _ & [[A _]|A]); [left; exact A|].
    right; eauto. }
  split; [exact Hgz'|].
  split; [|split; [exact Zni'|]].
  2:{ destruct r as [c|]; [apply Hr|]. destruct Hr as (_ & A & B & _). split; [exact B|left; exact A]. }
  unfold Mid7. rewrite Zni', Hfin.
  split; [|split; [exact Hsz1|split; [exact Hsz2|split; [exact Hsz3|split; [exact Hsz4|]]]]].
  { unfold zrun7. rewrite Zin', Zni', Zai', Zti', Zo', Hto', Zlength_app. repeat split; try lia.
    - exact Zin.
    - apply Forall_app; split; assumption. }
  rewrite HD, HO2, Zti', Hto'.
  rewrite HD in Htin, HbD, HlD.
  assert (HlO : Zlength (sublist 0 k H) = Zlength (O ++ z_out z)) by (rewrite HO; reflexivity).
  unfold Iapi7.
  split; [eapply (cf7_frame _ CF); eauto|].
  split; [exact Hout'|].
  split; [exact Hwr0|]. split; [exact Hw2|]. split; [exact Hbd|]. split; [exact Hld|].
  split; [destruct r as [c|]; [destruct Hr as (_ & _ & _ & -> & _); lia|
                               destruct Hr as (_ & _ & _ & _ & _ & ->); lia]|].
  split; [rewrite Hgz'; exact Hgz|].
  split; [rewrite Hto, (Zlength_app _ (sublist 0 k H)), HlO; lia|].
  split; [apply Forall_app; split; [rewrite <- HO; exact HbO|exact Hbx]|].
  split; [exact HbD|]. split; [exact HlD|]. split; [exact Htin|].
  split.
  { intros F. exfalso. destruct Hst as [A|(H1 & k1 & A)].
    - rewrite A in F. discriminate.
    - apply (hf7_status _ HF) in A. destruct A as (_ & _ & A & _).
      rewrite F in A. unfold FINISH_STATE, EXTRA_STATE, NAME_STATE, COMMENT_STATE, HCRC_STATE in A. lia. }
  split.
  { intros _. destruct (hs_pos _ _ Hce) as (P1 & P2 & P3). rewrite P1, P2, P3. exact (Hdz HD). }
  right. split.
  { destruct r as [c|]; [destruct Hr as (_ & _ & _ & -> & _); lia|
                         destruct Hr as (_ & _ & _ & _ & _ & ->); lia]. }
  destruct r as [c|].
  - destruct Hr as (-> & Hz0 & Hpn & Hlf' & [(Hb & Hk' & Had)|HI']).
    + right; left. unfold ph2. split; [exact Hb|]. split; [lia|]. split; [lia|].
      split. { intros _. intros E. apply app_eq_nil in E. destruct E as [_ E]. subst x.
        rewrite Zlength_nil in Zao'. lia. }
      split. { rewrite Had, Hwr. apply hs_chk_nil. }
      exists H, []. split; [exact HG|]. rewrite <- app_assoc, HJ, Hk', app_nil_r.
      apply sublist_same; reflexivity.
    + left. unfold ph1. pose proof (hf7_status _ HF _ _ _ _ HI') as (Hw2' & _).
      split; [lia|]. split; [reflexivity|].
      split. { intros E. apply app_eq_nil in E. destruct E as [_ E]. subst x.
        rewrite Zlength_nil in Zao'. lia. }
      split; [lia|]. split; [rewrite CEF; lia|].
      exists H, k'. split; [exact HI'|]. rewrite <- app_assoc. exact HJ.
  - destruct Hr as (Hk' & Hb & Hpn & Hpo & Had & Hlf').
    rewrite (pend_nil _ Hpn), app_nil_r in HJ.
    right; left. unfold ph2. split; [exact Hb|]. split; [lia|]. split; [lia|].
    split. { intros Hw. rewrite HJ, Hk', sublist_same by reflexivity.
      eapply hdr_good_ne; eauto. }
    split. { rewrite Had, Hwr. apply hs_chk_nil. }
    exists H, []. split; [exact HG|]. rewrite (pend_nil _ Hpn), app_nil_r, HJ, Hk', app_nil_r.
    apply sublist_same; reflexivity.
Qed.

Lemma hdr_stage_ok7 : forall W HI dict wrap D O inb aout tin tout flush s z s2 z2 r,
  core_facts7 W -> hdr_facts7 HI ->
  Mid7 W HI dict wrap D O inb aout tin tout flush s z ->
  d_pending s = 0 -> d_last_flush s = flush -> 0 <= flush <= 5 -> 0 < z_avail_out z ->
  (d_status s = FINISH_STATE -> z_avail_in z = 0) ->
  hdr_stages s z = Some (s2, z2, r) ->
  d_gzhead s2 = d_gzhead s /\ Mid7 W HI dict wrap D O inb aout tin tout flush s2 z2 /\
  z_next_in z2 = z_next_in z /\
  match r with
  | Some c => c = Z_OK
  | None => d_pending s2 = 0 /\ (d_status s2 = BUSY_STATE \/ (d_status s2 = FINISH_STATE /\ z_avail_in z2 = 0))
  end.
Proof.
  intros W HI dict wrap D O inb aout tin tout flush s z s2 z2 r CF HF M Hpend Hlf Hfl Hao Hfin HS.
  pose proof M as M0.
  destruct M as (ZR & Hsz1 & Hsz2 & Hsz3 & Hsz4 & IA).
  destruct IA as (HW & Hout & Hwr0 & Hw2 & Hbd & Hld & Hlfr & Hgz & Hto & HbO & HbD & HlD & Htin & HF6 & _ & Hph).
  pose proof ZR as (Zin & Zni & Zai & Zti & Zao & Zol & Zto & Zbo).
  assert (Hzao : 0 <= z_avail_out z <= 4294967295) by (pose proof (Zlength_nonneg (z_out z)); lia).
  assert (Hzto : 0 <= z_total_out z) by (rewrite Hto; apply Zlength_nonneg).
  assert (Hzto2 : z_total_out z + z_avail_out z <= 18446744073709551615) by (rewrite Hto, Zlength_app; lia).
  pose proof (cf7_prm _ CF _ HW) as Hprm.
  destruct Hph as [P0 | [Hlf2 [P1 | [P2 | P3]]]].
  - destruct P0 as (Hst & Hw & HD & HO & _ & Hbv & Hsym & _ & _ & Hss & Had).
    set (H := hdr_bytes s (z_adler z)).
    assert (HG : hdr_good dict wrap H).
    { destruct Hst as [[Hst Hwl]|[Hst Hw2']].
      - assert (wrap = 0 \/ wrap = 1) as [->| ->] by lia.
        + unfold H, hdr_bytes. rewrite Hw. simpl. apply hs_good_raw.
        + unfold H, hdr_bytes. rewrite Hw. simpl. apply hs_zlib_good; [exact Hprm|exact Hss|].
          intros _. apply Had. reflexivity.
      - subst wrap. rewrite (Hw2 eq_refl). unfold H, hdr_bytes. rewrite Hw. simpl.
        apply hs_gz_good7; [exact Hgz|intros _; apply hs_xfl]. }
    assert (Hpre : hdr_pre7 HI s z H 0).
    { unfold hdr_pre7. split; [exact Hprm|]. split; [exact Hout|]. split; [exact Hpend|].
      split; [exact Hsym|]. split; [exact Hbv|]. split; [exact Hzao|]. split; [exact Hzto|].
      split; [exact Hzto2|]. split; [exact Hgz|].
      destruct Hst as [[Hst Hwl]|[Hst Hw2']]; [left|right; left]; repeat split; auto; lia. }
    destruct (hf7_run _ HF _ _ _ _ Hpre) as (s' & z' & r' & HS' & HP).
    rewrite HS in HS'. injection HS' as <- <- <-.
    refine (hdr_tail7 W HI dict wrap D O inb aout tin tout flush s z H 0 s2 z2 r CF HF M0 Hpend Hlf Hfl Hao
              Hw Hbv Hsym HG ltac:(lia) HD _ HS HP).
    rewrite HO. symmetry. apply sublist_nil.
  - destruct P1 as (Hw & HD & HOne & Hbv & Hsym & H & k & HIk & HOk).
    destruct (hf7_status _ HF _ _ _ _ HIk) as (Hw' & [h Hh] & _ & [xfl HH] & Hk).
    assert (HG : hdr_good dict wrap H).
    { subst wrap. rewrite (Hw2 eq_refl), HH. apply hs_gz_good7; [exact Hgz|congruence]. }
    rewrite (pend_nil _ Hpend), app_nil_r in HOk.
    assert (Hpre : hdr_pre7 HI s z H k).
    { unfold hdr_pre7. split; [exact Hprm|]. split; [exact Hout|]. split; [exact Hpend|].
      split; [exact Hsym|]. split; [exact Hbv|]. split; [exact Hzao|]. split; [exact Hzto|].
      split; [exact Hzto2|]. split; [exact Hgz|]. right; right; exact HIk. }
    destruct (hf7_run _ HF _ _ _ _ Hpre) as (s' & z' & r' & HS' & HP).
    rewrite HS in HS'. injection HS' as <- <- <-.
    exact (hdr_tail7 W HI dict wrap D O inb aout tin tout flush s z H k s2 z2 r CF HF M0 Hpend Hlf Hfl Hao
             ltac:(lia) Hbv Hsym HG ltac:(lia) HD HOk HS HP).
  - rewrite hdr_stages_busy in HS by (left; apply P2). injection HS as <- <- <-.
    split; [reflexivity|]. split; [exact M0|]. split; [reflexivity|].
    split; [exact Hpend|left; apply P2].
  - rewrite hdr_stages_busy in HS by (right; apply P3). injection HS as <- <- <-.
    split; [reflexivity|]. split; [exact M0|]. split; [reflexivity|].
    split; [exact Hpend|right; split; [apply P3|apply Hfin, P3]].
Qed.
