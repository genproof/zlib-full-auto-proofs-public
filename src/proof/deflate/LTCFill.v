(** * Core part of the deflate law theory: fill_window
    Statement: LTCSpecs.v; invariant: LTCW.v; shared lemmas: LTCLib.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTCLib.
Require Import Zlib.proof.deflate.LTCFillKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Lemma set_hw_same s : set_d_high_water s (d_high_water s) = s.
Proof. destruct s; reflexivity. Qed.

Lemma prm_wsize s : prm s -> 512 <= d_w_size s <= 32768.
Proof.
  intros (Hb & Hw & _). rewrite Hw.
  split; [replace 512 with (2 ^ 9) by reflexivity|replace 32768 with (2 ^ 15) by reflexivity];
    apply Z.pow_le_mono_r; lia.
Qed.

Lemma u32_id' x : 0 <= x < 4294967296 -> u32 x = x.
Proof. intros H. unfold u32. apply Z.mod_small. exact H. Qed.

Lemma bytes_repeat0 n : bytes (repeat 0 n).
Proof. unfold bytes. apply Forall_forall. intros x Hx. apply repeat_spec in Hx. lia. Qed.

(** A window write together with new lookahead / high_water keeps fill_pre. *)
Lemma fill_pre_write s win lo src la' hw' :
  fill_pre s -> mb_write (d_window s) lo src = Some win -> bytes src ->
  0 <= la' -> d_strstart s + la' <= d_window_size s -> 0 <= hw' <= d_window_size s ->
  (forall i, 0 <= i < Z.max (d_strstart s + la') hw' ->
     0 <= i < Z.max (d_strstart s + d_lookahead s) (d_high_water s) \/ lo <= i < lo + Zlength src) ->
  fill_pre (set_d_high_water (set_d_lookahead (set_d_window s win) la') hw').
Proof.
  intros (Hp & (W1 & W2 & W3 & W4 & W5) & Hpos & Hw & Hc) Ew Hb Hla Hss Hhw Hcov.
  pose proof (mb_write_spec _ _ _ _ W2 Ew) as (M1 & M2 & M3 & M4 & M5 & M6).
  destruct Hpos as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
  split; [|split; [|split; [|split]]].
  - eapply prm_keep; [|exact Hp]. reflexivity.
  - unfold wstruct; cbn. split; [lia|]. split; [apply M6, Hb|]. split; [exact W3|]. split; [exact W4|exact W5].
  - unfold wpos, MAX_DIST, MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *; cbn. lia.
  - unfold wwin; cbn. intros i Hi. destruct (M5 i) as [D _]; [lia|].
    rewrite D. destruct (Hcov i Hi) as [Hi'|Hi'].
    + destruct ((lo <=? i) && (i <? lo + Zlength src)); [reflexivity|]. apply Hw. exact Hi'.
    + replace ((lo <=? i) && (i <? lo + Zlength src)) with true; [reflexivity|].
      symmetry. apply andb_true_iff. split; [apply Z.leb_le|apply Z.ltb_lt]; lia.
  - exact Hc.
Qed.

Lemma fw_high_proof : fw_high_stmt.
Proof.
  intros s Hf.
  pose proof Hf as (Hp & (W1 & W2 & W3 & W4 & W5) & Hpos & Hw & Hc).
  destruct Hpos as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
  pose proof (prm_wsize s Hp) as Hws.
  unfold c_fw_high_water, WIN_INIT, MAX_MATCH.
  destruct (Z.ltb_spec (d_high_water s) (d_window_size s)) as [H1|H1].
  2: { exists s. split; [reflexivity|]. split; [exact Hf|]. split; [destruct s; reflexivity|]. lia. }
  destruct (Z.ltb_spec (d_high_water s) (d_strstart s + d_lookahead s)) as [H2|H2].
  - remember (d_strstart s + d_lookahead s) as curr eqn:Ecurr.
    rewrite (u64_id (d_window_size s - curr)) by lia.
    set (init := if d_window_size s - curr >? 258 then 258 else d_window_size s - curr).
    assert (Hi : init = Z.min (d_window_size s - curr) 258).
    { unfold init. destruct (Z.gtb_spec (d_window_size s - curr) 258); lia. }
    rewrite (mb_write_some (d_window s) curr) by (rewrite ?Zlength_repeat by lia; lia).
    cbn [bind].
    eexists. split; [reflexivity|].
    set (win := mkMB _ _).
    assert (Ew : mb_write (d_window s) curr (repeat 0 (Z.to_nat init)) = Some win).
    { apply mb_write_some; rewrite ?Zlength_repeat by lia; lia. }
    assert (F := fill_pre_write s win curr (repeat 0 (Z.to_nat init)) (d_lookahead s) (curr + init)
                   Hf Ew (bytes_repeat0 _)).
    replace (set_d_lookahead (set_d_window s win) (d_lookahead s)) with (set_d_window s win) in F
      by (destruct s; reflexivity).
    split; [apply F; try lia;
            intros i Hi'; rewrite Zlength_repeat in * by lia; lia|].
    split; [reflexivity|]. cbn. lia.
  - destruct (Z.ltb_spec (d_high_water s) (d_strstart s + d_lookahead s + 258)) as [H3|H3].
    2: { exists s. split; [reflexivity|]. split; [exact Hf|]. split; [destruct s; reflexivity|]. lia. }
    remember (d_strstart s + d_lookahead s) as curr eqn:Ecurr.
    rewrite (u64_id (curr + 258 - d_high_water s)) by lia.
    rewrite (u64_id (d_window_size s - d_high_water s)) by lia.
    set (init := if curr + 258 - d_high_water s >? d_window_size s - d_high_water s
                 then d_window_size s - d_high_water s else curr + 258 - d_high_water s).
    assert (Hi : 0 < init /\ d_high_water s + init = Z.min (d_window_size s) (curr + 258)).
    { unfold init. destruct (Z.gtb_spec (curr + 258 - d_high_water s) (d_window_size s - d_high_water s)); lia. }
    assert (Hu : u32 init = init) by (unfold u32; apply Z.mod_small; lia).
    rewrite Hu.
    rewrite (mb_write_some (d_window s) (d_high_water s)) by (rewrite ?Zlength_repeat by lia; lia).
    cbn [bind].
    eexists. split; [reflexivity|].
    set (win := mkMB _ _).
    assert (Ew : mb_write (d_window s) (d_high_water s) (repeat 0 (Z.to_nat init)) = Some win).
    { apply mb_write_some; rewrite ?Zlength_repeat by lia; lia. }
    rewrite (u64_id (d_high_water s + init)) by lia.
    assert (F := fill_pre_write s win (d_high_water s) (repeat 0 (Z.to_nat init)) (d_lookahead s)
                   (d_high_water s + init) Hf Ew (bytes_repeat0 _)).
    replace (set_d_lookahead (set_d_window s win) (d_lookahead s)) with (set_d_window s win) in F
      by (destruct s; reflexivity).
    split; [apply F; try lia;
            intros i Hi'; rewrite Zlength_repeat in * by lia; lia|].
    split; [reflexivity|]. cbn. lia.
Qed.

(** read_buf *)
Lemma read_ok s z size :
  zall z -> adler_ok (d_wrap s) (z_adler z) -> 0 <= size ->
  exists z' data, c_read_buf s z size = Some (z', data) /\ Zlength data = Z.min (z_avail_in z) size /\
    bytes data /\ zstep (d_wrap s) z z' (Zlength data) [] /\ zall z' /\ adler_ok (d_wrap s) (z_adler z').
Proof.
  intros Hz Ha Hs. pose proof Hz as [(Hb & Hn & Hav & Hl & Ht) (Ho & Hto & Hs')].
  unfold c_read_buf.
  set (len := if z_avail_in z >? size then size else z_avail_in z).
  assert (Hlen : len = Z.min (z_avail_in z) size)
    by (unfold len; destruct (Z.gtb_spec (z_avail_in z) size); lia).
  clearbody len.
  destruct (Z.eqb_spec len 0) as [L0|L0].
  { exists z, []. split; [reflexivity|]. split; [rewrite Zlength_nil; lia|].
    split; [constructor|]. split; [apply zstep_refl; auto|]. split; auto. }
  unfold rds. cbn [set_z_avail_in z_in z_next_in z_avail_in].
  replace ((0 <=? z_next_in z) && (0 <=? len) && (z_next_in z + len <=? Zlength (z_in z))) with true
    by (symmetry; rewrite !andb_true_iff; rewrite !Z.leb_le; lia).
  cbn [bind].
  set (data := sublist (z_next_in z) (z_next_in z + len) (z_in z)).
  assert (Hdl : Zlength data = len) by (unfold data; rewrite Zlength_sublist; lia).
  assert (Hdb : bytes data) by (apply bytes_sublist; exact Hb).
  set (z' := set_z_total_in (set_z_next_in (if d_wrap s =? 1 then _ else _) _) _).
  assert (Hst : zstep (d_wrap s) z z' (Zlength data) []).
  { rewrite Hdl. unfold zstep, z'.
    destruct (Z.eqb_spec (d_wrap s) 1) as [W1|W1]; [|destruct (Z.eqb_spec (d_wrap s) 2) as [W2|W2]];
      cbn [set_z_total_in set_z_next_in set_z_adler set_z_avail_in z_in z_next_in z_avail_in z_total_in
           z_out z_avail_out z_total_out z_adler z_msg];
      (split; [reflexivity|]); (split; [lia|]); (split; [reflexivity|]); (split; [reflexivity|]);
      (split; [reflexivity|]);
      (split; [|split; [rewrite app_nil_r; reflexivity|split; [rewrite Zlength_nil; lia|split; [rewrite Zlength_nil; lia|
         split; [rewrite Z.add_0_r; symmetry; apply u64_id; lia|reflexivity]]]]]);
      fold data; unfold adler_upd; rewrite ?W1, ?W2; cbn -[data].
    - apply Zlib.proof.adler32.Model.adler32_z_val_ref. destruct Ha as [Ha _]. auto.
    - reflexivity.
    - destruct (Z.eqb_spec (d_wrap s) 1); [lia|]. destruct (Z.eqb_spec (d_wrap s) 2); [lia|]. reflexivity. }
  exists z', data. split; [reflexivity|]. split; [lia|]. split; [exact Hdb|]. split; [exact Hst|].
  split; [eapply zall_zstep; eauto; destruct Hst as (_ & _ & _ & _ & _ & _ & _ & _ & E & _); rewrite E, Zlength_nil; lia|].
  destruct Hst as (_ & _ & _ & _ & _ & E & _). rewrite E, Hdl.
  fold data. apply adler_ok_upd; auto.
Qed.

Lemma keep_fields s s' : fw_keep s' = fw_keep s ->
  d_wrap s' = d_wrap s /\ d_w_size s' = d_w_size s /\ d_window_size s' = d_window_size s /\
  MAX_DIST s' = MAX_DIST s.
Proof.
  intros E. assert (E1 := f_equal d_wrap E). assert (E2 := f_equal d_w_size E).
  assert (E3 := f_equal d_window_size E). cbn in E1, E2, E3. unfold MAX_DIST. rewrite E2. auto.
Qed.

Lemma hc_fields s s' : set_d_insert (hc_keep s') 0 = set_d_insert (hc_keep s) 0 ->
  fw_keep s' = fw_keep s /\ d_strstart s' = d_strstart s /\ d_block_start s' = d_block_start s /\
  d_match_start s' = d_match_start s /\ d_lookahead s' = d_lookahead s.
Proof.
  intros E.
  assert (E0 : fw_keep (set_d_insert (hc_keep s') 0) = fw_keep (set_d_insert (hc_keep s) 0)) by (rewrite E; reflexivity).
  assert (E1 := f_equal d_strstart E). assert (E2 := f_equal d_block_start E).
  assert (E3 := f_equal d_match_start E). assert (E4 := f_equal d_lookahead E).
  cbn in E1, E2, E3, E4. split; [exact E0|]. auto.
Qed.

(** One iteration of the do-while loop *)
Lemma body_ok s z :
  fill_pre s -> zall z -> adler_ok (d_wrap s) (z_adler z) ->
  exists s' z' d k (b : bool),
    fw_body (s, z) = Some (if b then inl (s', z') else inr (s', z')) /\
    fill_pre s' /\ zall z' /\ adler_ok (d_wrap s) (z_adler z') /\ fwstep s z s' z' d k /\
    d_strstart s' < d_w_size s + MAX_DIST s /\
    (b = true -> 1 <= k /\ d_lookahead s' < MIN_LOOKAHEAD /\ z_avail_in z' <> 0) /\
    (b = false -> MIN_LOOKAHEAD <= d_lookahead s' \/ z_avail_in z' = 0).
Proof.
  intros Hf Hz Ha.
  destruct (fw_slide_ok s Hf) as (s1 & d & Esl & Hf1 & K1 & La1 & Hd & Ss1 & Bs1 & Ms1 & Ms1' & Lt1).
  destruct (keep_fields s s1 K1) as (Wr1 & Ws1 & Wz1 & Md1).
  unfold fw_body. rewrite Esl. cbn [bind].
  destruct (Z.eqb_spec (z_avail_in z) 0) as [A0|A0].
  { exists s1, z, d, 0, false. split; [reflexivity|]. split; [exact Hf1|]. split; [exact Hz|].
    split; [exact Ha|].
    split; [unfold fwstep; split; [exact K1|]; split; [apply zstep_refl; auto|]; lia|].
    split; [exact Lt1|]. split; [discriminate|]. intros _. right. exact A0. }
  pose proof Hf1 as (Hp1 & (W1 & W2 & W3 & W4 & W5) & (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9) & Hw1 & Hc1).
  pose proof (prm_wsize s1 Hp1) as Hws.
  destruct (read_ok s1 z (d_window_size s1 - d_lookahead s1 - d_strstart s1)) as
    (z1 & data & Er & Hlen & Hdb & Hst & Hz1 & Ha1); [exact Hz|rewrite Wr1; exact Ha|lia|].
  pose proof (Zlength_nonneg data) as Hdn.
  pose proof Hz as [(Zb & Zn & Zav & Zl & Zt) _].
  rewrite Er. cbn [bind].
  rewrite (mb_write_some (d_window s1) (d_strstart s1 + d_lookahead s1) data) by lia.
  cbn [bind].
  set (win := mkMB _ _).
  assert (Ew : mb_write (d_window s1) (d_strstart s1 + d_lookahead s1) data = Some win)
    by (apply mb_write_some; lia).
  change (d_lookahead (set_d_window s1 win)) with (d_lookahead s1).
  rewrite (u32_id' (d_lookahead s1 + Zlength data)) by lia.
  assert (F := fill_pre_write s1 win (d_strstart s1 + d_lookahead s1) data (d_lookahead s1 + Zlength data)
                 (d_high_water s1) Hf1 Ew Hdb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros i Hi; lia)).
  change (d_high_water s1) with (d_high_water (set_d_lookahead (set_d_window s1 win) (d_lookahead s1 + Zlength data))) in F.
  rewrite set_hw_same in F.
  set (s2 := set_d_lookahead (set_d_window s1 win) (d_lookahead s1 + Zlength data)) in F |- *.
  destruct (fw_insert_ok s2 F) as (s3 & Ei & Hf3 & K3).
  destruct (hc_fields s2 s3 K3) as (K3' & Ss3 & Bs3 & Ms3 & La3).
  rewrite Ei. cbn [bind].
  exists s3, z1, d, (Zlength data), ((d_lookahead s3 <? MIN_LOOKAHEAD) && negb (z_avail_in z1 =? 0)).
  split; [destruct ((d_lookahead s3 <? MIN_LOOKAHEAD) && negb (z_avail_in z1 =? 0)); reflexivity|].
  cbn in Ss3, Bs3, Ms3, La3.
  split; [exact Hf3|]. split; [exact Hz1|]. split; [rewrite <- Wr1; exact Ha1|].
  split.
  { unfold fwstep. split; [rewrite K3', <- K1; reflexivity|]. split; [rewrite <- Wr1; exact Hst|].
    rewrite Ss3, Bs3, Ms3, La3. lia. }
  split; [lia|].
  split.
  - intros Hb. apply andb_true_iff in Hb as [Hb1 Hb2]. apply Z.ltb_lt in Hb1.
    apply negb_true_iff, Z.eqb_neq in Hb2. split; [|split; [exact Hb1|exact Hb2]].
    rewrite La3 in Hb1. unfold MAX_DIST, MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *. lia.
  - intros Hb. apply andb_false_iff in Hb as [Hb|Hb].
    + left. apply Z.ltb_ge in Hb. exact Hb.
    + right. apply negb_false_iff, Z.eqb_eq in Hb. exact Hb.
Qed.

Lemma fwstep_trans s0 z0 s z s' z' d k d' k' :
  fill_pre s0 -> zall z0 -> adler_ok (d_wrap s0) (z_adler z0) ->
  fwstep s0 z0 s z d k -> fwstep s z s' z' d' k' -> fwstep s0 z0 s' z' (d + d') (k + k').
Proof.
  intros (Hp & (W1 & W2 & W3 & W4 & W5) & (P1 & P2 & P3 & _) & _) [Hzi _] Ha
    (K1 & Z1 & D1 & S1 & B1 & M1 & M1' & L1) (K2 & Z2 & D2 & S2 & B2 & M2 & M2' & L2).
  pose proof (prm_wsize s0 Hp) as Hws.
  destruct (keep_fields s0 s K1) as (Wr & Ws & Wz & Md).
  rewrite Wr in Z2. rewrite Ws, Md in D2.
  assert (Hmd : MAX_DIST s0 = d_w_size s0 - 262) by reflexivity.
  unfold fwstep. split; [rewrite K2; exact K1|].
  split; [change (@nil Z) with (@nil Z ++ []); eapply zstep_trans; eauto|].
  destruct D1 as [D1|D1]; destruct D2 as [D2|D2].
  - subst d d'. rewrite Z.add_0_r. split; [left; reflexivity|]. split; [lia|]. split; [lia|].
    split; [intros _; rewrite M2, M1; auto|]. split; [intros C; lia|]. lia.
  - subst d. rewrite Z.add_0_l. split; [right; lia|]. split; [lia|]. split; [lia|].
    split; [intros C; lia|]. split; [intros C; rewrite M2' by lia; rewrite M1 by reflexivity; reflexivity|]. lia.
  - subst d'. rewrite Z.add_0_r. split; [right; lia|]. split; [lia|]. split; [lia|].
    split; [intros C; lia|]. split; [intros C; rewrite M2 by reflexivity; apply M1'; lia|]. lia.
  - exfalso. lia.
Qed.

Definition fwP (s0 : dstate) (z0 : strm) (a : dstate * strm) : Prop :=
  fill_pre (fst a) /\ zall (snd a) /\ adler_ok (d_wrap s0) (z_adler (snd a)) /\
  exists d k, fwstep s0 z0 (fst a) (snd a) d k.

Definition fwQ (s0 : dstate) (z0 : strm) (a : dstate * strm) : Prop :=
  fwP s0 z0 a /\ d_strstart (fst a) < d_w_size s0 + MAX_DIST s0 /\
  (MIN_LOOKAHEAD <= d_lookahead (fst a) \/ z_avail_in (snd a) = 0).

Lemma loop_ok s0 z0 :
  fill_pre s0 -> zall z0 -> adler_ok (d_wrap s0) (z_adler z0) ->
  exists r, loop FUEL fw_body (s0, z0) = Some r /\ fwQ s0 z0 r.
Proof.
  intros Hf0 Hz0 Ha0.
  apply (loop_measure fw_body (fwP s0 z0) (fwQ s0 z0) (fun a => z_avail_in (snd a))).
  - intros [s z] (Hf & Hz & Ha & d & k & Hs). cbn [fst snd] in *.
    split; [destruct Hz as [(_ & _ & ? & _) _]; lia|].
    pose proof Hs as (K & _).
    destruct (keep_fields s0 s K) as (Wr & Ws & Wz & Md).
    rewrite <- Wr in Ha.
    destruct (body_ok s z Hf Hz Ha) as (s' & z' & d' & k' & b & Eb & Hf' & Hz' & Ha' & Hs' & Lt & Hcont & Hexit).
    assert (Hs'' := fwstep_trans s0 z0 s z s' z' d k d' k' Hf0 Hz0 Ha0 Hs Hs').
    rewrite Wr in Ha'.
    destruct b.
    + left. exists (s', z'). split; [exact Eb|].
      split; [split; [exact Hf'|]; split; [exact Hz'|]; split; [exact Ha'|]; eauto|].
      cbn [snd]. destruct (Hcont eq_refl) as (Hk & _).
      destruct Hs' as (_ & (_ & Hk' & _ & Ha2 & _) & _). lia.
    + right. exists (s', z'). split; [exact Eb|].
      split; [split; [exact Hf'|]; split; [exact Hz'|]; split; [exact Ha'|]; eauto|].
      cbn [fst snd]. rewrite <- Ws, <- Md. split; [exact Lt|]. apply Hexit. reflexivity.
  - split; [exact Hf0|]. split; [exact Hz0|]. split; [exact Ha0|]. exists 0, 0. cbn [fst snd].
    unfold fwstep. split; [reflexivity|]. split; [apply zstep_refl; auto|]. lia.
  - cbn [snd]. destruct Hz0 as [(_ & _ & ? & _) _]. lia.
Qed.

Theorem fill_ok : fill_spec.
Proof.
  intros s z Hf Hz Ha.
  destruct (loop_ok s z Hf Hz Ha) as ([s1 z1] & El & (Hf1 & Hz1 & Ha1 & d & k & Hs) & Lt & Hex).
  cbn [fst snd] in *.
  destruct (fw_high_proof s1 Hf1) as (s2 & Eh & Hf2 & E2 & Hb2).
  assert (F2 : fw_keep s2 = fw_keep s1 /\ d_strstart s2 = d_strstart s1 /\ d_block_start s2 = d_block_start s1 /\
               d_match_start s2 = d_match_start s1 /\ d_lookahead s2 = d_lookahead s1)
    by (rewrite E2; repeat split; reflexivity).
  destruct F2 as (K2 & S2 & B2 & M2 & L2).
  destruct Hs as (K1 & Zs & D & S1 & B1 & M1 & M1' & L1).
  destruct (keep_fields s s1 K1) as (Wr & Ws & Wz & Md).
  exists s2, z1, k, d.
  split; [unfold c_fill_window; rewrite El; cbn [bind]; rewrite Eh; reflexivity|].
  split; [exact Hf2|]. split; [rewrite K2; exact K1|]. split; [exact Zs|]. split; [exact D|].
  rewrite S2, B2, M2, L2. split; [exact S1|]. split; [exact B1|]. split; [exact M1|]. split; [exact M1'|].
  split; [exact L1|]. split; [exact Lt|]. split; [exact Hex|].
  rewrite <- Wz. exact Hb2.
Qed.
