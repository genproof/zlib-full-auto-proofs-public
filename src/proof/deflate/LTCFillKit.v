(** * Kit for fill_ok: generic loop lemma, masked-buffer writes, the parts of fill_window *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTCLib.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** A loop runs to completion when a measure decreases on every continuing iteration *)
Lemma loop2_measure {A B : Type} (body : A -> option (A + B)) (P : A -> Prop) (Q : B -> Prop) (m : A -> Z) :
  (forall a, P a -> 0 <= m a /\
     ((exists a', body a = Some (inl a') /\ P a' /\ m a' < m a) \/ (exists r, body a = Some (inr r) /\ Q r))) ->
  forall d a, P a ->
    (exists r, loop2 d body a = Some (inr r) /\ Q r) \/
    (exists a', loop2 d body a = Some (inl a') /\ P a' /\ m a' <= m a - 2 ^ Z.of_nat d).
Proof.
  intros H. induction d as [|d IH]; intros a Pa; cbn [loop2].
  - destruct (H a Pa) as [_ [(a' & E & Pa' & Lt)|(r & E & Qr)]]; rewrite E.
    + right. exists a'. split; [reflexivity|]. split; [exact Pa'|]. cbn. lia.
    + left. eauto.
  - destruct (IH a Pa) as [(r & E & Qr)|(a' & E & Pa' & Le)]; rewrite E.
    + left. eauto.
    + destruct (IH a' Pa') as [(r & E' & Qr)|(a'' & E' & Pa'' & Le')]; rewrite E'.
      * left. eauto.
      * right. exists a''. split; [reflexivity|]. split; [exact Pa''|].
        rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
Qed.

Lemma loop_measure {A B : Type} (body : A -> option (A + B)) (P : A -> Prop) (Q : B -> Prop) (m : A -> Z) :
  (forall a, P a -> 0 <= m a /\
     ((exists a', body a = Some (inl a') /\ P a' /\ m a' < m a) \/ (exists r, body a = Some (inr r) /\ Q r))) ->
  forall a, P a -> m a < 2 ^ 40 -> exists r, loop FUEL body a = Some r /\ Q r.
Proof.
  intros H a Pa Hm. unfold loop.
  destruct (loop2_measure body P Q m H FUEL a Pa) as [(r & E & Qr)|(a' & E & Pa' & Le)]; rewrite E.
  - eauto.
  - exfalso. destruct (H a' Pa') as [Hm' _]. change (Z.of_nat FUEL) with 40 in Le. lia.
Qed.

(** ** Masked-buffer block writes *)
Lemma mb_write_some b lo src :
  0 <= lo -> lo + Zlength src <= Zlength (mb_val b) ->
  mb_write b lo src =
    Some (mkMB (sublist 0 lo (mb_val b) ++ src ++ sublist (lo + Zlength src) (Zlength (mb_val b)) (mb_val b))
               (sublist 0 lo (mb_def b) ++ repeat true (Z.to_nat (Zlength src)) ++
                sublist (lo + Zlength src) (Zlength (mb_def b)) (mb_def b))).
Proof.
  intros H1 H2. unfold mb_write. replace ((0 <=? lo) && (lo + Zlength src <=? Zlength (mb_val b))) with true.
  - reflexivity.
  - symmetry. apply andb_true_iff. split; apply Z.leb_le; lia.
Qed.

Lemma mb_write_spec b lo src b' :
  mb_ok b -> mb_write b lo src = Some b' ->
  0 <= lo /\ lo + Zlength src <= Zlength (mb_val b) /\
  Zlength (mb_val b') = Zlength (mb_val b) /\ Zlength (mb_def b') = Zlength (mb_def b) /\
  (forall i, 0 <= i < Zlength (mb_val b) ->
     Znth i (mb_def b') = (if (lo <=? i) && (i <? lo + Zlength src) then true else Znth i (mb_def b)) /\
     Znth i (mb_val b') = (if (lo <=? i) && (i <? lo + Zlength src) then Znth (i - lo) src
                           else Znth i (mb_val b))) /\
  (bytes src -> mb_ok b').
Proof.
  intros [Hl Hok] Hw. unfold mb_write in Hw.
  destruct ((0 <=? lo) && (lo + Zlength src <=? Zlength (mb_val b))) eqn:E; [|discriminate].
  apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1, E2. injection Hw as <-.
  pose proof (Zlength_nonneg src).
  assert (L1 : Zlength (sublist 0 lo (mb_val b) ++ src ++
                        sublist (lo + Zlength src) (Zlength (mb_val b)) (mb_val b)) = Zlength (mb_val b)).
  { rewrite !Zlength_app, !Zlength_sublist by lia. lia. }
  assert (L2 : Zlength (sublist 0 lo (mb_def b) ++ repeat true (Z.to_nat (Zlength src)) ++
                        sublist (lo + Zlength src) (Zlength (mb_def b)) (mb_def b)) = Zlength (mb_def b)).
  { rewrite !Zlength_app, !Zlength_sublist, Zlength_repeat by lia. lia. }
  assert (G : forall i, 0 <= i < Zlength (mb_val b) ->
     Znth i (sublist 0 lo (mb_def b) ++ repeat true (Z.to_nat (Zlength src)) ++
             sublist (lo + Zlength src) (Zlength (mb_def b)) (mb_def b)) =
       (if (lo <=? i) && (i <? lo + Zlength src) then true else Znth i (mb_def b)) /\
     Znth i (sublist 0 lo (mb_val b) ++ src ++ sublist (lo + Zlength src) (Zlength (mb_val b)) (mb_val b)) =
       (if (lo <=? i) && (i <? lo + Zlength src) then Znth (i - lo) src else Znth i (mb_val b))).
  { intros i Hi.
    destruct (Z_lt_le_dec i lo) as [Lo|Lo].
    - replace ((lo <=? i) && (i <? lo + Zlength src)) with false by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
      rewrite !app_Znth1 by (rewrite Zlength_sublist; lia).
      rewrite !Znth_sublist by lia. rewrite !Z.add_0_r. auto.
    - destruct (Z_lt_le_dec i (lo + Zlength src)) as [Hi2|Hi2].
      + replace ((lo <=? i) && (i <? lo + Zlength src)) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
        split.
        * rewrite app_Znth2 by (rewrite Zlength_sublist; lia). rewrite Zlength_sublist by lia.
          rewrite app_Znth1 by (rewrite Zlength_repeat; lia).
          rewrite Znth_repeat_inrange by lia. reflexivity.
        * rewrite app_Znth2 by (rewrite Zlength_sublist; lia). rewrite Zlength_sublist by lia.
          rewrite app_Znth1 by lia. f_equal. lia.
      + replace ((lo <=? i) && (i <? lo + Zlength src)) with false by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; lia).
        split.
        * rewrite app_Znth2 by (rewrite Zlength_sublist; lia). rewrite Zlength_sublist by lia.
          rewrite app_Znth2 by (rewrite Zlength_repeat; lia). rewrite Zlength_repeat by lia.
          rewrite Znth_sublist by (rewrite ?Z2Nat.id; lia). f_equal. lia.
        * rewrite app_Znth2 by (rewrite Zlength_sublist; lia). rewrite Zlength_sublist by lia.
          rewrite app_Znth2 by lia.
          rewrite Znth_sublist by lia. f_equal. lia. }
  split; [lia|]. split; [lia|]. split; [exact L1|]. split; [exact L2|]. split; [exact G|].
  intros Hb. split; [cbn [mb_val mb_def]; lia|]. cbn [mb_val mb_def]. intros i Hi Hd.
  rewrite L1 in Hi. destruct (G i Hi) as [G1 G2]. rewrite G2. rewrite G1 in Hd.
  destruct ((lo <=? i) && (i <? lo + Zlength src)) eqn:Ei.
  - apply andb_true_iff in Ei as [Ei1 Ei2]. apply Z.leb_le in Ei1. apply Z.ltb_lt in Ei2.
    unfold bytes in Hb. rewrite Forall_forall in Hb. apply Hb. apply Znth_In. lia.
  - apply Hok; auto.
Qed.

(** ** The fields fill_window keeps *)
Lemma prm_keep s s' : fw_keep s' = fw_keep s -> prm s -> prm s'.
Proof.
  intros E. unfold prm, d_L, d_level, d_strategy.
  assert (E1 := f_equal d_w_bits E). assert (E2 := f_equal d_w_size E). assert (E3 := f_equal d_w_mask E).
  assert (E4 := f_equal d_hash_bits E). assert (E5 := f_equal d_hash_size E).
  assert (E6 := f_equal d_hash_mask E). assert (E7 := f_equal d_hash_shift E).
  assert (E8 := f_equal d_tr E). assert (E9 := f_equal d_pending_buf_size E).
  assert (E10 := f_equal d_pbm E). assert (E11 := f_equal d_method E).
  cbn in E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11.
  rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11. exact (fun H => H).
Qed.

(** ** One step of fill_window from [s, z] to [s', z']: [d] the slide, [k] the bytes read *)
Definition fwstep (s : dstate) (z : strm) (s' : dstate) (z' : strm) (d k : Z) : Prop :=
  fw_keep s' = fw_keep s /\ zstep (d_wrap s) z z' k [] /\
  (d = 0 \/ (d = d_w_size s /\ d_w_size s + MAX_DIST s <= d_strstart s)) /\
  d_strstart s' = d_strstart s - d /\ d_block_start s' = d_block_start s - d /\
  (d = 0 -> d_match_start s' = d_match_start s) /\
  (d <> 0 -> d_match_start s' = u32 (d_match_start s - d)) /\
  d_lookahead s' = d_lookahead s + k.

(** ** The parts *)

(** The slide (c_fw_slide) with [more] as fw_body computes it. *)
Definition fw_slide_stmt : Prop :=
  forall s, fill_pre s ->
  exists s' d,
    c_fw_slide s (u32 (d_window_size s - d_lookahead s - d_strstart s)) =
      Some (s', d_window_size s' - d_lookahead s' - d_strstart s') /\
    fill_pre s' /\ fw_keep s' = fw_keep s /\ d_lookahead s' = d_lookahead s /\
    (d = 0 \/ (d = d_w_size s /\ d_w_size s + MAX_DIST s <= d_strstart s)) /\
    d_strstart s' = d_strstart s - d /\ d_block_start s' = d_block_start s - d /\
    (d = 0 -> d_match_start s' = d_match_start s) /\
    (d <> 0 -> d_match_start s' = u32 (d_match_start s - d)) /\
    d_strstart s' < d_w_size s + MAX_DIST s.

(** The hash insertion (c_fw_insert): only ins_h, prev, head and insert change. *)
Definition fw_insert_stmt : Prop :=
  forall s, fill_pre s ->
  exists s', c_fw_insert s = Some s' /\ fill_pre s' /\
    set_d_insert (hc_keep s') 0 = set_d_insert (hc_keep s) 0.

(** The WIN_INIT zeroing (c_fw_high_water). *)
Definition fw_high_stmt : Prop :=
  forall s, fill_pre s ->
  exists s', c_fw_high_water s = Some s' /\ fill_pre s' /\
    s' = set_d_high_water (set_d_window s (d_window s')) (d_high_water s') /\
    Z.min (d_window_size s) (d_strstart s + d_lookahead s + WIN_INIT) <= d_high_water s'.

(** ** Helpers of fw_slide_ok *)
Lemma u32_small x : 0 <= x < 4294967296 -> u32 x = x.
Proof. intros H. unfold u32. apply Z.mod_small. exact H. Qed.

Lemma mb_definedb_true b lo hi :
  0 <= lo -> hi <= Zlength (mb_val b) -> (forall i, lo <= i < hi -> Znth i (mb_def b) = true) ->
  mb_definedb b lo hi = true.
Proof.
  intros H1 H2 H3. unfold mb_definedb.
  apply andb_true_iff. split; [apply andb_true_iff; split; apply Z.leb_le; lia|].
  apply forallb_forall. intros x Hx. apply in_map_iff in Hx as (k & <- & Hk).
  apply in_seq in Hk. apply H3. lia.
Qed.

Lemma land_sub_pow u wb : 0 <= wb -> Z.land (u - 2 ^ wb) (2 ^ wb - 1) = Z.land u (2 ^ wb - 1).
Proof.
  intros H. replace (2 ^ wb - 1) with (Z.ones wb) by (rewrite Z.ones_equiv; lia).
  rewrite !Z.land_ones by lia.
  replace (u - 2 ^ wb) with (u + (-1) * 2 ^ wb) by lia. apply Z_mod_plus_full.
Qed.

Ltac fw_proj := cbn [set_d_slid set_d_prev set_d_head set_d_insert set_d_block_start set_d_strstart
  set_d_match_start set_d_window d_status d_po d_wrap d_gzhead d_gzindex d_method d_last_flush d_w_size
  d_w_bits d_w_mask d_window d_window_size d_prev d_head d_ins_h d_hash_size d_hash_bits d_hash_mask
  d_hash_shift d_block_start d_match_length d_prev_match d_match_available d_strstart d_match_start
  d_lookahead d_prev_length d_max_chain_length d_max_lazy_match d_good_match d_nice_match d_insert
  d_high_water d_slid d_pending_buf_size d_tr d_pbm].

Lemma fw_slide_ok : fw_slide_stmt.
Proof.
  intros s Hf. pose proof Hf as Hf0. destruct Hf as (Hp & Hws & Hwp & Hww & Hc).
  pose proof Hp as Hp0. destruct Hp as (Hwb & Hw & Hm & Hhb & Hhs & _).
  destruct Hws as (Hlv & Hok & Hwsz & Hlp & Hlh).
  destruct Hwp as (Hla & Hss & Hsl & Hbs & Hbd & Hbn & Hins & Hinsw & Hhw).
  assert (MD : MAX_DIST s = d_w_size s - 262) by reflexivity.
  assert (W1 : 512 <= d_w_size s <= 32768).
  { rewrite Hw. split; [change 512 with (2 ^ 9)|change 32768 with (2 ^ 15)];
      apply Z.pow_le_mono_r; lia. }
  assert (Emore : u32 (d_window_size s - d_lookahead s - d_strstart s) =
                  d_window_size s - d_lookahead s - d_strstart s) by (apply u32_small; lia).
  rewrite Emore. unfold c_fw_slide.
  assert (Eg : u32 (d_w_size s + u32 (d_w_size s - MIN_LOOKAHEAD)) = d_w_size s + MAX_DIST s).
  { rewrite MD. change MIN_LOOKAHEAD with 262. rewrite (u32_small (d_w_size s - 262)) by lia.
    apply u32_small; lia. }
  rewrite Eg.
  destruct (d_strstart s >=? d_w_size s + MAX_DIST s) eqn:Ess.
  2:{ rewrite Z.geb_leb, Z.leb_gt in Ess. exists s, 0. split; [reflexivity|].
      split; [exact Hf0|]. split; [reflexivity|]. split; [reflexivity|].
      split; [left; reflexivity|]. split; [lia|]. split; [lia|].
      split; [reflexivity|]. split; [lia|]. exact Ess. }
  rewrite Z.geb_leb, Z.leb_le in Ess.
  set (w := d_w_size s) in *. set (ss := d_strstart s) in *. set (la := d_lookahead s) in *.
  assert (E1 : u32 (w - (d_window_size s - la - ss)) = ss + la - w) by (rewrite u32_small by lia; lia).
  rewrite E1. replace (ss + la - w <=? w) with true by (symmetry; apply Z.leb_le; lia). cbn [guard bind].
  assert (E2 : mb_read (d_window s) w (ss + la - w) = Some (sublist w (ss + la) (mb_val (d_window s)))).
  { unfold mb_read. rewrite mb_definedb_true by (try lia; intros i Hi; apply Hww; lia).
    replace (0 <=? ss + la - w) with true by (symmetry; apply Z.leb_le; lia). cbn. f_equal; f_equal; lia. }
  rewrite E2. cbn [bind].
  destruct (mb_write (d_window s) 0 (sublist w (ss + la) (mb_val (d_window s)))) as [win|] eqn:Ew.
  2:{ rewrite mb_write_some in Ew. discriminate. lia. rewrite Zlength_sublist; lia. }
  cbn [bind]. fw_proj.
  replace (in_long (d_block_start s - w)) with true by (symmetry; unfold in_long; apply andb_true_iff; split; apply Z.leb_le; lia).
  cbn [guard bind]. change (d_strstart s) with ss.
  rewrite (u32_small (ss - w)) by lia.
  set (s1 := if d_insert s >? ss - w then _ else _).
  assert (S1 : d_window s1 = win /\ d_match_start s1 = u32 (d_match_start s - w) /\ d_strstart s1 = ss - w /\
    d_block_start s1 = d_block_start s - w /\ d_insert s1 = Z.min (d_insert s) (ss - w) /\
    d_head s1 = d_head s /\ d_prev s1 = d_prev s /\ d_lookahead s1 = la /\
    d_high_water s1 = d_high_water s /\ d_hash_size s1 = d_hash_size s /\ d_w_size s1 = w /\
    d_w_mask s1 = d_w_mask s /\ d_window_size s1 = d_window_size s /\ fw_keep s1 = fw_keep s).
  { subst s1. destruct (d_insert s >? ss - w) eqn:Ei.
    - rewrite Z.gtb_ltb, Z.ltb_lt in Ei. unfold fw_keep. fw_proj.
      repeat split; try reflexivity. lia.
    - rewrite Z.gtb_ltb, Z.ltb_ge in Ei. unfold fw_keep. fw_proj.
      repeat split; try reflexivity. lia. }
  clearbody s1.
  destruct S1 as (S1w & S1ms & S1ss & S1bs & S1ins & S1h & S1p & S1la & S1hw & S1hs & S1ws & S1m & S1wsz & S1k).
  unfold c_slide_hash. rewrite S1h, S1p, S1hs, S1ws, Hlh, Hlp, !Z.eqb_refl.
  replace (1 <=? d_hash_size s) with true by (symmetry; apply Z.leb_le; rewrite Hhs; assert (0 < 2 ^ d_hash_bits s) by (apply Z.pow_pos_nonneg; lia); lia).
  replace (1 <=? w) with true by (symmetry; apply Z.leb_le; lia).
  cbn [andb guard bind].
  pose proof (mb_write_spec _ _ _ _ Hok Ew) as (_ & Wl & Wlv & Wld & WZ & Wok).
  rewrite Zlength_sublist in Wl, WZ by lia.
  cbn [d_prev set_d_head]. rewrite S1p.
  set (s2 := set_d_slid (set_d_prev (set_d_head s1 (map (slide_entry w) (d_head s)))
                                    (map (slide_entry w) (d_prev s))) 1).
  assert (K : fw_keep s2 = fw_keep s).
  { rewrite <- S1k. subst s2. unfold fw_keep. fw_proj. reflexivity. }
  exists s2, w. subst s2. fw_proj. rewrite S1wsz, S1la, S1ss, S1bs, S1ms.
  split. { rewrite u32_small by lia. f_equal. f_equal. lia. }
  split.
  2:{ split; [exact K|]. split; [reflexivity|]. split; [right; split; [reflexivity|lia]|].
      split; [lia|]. split; [lia|]. split; [intros; lia|]. split; [intros; reflexivity|]. lia. }
  set (s2 := set_d_slid (set_d_prev (set_d_head s1 (map (slide_entry w) (d_head s)))
                                    (map (slide_entry w) (d_prev s))) 1) in *.
  assert (P2 : prm s2) by (exact (prm_keep s s2 K Hp0)).
  split; [exact P2|].
  assert (T : d_window s2 = win /\ d_strstart s2 = ss - w /\ d_lookahead s2 = la /\
              d_block_start s2 = d_block_start s - w /\ d_insert s2 = Z.min (d_insert s) (ss - w) /\
              d_high_water s2 = d_high_water s /\ d_window_size s2 = d_window_size s /\
              d_head s2 = map (slide_entry w) (d_head s) /\ d_prev s2 = map (slide_entry w) (d_prev s) /\
              d_w_size s2 = w /\ d_w_mask s2 = d_w_mask s /\ d_hash_size s2 = d_hash_size s).
  { subst s2. fw_proj. rewrite S1w, S1ss, S1la, S1bs, S1ins, S1hw, S1wsz, S1ws, S1m, S1hs.
    repeat split; reflexivity. }
  clearbody s2.
  destruct T as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12).
  assert (MD2 : MAX_DIST s2 = w - 262) by (unfold MAX_DIST; rewrite T10; reflexivity).
  split.
  { (* wstruct *)
    unfold wstruct. rewrite T1, T7, T8, T9, T10, T12, !Zlength_map. split; [lia|]. split.
    - apply Wok. unfold bytes. rewrite Forall_forall. intros x Hx.
      apply In_Znth in Hx as (j & Hj & <-). rewrite Zlength_sublist in Hj by lia.
      rewrite Znth_sublist by lia. destruct Hok as [_ Hok]. apply Hok; [lia|]. apply Hww. lia.
    - split; [lia|]. split; lia. }
  split.
  { (* wpos *)
    unfold wpos. rewrite T2, T3, T4, T5, T6, T7, MD2. rewrite MD in Hbn.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [lia|]. split; lia. }
  split.
  { (* wwin *)
    unfold wwin. intros i Hi. unfold wwin in Hww. rewrite T2, T3, T6 in Hi. rewrite T1.
    destruct (WZ i ltac:(lia)) as [D _]. rewrite D.
    destruct ((0 <=? i) && (i <? 0 + (ss + la - w))) eqn:Ei; [reflexivity|].
    apply andb_false_iff in Ei as [Ei|Ei]; [apply Z.leb_gt in Ei; lia|apply Z.ltb_ge in Ei].
    apply Hww. lia. }
  (* chain_ok *)
  destruct Hc as (G & HG1 & HG2 & HG3).
  assert (Hmod : forall x, Z.land x (w - 1) = x mod w).
  { intros x. rewrite Hw. replace (2 ^ d_w_bits s - 1) with (Z.ones (d_w_bits s)) by (rewrite Z.ones_equiv; lia).
    apply Z.land_ones. lia. }
  assert (Hl : lim s = ss - MAX_DIST s).
  { unfold lim. change (d_strstart s) with ss.
    replace (ss >? MAX_DIST s) with true by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_lt; lia). reflexivity. }
  exists (fun v => exists u, G u /\ v = slide_entry w u).
  unfold chain_with. rewrite T2, T8, T9, T11, T12, Hm.
  split; [|split].
  - intros v (u & Gu & ->). unfold slide_entry, NIL. rewrite Z.geb_leb.
    destruct (HG1 u Gu); destruct (Z.leb_spec w u); lia.
  - intros h Hh. rewrite Znth_map by lia. eexists; split; [apply HG2; exact Hh|reflexivity].
  - intros q (u & Gu & ->) Hq Hlq. unfold slide_entry in Hq, Hlq |- *. rewrite Z.geb_leb in Hq, Hlq |- *.
    destruct (Z.leb_spec w u) as [Hu|Hu]; [|unfold NIL in Hq; lia].
    rewrite !Hmod.
    replace ((u - w) mod w) with (u mod w)
      by (replace (u - w) with (u + (-1) * w) by lia; rewrite Z_mod_plus_full; reflexivity).
    rewrite Znth_map by (rewrite Hlp; apply Z.mod_pos_bound; lia).
    eexists; split; [|reflexivity]. rewrite <- Hmod, <- Hm. apply HG3; [exact Gu|lia|].
    rewrite Hl, MD. unfold lim in Hlq. rewrite T2, MD2 in Hlq.
    destruct (ss - w >? w - 262) eqn:E; [rewrite Z.gtb_ltb, Z.ltb_lt in E|rewrite Z.gtb_ltb, Z.ltb_ge in E]; lia.
Qed.

(** ** Helpers of fw_insert_ok *)
Lemma fi_prm_facts s : prm s ->
  512 <= d_w_size s <= 32768 /\ 256 <= d_hash_size s <= 65536 /\ d_hash_shift s < 32 /\
  (forall x, Z.land x (d_w_mask s) = x mod d_w_size s) /\
  (forall x, Z.land x (d_hash_mask s) = x mod d_hash_size s).
Proof.
  intros P. destruct P as (Hwb & Hws & Hwm & Hhb & Hhs & Hhm & Hsh & _).
  assert (W1 : 2 ^ 9 <= 2 ^ d_w_bits s) by (apply Z.pow_le_mono_r; lia).
  assert (W2 : 2 ^ d_w_bits s <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia).
  assert (H1 : 2 ^ 8 <= 2 ^ d_hash_bits s) by (apply Z.pow_le_mono_r; lia).
  assert (H2 : 2 ^ d_hash_bits s <= 2 ^ 16) by (apply Z.pow_le_mono_r; lia).
  change (2 ^ 9) with 512 in W1. change (2 ^ 15) with 32768 in W2.
  change (2 ^ 8) with 256 in H1. change (2 ^ 16) with 65536 in H2.
  split; [lia|]. split; [lia|]. split.
  { rewrite Hsh. apply Z.div_lt_upper_bound; lia. }
  split; intros x.
  - rewrite Hwm, Hws. replace (2 ^ d_w_bits s - 1) with (Z.ones (d_w_bits s)) by (rewrite Z.ones_equiv; lia).
    apply Z.land_ones. lia.
  - rewrite Hhm, Hhs. replace (2 ^ d_hash_bits s - 1) with (Z.ones (d_hash_bits s)) by (rewrite Z.ones_equiv; lia).
    apply Z.land_ones. lia.
Qed.

Lemma fi_rd l i : 0 <= i < Zlength l -> rd l i = Some (Znth i l).
Proof.
  intros H. unfold rd, in_range. replace ((0 <=? i) && (i <? Zlength l)) with true; [reflexivity|].
  symmetry. apply andb_true_iff. split; [apply Z.leb_le|apply Z.ltb_lt]; lia.
Qed.

Lemma fi_wr l i v : 0 <= i < Zlength l -> wr l i v = Some (upd_Znth i l v).
Proof.
  intros H. unfold wr, in_range. replace ((0 <=? i) && (i <? Zlength l)) with true; [reflexivity|].
  symmetry. apply andb_true_iff. split; [apply Z.leb_le|apply Z.ltb_lt]; lia.
Qed.

Lemma fi_mb_rd s i : wstruct s -> wpos s -> wwin s -> 0 <= i < d_strstart s + d_lookahead s ->
  mb_rd (d_window s) i = Some (Znth i (mb_val (d_window s))) /\ 0 <= Znth i (mb_val (d_window s)) < 256.
Proof.
  intros (Hl & [_ Hok] & Hws & _) Hp Hw Hi.
  assert (Hd : Znth i (mb_def (d_window s)) = true) by (apply Hw; lia).
  unfold wpos in Hp.
  assert (Hr : 0 <= i < Zlength (mb_val (d_window s))) by lia.
  split; [|apply Hok; auto].
  unfold mb_rd, in_range. rewrite Hd.
  replace ((0 <=? i) && (i <? Zlength (mb_val (d_window s)))) with true; [reflexivity|].
  symmetry. apply andb_true_iff. split; [apply Z.leb_le|apply Z.ltb_lt]; lia.
Qed.

Lemma fi_uh_range s h c : prm s -> 0 <= update_hash s h c < d_hash_size s.
Proof.
  intros P. destruct (fi_prm_facts s P) as (_ & Hhs & _ & _ & Hm).
  unfold update_hash, u32. rewrite Hm.
  pose proof (Z.mod_pos_bound (Z.lxor (Z.shiftl h (d_hash_shift s) mod 4294967296) c) (d_hash_size s)).
  rewrite Z.mod_small; lia.
Qed.

(** One insertion: the state after it. *)
Definition fi_next (s : dstate) (h : Z) : dstate :=
  let str := d_strstart s - d_insert s in
  set_d_insert
    (set_d_head (set_d_prev (set_d_ins_h s h) (upd_Znth (Z.land str (d_w_mask s)) (d_prev s) (Znth h (d_head s))))
       (upd_Znth h (d_head s) str))
    (d_insert s - 1).

Lemma fi_next_pre s h : fill_pre s -> 0 < d_insert s -> 3 <= d_lookahead s + d_insert s ->
  0 <= h < d_hash_size s -> fill_pre (fi_next s h).
Proof.
  intros (P & Ws & Wp & Ww & [G (G1 & G2 & G3)]) Hi H3 Hh.
  destruct (fi_prm_facts s P) as (Hws & Hhs & _ & Hwm & _).
  pose proof Ws as (Hl & Hok & Hwz & Hlp & Hlh).
  pose proof Wp as (Wp1 & Wp2 & Wp3 & Wp4 & Wp5 & Wp6 & Wp7 & Wp8 & Wp9).
  set (str := d_strstart s - d_insert s).
  assert (Hlm : forall q, 0 <= q -> 0 <= Z.land q (d_w_mask s) < Zlength (d_prev s)).
  { intros q Hq. rewrite Hwm, Hlp. apply Z.mod_pos_bound. lia. }
  unfold fill_pre, fi_next. fold str. split; [|split; [|split; [|split]]].
  - apply (prm_keep s); [reflexivity|exact P].
  - unfold wstruct; cbn [d_window d_w_size d_window_size d_prev d_head d_hash_size set_d_insert set_d_head
      set_d_prev set_d_ins_h]. rewrite !upd_Znth_Zlength by (try apply Hlm; unfold str; lia). auto.
  - unfold wpos; cbn [d_lookahead d_strstart d_window_size d_block_start d_insert d_w_size d_high_water
      set_d_insert set_d_head set_d_prev set_d_ins_h]. unfold MAX_DIST in *. cbn [d_w_size set_d_insert set_d_head
      set_d_prev set_d_ins_h]. lia.
  - unfold wwin; cbn [d_window d_strstart d_lookahead d_high_water set_d_insert set_d_head set_d_prev set_d_ins_h].
    exact Ww.
  - exists (fun v => G v \/ v = str). unfold chain_with, lim, MAX_DIST.
    cbn [d_strstart d_hash_size d_head d_prev d_w_mask d_w_size set_d_insert set_d_head set_d_prev set_d_ins_h].
    split; [|split].
    + intros v [Gv | ->]; [apply G1; exact Gv|]. unfold str. lia.
    + intros h' Hh'. destruct (Z.eq_dec h' h) as [-> | Ne].
      * right. apply upd_Znth_same. lia.
      * left. rewrite upd_Znth_diff by lia. apply G2. exact Hh'.
    + intros q Gq Hq Hlq. left.
      destruct (Z.eq_dec (Z.land q (d_w_mask s)) (Z.land str (d_w_mask s))) as [E|Ne].
      * rewrite E, upd_Znth_same by (apply Hlm; unfold str; lia). apply G2. lia.
      * rewrite upd_Znth_diff by (try apply Hlm; unfold str in *; lia).
        destruct Gq as [Gq | ->]; [|congruence]. apply G3; [exact Gq|exact Hq|exact Hlq].
Qed.

Lemma fi_body s : fill_pre s -> 0 < d_insert s -> 3 <= d_lookahead s + d_insert s ->
  exists h, 0 <= h < d_hash_size s /\
  fw_insert_body (s, d_strstart s - d_insert s) =
    if d_lookahead s + d_insert s - 1 <? 3 then Some (inr (fi_next s h))
    else Some (inl (fi_next s h, d_strstart s - d_insert s + 1)).
Proof.
  intros Hf Hi H3. pose proof Hf as (P & Ws & Wp & Ww & _).
  destruct (fi_prm_facts s P) as (Hws & Hhs & Hsh & Hwm & _).
  pose proof Wp as (Wp1 & Wp2 & Wp3 & Wp4 & Wp5 & Wp6 & Wp7 & Wp8 & Wp9).
  pose proof Ws as (Hl & Hok & Hwz & Hlp & Hlh).
  set (str := d_strstart s - d_insert s).
  destruct (fi_mb_rd s (str + 2) Ws Wp Ww) as [Erd Hc]; [unfold str; lia|].
  exists (update_hash s (d_ins_h s) (Znth (str + 2) (mb_val (d_window s)))).
  split; [apply fi_uh_range; exact P|].
  unfold fw_insert_body. replace (d_insert s =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  unfold guard. replace (d_hash_shift s <? 32) with true by (symmetry; apply Z.ltb_lt; lia). cbn [bind].
  replace (u32 (str + MIN_MATCH - 1)) with (str + 2) by (unfold u32, MIN_MATCH; rewrite Z.mod_small; unfold str; lia).
  rewrite Erd. cbn [bind].
  pose proof (fi_uh_range s (d_ins_h s) (Znth (str + 2) (mb_val (d_window s))) P) as Hh.
  set (h := update_hash s (d_ins_h s) (Znth (str + 2) (mb_val (d_window s)))) in *.
  change (d_head (set_d_ins_h s h)) with (d_head s). change (d_ins_h (set_d_ins_h s h)) with h.
  change (d_prev (set_d_ins_h s h)) with (d_prev s). change (d_w_mask (set_d_ins_h s h)) with (d_w_mask s).
  rewrite fi_rd by lia. cbn [bind].
  rewrite fi_wr by (rewrite Hwm, Hlp; apply Z.mod_pos_bound; lia). cbn [bind].
  change (d_head (set_d_prev (set_d_ins_h s h) ?p)) with (d_head s).
  change (d_ins_h (set_d_prev (set_d_ins_h s h) ?p)) with h.
  rewrite fi_wr by lia. cbn [bind].
  cbn [d_insert d_lookahead set_d_insert set_d_head set_d_prev set_d_ins_h].
  replace (u32 (d_insert s - 1)) with (d_insert s - 1) by (unfold u32; rewrite Z.mod_small; lia).
  replace (u32 (d_lookahead s + (d_insert s - 1))) with (d_lookahead s + d_insert s - 1)
    by (unfold u32; rewrite Z.mod_small; lia).
  replace (u16 str) with str by (unfold u16; rewrite Z.mod_small; unfold str; lia).
  replace (u32 (str + 1)) with (str + 1) by (unfold u32; rewrite Z.mod_small; unfold str; lia).
  unfold MIN_MATCH. reflexivity.
Qed.

Lemma fi_ins_h_pre s x : fill_pre s -> fill_pre (set_d_ins_h s x).
Proof.
  intros (P & Ws & Wp & Ww & C). split; [|split; [|split; [|split]]].
  - apply (prm_keep s); [reflexivity|exact P].
  - exact Ws.
  - exact Wp.
  - exact Ww.
  - exact C.
Qed.

Lemma fi_next_fields s h :
  d_strstart (fi_next s h) = d_strstart s /\ d_insert (fi_next s h) = d_insert s - 1 /\
  d_lookahead (fi_next s h) = d_lookahead s /\
  set_d_insert (hc_keep (fi_next s h)) 0 = set_d_insert (hc_keep s) 0.
Proof. split; [reflexivity|]. split; [reflexivity|]. split; reflexivity. Qed.

Lemma fw_insert_ok : fw_insert_stmt.
Proof.
  intros s Hf. pose proof Hf as (P & Ws & Wp & Ww & _).
  destruct (fi_prm_facts s P) as (Hws & Hhs & Hsh & Hwm & _).
  pose proof Wp as (Wp1 & Wp2 & Wp3 & Wp4 & Wp5 & Wp6 & Wp7 & Wp8 & Wp9).
  pose proof Ws as (Hl & Hok & Hwz & Hlp & Hlh).
  unfold c_fw_insert.
  replace (u32 (d_lookahead s + d_insert s)) with (d_lookahead s + d_insert s) by (unfold u32; rewrite Z.mod_small; lia).
  destruct (d_lookahead s + d_insert s >=? MIN_MATCH) eqn:E3.
  2: { exists s. split; [reflexivity|]. split; [exact Hf|reflexivity]. }
  apply Z.geb_le in E3. unfold MIN_MATCH in E3.
  replace (u32 (d_strstart s - d_insert s)) with (d_strstart s - d_insert s) by (unfold u32; rewrite Z.mod_small; lia).
  set (str := d_strstart s - d_insert s).
  destruct (fi_mb_rd s str Ws Wp Ww) as [Erd0 _]; [unfold str; lia|].
  rewrite Erd0. cbn [bind].
  change (d_hash_shift (set_d_ins_h s (Znth str (mb_val (d_window s))))) with (d_hash_shift s).
  unfold guard. replace (d_hash_shift s <? 32) with true by (symmetry; apply Z.ltb_lt; lia). cbn [bind].
  change (d_window (set_d_ins_h s (Znth str (mb_val (d_window s))))) with (d_window s).
  replace (u32 (str + 1)) with (str + 1) by (unfold u32; rewrite Z.mod_small; unfold str; lia).
  destruct (fi_mb_rd s (str + 1) Ws Wp Ww) as [Erd1 _]; [unfold str; lia|].
  rewrite Erd1. cbn [bind].
  set (s1 := set_d_ins_h (set_d_ins_h s _) _).
  assert (Hf1 : fill_pre s1) by (apply fi_ins_h_pre, fi_ins_h_pre; exact Hf).
  destruct (loop_measure fw_insert_body
     (fun a => fill_pre (fst a) /\ snd a = d_strstart (fst a) - d_insert (fst a) /\
               3 <= d_lookahead (fst a) + d_insert (fst a) /\
               set_d_insert (hc_keep (fst a)) 0 = set_d_insert (hc_keep s) 0)
     (fun r => fill_pre r /\ set_d_insert (hc_keep r) 0 = set_d_insert (hc_keep s) 0)
     (fun a => d_insert (fst a))) with (a := (s1, str)) as (r & Er & Qr).
  - intros [s' str'] (Hf' & Hstr & H3' & Hfr). cbn [fst snd] in *. subst str'.
    pose proof Hf' as (_ & _ & Wp' & _ & _). destruct Wp' as (_ & _ & _ & _ & _ & _ & Wi' & _).
    split; [lia|].
    destruct (Z.eq_dec (d_insert s') 0) as [E0|E0].
    + right. exists s'. split; [|split; [exact Hf'|exact Hfr]].
      unfold fw_insert_body. rewrite E0, Z.eqb_refl. reflexivity.
    + destruct (fi_body s' Hf' ltac:(lia) H3') as (h & Hh & Eb). rewrite Eb.
      pose proof (fi_next_pre s' h Hf' ltac:(lia) H3' Hh) as Hn.
      destruct (fi_next_fields s' h) as (F1 & F2 & F3 & F4).
      destruct (d_lookahead s' + d_insert s' - 1 <? 3) eqn:Ec.
      * right. exists (fi_next s' h). split; [reflexivity|]. split; [exact Hn|]. rewrite F4. exact Hfr.
      * left. exists (fi_next s' h, d_strstart s' - d_insert s' + 1). split; [reflexivity|].
        cbn [fst snd]. apply Z.ltb_ge in Ec. rewrite F1, F2, F3, F4.
        split; [split; [exact Hn|]; split; [lia|]; split; [lia|exact Hfr]|]. lia.
  - cbn [fst snd]. split; [exact Hf1|]. split; [reflexivity|]. split; [exact E3|reflexivity].
  - cbn [fst snd]. change (d_insert s1) with (d_insert s). change (2 ^ 40) with 1099511627776. lia.
  - exists r. split; [exact Er|exact Qr].
Qed.

(* fw_high_stmt is proved in LTCFill.v (fw_high_proof). *)
