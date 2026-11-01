(* RT-D part STORED: the window update c_ds_window (statement: RTDStoredKit.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDStoredKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** The values of mb_write / mb_move *)

Lemma rtdsw_write_val b lo src b' :
  mb_write b lo src = Some b' ->
  Zlength (mb_val b') = Zlength (mb_val b) /\
  forall i, 0 <= i < Zlength (mb_val b) ->
    Znth i (mb_val b') = if (lo <=? i) && (i <? lo + Zlength src) then Znth (i - lo) src else Znth i (mb_val b).
Proof.
  unfold mb_write. destruct (Z.leb_spec 0 lo), (Z.leb_spec (lo + Zlength src) (Zlength (mb_val b)));
    cbn [andb]; try discriminate.
  intros E. injection E as <-. cbn [mb_val].
  pose proof (Zlength_nonneg src).
  split; [rewrite !Zlength_app, !Zlength_sublist by lia; lia|].
  intros i Hi. destruct (Z_lt_dec i lo).
  - rewrite app_Znth1 by (rewrite Zlength_sublist by lia; lia). rewrite Znth_sublist by lia.
    destruct (Z.leb_spec lo i); [lia|]. cbn [andb]. f_equal; lia.
  - rewrite app_Znth2 by (rewrite Zlength_sublist by lia; lia). rewrite Zlength_sublist by lia.
    destruct (Z_lt_dec i (lo + Zlength src)).
    + rewrite app_Znth1 by lia.
      destruct (Z.leb_spec lo i), (Z.ltb_spec i (lo + Zlength src)); try lia. cbn [andb]. f_equal; lia.
    + rewrite app_Znth2 by lia. rewrite Znth_sublist by lia.
      destruct (Z.leb_spec lo i), (Z.ltb_spec i (lo + Zlength src)); try lia. cbn [andb]. f_equal; lia.
Qed.

Lemma rtdsw_move_val b dst src len b' :
  0 <= src -> 0 <= len -> src + len <= Zlength (mb_val b) ->
  mb_move b dst src len = Some b' ->
  Zlength (mb_val b') = Zlength (mb_val b) /\
  forall i, 0 <= i < Zlength (mb_val b) -> dst <= i < dst + len ->
    Znth i (mb_val b') = Znth (i - dst + src) (mb_val b).
Proof.
  intros H0 H1 H2. unfold mb_move.
  destruct (_ || _); cbn [guard bind]; [|discriminate].
  destruct (mb_read b src len) as [l|] eqn:R; cbn [bind]; [|discriminate].
  unfold mb_read in R. destruct (_ && _); [|discriminate]. injection R as <-.
  intros E. apply rtdsw_write_val in E. destruct E as [L V].
  rewrite Zlength_sublist in V by lia.
  split; [exact L|]. intros i Hi Hi2. rewrite V by exact Hi.
  destruct (Z.leb_spec dst i), (Z.ltb_spec i (dst + (src + len - src))); try lia. cbn [andb].
  rewrite Znth_sublist by lia. f_equal; lia.
Qed.

Lemma rtdsw_u32 x : 0 <= x < 4294967296 -> u32 x = x.
Proof. intros H. unfold u32. apply Z.mod_small. exact H. Qed.

Lemma rtdsw_app_r (H C : list Z) j : Zlength H <= j -> Znth j (H ++ C) = Znth (j - Zlength H) C.
Proof. intros. apply app_Znth2. lia. Qed.

Lemma rtdsw_app_l (H C : list Z) j : 0 <= j < Zlength H -> Znth j (H ++ C) = Znth j H.
Proof. intros. apply app_Znth1. lia. Qed.

Lemma rtdsw_khash s :
  d_level s = 0 ->
  ((d_matches s = 0 /\ chain_hok s) \/ (d_matches s = 1 /\ chain_hok (slide_hc s)) \/ d_matches s = 2) ->
  khash s.
Proof.
  intros E M. unfold khash. rewrite E. split; [exact M|].
  unfold fn_of. rewrite E. intros [F|F]; discriminate F.
Qed.

Ltac rtdsw_ifs := unfold clamp_insert, incr_matches;
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.

Theorem rtds_win_ok : chainh_stmt -> fwin_stmt.
Proof.
  unfold chainh_stmt, fwin_stmt. intros [C1 [C2 C3]] s z used s' H HW Hlev Hb Hu Hn Hu1 Hbs Hc Hkw Hkh.
  pose proof HW as HW'.
  destruct HW' as (Hp & Hws & Hwp & Hww & Hwh & Hwm & H0 & _).
  pose proof Hp as Hp'. destruct Hp' as (Hwb & Hwsz & _).
  assert (Hw : 512 <= d_w_size s <= 32768).
  { rewrite Hwsz. split; [change 512 with (2^9) | change 32768 with (2^15)]; apply Z.pow_le_mono_r; lia. }
  pose proof Hws as Hws'. destruct Hws' as (Hlw & Hok & Hwsize & Hlp & Hlh).
  destruct Hwp as (Hla0 & Hss0 & Hsl & Hbss & _ & _ & Hi & Hi2 & Hhw0).
  destruct (H0 Hlev) as [Hla Hbs0].
  destruct Hkw as [Hk1 Hk2]. rewrite Hla, Z.add_0_r in Hk1, Hk2.
  destruct Hkh as [Hh _]. rewrite Hlev in Hh. cbv beta iota in Hh. change (0 =? 0) with true in Hh. cbv beta iota in Hh.
  unfold c_ds_window in Hc.
  destruct (Z.eqb_spec used 0) as [U0|U0].
  { injection Hc as <-. subst used. rewrite Z.sub_0_r, sublist_nil, app_nil_r.
    split; [split; [rewrite Hla, Z.add_0_r; exact Hk1|rewrite Hla, Z.add_0_r; exact Hk2]|].
    split; [|reflexivity]. split.
    - rewrite Hlev. exact Hh.
    - unfold fn_of. rewrite Hlev. intros [F|F]; discriminate F. }
  assert (Hbs1 : d_block_start s = d_strstart s) by (apply Hbs; lia).
  set (C := sublist (z_next_in z - used) (z_next_in z) (z_in z)).
  assert (LC : Zlength C = used) by (unfold C; rewrite Zlength_sublist by lia; lia).
  destruct (Z.geb_spec used (d_w_size s)) as [G|G].
  - (* used >= w_size *)
    change (d_w_size (set_d_matches s 2)) with (d_w_size s) in Hc.
    unfold rds in Hc.
    replace ((0 <=? z_next_in z - d_w_size s) && (0 <=? d_w_size s) &&
             (z_next_in z - d_w_size s + d_w_size s <=? Zlength (z_in z))) with true in Hc
      by (symmetry; rewrite !andb_true_iff, !Z.leb_le; lia).
    cbn [bind] in Hc.
    change (d_window (set_d_matches s 2)) with (d_window s) in Hc.
    destruct (mb_write (d_window s) 0 _) as [b'|] eqn:E; cbn [bind] in Hc; [|discriminate].
    injection Hc as <-.
    apply rtdsw_write_val in E. destruct E as [L V]. rewrite Zlength_sublist in V by lia.
    replace (z_next_in z - d_w_size s + d_w_size s - (z_next_in z - d_w_size s)) with (d_w_size s) in V by lia.
    match goal with |- kwin _ ?x /\ _ => set (s2 := x) end.
    assert (Ss : d_strstart s2 = d_w_size s) by reflexivity.
    assert (Sl : d_lookahead s2 = d_lookahead s) by reflexivity.
    assert (Sw : d_window s2 = b') by reflexivity.
    assert (Sv : d_level s2 = d_level s) by reflexivity.
    assert (Sm : d_matches s2 = 2) by reflexivity.
    assert (Sb : d_block_start s2 = d_w_size s) by reflexivity.
    split; [|split; [apply rtdsw_khash; [rewrite Sv; exact Hlev|right; right; exact Sm]|rewrite Ss, Sb, Hbs1; lia]].
    unfold kwin. rewrite Ss, Sl, Hla, Sw, Z.add_0_r, Zlength_app, LC. split; [lia|].
    intros i Hj. rewrite V by lia.
    destruct (Z.leb_spec 0 i), (Z.ltb_spec i (0 + d_w_size s)); try lia. cbn [andb].
    rewrite rtdsw_app_r by lia. unfold C. rewrite !Znth_sublist by lia. f_equal. lia.
  - (* used < w_size *)
    replace (u64 (d_window_size s - d_strstart s)) with (d_window_size s - d_strstart s) in Hc
      by (symmetry; apply u64_id; lia).
    destruct (Z.leb_spec (d_window_size s - d_strstart s) used) as [S|S].
    + (* slide *)
      rewrite (rtdsw_u32 (d_strstart s - d_w_size s)) in Hc by lia.
      change (mb_move (d_window (set_d_strstart s (d_strstart s - d_w_size s))) 0
                (d_w_size (set_d_strstart s (d_strstart s - d_w_size s)))
                (d_strstart (set_d_strstart s (d_strstart s - d_w_size s))))
        with (mb_move (d_window s) 0 (d_w_size s) (d_strstart s - d_w_size s)) in Hc.
      destruct (mb_move (d_window s) 0 (d_w_size s) (d_strstart s - d_w_size s)) as [b1|] eqn:E1;
        cbn [bind] in Hc; [|discriminate].
      apply rtdsw_move_val in E1; [|lia..]. destruct E1 as [L1 V1].
      set (s2 := clamp_insert (incr_matches (set_d_window (set_d_strstart s (d_strstart s - d_w_size s)) b1))) in Hc.
      assert (S2s : d_strstart s2 = d_strstart s - d_w_size s) by (unfold s2; rtdsw_ifs).
      assert (S2w : d_window s2 = b1) by (unfold s2; rtdsw_ifs).
      assert (S2l : d_lookahead s2 = d_lookahead s) by (unfold s2; rtdsw_ifs).
      assert (S2v : d_level s2 = d_level s) by (unfold s2; rtdsw_ifs).
      assert (S2m : d_matches s2 = if d_matches s <? 2 then u32 (d_matches s + 1) else d_matches s).
      { unfold s2. transitivity (d_matches (incr_matches (set_d_window (set_d_strstart s (d_strstart s - d_w_size s)) b1))).
        - unfold clamp_insert. destruct (_ >? _); reflexivity.
        - unfold incr_matches.
          change (d_matches (set_d_window (set_d_strstart s (d_strstart s - d_w_size s)) b1)) with (d_matches s).
          destruct (d_matches s <? 2); reflexivity. }
      unfold rds in Hc.
      replace ((0 <=? z_next_in z - used) && (0 <=? used) && (z_next_in z - used + used <=? Zlength (z_in z)))
        with true in Hc by (symmetry; rewrite !andb_true_iff, !Z.leb_le; lia).
      cbn [bind] in Hc. rewrite S2w, S2s in Hc.
      destruct (mb_write b1 (d_strstart s - d_w_size s) (sublist (z_next_in z - used) (z_next_in z - used + used) (z_in z)))
        as [b'|] eqn:E; cbn [bind] in Hc; [|discriminate].
      change (d_strstart (set_d_window s2 b')) with (d_strstart s2) in Hc. rewrite S2s in Hc.
      rewrite (rtdsw_u32 (d_strstart s - d_w_size s + used)) in Hc by lia.
      injection Hc as <-.
      apply rtdsw_write_val in E. destruct E as [L V]. rewrite Zlength_sublist in V by lia.
      replace (z_next_in z - used + used - (z_next_in z - used)) with used in V by lia.
      match goal with |- kwin _ ?x /\ _ => set (s3 := x) end.
      assert (Ss : d_strstart s3 = d_strstart s - d_w_size s + used) by reflexivity.
      assert (Sl : d_lookahead s3 = d_lookahead s) by (rewrite <- S2l; reflexivity).
      assert (Sw : d_window s3 = b') by reflexivity.
      assert (Sv : d_level s3 = d_level s) by (rewrite <- S2v; reflexivity).
      assert (Sm : d_matches s3 = d_matches s2) by reflexivity.
      assert (Sb : d_block_start s3 = d_strstart s3) by reflexivity.
      split; [|split; [apply rtdsw_khash; [rewrite Sv; exact Hlev|]|rewrite Sb, Hbs1; lia]].
      * unfold kwin. rewrite Ss, Sl, Hla, Sw, Z.add_0_r, Zlength_app, LC. split; [lia|].
        intros i Hj. rewrite V by lia.
        destruct (Z_lt_dec i (d_strstart s - d_w_size s)).
        -- destruct (Z.leb_spec (d_strstart s - d_w_size s) i); [lia|]. cbn [andb].
           rewrite V1 by lia. rewrite Hk2 by lia. rewrite rtdsw_app_l by lia. f_equal. lia.
        -- destruct (Z.leb_spec (d_strstart s - d_w_size s) i), (Z.ltb_spec i (d_strstart s - d_w_size s + used));
             try lia. cbn [andb].
           rewrite rtdsw_app_r by lia. unfold C. rewrite !Znth_sublist by lia. f_equal. lia.
      * rewrite Sm, S2m.
        destruct Hh as [[M Ch]|[[M Ch]|M]]; rewrite M; cbn.
        -- right; left. split; [reflexivity|].
           assert (Ch2 : chain_hok (slide_hc s2)).
           { apply (C3 s s2 Hp Hws Ch); try (unfold s2; rtdsw_ifs).
             intros i Hj. rewrite S2w. rewrite S2s, S2l, Hla in Hj. rewrite V1 by lia. f_equal. lia. }
           apply (C2 s2 s3 Ch2); try reflexivity.
           ++ rewrite Ss, S2s. lia.
           ++ rewrite Ss, S2s, Sl, S2l. lia.
           ++ intros i Hj. rewrite Sw, S2w. rewrite S2s, S2l, Hla in Hj. rewrite V by lia.
              destruct (Z.leb_spec (d_strstart s - d_w_size s) i); [lia|]. reflexivity.
        -- right; right; reflexivity.
        -- right; right; reflexivity.
    + (* no slide *)
      cbn [bind] in Hc.
      unfold rds in Hc.
      replace ((0 <=? z_next_in z - used) && (0 <=? used) && (z_next_in z - used + used <=? Zlength (z_in z)))
        with true in Hc by (symmetry; rewrite !andb_true_iff, !Z.leb_le; lia).
      cbn [bind] in Hc.
      destruct (mb_write (d_window s) (d_strstart s) (sublist (z_next_in z - used) (z_next_in z - used + used) (z_in z)))
        as [b'|] eqn:E; cbn [bind] in Hc; [|discriminate].
      change (d_strstart (set_d_window s b')) with (d_strstart s) in Hc.
      rewrite (rtdsw_u32 (d_strstart s + used)) in Hc by lia.
      injection Hc as <-.
      apply rtdsw_write_val in E. destruct E as [L V]. rewrite Zlength_sublist in V by lia.
      replace (z_next_in z - used + used - (z_next_in z - used)) with used in V by lia.
      match goal with |- kwin _ ?x /\ _ => set (s3 := x) end.
      assert (Ss : d_strstart s3 = d_strstart s + used) by reflexivity.
      assert (Sl : d_lookahead s3 = d_lookahead s) by reflexivity.
      assert (Sw : d_window s3 = b') by reflexivity.
      assert (Sv : d_level s3 = d_level s) by reflexivity.
      assert (Sm : d_matches s3 = d_matches s) by reflexivity.
      assert (Sb : d_block_start s3 = d_strstart s3) by reflexivity.
      assert (Wk : forall i, 0 <= i < d_strstart s + d_lookahead s ->
                     Znth i (mb_val (d_window s3)) = Znth i (mb_val (d_window s))).
      { intros i Hj. rewrite Hla in Hj. rewrite Sw, V by lia.
        destruct (Z.leb_spec (d_strstart s) i); [lia|]. reflexivity. }
      split; [|split; [apply rtdsw_khash; [rewrite Sv; exact Hlev|]|rewrite Sb, Hbs1; lia]].
      * unfold kwin. rewrite Ss, Sl, Hla, Sw, Z.add_0_r, Zlength_app, LC. split; [lia|].
        intros i Hj. rewrite V by lia.
        destruct (Z_lt_dec i (d_strstart s)).
        -- destruct (Z.leb_spec (d_strstart s) i); [lia|]. cbn [andb].
           rewrite Hk2 by lia. rewrite rtdsw_app_l by lia. f_equal. lia.
        -- destruct (Z.leb_spec (d_strstart s) i), (Z.ltb_spec i (d_strstart s + used)); try lia. cbn [andb].
           rewrite rtdsw_app_r by lia. unfold C. rewrite !Znth_sublist by lia. f_equal. lia.
      * rewrite Sm.
        destruct Hh as [[M Ch]|[[M Ch]|M]].
        -- left. split; [exact M|]. apply (C1 s s3 Ch); try reflexivity; [rewrite Ss; lia|rewrite Ss, Sl; lia|exact Wk].
        -- right; left. split; [exact M|].
           apply (C2 s s3 Ch); try reflexivity; [rewrite Ss; lia|rewrite Ss, Sl; lia|exact Wk].
        -- right; right; exact M.
Qed.
