(** * deflate_stored at level 0: c_ds_window
    Statement and design: LTCStoredKit.v and its header. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTCStoredKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** Masked-buffer facts *)

Lemma dsw_definedb b lo hi :
  0 <= lo -> hi <= Zlength (mb_val b) -> (forall i, lo <= i < hi -> Znth i (mb_def b) = true) ->
  mb_definedb b lo hi = true.
Proof.
  intros H0 H1 H2. unfold mb_definedb.
  rewrite (proj2 (Z.leb_le _ _) H0), (proj2 (Z.leb_le _ _) H1). cbn [andb].
  apply forallb_forall. intros x Hx. apply in_map_iff in Hx. destruct Hx as [k [<- Hk]].
  apply in_seq in Hk. apply H2. lia.
Qed.

Lemma dsw_write b lo src :
  mb_ok b -> bytes src -> 0 <= lo -> lo + Zlength src <= Zlength (mb_val b) ->
  exists b', mb_write b lo src = Some b' /\ Zlength (mb_val b') = Zlength (mb_val b) /\ mb_ok b' /\
    (forall i, Znth i (mb_def b) = true -> Znth i (mb_def b') = true) /\
    (forall i, lo <= i < lo + Zlength src -> Znth i (mb_def b') = true).
Proof.
  intros [Hl Hb] Hs H0 H1. unfold mb_write.
  rewrite (proj2 (Z.leb_le _ _) H0), (proj2 (Z.leb_le _ _) H1). cbn [andb].
  eexists. split; [reflexivity|]. cbn [mb_val mb_def].
  pose proof (Zlength_nonneg src).
  assert (Lv : Zlength (sublist 0 lo (mb_val b) ++ src ++ sublist (lo + Zlength src) (Zlength (mb_val b)) (mb_val b))
               = Zlength (mb_val b)) by (rewrite !Zlength_app, !Zlength_sublist by lia; lia).
  assert (Ld : Zlength (sublist 0 lo (mb_def b) ++ repeat true (Z.to_nat (Zlength src)) ++
                 sublist (lo + Zlength src) (Zlength (mb_def b)) (mb_def b)) = Zlength (mb_val b))
    by (rewrite !Zlength_app, Zlength_repeat, !Zlength_sublist by lia; lia).
  assert (Dd : forall i, Znth i (sublist 0 lo (mb_def b) ++ repeat true (Z.to_nat (Zlength src)) ++
                 sublist (lo + Zlength src) (Zlength (mb_def b)) (mb_def b)) =
                 if (lo <=? i) && (i <? lo + Zlength src) then true else Znth i (mb_def b)).
  { intros i. destruct (Z_lt_dec i 0).
    - rewrite !Znth_underflow by lia. destruct (Z.leb_spec lo i); [lia|reflexivity].
    - destruct (Z_lt_dec i lo).
      + rewrite app_Znth1 by (rewrite Zlength_sublist by lia; lia). rewrite Znth_sublist by lia.
        destruct (Z.leb_spec lo i); [lia|]. cbn [andb]. f_equal; lia.
      + rewrite app_Znth2 by (rewrite Zlength_sublist by lia; lia). rewrite Zlength_sublist by lia.
        destruct (Z_lt_dec i (lo + Zlength src)).
        * rewrite app_Znth1 by (rewrite Zlength_repeat; lia). rewrite Znth_repeat' by lia.
          destruct (Z.leb_spec lo i), (Z.ltb_spec i (lo + Zlength src)); try lia; reflexivity.
        * rewrite app_Znth2 by (rewrite Zlength_repeat; lia). rewrite Zlength_repeat by lia.
          destruct (Z.leb_spec lo i), (Z.ltb_spec i (lo + Zlength src)); try lia. cbn [andb].
          destruct (Z_lt_dec i (Zlength (mb_def b))).
          -- rewrite Znth_sublist by lia. f_equal. lia.
          -- rewrite !Znth_overflow; try reflexivity; rewrite ?Zlength_sublist by lia; lia. }
  split; [exact Lv|]. split; [unfold mb_ok; cbn [mb_val mb_def]; split|split].
  - rewrite Ld, Lv. reflexivity.
  - rewrite Lv. intros i Hi Hd. rewrite Dd in Hd.
    destruct (Z_lt_dec i lo).
    + rewrite app_Znth1 by (rewrite Zlength_sublist by lia; lia). rewrite Znth_sublist by lia.
      replace (i + 0) with i by lia. apply Hb; [lia|].
      destruct (Z.leb_spec lo i); [lia|exact Hd].
    + rewrite app_Znth2 by (rewrite Zlength_sublist by lia; lia). rewrite Zlength_sublist by lia.
      destruct (Z_lt_dec i (lo + Zlength src)).
      * rewrite app_Znth1 by lia. unfold bytes in Hs. rewrite Forall_forall in Hs.
        apply Hs, Znth_In. lia.
      * rewrite app_Znth2 by lia. rewrite Znth_sublist by lia.
        replace (i - (lo - 0) - Zlength src + (lo + Zlength src)) with i by lia.
        apply Hb; [lia|]. destruct (Z.ltb_spec i (lo + Zlength src)); [lia|].
        rewrite andb_false_r in Hd. exact Hd.
  - intros i Hd. rewrite Dd, Hd. destruct (_ && _); reflexivity.
  - intros i Hi. rewrite Dd. destruct (Z.leb_spec lo i), (Z.ltb_spec i (lo + Zlength src)); try lia. reflexivity.
Qed.

Lemma dsw_read b lo len :
  0 <= lo -> 0 <= len -> lo + len <= Zlength (mb_val b) ->
  (forall i, lo <= i < lo + len -> Znth i (mb_def b) = true) ->
  mb_read b lo len = Some (sublist lo (lo + len) (mb_val b)).
Proof.
  intros H0 H1 H2 H3. unfold mb_read. rewrite dsw_definedb by auto.
  rewrite (proj2 (Z.leb_le _ _) H1). reflexivity.
Qed.

Lemma dsw_move b dst src len :
  mb_ok b -> 0 <= dst -> 0 <= len -> dst + len <= src -> src + len <= Zlength (mb_val b) ->
  (forall i, src <= i < src + len -> Znth i (mb_def b) = true) ->
  exists b', mb_move b dst src len = Some b' /\ Zlength (mb_val b') = Zlength (mb_val b) /\ mb_ok b' /\
    (forall i, Znth i (mb_def b) = true -> Znth i (mb_def b') = true) /\
    (forall i, dst <= i < dst + len -> Znth i (mb_def b') = true).
Proof.
  intros Hok H0 H1 H2 H3 H4. unfold mb_move.
  rewrite (proj2 (Z.leb_le _ _) H2). cbn [orb guard bind].
  rewrite dsw_read by first [lia | exact H4]. cbn [bind].
  assert (Hl : Zlength (sublist src (src + len) (mb_val b)) = len) by (rewrite Zlength_sublist; lia).
  destruct (dsw_write b dst (sublist src (src + len) (mb_val b))) as (b' & E & L & K & P & N); auto.
  - destruct Hok as [_ Hb]. unfold bytes. apply Forall_forall. intros x Hx.
    apply In_Znth in Hx. destruct Hx as [k [Hk <-]]. rewrite Hl in Hk.
    rewrite Znth_sublist by lia. apply Hb; [lia|]. apply H4. lia.
  - lia.
  - exists b'. rewrite Hl in N. auto.
Qed.

(** ** Frames: c_ds_window only changes what [win_keep] blanks *)

Lemma wk_window s x : win_keep (set_d_window s x) = win_keep s. Proof. reflexivity. Qed.
Lemma wk_strstart s x : win_keep (set_d_strstart s x) = win_keep s. Proof. reflexivity. Qed.
Lemma wk_insert s x : win_keep (set_d_insert s x) = win_keep s. Proof. reflexivity. Qed.
Lemma wk_block_start s x : win_keep (set_d_block_start s x) = win_keep s. Proof. reflexivity. Qed.
Lemma wk_matches s x : win_keep (set_d_matches s x) = win_keep s. Proof. reflexivity. Qed.
Lemma wk_incr s : win_keep (incr_matches s) = win_keep s.
Proof. unfold incr_matches. destruct (_ <? _); [apply wk_matches|reflexivity]. Qed.
Lemma wk_clamp s : win_keep (clamp_insert s) = win_keep s.
Proof. unfold clamp_insert. destruct (_ >? _); [apply wk_insert|reflexivity]. Qed.
Lemma wk_add s n : win_keep (add_insert s n) = win_keep s.
Proof. unfold add_insert. apply wk_insert. Qed.

Lemma wk_inv (P : dstate -> Prop) s s' : win_keep s' = win_keep s -> P (win_keep s) -> P (win_keep s').
Proof. intros E H. rewrite E. exact H. Qed.

Lemma dsw_W s s' :
  W s -> d_level s = 0 -> win_keep s' = win_keep s ->
  Zlength (mb_val (d_window s')) = 2 * d_w_size s -> mb_ok (d_window s') ->
  0 <= d_strstart s' <= d_window_size s -> d_block_start s' = d_strstart s' ->
  0 <= d_insert s' <= d_strstart s' -> d_insert s' <= d_w_size s ->
  d_high_water s' = d_high_water s ->
  (forall i, 0 <= i < Z.max (d_strstart s') (d_high_water s) -> Znth i (mb_def (d_window s')) = true) ->
  ((d_matches s' = 0 /\ chain_ok s') \/ (d_matches s' = 1 /\ chain_ok (slide_hc s')) \/ d_matches s' = 2) ->
  W s'.
Proof.
  intros HW Hlev E Hlw Hok Hss Hbs Hin Hin2 Hhw Hdef Hh.
  destruct HW as (Hp & Hws & Hwp & Hww & Hwh & Hwm & H0 & syms & Hwt).
  destruct (H0 Hlev) as [Hla Hbs0].
  assert (Elev : d_level s' = d_level s) by exact (f_equal d_level E).
  assert (Ews : d_w_size s' = d_w_size s) by exact (f_equal d_w_size E).
  assert (Ewz : d_window_size s' = d_window_size s) by exact (f_equal d_window_size E).
  assert (Ela : d_lookahead s' = d_lookahead s) by exact (f_equal d_lookahead E).
  assert (Elp : d_prev s' = d_prev s) by exact (f_equal d_prev E).
  assert (Elh : d_head s' = d_head s) by exact (f_equal d_head E).
  assert (Ehs : d_hash_size s' = d_hash_size s) by exact (f_equal d_hash_size E).
  assert (Eml : d_match_length s' = d_match_length s) by exact (f_equal d_match_length E).
  assert (Epl : d_prev_length s' = d_prev_length s) by exact (f_equal d_prev_length E).
  assert (Ema : d_match_available s' = d_match_available s) by exact (f_equal d_match_available E).
  assert (EL : d_L s' = d_L s) by exact (f_equal d_L E).
  destruct Hws as (Hlw0 & Hok0 & Hwsize & Hlp & Hlh).
  destruct Hwp as (Hla0 & Hss0 & Hsl & Hbss & Hd & Hneg & Hi & Hi2 & Hhw0).
  split; [exact (wk_inv prm s s' E Hp)|].
  split; [unfold wstruct; rewrite Ewz, Elp, Elh, Ehs, Ews; auto|].
  split; [unfold wpos; rewrite Ewz, Ela, Hbs, Hla, Hhw, Ews; lia|].
  split; [unfold wwin; rewrite Ela, Hla, Z.add_0_r, Hhw; exact Hdef|].
  split; [unfold whash; rewrite Elev, Hlev; exact Hh|].
  split.
  { assert (Hma : d_match_available s = 0).
    { destruct Hwm as (_ & _ & [A|A] & _ & B); [exact A|]. destruct (B A) as [F _].
      unfold fn_of in F. rewrite Hlev in F. discriminate F. }
    destruct Hwm as (A1 & A2 & _ & A4 & _).
    unfold wmatch. rewrite Eml, Epl, Ema, Hma. split; [lia|]. split; [lia|]. split; [left; reflexivity|].
    split; [intros _; apply A4, Hma|]. intros F; discriminate F. }
  split; [rewrite Ela, Hbs; lia|].
  exists syms. destruct Hwt as (T1 & T2 & T3 & T4 & T5).
  split; [exact (wk_inv (fun x => tree_ok (d_tr x) (d_pbm x) syms) s s' E T1)|].
  split; [rewrite EL; exact T2|].
  split; [exact (wk_inv (fun x => Forall (sym_ok x) syms) s s' E T3)|].
  split; [rewrite Elev; exact T4|].
  rewrite Elev, Hlev. intros F; contradiction F; reflexivity.
Qed.

Lemma dsw_u32 x : 0 <= x < 4294967296 -> u32 x = x.
Proof. intros H. unfold u32. apply Z.mod_small. exact H. Qed.

Lemma incr_strstart s : d_strstart (incr_matches s) = d_strstart s.
Proof. unfold incr_matches. destruct (_ <? _); reflexivity. Qed.
Lemma incr_window s : d_window (incr_matches s) = d_window s.
Proof. unfold incr_matches. destruct (_ <? _); reflexivity. Qed.
Lemma incr_insert s : d_insert (incr_matches s) = d_insert s.
Proof. unfold incr_matches. destruct (_ <? _); reflexivity. Qed.
Lemma incr_hw s : d_high_water (incr_matches s) = d_high_water s.
Proof. unfold incr_matches. destruct (_ <? _); reflexivity. Qed.
Lemma incr_m s : d_matches (incr_matches s) = if d_matches s <? 2 then u32 (d_matches s + 1) else d_matches s.
Proof. unfold incr_matches. destruct (_ <? _); reflexivity. Qed.
Lemma clamp_strstart s : d_strstart (clamp_insert s) = d_strstart s.
Proof. unfold clamp_insert. destruct (_ >? _); reflexivity. Qed.
Lemma clamp_window s : d_window (clamp_insert s) = d_window s.
Proof. unfold clamp_insert. destruct (_ >? _); reflexivity. Qed.
Lemma clamp_hw s : d_high_water (clamp_insert s) = d_high_water s.
Proof. unfold clamp_insert. destruct (_ >? _); reflexivity. Qed.
Lemma clamp_m s : d_matches (clamp_insert s) = d_matches s.
Proof. unfold clamp_insert. destruct (_ >? _); reflexivity. Qed.
Lemma clamp_insert_v s : d_insert (clamp_insert s) = Z.min (d_insert s) (d_strstart s).
Proof. unfold clamp_insert. destruct (Z.gtb_spec (d_insert s) (d_strstart s)); cbn; lia. Qed.

Lemma dsw_bs s : d_block_start (set_d_block_start s (d_strstart s)) = d_strstart (set_d_block_start s (d_strstart s)).
Proof. reflexivity. Qed.

Theorem dswin_ok : chain_stmt -> dswin_stmt.
Proof.
  intros [C1 C2] s z used HW Hlev Hb Hu Hn Hu1 Hbs.
  pose proof HW as HW'.
  destruct HW' as (Hp & Hws & Hwp & Hww & Hwh & Hwm & H0 & _).
  pose proof Hp as Hp'. destruct Hp' as (Hwb & Hwsz & _).
  assert (Hw : 512 <= d_w_size s <= 32768).
  { rewrite Hwsz. split; [change 512 with (2^9) | change 32768 with (2^15)]; apply Z.pow_le_mono_r; lia. }
  pose proof Hws as Hws'. destruct Hws' as (Hlw & Hok & Hwsize & Hlp & Hlh).
  destruct Hwp as (Hla0 & Hss0 & Hsl & Hbss & _ & _ & Hi & Hi2 & Hhw0).
  destruct (H0 Hlev) as [Hla Hbs0].
  rewrite Hla in Hsl. unfold wwin in Hww. rewrite Hla, Z.add_0_r in Hww.
  assert (Hbyt : forall lo hi, bytes (sublist lo hi (z_in z))) by (intros; apply Forall_sublist, Hb).
  unfold c_ds_window.
  destruct (Z.eqb_spec used 0) as [U0|U0].
  { exists s. split; [reflexivity|]. split; [exact HW|]. split; reflexivity. }
  assert (Hbs1 : d_block_start s = d_strstart s) by (apply Hbs; lia).
  destruct (Z.geb_spec used (d_w_size s)) as [G|G].
  - (* used >= w_size *)
    change (d_w_size (set_d_matches s 2)) with (d_w_size s).
    unfold rds.
    replace ((0 <=? z_next_in z - d_w_size s) && (0 <=? d_w_size s) &&
             (z_next_in z - d_w_size s + d_w_size s <=? Zlength (z_in z))) with true
      by (symmetry; rewrite !andb_true_iff, !Z.leb_le; lia).
    cbn [bind].
    change (d_window (set_d_matches s 2)) with (d_window s).
    destruct (dsw_write (d_window s) 0 (sublist (z_next_in z - d_w_size s) (z_next_in z - d_w_size s + d_w_size s) (z_in z)))
      as (b' & E & L & K & P & N); auto; [lia|rewrite Zlength_sublist by lia; lia|].
    rewrite Zlength_sublist in N by lia.
    rewrite E. cbn [bind].
    eexists. split; [reflexivity|].
    match goal with |- W ?x /\ _ => set (s' := x) end.
    assert (Ek : win_keep s' = win_keep s)
      by (unfold s'; rewrite wk_block_start, wk_insert, wk_strstart, wk_window, wk_matches; reflexivity).
    split; [|split; [exact Ek|]].
    + apply (dsw_W s s' HW Hlev Ek).
      * change (Zlength (mb_val b') = 2 * d_w_size s). lia.
      * exact K.
      * change (0 <= d_w_size s <= d_window_size s). lia.
      * exact (dsw_bs _).
      * change (0 <= d_w_size s <= d_w_size s). lia.
      * change (d_w_size s <= d_w_size s). lia.
      * reflexivity.
      * change (forall i, 0 <= i < Z.max (d_w_size s) (d_high_water s) -> Znth i (mb_def b') = true).
        intros j Hj. destruct (Z_lt_dec j (d_w_size s)); [apply N; lia|].
        apply P, Hww. lia.
      * right; right; reflexivity.
    + unfold ub. rewrite (dsw_bs _ : d_block_start s' = d_strstart s').
      rewrite (f_equal d_lookahead Ek : d_lookahead s' = d_lookahead s), Hbs1. lia.
  - (* used < w_size *)
    replace (u64 (d_window_size s - d_strstart s)) with (d_window_size s - d_strstart s)
      by (symmetry; apply u64_id; lia).
    destruct (Z.leb_spec (d_window_size s - d_strstart s) used) as [S|S].
    + (* slide *)
      rewrite (dsw_u32 (d_strstart s - d_w_size s)) by lia.
      change (mb_move (d_window (set_d_strstart s (d_strstart s - d_w_size s))) 0
                (d_w_size (set_d_strstart s (d_strstart s - d_w_size s)))
                (d_strstart (set_d_strstart s (d_strstart s - d_w_size s))))
        with (mb_move (d_window s) 0 (d_w_size s) (d_strstart s - d_w_size s)).
      destruct (dsw_move (d_window s) 0 (d_w_size s) (d_strstart s - d_w_size s))
        as (b1 & E1 & L1 & K1 & P1 & N1); auto; try lia.
      { intros j Hj. apply Hww. lia. }
      rewrite E1. cbn [bind].
      set (s2 := clamp_insert (incr_matches (set_d_window (set_d_strstart s (d_strstart s - d_w_size s)) b1))).
      assert (S2s : d_strstart s2 = d_strstart s - d_w_size s)
        by (unfold s2; rewrite clamp_strstart, incr_strstart; reflexivity).
      assert (S2w : d_window s2 = b1) by (unfold s2; rewrite clamp_window, incr_window; reflexivity).
      assert (S2i : d_insert s2 = Z.min (d_insert s) (d_strstart s - d_w_size s))
        by (unfold s2; rewrite clamp_insert_v, incr_strstart, incr_insert; reflexivity).
      assert (S2h : d_high_water s2 = d_high_water s) by (unfold s2; rewrite clamp_hw, incr_hw; reflexivity).
      assert (S2m : d_matches s2 = if d_matches s <? 2 then u32 (d_matches s + 1) else d_matches s)
        by (unfold s2; rewrite clamp_m, incr_m; reflexivity).
      assert (S2k : win_keep s2 = win_keep s)
        by (unfold s2; rewrite wk_clamp, wk_incr, wk_window, wk_strstart; reflexivity).
      assert (S2z : d_w_size s2 = d_w_size s) by exact (f_equal d_w_size S2k).
      unfold rds.
      replace ((0 <=? z_next_in z - used) && (0 <=? used) && (z_next_in z - used + used <=? Zlength (z_in z)))
        with true by (symmetry; rewrite !andb_true_iff, !Z.leb_le; lia).
      cbn [bind]. rewrite S2w, S2s.
      destruct (dsw_write b1 (d_strstart s - d_w_size s) (sublist (z_next_in z - used) (z_next_in z - used + used) (z_in z)))
        as (b' & E & L & K & P & N); auto; [lia|rewrite Zlength_sublist by lia; lia|].
      rewrite Zlength_sublist in N by lia.
      rewrite E. cbn [bind].
      change (d_strstart (set_d_window s2 b')) with (d_strstart s2). rewrite S2s.
      rewrite (dsw_u32 (d_strstart s - d_w_size s + used)) by lia.
      eexists. split; [reflexivity|].
      match goal with |- W ?x /\ _ => set (s' := x) end.
      assert (Ek : win_keep s' = win_keep s)
        by (unfold s'; rewrite wk_block_start, wk_add, wk_strstart, wk_window; exact S2k).
      assert (Ss : d_strstart s' = d_strstart s - d_w_size s + used) by reflexivity.
      assert (Si : d_insert s' = u32 (d_insert s2 + (if used >? u32 (d_w_size s2 - d_insert s2) then
                                                        u32 (d_w_size s2 - d_insert s2) else used)))
        by reflexivity.
      rewrite S2z, S2i, (dsw_u32 (d_w_size s - _)) in Si by lia.
      assert (Si' : 0 <= d_insert s' <= d_strstart s' /\ d_insert s' <= d_w_size s).
      { rewrite Si, Ss. destruct (Z.gtb_spec used (d_w_size s - Z.min (d_insert s) (d_strstart s - d_w_size s)));
          rewrite dsw_u32 by lia; lia. }
      split; [|split; [exact Ek|]].
      * apply (dsw_W s s' HW Hlev Ek).
        -- change (Zlength (mb_val b') = 2 * d_w_size s). lia.
        -- exact K.
        -- rewrite Ss. lia.
        -- exact (dsw_bs _).
        -- lia.
        -- lia.
        -- exact S2h.
        -- change (forall i, 0 <= i < Z.max (d_strstart s') (d_high_water s) -> Znth i (mb_def b') = true).
           rewrite Ss. intros j Hj.
           destruct (Z_lt_dec j (d_strstart s - d_w_size s)); [apply P, N1; lia|].
           destruct (Z_lt_dec j (d_strstart s - d_w_size s + used)); [apply N; lia|].
           apply P, P1, Hww. lia.
        -- change (d_matches s') with (d_matches s2). rewrite S2m.
           unfold whash in Hwh. rewrite Hlev in Hwh. cbn in Hwh.
           destruct Hwh as [[M C]|[[M C]|M]]; rewrite M; cbn.
           ++ right; left. split; [reflexivity|].
              apply (C2 s s' Hp Hws C).
              ** exact (f_equal d_head Ek).
              ** exact (f_equal d_prev Ek).
              ** exact (f_equal d_w_size Ek).
              ** exact (f_equal d_w_mask Ek).
              ** exact (f_equal d_hash_size Ek).
              ** rewrite Ss. lia.
           ++ right; right; reflexivity.
           ++ right; right; reflexivity.
      * unfold ub. rewrite (dsw_bs _ : d_block_start s' = d_strstart s').
        rewrite (f_equal d_lookahead Ek : d_lookahead s' = d_lookahead s), Hbs1. lia.
    + (* no slide *)
      unfold rds.
      replace ((0 <=? z_next_in z - used) && (0 <=? used) && (z_next_in z - used + used <=? Zlength (z_in z)))
        with true by (symmetry; rewrite !andb_true_iff, !Z.leb_le; lia).
      cbn [bind].
      destruct (dsw_write (d_window s) (d_strstart s) (sublist (z_next_in z - used) (z_next_in z - used + used) (z_in z)))
        as (b' & E & L & K & P & N); auto; [rewrite Zlength_sublist by lia; lia|].
      rewrite Zlength_sublist in N by lia.
      rewrite E. cbn [bind].
      change (d_strstart (set_d_window s b')) with (d_strstart s).
      rewrite (dsw_u32 (d_strstart s + used)) by lia.
      eexists. split; [reflexivity|].
      match goal with |- W ?x /\ _ => set (s' := x) end.
      assert (Ek : win_keep s' = win_keep s)
        by (unfold s'; rewrite wk_block_start, wk_add, wk_strstart, wk_window; reflexivity).
      assert (Ss : d_strstart s' = d_strstart s + used) by reflexivity.
      assert (Si : d_insert s' = u32 (d_insert s + (if used >? u32 (d_w_size s - d_insert s) then
                                                        u32 (d_w_size s - d_insert s) else used)))
        by reflexivity.
      rewrite (dsw_u32 (d_w_size s - _)) in Si by lia.
      assert (Si' : 0 <= d_insert s' <= d_strstart s' /\ d_insert s' <= d_w_size s).
      { rewrite Si, Ss. destruct (Z.gtb_spec used (d_w_size s - d_insert s));
          rewrite dsw_u32 by lia; lia. }
      split; [|split; [exact Ek|]].
      * apply (dsw_W s s' HW Hlev Ek).
        -- change (Zlength (mb_val b') = 2 * d_w_size s). lia.
        -- exact K.
        -- rewrite Ss. lia.
        -- exact (dsw_bs _).
        -- lia.
        -- lia.
        -- reflexivity.
        -- change (forall i, 0 <= i < Z.max (d_strstart s') (d_high_water s) -> Znth i (mb_def b') = true).
           rewrite Ss. intros j Hj.
           destruct (Z_lt_dec j (d_strstart s)); [apply P, Hww; lia|].
           destruct (Z_lt_dec j (d_strstart s + used)); [apply N; lia|].
           apply P, Hww. lia.
        -- change (d_matches s') with (d_matches s).
           unfold whash in Hwh. rewrite Hlev in Hwh. cbn in Hwh.
           destruct Hwh as [[M C]|[[M C]|M]].
           ++ left. split; [exact M|].
              apply (C1 s s' C).
              ** exact (f_equal d_head Ek).
              ** exact (f_equal d_prev Ek).
              ** exact (f_equal d_w_size Ek).
              ** exact (f_equal d_w_mask Ek).
              ** exact (f_equal d_hash_size Ek).
              ** rewrite Ss. lia.
           ++ right; left. split; [exact M|].
              apply (C1 (slide_hc s) (slide_hc s') C).
              ** exact (f_equal (fun x => d_head (slide_hc x)) Ek).
              ** exact (f_equal (fun x => d_prev (slide_hc x)) Ek).
              ** exact (f_equal d_w_size Ek).
              ** exact (f_equal d_w_mask Ek).
              ** exact (f_equal d_hash_size Ek).
              ** change (d_strstart s <= d_strstart s'). rewrite Ss. lia.
           ++ right; right; exact M.
      * unfold ub. rewrite (dsw_bs _ : d_block_start s' = d_strstart s').
        rewrite (f_equal d_lookahead Ek : d_lookahead s' = d_lookahead s), Hbs1. lia.
Qed.
