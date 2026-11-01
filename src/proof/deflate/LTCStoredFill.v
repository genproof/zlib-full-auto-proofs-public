(** * deflate_stored at level 0: the second-phase window refill
    Statement and design: LTCStoredKit.v and its header. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTCStoredKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** Masked buffers *)

Lemma Znth_splice {A} {d : Inhabitant A} (x m : list A) lo i :
  0 <= lo -> lo + Zlength m <= Zlength x -> 0 <= i < Zlength x ->
  Znth i (sublist 0 lo x ++ m ++ sublist (lo + Zlength m) (Zlength x) x) =
  if (i <? lo) || (lo + Zlength m <=? i) then Znth i x else Znth (i - lo) m.
Proof.
  intros Hlo Hhi Hi. pose proof (Zlength_nonneg m).
  assert (L0 : Zlength (sublist 0 lo x) = lo) by (rewrite Zlength_sublist; lia).
  destruct (Z.ltb_spec i lo).
  - rewrite app_Znth1 by (rewrite L0; lia). rewrite Znth_sublist by lia. cbn [orb]. f_equal; lia.
  - rewrite app_Znth2 by (rewrite L0; lia). rewrite L0. destruct (Z.leb_spec (lo + Zlength m) i); cbn [orb].
    + rewrite app_Znth2 by lia. rewrite Znth_sublist by lia. f_equal; lia.
    + rewrite app_Znth1 by lia. reflexivity.
Qed.

Lemma mb_definedb_true b lo hi :
  0 <= lo -> lo <= hi -> hi <= Zlength (mb_val b) ->
  (forall i, lo <= i < hi -> Znth i (mb_def b) = true) -> mb_definedb b lo hi = true.
Proof.
  intros H1 H2 H3 H4. unfold mb_definedb.
  rewrite (proj2 (Z.leb_le _ _) H1), (proj2 (Z.leb_le _ _) H3). cbn [andb].
  apply forallb_forall. intros x Hx. apply in_map_iff in Hx. destruct Hx as (k & <- & Hk).
  apply in_seq in Hk. apply H4. lia.
Qed.

Lemma mb_write_ok b lo src :
  mb_ok b -> bytes src -> 0 <= lo -> lo + Zlength src <= Zlength (mb_val b) ->
  exists b', mb_write b lo src = Some b' /\ Zlength (mb_val b') = Zlength (mb_val b) /\ mb_ok b' /\
    (forall i, 0 <= i < Zlength (mb_val b) -> Znth i (mb_def b) = true -> Znth i (mb_def b') = true) /\
    (forall i, lo <= i < lo + Zlength src -> Znth i (mb_def b') = true).
Proof.
  intros [Hd Hv] Hb Hlo Hhi. pose proof (Zlength_nonneg src).
  unfold mb_write. rewrite (proj2 (Z.leb_le _ _) Hlo), (proj2 (Z.leb_le _ _) Hhi). cbn [andb].
  eexists. split; [reflexivity|]. cbn [mb_val mb_def].
  set (r := repeat true (Z.to_nat (Zlength src))).
  assert (Lr : Zlength r = Zlength src) by (apply Zlength_repeat; lia).
  assert (Ed : forall i, 0 <= i < Zlength (mb_val b) ->
     Znth i (sublist 0 lo (mb_def b) ++ r ++ sublist (lo + Zlength src) (Zlength (mb_def b)) (mb_def b)) =
     if (i <? lo) || (lo + Zlength src <=? i) then Znth i (mb_def b) else true).
  { intros i Hi. rewrite <- Lr. rewrite Znth_splice by lia. rewrite Lr.
    destruct (_ || _) eqn:C; [reflexivity|].
    apply orb_false_iff in C. destruct C as [C1 C2]. apply Z.ltb_ge in C1. apply Z.leb_gt in C2.
    unfold r. apply Znth_repeat_inrange. lia. }
  assert (Ev : forall i, 0 <= i < Zlength (mb_val b) ->
     Znth i (sublist 0 lo (mb_val b) ++ src ++ sublist (lo + Zlength src) (Zlength (mb_val b)) (mb_val b)) =
     if (i <? lo) || (lo + Zlength src <=? i) then Znth i (mb_val b) else Znth (i - lo) src).
  { intros i Hi. apply Znth_splice; lia. }
  assert (Lv : Zlength (sublist 0 lo (mb_val b) ++ src ++ sublist (lo + Zlength src) (Zlength (mb_val b)) (mb_val b))
               = Zlength (mb_val b)).
  { rewrite !Zlength_app, !Zlength_sublist by lia. lia. }
  assert (Ld : Zlength (sublist 0 lo (mb_def b) ++ r ++ sublist (lo + Zlength src) (Zlength (mb_def b)) (mb_def b))
               = Zlength (mb_val b)).
  { rewrite !Zlength_app, !Zlength_sublist by lia. lia. }
  split; [exact Lv|]. unfold mb_ok; cbn [mb_val mb_def]. split; [split; [lia|]|split].
  - rewrite Lv. intros i Hi Hdi. rewrite Ed in Hdi by lia. rewrite Ev by lia.
    destruct (_ || _) eqn:C; [auto|]. refine (Forall_Znth (fun v => 0 <= v < 256) src (i - lo) _ Hb).
    apply orb_false_iff in C. destruct C as [C1 C2]. apply Z.ltb_ge in C1. apply Z.leb_gt in C2. lia.
  - intros i Hi Hdi. rewrite Ed by lia. destruct (_ || _); auto.
  - intros i Hi. rewrite Ed by lia.
    replace ((i <? lo) || (lo + Zlength src <=? i)) with false; [reflexivity|].
    symmetry. apply orb_false_iff. split; [apply Z.ltb_ge|apply Z.leb_gt]; lia.
Qed.

Lemma mb_move_ok b w n :
  mb_ok b -> Zlength (mb_val b) = 2 * w -> 0 <= n <= w ->
  (forall i, w <= i < w + n -> Znth i (mb_def b) = true) ->
  exists b', mb_move b 0 w n = Some b' /\ Zlength (mb_val b') = Zlength (mb_val b) /\ mb_ok b' /\
    (forall i, 0 <= i < Zlength (mb_val b) -> Znth i (mb_def b) = true -> Znth i (mb_def b') = true) /\
    (forall i, 0 <= i < n -> Znth i (mb_def b') = true).
Proof.
  intros Hok HL Hn Hdef. unfold mb_move.
  replace ((0 + n <=? w) || (w + n <=? 0)) with true by (symmetry; apply orb_true_iff; left; apply Z.leb_le; lia).
  cbn [guard bind]. unfold mb_read.
  rewrite mb_definedb_true by (auto; lia).
  replace (0 <=? n) with true by (symmetry; apply Z.leb_le; lia). cbn [andb bind].
  assert (Ls : Zlength (sublist w (w + n) (mb_val b)) = n) by (rewrite Zlength_sublist; lia).
  destruct (mb_write_ok b 0 (sublist w (w + n) (mb_val b))) as (b' & E & H1 & H2 & H3 & H4); auto; try lia.
  - apply Forall_forall_Znth. intros i Hi. rewrite Ls in Hi. rewrite Znth_sublist by lia.
    destruct Hok as [_ Hv]. apply Hv; [lia|]. apply Hdef. lia.
  - exists b'. rewrite Ls in H4. split; [exact E|]. split; [exact H1|]. split; [exact H2|].
    split; [exact H3|]. intros i Hi. apply H4. lia.
Qed.

(** ** Frames of the setters *)

Lemma u32_id' x : 0 <= x < 4294967296 -> u32 x = x.
Proof. intros H. unfold u32. apply Z.mod_small. exact H. Qed.

Lemma w_bounds s : prm s -> 512 <= d_w_size s <= 32768.
Proof.
  intros (Hb & Hw & _). rewrite Hw. split.
  - change 512 with (2 ^ 9). apply Z.pow_le_mono_r; lia.
  - change 32768 with (2 ^ 15). apply Z.pow_le_mono_r; lia.
Qed.

Lemma wk_window s x : win_keep (set_d_window s x) = win_keep s. Proof. destruct s; reflexivity. Qed.
Lemma wk_strstart s x : win_keep (set_d_strstart s x) = win_keep s. Proof. destruct s; reflexivity. Qed.
Lemma wk_block_start s x : win_keep (set_d_block_start s x) = win_keep s. Proof. destruct s; reflexivity. Qed.
Lemma wk_insert s x : win_keep (set_d_insert s x) = win_keep s. Proof. destruct s; reflexivity. Qed.
Lemma wk_high_water s x : win_keep (set_d_high_water s x) = win_keep s. Proof. destruct s; reflexivity. Qed.
Lemma wk_matches s x : win_keep (set_d_matches s x) = win_keep s. Proof. destruct s; reflexivity. Qed.

Lemma wk_incr s : win_keep (incr_matches s) = win_keep s.
Proof. unfold incr_matches. destruct (_ <? 2); [apply wk_matches|reflexivity]. Qed.
Lemma wk_clamp s : win_keep (clamp_insert s) = win_keep s.
Proof. unfold clamp_insert. destruct (_ >? _); [apply wk_insert|reflexivity]. Qed.
Lemma wk_add s n : win_keep (add_insert s n) = win_keep s.
Proof. unfold add_insert. apply wk_insert. Qed.
Lemma wk_hw s : win_keep (upd_high_water s) = win_keep s.
Proof. unfold upd_high_water. destruct (_ <? _); [apply wk_high_water|reflexivity]. Qed.

Lemma incr_pj x :
  d_strstart (incr_matches x) = d_strstart x /\ d_window (incr_matches x) = d_window x /\
  d_block_start (incr_matches x) = d_block_start x /\ d_insert (incr_matches x) = d_insert x /\
  d_high_water (incr_matches x) = d_high_water x /\
  d_matches (incr_matches x) = (if d_matches x <? 2 then u32 (d_matches x + 1) else d_matches x).
Proof. unfold incr_matches. destruct (d_matches x <? 2); repeat split; reflexivity. Qed.

Lemma clamp_pj x :
  d_strstart (clamp_insert x) = d_strstart x /\ d_window (clamp_insert x) = d_window x /\
  d_block_start (clamp_insert x) = d_block_start x /\
  d_insert (clamp_insert x) = (if d_insert x >? d_strstart x then d_strstart x else d_insert x) /\
  d_high_water (clamp_insert x) = d_high_water x /\ d_matches (clamp_insert x) = d_matches x.
Proof. unfold clamp_insert. destruct (d_insert x >? d_strstart x); repeat split; reflexivity. Qed.

Lemma hw_pj x :
  d_strstart (upd_high_water x) = d_strstart x /\ d_window (upd_high_water x) = d_window x /\
  d_block_start (upd_high_water x) = d_block_start x /\ d_insert (upd_high_water x) = d_insert x /\
  d_high_water (upd_high_water x) = Z.max (d_high_water x) (d_strstart x) /\
  d_matches (upd_high_water x) = d_matches x.
Proof.
  unfold upd_high_water. destruct (Z.ltb_spec (d_high_water x) (d_strstart x)); repeat split; cbn; lia.
Qed.

Lemma wk_tr s : d_tr (win_keep s) = set_matches (d_tr s) 0.
Proof. destruct s; reflexivity. Qed.

Lemma tree_ok_sm t m syms x : tree_ok (set_matches t x) m syms -> tree_ok t m syms.
Proof. destruct t. intros H. exact H. Qed.
Lemma tree_ok_sm' t m syms x : tree_ok t m syms -> tree_ok (set_matches t x) m syms.
Proof. destruct t. intros H. exact H. Qed.

Lemma wk_level s s' : win_keep s' = win_keep s -> d_level s' = d_level s.
Proof.
  intros H. pose proof (f_equal (fun x => tr_level (d_tr x)) H) as X. cbv beta in X.
  rewrite !wk_tr in X. exact X.
Qed.

(** ** W from its frame *)
Lemma W_frame s s' :
  W s -> d_level s = 0 -> win_keep s' = win_keep s ->
  Zlength (mb_val (d_window s')) = 2 * d_w_size s -> mb_ok (d_window s') ->
  0 <= d_block_start s' <= d_strstart s' -> d_strstart s' <= 2 * d_w_size s ->
  0 <= d_insert s' <= d_strstart s' -> d_insert s' <= d_w_size s ->
  0 <= d_high_water s' <= 2 * d_w_size s ->
  (forall i, 0 <= i < Z.max (d_strstart s') (d_high_water s') -> Znth i (mb_def (d_window s')) = true) ->
  whash s' -> W s'.
Proof.
  intros HW L0 Hk Hwl Hwok Hbs Hss Hi1 Hi2 Hhw Hdef Hh.
  destruct HW as (Hp & Hs & Hpos & Hwin & Hwh & Hm & Hl & syms & Ht).
  assert (Hp' : prm s') by (change (prm (win_keep s')); rewrite Hk; exact Hp).
  assert (E1 : d_w_size s' = d_w_size s) by exact (f_equal d_w_size Hk).
  assert (E2 : d_window_size s' = d_window_size s) by exact (f_equal d_window_size Hk).
  assert (E3 : d_prev s' = d_prev s) by exact (f_equal d_prev Hk).
  assert (E4 : d_head s' = d_head s) by exact (f_equal d_head Hk).
  assert (E5 : d_hash_size s' = d_hash_size s) by exact (f_equal d_hash_size Hk).
  assert (E6 : set_matches (d_tr s') 0 = set_matches (d_tr s) 0) by (rewrite <- !wk_tr, Hk; reflexivity).
  assert (E7 : d_pbm s' = d_pbm s) by exact (f_equal d_pbm Hk).
  assert (E8 : d_lookahead s' = d_lookahead s) by exact (f_equal d_lookahead Hk).
  assert (E9 : d_match_length s' = d_match_length s) by exact (f_equal d_match_length Hk).
  assert (E10 : d_prev_length s' = d_prev_length s) by exact (f_equal d_prev_length Hk).
  assert (E11 : d_match_available s' = d_match_available s) by exact (f_equal d_match_available Hk).
  assert (EL : d_level s' = d_level s).
  { pose proof (f_equal tr_level E6) as X. unfold set_matches in X. cbn [tr_level] in X. exact X. }
  assert (ELB : d_L s' = d_L s).
  { pose proof (f_equal tr_lit_bufsize E6) as X. unfold set_matches in X. cbn [tr_lit_bufsize] in X. exact X. }
  destruct (Hl L0) as [La Lb].
  destruct Hs as (Hs1 & Hs2 & Hs3 & Hs4 & Hs5).
  assert (MA : d_match_available s = 0).
  { destruct Hm as (_ & _ & [A|A] & _ & Hm5); [exact A|].
    destruct (Hm5 A) as [F _]. unfold fn_of in F. rewrite L0 in F. discriminate F. }
  split; [exact Hp'|]. split; [|split; [|split; [|split; [|split; [|split]]]]].
  - unfold wstruct. rewrite E1, E2, E3, E4, E5. split; [lia|]. split; [exact Hwok|]. split; [lia|].
    split; [exact Hs4|exact Hs5].
  - unfold wpos. rewrite E8, La, E2. pose proof (w_bounds s Hp). lia.
  - unfold wwin. rewrite E8, La, Z.add_0_r. exact Hdef.
  - exact Hh.
  - destruct Hm as (Hm1 & Hm2 & _ & Hm4 & _). unfold wmatch. rewrite E9, E10, E11, MA.
    split; [exact Hm1|]. split; [exact Hm2|]. split; [left; reflexivity|]. split; [intros _; exact (Hm4 MA)|].
    intros C; discriminate C.
  - intros _. rewrite E8. lia.
  - exists syms. destruct Ht as (T1 & T2 & T3 & T4 & T5). rewrite (T4 L0) in *.
    unfold wtrees. rewrite E7, EL, ELB. split.
    { apply (tree_ok_sm _ _ _ 0). rewrite E6. apply tree_ok_sm'. exact T1. }
    split; [exact T2|].
    split; [constructor|]. split; [intros _; reflexivity|]. intros C; contradiction.
Qed.

(** ** ds_fill2 in two pieces *)
Definition fill_slide (s : dstate) (z : strm) (have : Z) : option (dstate * Z) :=
    (if (z_avail_in z >? have) && (d_block_start s >=? d_w_size s) then
       let s := set_d_block_start s (d_block_start s - d_w_size s) in
       let s := set_d_strstart s (u32 (d_strstart s - d_w_size s)) in
       let* win := mb_move (d_window s) 0 (d_w_size s) (d_strstart s) in
       let s := set_d_window s win in
       let s := incr_matches s in
       let have := u32 (have + d_w_size s) in
       Some (clamp_insert s, have)
     else Some (s, have)).

Definition fill_read (s : dstate) (z : strm) (have : Z) : option (dstate * strm) :=
    (if have =? 0 then Some (s, z) else
     let* (z, data) := c_read_buf s z have in
     let* win := mb_write (d_window s) (d_strstart s) data in
     let s := set_d_window s win in
     let s := set_d_strstart s (u32 (d_strstart s + have)) in
     Some (add_insert s have, z)).

Lemma ds_fill2_eq {A : Type} s z (K : dstate -> strm -> option A) :
  ds_fill2 s z K =
  let* (s1, h1) := fill_slide s z (u32 (u64 (d_window_size s - d_strstart s))) in
  let* (s2, z2) := fill_read s1 z (if h1 >? z_avail_in z then z_avail_in z else h1) in
  K (upd_high_water s2) z2.
Proof. reflexivity. Qed.

Lemma whash0 s : d_level s = 0 -> whash s ->
  (d_matches s = 0 /\ chain_ok s) \/ (d_matches s = 1 /\ chain_ok (slide_hc s)) \/ d_matches s = 2.
Proof. intros L H. unfold whash in H. rewrite L, Z.eqb_refl in H. exact H. Qed.

Lemma whash0' s : d_level s = 0 ->
  (d_matches s = 0 /\ chain_ok s) \/ (d_matches s = 1 /\ chain_ok (slide_hc s)) \/ d_matches s = 2 -> whash s.
Proof. intros L H. unfold whash. rewrite L, Z.eqb_refl. exact H. Qed.

Lemma slide_ok s z have :
  chain_stmt -> W s -> d_level s = 0 -> have = 2 * d_w_size s - d_strstart s ->
  exists s1, fill_slide s z have = Some (s1, 2 * d_w_size s - d_strstart s1) /\
    W s1 /\ win_keep s1 = win_keep s /\ ub s1 = ub s /\ d_w_size s1 = d_w_size s.
Proof.
  intros [CH1 CH2] HW L0 Eh. pose proof HW as HW0.
  destruct HW0 as (Hp & Hs & Hpos & Hwin & Hwh & Hm & Hl & _).
  pose proof (w_bounds s Hp) as Wb. destruct (Hl L0) as [La Lb].
  destruct Hs as (Hs1 & Hs2 & Hs3 & Hs4 & Hs5).
  destruct Hpos as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
  unfold fill_slide.
  destruct ((z_avail_in z >? have) && (d_block_start s >=? d_w_size s)) eqn:C.
  2:{ exists s. rewrite Eh. split; [reflexivity|]. split; [exact HW|]. auto. }
  apply andb_true_iff in C. destruct C as [_ C]. apply Z.geb_le in C.
  cbv zeta.
  change (d_strstart (set_d_block_start s (d_block_start s - d_w_size s))) with (d_strstart s).
  change (d_w_size (set_d_block_start s (d_block_start s - d_w_size s))) with (d_w_size s).
  remember (set_d_strstart (set_d_block_start s (d_block_start s - d_w_size s))
              (u32 (d_strstart s - d_w_size s))) as sb eqn:Esb.
  assert (Sw : d_window sb = d_window s) by (subst sb; reflexivity).
  assert (Sws : d_w_size sb = d_w_size s) by (subst sb; reflexivity).
  assert (Sss : d_strstart sb = d_strstart s - d_w_size s)
    by (subst sb; apply u32_id'; lia).
  assert (Sbs : d_block_start sb = d_block_start s - d_w_size s) by (subst sb; reflexivity).
  assert (Sin : d_insert sb = d_insert s) by (subst sb; reflexivity).
  assert (Shw : d_high_water sb = d_high_water s) by (subst sb; reflexivity).
  assert (Sm : d_matches sb = d_matches s) by (subst sb; reflexivity).
  assert (Sk : win_keep sb = win_keep s) by (subst sb; rewrite wk_strstart, wk_block_start; reflexivity).
  rewrite Sw, Sws, Sss.
  destruct (mb_move_ok (d_window s) (d_w_size s) (d_strstart s - d_w_size s)) as (win & Em & M1 & M2 & M3 & M4);
    auto; try lia.
  { intros i Hi. apply Hwin. rewrite La, Z.add_0_r. lia. }
  rewrite Em. cbn [bind].
  set (s1 := clamp_insert (incr_matches (set_d_window sb win))).
  assert (Hk : win_keep s1 = win_keep s) by (unfold s1; rewrite wk_clamp, wk_incr, wk_window; exact Sk).
  assert (Ews : d_w_size s1 = d_w_size s) by exact (f_equal d_w_size Hk).
  destruct (incr_pj (set_d_window sb win)) as (I1 & I2 & I3 & I4 & I5 & I6).
  destruct (clamp_pj (incr_matches (set_d_window sb win))) as (C1 & C2 & C3 & C4 & C5 & C6).
  fold s1 in C1, C2, C3, C4, C5, C6.
  assert (Q1 : d_strstart s1 = d_strstart s - d_w_size s) by (rewrite C1, I1; exact Sss).
  assert (Q2 : d_window s1 = win) by (rewrite C2, I2; reflexivity).
  assert (Q3 : d_block_start s1 = d_block_start s - d_w_size s) by (rewrite C3, I3; exact Sbs).
  assert (Q4 : d_insert s1 = Z.min (d_insert s) (d_strstart s - d_w_size s)).
  { rewrite C4, I4, I1. change (d_insert (set_d_window sb win)) with (d_insert sb).
    change (d_strstart (set_d_window sb win)) with (d_strstart sb). rewrite Sin, Sss.
    destruct (Z.gtb_spec (d_insert s) (d_strstart s - d_w_size s)); lia. }
  assert (Q5 : d_high_water s1 = d_high_water s) by (rewrite C5, I5; exact Shw).
  assert (Q6 : d_matches s1 = if d_matches s <? 2 then u32 (d_matches s + 1) else d_matches s)
    by (rewrite C6, I6; change (d_matches (set_d_window sb win)) with (d_matches sb); rewrite Sm; reflexivity).
  exists s1.
  assert (Wi : d_w_size (incr_matches (set_d_window sb win)) = d_w_size sb)
    by exact (f_equal d_w_size (wk_incr (set_d_window sb win))).
  rewrite Wi, Sws, Eh, Q1.
  split; [rewrite u32_id' by lia; do 2 f_equal; lia|].
  assert (La1 : d_lookahead s1 = d_lookahead s) by exact (f_equal d_lookahead Hk).
  assert (Hub : ub s1 = ub s) by (unfold ub; rewrite Q1, Q3, La1; lia).
  split; [|split; [exact Hk|split; [exact Hub|exact Ews]]].
  apply (W_frame s s1 HW L0 Hk).
  - rewrite Q2, M1. exact Hs1.
  - rewrite Q2. exact M2.
  - rewrite Q3, Q1. lia.
  - rewrite Q1. lia.
  - rewrite Q4, Q1. lia.
  - rewrite Q4. lia.
  - rewrite Q5. lia.
  - intros i Hi. rewrite Q2. rewrite Q1, Q5 in Hi.
    destruct (Z_lt_le_dec i (d_strstart s - d_w_size s)).
    + apply M4. lia.
    + apply M3; [lia|]. apply Hwin. rewrite La, Z.add_0_r. lia.
  - apply whash0'; [rewrite (wk_level _ _ Hk); exact L0|].
    destruct (whash0 s L0 Hwh) as [[M0 Hc]|[[M0 Hc]|M0]].
    + right; left. split; [rewrite Q6, M0; reflexivity|].
      apply (CH2 s s1 Hp (conj Hs1 (conj Hs2 (conj Hs3 (conj Hs4 Hs5)))) Hc).
      * exact (f_equal d_head Hk).
      * exact (f_equal d_prev Hk).
      * exact Ews.
      * exact (f_equal d_w_mask Hk).
      * exact (f_equal d_hash_size Hk).
      * rewrite Q1. lia.
    + right; right. rewrite Q6, M0. reflexivity.
    + right; right. rewrite Q6, M0. reflexivity.
Qed.

Lemma whash_mono s s' :
  chain_stmt -> d_level s = 0 -> whash s -> win_keep s' = win_keep s -> d_matches s' = d_matches s ->
  d_strstart s <= d_strstart s' -> whash s'.
Proof.
  intros [CH1 _] L0 Hh Hk Hm Hss.
  assert (Eh : d_head s' = d_head s) by exact (f_equal d_head Hk).
  assert (Ep : d_prev s' = d_prev s) by exact (f_equal d_prev Hk).
  assert (Ew : d_w_size s' = d_w_size s) by exact (f_equal d_w_size Hk).
  assert (Em : d_w_mask s' = d_w_mask s) by exact (f_equal d_w_mask Hk).
  assert (Ehs : d_hash_size s' = d_hash_size s) by exact (f_equal d_hash_size Hk).
  apply whash0'; [rewrite (wk_level _ _ Hk); exact L0|]. rewrite Hm.
  destruct (whash0 s L0 Hh) as [[M0 Hc]|[[M0 Hc]|M0]].
  - left. split; [exact M0|]. apply (CH1 s s' Hc Eh Ep Ew Em Ehs Hss).
  - right; left. split; [exact M0|]. apply (CH1 (slide_hc s) (slide_hc s') Hc).
    + change (map (slide_entry (d_w_size s')) (d_head s') = map (slide_entry (d_w_size s)) (d_head s)).
      rewrite Ew, Eh. reflexivity.
    + change (map (slide_entry (d_w_size s')) (d_prev s') = map (slide_entry (d_w_size s)) (d_prev s)).
      rewrite Ew, Ep. reflexivity.
    + exact Ew.
    + exact Em.
    + exact Ehs.
    + exact Hss.
  - right; right. exact M0.
Qed.

Lemma read_ok s z k :
  chain_stmt -> W s -> d_level s = 0 -> zall z -> adler_ok (d_wrap s) (z_adler z) ->
  0 <= k <= z_avail_in z -> d_strstart s + k <= 2 * d_w_size s ->
  exists s2 z2, fill_read s z k = Some (s2, z2) /\ W (upd_high_water s2) /\
    win_keep (upd_high_water s2) = win_keep s /\ zstep (d_wrap s) z z2 k [] /\
    ub (upd_high_water s2) = ub s + k.
Proof.
  intros CH HW L0 Hz Ha Hk Hroom. pose proof HW as HW0.
  destruct HW0 as (Hp & Hs & Hpos & Hwin & Hwh & Hm & Hl & _).
  pose proof (w_bounds s Hp) as Wb. destruct (Hl L0) as [La Lb].
  destruct Hs as (Hs1 & Hs2 & Hs3 & Hs4 & Hs5).
  destruct Hpos as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
  unfold fill_read.
  destruct (Z.eqb_spec k 0) as [K0|K0].
  - subst k. exists s, z. split; [reflexivity|].
    destruct (hw_pj s) as (H1 & H2 & H3 & H4 & H5 & H6).
    split; [|split; [apply wk_hw|split; [apply zstep_refl; auto|]]].
    + apply (W_frame s (upd_high_water s) HW L0 (wk_hw s)); rewrite ?H1, ?H2, ?H3, ?H4, ?H5; try lia; auto.
      * intros i Hi. apply Hwin. rewrite La, Z.add_0_r. lia.
      * apply (whash_mono s _ CH L0 Hwh (wk_hw s) H6). lia.
    + unfold ub. rewrite H1, H3. rewrite (f_equal d_lookahead (wk_hw s) : d_lookahead (upd_high_water s) = d_lookahead s).
      lia.
  - cbv iota.
    destruct (read_buf_ok s z k Hz Ha ltac:(lia)) as (z2 & Er & Hzs & _).
    replace (Z.min k (z_avail_in z)) with k in * by lia. rewrite Er. cbn [bind].
    set (data := sublist (z_next_in z) (z_next_in z + k) (z_in z)).
    assert (Ld : Zlength data = k).
    { unfold data. destruct Hz as [(Hb & Hni & Hai & Hl' & Ht) _]. rewrite Zlength_sublist; lia. }
    assert (Bd : bytes data) by (apply bytes_sublist; destruct Hz as [(Hb & _) _]; exact Hb).
    destruct (mb_write_ok (d_window s) (d_strstart s) data Hs2 Bd P2 ltac:(lia)) as (win & Ew & W1 & W2 & W3 & W4).
    rewrite Ew. cbn [bind].
    change (d_strstart (set_d_window s win)) with (d_strstart s).
    rewrite (u32_id' (d_strstart s + k)) by lia.
    set (s2 := add_insert (set_d_strstart (set_d_window s win) (d_strstart s + k)) k).
    exists s2, z2. split; [reflexivity|].
    assert (Hk2 : win_keep (upd_high_water s2) = win_keep s)
      by (unfold s2; rewrite wk_hw, wk_add, wk_strstart, wk_window; reflexivity).
    destruct (hw_pj s2) as (H1 & H2 & H3 & H4 & H5 & H6).
    assert (R1 : d_strstart s2 = d_strstart s + k) by reflexivity.
    assert (R2 : d_window s2 = win) by reflexivity.
    assert (R3 : d_block_start s2 = d_block_start s) by reflexivity.
    assert (R4 : d_insert s2 = d_insert s + Z.min k (d_w_size s - d_insert s)).
    { change (d_insert s2) with
        (u32 (d_insert s + (if k >? u32 (d_w_size s - d_insert s) then u32 (d_w_size s - d_insert s) else k))).
      rewrite (u32_id' (d_w_size s - d_insert s)) by lia.
      destruct (Z.gtb_spec k (d_w_size s - d_insert s)); rewrite u32_id' by lia; lia. }
    assert (R5 : d_high_water s2 = d_high_water s) by reflexivity.
    assert (R6 : d_matches s2 = d_matches s) by reflexivity.
    assert (La2 : d_lookahead (upd_high_water s2) = d_lookahead s) by exact (f_equal d_lookahead Hk2).
    split; [|split; [exact Hk2|split; [exact Hzs|]]].
    + apply (W_frame s (upd_high_water s2) HW L0 Hk2); rewrite ?H1, ?H2, ?H3, ?H4, ?H5, ?R1, ?R2, ?R3, ?R4, ?R5;
        try lia; auto.
      * intros i Hi.
        destruct (Z_lt_le_dec i (d_strstart s)); [|destruct (Z_lt_le_dec i (d_strstart s + k))].
        -- apply W3; [lia|]. apply Hwin. rewrite La, Z.add_0_r. lia.
        -- apply W4. lia.
        -- apply W3; [lia|]. apply Hwin. rewrite La, Z.add_0_r. lia.
      * apply (whash_mono s _ CH L0 Hwh Hk2); [rewrite H6; exact R6|rewrite H1, R1; lia].
    + unfold ub. rewrite H1, H3, R1, R3, La2. lia.
Qed.

Theorem fill2_ok : chain_stmt -> fill2_stmt.
Proof.
  intros CH s z HW L0 Hz Ha.
  pose proof HW as HW0. destruct HW0 as (Hp & Hs & Hpos & _).
  pose proof (w_bounds s Hp) as Wb. destruct Hs as (_ & _ & Hs3 & _). destruct Hpos as (P1 & P2 & P3 & _).
  assert (Eh : u32 (u64 (d_window_size s - d_strstart s)) = 2 * d_w_size s - d_strstart s).
  { rewrite Hs3. rewrite u64_id by lia. apply u32_id'. lia. }
  destruct (slide_ok s z _ CH HW L0 Eh) as (s1 & Es & HW1 & Hk1 & Hu1 & Hw1).
  assert (L1 : d_level s1 = 0) by (rewrite (wk_level _ _ Hk1); exact L0).
  assert (Wr : d_wrap s1 = d_wrap s) by exact (f_equal d_wrap Hk1).
  pose proof HW1 as HW10. destruct HW10 as (_ & Hs' & Hpos' & _).
  destruct Hs' as (_ & _ & Hs3' & _). destruct Hpos' as (Q1 & Q2 & Q3 & _).
  destruct Hz as [Hzi Hzo]. pose proof Hzi as Hzi'. destruct Hzi' as (_ & _ & Hai & _).
  destruct (read_ok s1 z (if 2 * d_w_size s1 - d_strstart s1 >? z_avail_in z then z_avail_in z
                          else 2 * d_w_size s1 - d_strstart s1) CH HW1 L1 (conj Hzi Hzo))
    as (s2 & z2 & Er & HW2 & Hk2 & Hzs & Hu2).
  { rewrite Wr. exact Ha. }
  { destruct (Z.gtb_spec (2 * d_w_size s1 - d_strstart s1) (z_avail_in z)); lia. }
  { destruct (Z.gtb_spec (2 * d_w_size s1 - d_strstart s1) (z_avail_in z)); lia. }
  exists (upd_high_water s2), z2,
    (if 2 * d_w_size s1 - d_strstart s1 >? z_avail_in z then z_avail_in z else 2 * d_w_size s1 - d_strstart s1).
  split.
  { intros A K. rewrite ds_fill2_eq, Es. cbn [bind]. rewrite <- Hw1, Er. reflexivity. }
  split; [exact HW2|]. split; [rewrite Hk2; exact Hk1|]. split.
  - rewrite <- Wr. exact Hzs.
  - rewrite Hu2, Hu1. reflexivity.
Qed.
