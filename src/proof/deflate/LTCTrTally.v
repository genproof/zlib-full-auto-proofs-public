(** * TREES part, sub-part TALLY: see LTCTrKit.v for the statement and its purpose. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.zlist.list_solver.
Require Export Zlib.proof.deflate.LTCTrKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** List facts *)

Lemma tt_Znth_upd_any {A} {d : Inhabitant A} (l : list A) i j v :
  Znth i (upd_Znth j l v) = if (i =? j) && (0 <=? j) && (j <? Zlength l) then v else Znth i l.
Proof.
  destruct (Z.eqb_spec i j), (Z.leb_spec 0 j), (Z.ltb_spec j (Zlength l)); cbn [andb];
    try (rewrite upd_Znth_out_of_range by lia; reflexivity).
  - subst; apply upd_Znth_same; lia.
  - destruct (Z_le_gt_dec 0 i); [destruct (Z_lt_ge_dec i (Zlength l))|].
    + apply upd_Znth_diff; lia.
    + rewrite !Znth_overflow by (rewrite ?Zlength_upd_Znth_any; lia). reflexivity.
    + rewrite !Znth_underflow by lia. reflexivity.
Qed.

Lemma tt_sub3 {A} {d : Inhabitant A} (l : list A) lo a v0 v1 v2 :
  0 <= lo <= a -> a + 3 <= Zlength l ->
  sublist lo (a + 3) (upd_Znth (a + 2) (upd_Znth (a + 1) (upd_Znth a l v0) v1) v2) =
  sublist lo a l ++ [v0; v1; v2].
Proof. intros. list_solve. Qed.

Lemma tt_sym_bytes_app syms x : sym_bytes (syms ++ [x]) = sym_bytes syms ++ [fst x mod 256; fst x / 256; snd x].
Proof. unfold sym_bytes. rewrite map_app, concat_app. reflexivity. Qed.

Lemma tt_Zlength_filter {A} (f : A -> bool) l : Zlength (filter f l) <= Zlength l.
Proof.
  induction l as [|a l IH]; cbn [filter]; [lia|].
  destruct (f a); rewrite ?Zlength_cons; lia.
Qed.

Lemma tt_filter_app1 {A} (f : A -> bool) l x :
  Zlength (filter f (l ++ [x])) = Zlength (filter f l) + (if f x then 1 else 0).
Proof. rewrite filter_app, Zlength_app. cbn [filter]. destruct (f x); reflexivity. Qed.

Lemma tt_lfreq_app syms x c :
  lfreq (syms ++ [x]) c = lfreq syms c + (if lcode_of x =? c then 1 else 0).
Proof. unfold lfreq. rewrite tt_filter_app1. lia. Qed.

Lemma tt_dfreq_app syms x c :
  dfreq (syms ++ [x]) c = dfreq syms c + (if negb (fst x =? 0) && (d_code (fst x - 1) =? c) then 1 else 0).
Proof. unfold dfreq. rewrite tt_filter_app1. reflexivity. Qed.

Lemma tt_lfreq_le syms c : 0 <= lfreq syms c <= Zlength syms + 1.
Proof.
  unfold lfreq. pose proof (tt_Zlength_filter (fun s => lcode_of s =? c) syms).
  pose proof (Zlength_nonneg (filter (fun s => lcode_of s =? c) syms)). destruct (c =? END_BLOCK); lia.
Qed.

Lemma tt_dfreq_le syms c : 0 <= dfreq syms c <= Zlength syms.
Proof.
  unfold dfreq. match goal with |- context [filter ?f syms] =>
    pose proof (tt_Zlength_filter f syms); pose proof (Zlength_nonneg (filter f syms)) end. lia.
Qed.

(** ** Table facts *)

Lemma tt_length_code_tab : Zlength length_code_tab = 256 /\ Forall (fun x => 0 <= x < 29) length_code_tab.
Proof. split; [reflexivity|]. vm_compute. repeat constructor; discriminate. Qed.

Lemma tt_dist_code_tab : Zlength dist_code_tab = 512 /\ Forall (fun x => 0 <= x < 30) dist_code_tab.
Proof. split; [reflexivity|]. vm_compute. repeat constructor; discriminate. Qed.

(** ** The frequency components of tree_ok *)

Definition tt_lok (lt : tree) (syms : list (Z * Z)) : Prop :=
  Zlength (fc lt) = HEAP_SIZE /\ Zlength (dl lt) = HEAP_SIZE /\
  (forall n, 0 <= n < HEAP_SIZE -> 0 <= Znth n (fc lt) < 65536) /\
  forall c, 0 <= c < L_CODES -> Znth c (fc lt) = lfreq syms c.

Definition tt_dok (dt : tree) (syms : list (Z * Z)) : Prop :=
  Zlength (fc dt) = 2 * D_CODES + 1 /\ Zlength (dl dt) = 2 * D_CODES + 1 /\
  (forall n, 0 <= n < 2 * D_CODES + 1 -> 0 <= Znth n (fc dt) < 65536) /\
  forall c, 0 <= c < D_CODES -> Znth c (fc dt) = dfreq syms c.

Lemma tt_incr_l lt syms x i :
  tt_lok lt syms -> Zlength syms <= 32766 -> i = lcode_of x -> 0 <= i < HEAP_SIZE ->
  tt_lok (mkTree (upd_Znth i (fc lt) (u16 (Znth i (fc lt) + 1))) (dl lt)) (syms ++ [x]).
Proof.
  intros (H1 & H2 & H3 & H4) Hn -> Hi. unfold tt_lok. cbn [fc dl].
  split; [rewrite Zlength_upd_Znth_any; auto|]. split; [auto|]. split.
  - intros n Hn'. rewrite tt_Znth_upd_any.
    destruct (_ && _ && _); [unfold u16; apply Z.mod_pos_bound; lia | auto].
  - intros c Hc. rewrite tt_Znth_upd_any, tt_lfreq_app, H1.
    destruct (Z.eqb_spec c (lcode_of x)) as [->|Hne].
    + rewrite Z.eqb_refl, (proj2 (Z.leb_le _ _)), (proj2 (Z.ltb_lt _ _)) by lia. cbn [andb].
      rewrite H4 by lia. pose proof (tt_lfreq_le syms (lcode_of x)).
      unfold u16. rewrite Z.mod_small by lia. lia.
    + rewrite (proj2 (Z.eqb_neq _ _)) by auto. cbn [andb].
      try rewrite (proj2 (Z.eqb_neq (lcode_of x) c)) by auto. rewrite H4 by lia. lia.
Qed.

Lemma tt_incr_d dt syms x i :
  tt_dok dt syms -> Zlength syms <= 32766 -> fst x <> 0 -> i = d_code (fst x - 1) -> 0 <= i < D_CODES ->
  tt_dok (mkTree (upd_Znth i (fc dt) (u16 (Znth i (fc dt) + 1))) (dl dt)) (syms ++ [x]).
Proof.
  intros (H1 & H2 & H3 & H4) Hn Hx -> Hi. unfold tt_dok. cbn [fc dl].
  split; [rewrite Zlength_upd_Znth_any; auto|]. split; [auto|]. split.
  - intros n Hn'. rewrite tt_Znth_upd_any.
    destruct (_ && _ && _); [unfold u16; apply Z.mod_pos_bound; lia | auto].
  - intros c Hc. rewrite tt_Znth_upd_any, tt_dfreq_app, H1.
    rewrite (proj2 (Z.eqb_neq (fst x) 0)) by auto. cbn [negb].
    destruct (Z.eqb_spec c (d_code (fst x - 1))) as [->|Hne].
    + rewrite Z.eqb_refl, (proj2 (Z.leb_le _ _)), (proj2 (Z.ltb_lt _ _)) by (unfold D_CODES in *; lia).
      cbn [andb].
      rewrite H4 by lia. pose proof (tt_dfreq_le syms (d_code (fst x - 1))).
      unfold u16. rewrite Z.mod_small by lia. lia.
    + rewrite (proj2 (Z.eqb_neq _ _)) by auto. cbn [andb].
      try rewrite (proj2 (Z.eqb_neq (d_code (fst x - 1)) c)) by auto. rewrite H4 by lia. lia.
Qed.

Lemma tt_dfreq_lit syms x c : fst x = 0 -> dfreq (syms ++ [x]) c = dfreq syms c.
Proof. intros H. rewrite tt_dfreq_app, H. cbn. lia. Qed.

Lemma tt_lfreq_nolit syms x c : lcode_of x <> c -> lfreq (syms ++ [x]) c = lfreq syms c.
Proof. intros H. rewrite tt_lfreq_app, (proj2 (Z.eqb_neq _ _)) by auto. lia. Qed.

(** ** The three stores and the state afterwards *)

Definition tt_upd3 {A} (l : list A) (a : Z) (v0 v1 v2 : A) : list A :=
  upd_Znth (a + 2) (upd_Znth (a + 1) (upd_Znth a l v0) v1) v2.

Lemma tt_upd3_Zlength {A} (l : list A) a v0 v1 v2 : Zlength (tt_upd3 l a v0 v1 v2) = Zlength l.
Proof. unfold tt_upd3. rewrite !Zlength_upd_Znth_any. reflexivity. Qed.

Lemma tt_upd3_Znth {A} {d : Inhabitant A} (l : list A) a v0 v1 v2 i :
  0 <= a -> a + 3 <= Zlength l ->
  Znth i (tt_upd3 l a v0 v1 v2) =
  if i =? a + 2 then v2 else if i =? a + 1 then v1 else if i =? a then v0 else Znth i l.
Proof.
  intros. unfold tt_upd3. rewrite !tt_Znth_upd_any, !Zlength_upd_Znth_any.
  destruct (Z.eqb_spec i (a + 2)), (Z.eqb_spec i (a + 1)), (Z.eqb_spec i a);
    rewrite ?(proj2 (Z.leb_le _ _)), ?(proj2 (Z.ltb_lt _ _)) by lia; cbn [andb]; auto; lia.
Qed.

Lemma tt_post t m syms x t' m' :
  tree_ok t m syms -> Zlength syms <= tr_lit_bufsize t - 2 -> valid_sym (fst x) (snd x) ->
  tt_lok (tr_ltree t') (syms ++ [x]) -> tt_dok (tr_dtree t') (syms ++ [x]) ->
  tr_bltree t' = tr_bltree t -> tr_wk t' = tr_wk t ->
  tr_lit_bufsize t' = tr_lit_bufsize t -> tr_sym_end t' = tr_sym_end t ->
  tr_level t' = tr_level t -> tr_strategy t' = tr_strategy t -> tr_matches t' = tr_matches t ->
  tr_sym_next t' = 3 * Zlength syms + 3 ->
  o_pending (tr_out t') = o_pending (tr_out t) -> o_bi_buf (tr_out t') = o_bi_buf (tr_out t) ->
  o_bi_valid (tr_out t') = o_bi_valid (tr_out t) -> o_bi_used (tr_out t') = o_bi_used (tr_out t) ->
  o_buf (tr_out t') = tt_upd3 (o_buf (tr_out t)) (tr_lit_bufsize t + 3 * Zlength syms)
                        (fst x mod 256) (fst x / 256) (snd x) ->
  m' = tt_upd3 m (tr_lit_bufsize t + 3 * Zlength syms) true true true ->
  tree_ok t' m' (syms ++ [x]) /\ tally_frame t m t' m'.
Proof.
  intros (Hb & Hm & Hk & Hv & Hs & Hsm & Hl & Hd & Hbl & Hw) Hn Hx Hl' Hd' Ebl Ew EL Ee Elv Est Emt Ek
    Ep Ebb Ebv Ebu Ebuf Em.
  set (L := tr_lit_bufsize t) in *. set (n := Zlength syms) in *.
  assert (0 <= n) by apply Zlength_nonneg.
  assert (Hlen : Zlength (syms ++ [x]) = n + 1) by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  assert (Ha : L + 3 * n + 3 <= Zlength (o_buf (tr_out t))) by lia.
  split.
  - unfold tree_ok. rewrite EL, Ebuf, Em, Hlen, Ek, Ebl, Ew. fold L.
    rewrite !tt_upd3_Zlength. unfold tt_lok, tt_dok in *.
    split; [lia|]. split; [lia|]. split; [lia|]. split.
    { intros y Hy. apply in_app_or in Hy as [Hy|[<-|[]]]; auto. }
    split.
    { replace (L + 3 * (n + 1)) with (L + 3 * n + 3) by lia. unfold tt_upd3.
      rewrite tt_sub3 by lia. fold n. rewrite Hs, tt_sym_bytes_app. reflexivity. }
    split.
    { replace (L + 3 * (n + 1)) with (L + 3 * n + 3) by lia. unfold tt_upd3.
      rewrite tt_sub3 by lia. fold n. rewrite Hsm.
      replace (Z.to_nat (3 * (n + 1))) with (Z.to_nat (3 * n) + 3)%nat by lia.
      rewrite repeat_app. reflexivity. }
    split; [exact Hl'|]. split; [exact Hd'|]. split; [exact Hbl|]. exact Hw.
  - unfold tally_frame, tr_cfg, pb_grow. rewrite EL, Ee, Elv, Est, Emt, Ep, Ebb, Ebv, Ebu, Ebuf, Em. fold L.
    rewrite !tt_upd3_Zlength.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split.
    + intros i Hi. rewrite tt_upd3_Znth by lia.
      destruct (i =? _); [reflexivity|]. destruct (i =? _); [reflexivity|]. destruct (i =? _); auto.
    + unfold mb_ok. cbn [mb_def mb_val]. rewrite !tt_upd3_Zlength. intros [E1 E2]. split; [exact E1|].
      intros i Hi Hdef. rewrite tt_upd3_Znth in Hdef by lia. rewrite tt_upd3_Znth by lia.
      destruct Hx as [Hx1 Hx2].
      destruct (i =? _); [lia|]. destruct (i =? _).
      { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
      destruct (i =? _); [apply Z.mod_pos_bound; lia|]. auto.
Qed.

(** ** Equations of the checked steps *)

Lemma tt_put_sym s m b i :
  i = tr_lit_bufsize s + tr_sym_next s -> 0 <= i < Zlength (o_buf (tr_out s)) ->
  c_put_sym (s, m) b =
  Some (set_sym_next (set_out s (mkOut (upd_Znth i (o_buf (tr_out s)) (u8 b)) (o_pending (tr_out s))
                                   (o_bi_buf (tr_out s)) (o_bi_valid (tr_out s)) (o_bi_used (tr_out s))))
                     (tr_sym_next s + 1),
        upd_Znth i m true).
Proof.
  intros -> Hi. unfold c_put_sym, wr, in_range.
  rewrite (proj2 (Z.leb_le _ _)), (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

Lemma tt_incr_lfreq s i :
  0 <= i < Zlength (fc (tr_ltree s)) ->
  c_incr_lfreq s i =
  Some (set_ltree s (mkTree (upd_Znth i (fc (tr_ltree s)) (u16 (Znth i (fc (tr_ltree s)) + 1)))
                            (dl (tr_ltree s)))).
Proof.
  intros Hi. unfold c_incr_lfreq, c_set_fc, rd, wr, in_range.
  rewrite (proj2 (Z.leb_le _ _)), (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

Lemma tt_incr_dfreq s i :
  0 <= i < Zlength (fc (tr_dtree s)) ->
  c_incr_dfreq s i =
  Some (set_dtree s (mkTree (upd_Znth i (fc (tr_dtree s)) (u16 (Znth i (fc (tr_dtree s)) + 1)))
                            (dl (tr_dtree s)))).
Proof.
  intros Hi. unfold c_incr_dfreq, c_set_fc, rd, wr, in_range.
  rewrite (proj2 (Z.leb_le _ _)), (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

Lemma tt_rd_length_code lc : 0 <= lc < 256 ->
  rd length_code_tab lc = Some (Znth lc length_code_tab) /\ 0 <= Znth lc length_code_tab < 29.
Proof.
  intros H. destruct tt_length_code_tab as [E F]. split.
  - unfold rd, in_range. rewrite E, (proj2 (Z.leb_le _ _)), (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
  - rewrite Forall_forall in F. apply F, Znth_In. lia.
Qed.

Lemma tt_d_code d : 0 <= d < 32768 -> c_d_code d = Some (d_code d) /\ 0 <= d_code d < 30.
Proof.
  intros H. destruct tt_dist_code_tab as [E F]. rewrite Forall_forall in F.
  assert (Hs : 0 <= Z.shiftr d 7 < 256).
  { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 7) with 128. split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia. }
  unfold c_d_code, d_code, rd, in_range. rewrite E.
  destruct (Z.ltb_spec d 256).
  - rewrite (proj2 (Z.leb_le _ _)), (proj2 (Z.ltb_lt _ _)) by lia. split; [reflexivity|]. apply F, Znth_In; lia.
  - rewrite (proj2 (Z.leb_le _ _)), (proj2 (Z.ltb_lt _ _)) by lia. split; [reflexivity|]. apply F, Znth_In; lia.
Qed.

Ltac tt_simp := cbn [set_ltree set_dtree set_sym_next set_out tr_ltree tr_dtree tr_bltree tr_lmax tr_dmax tr_blmax
  tr_wk tr_out tr_sym_next tr_sym_end tr_matches tr_lit_bufsize tr_level tr_strategy tr_data_type
  o_buf o_pending o_bi_buf o_bi_valid o_bi_used fc dl fst snd] in *.

Theorem tally_some : tally_statement.
Proof.
  split.
  - intros t m syms c Hok Hn HL Hc.
    pose proof Hok as (Hb & Hm & Hk & _ & _ & _ & Hl & Hd & _).
    set (n := Zlength syms) in *. assert (0 <= n) by apply Zlength_nonneg.
    unfold c_tr_tally_lit at 1.
    rewrite (tt_put_sym t m 0 (tr_lit_bufsize t + 3 * n)) by lia. cbn [bind].
    rewrite (tt_put_sym _ _ 0 (tr_lit_bufsize t + 3 * n + 1))
      by (tt_simp; rewrite ?Zlength_upd_Znth_any; lia).
    cbn [bind].
    rewrite (tt_put_sym _ _ (u8 c) (tr_lit_bufsize t + 3 * n + 2))
      by (tt_simp; rewrite ?Zlength_upd_Znth_any; lia).
    cbn [bind].
    rewrite tt_incr_lfreq by (tt_simp; unfold u8; rewrite Z.mod_small by lia; destruct Hl as [-> _]; unfold HEAP_SIZE, L_CODES; lia).
    cbn [bind].
    match goal with |- exists _ _, Some ((?T, ?M), ?F) = _ /\ _ => exists T, M end.
    split.
    { f_equal. f_equal. tt_simp. rewrite Hk. f_equal. lia. }
    assert (Hu : u8 c = c) by (unfold u8; apply Z.mod_small; lia).
    apply (tt_post t m syms (0, c)); tt_simp; try reflexivity.
    + exact Hok.
    + lia.
    + split; cbn [fst snd]; lia.
    + rewrite Hu. apply tt_incr_l; [exact Hl | lia | reflexivity | unfold HEAP_SIZE, L_CODES in *; lia].
    + destruct Hd as (D1 & D2 & D3 & D4). split; [auto|]. split; [auto|]. split; [auto|].
      intros c0 Hc0. rewrite tt_dfreq_lit by reflexivity. auto.
    + lia.
    + rewrite !Hu. unfold tt_upd3. reflexivity.
  - intros t m syms dist len Hok Hn HL Hdist Hlen.
    pose proof Hok as (Hb & Hm & Hk & _ & _ & _ & Hl & Hd & _).
    set (n := Zlength syms) in *. assert (0 <= n) by apply Zlength_nonneg.
    assert (Hul : u8 len = len) by (unfold u8; apply Z.mod_small; lia).
    assert (Hud : u16 dist = dist) by (unfold u16; apply Z.mod_small; lia).
    assert (Hud1 : u16 (dist - 1) = dist - 1) by (unfold u16; apply Z.mod_small; lia).
    assert (Hsh : u8 (Z.shiftr dist 8) = dist / 256).
    { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. unfold u8. apply Z.mod_small.
      split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia. }
    destruct (tt_rd_length_code len ltac:(lia)) as [Rl Rl'].
    destruct (tt_d_code (dist - 1) ltac:(lia)) as [Rd Rd'].
    unfold c_tr_tally_dist at 1. rewrite Hul, Hud, Hud1.
    rewrite (tt_put_sym t m dist (tr_lit_bufsize t + 3 * n)) by lia. cbn [bind].
    rewrite (tt_put_sym _ _ (Z.shiftr dist 8) (tr_lit_bufsize t + 3 * n + 1))
      by (tt_simp; rewrite ?Zlength_upd_Znth_any; lia).
    cbn [bind].
    rewrite (tt_put_sym _ _ len (tr_lit_bufsize t + 3 * n + 2))
      by (tt_simp; rewrite ?Zlength_upd_Znth_any; lia).
    cbn [bind]. rewrite Rl. cbn [bind].
    rewrite tt_incr_lfreq by (tt_simp; destruct Hl as [-> _]; unfold HEAP_SIZE, LITERALS in *; lia).
    cbn [bind]. rewrite Rd. cbn [bind].
    rewrite tt_incr_dfreq by (tt_simp; destruct Hd as [-> _]; unfold D_CODES in *; lia).
    cbn [bind].
    match goal with |- exists _ _, Some ((?T, ?M), ?F) = _ /\ _ => exists T, M end.
    split.
    { f_equal. f_equal. tt_simp. rewrite Hk. f_equal. lia. }
    apply (tt_post t m syms (dist, len)); tt_simp; try reflexivity.
    + exact Hok.
    + lia.
    + split; cbn [fst snd]; lia.
    + apply tt_incr_l; [exact Hl | lia | | unfold HEAP_SIZE, LITERALS in *; lia].
      unfold lcode_of. cbn [fst snd]. rewrite (proj2 (Z.eqb_neq dist 0)) by lia. reflexivity.
    + apply tt_incr_d; [exact Hd | lia | cbn [fst]; lia | reflexivity | unfold D_CODES; lia].
    + lia.
    + rewrite Hsh, Hul. unfold tt_upd3. reflexivity.
Qed.
