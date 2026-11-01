(** * Body proof of deflateBound_z.  The proof uses the byte fact of [opt_obj]
    (v6: [!! Forall (fun x => 0 <= x < 256) b &&] in the [Some b] case) through [opt_obj_bytes]. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.deflate.DModel3 Zlib.proof.deflate.DSpec Zlib.proof.deflate.DCS.
Require Import Zlib.deflate.code.
Require Import Zlib.proof.deflate.ApiKit.

(** The model's loops run with [loop FUEL] (2^40): keep the kernel from unfolding them at Qed. *)
Local Strategy opaque [loop loop2].

(** ** u64 arithmetic *)
Lemma bz_UMAX64 : Int64.repr UMAX64 = Int64.repr (-1).
Proof. apply Int64.eqm_samerepr. exists 1. reflexivity. Qed.

Lemma bz_repr_u64 x : Int64.repr (u64 x) = Int64.repr x.
Proof. unfold u64. change 18446744073709551616 with Int64.modulus. rewrite <- Int64.unsigned_repr_eq, Int64.repr_unsigned. reflexivity. Qed.

Lemma bz_shr n k : 0 <= n <= Int64.max_unsigned -> 0 <= k < 64 ->
  Int64.shru (Int64.repr n) (Int64.repr (Int.unsigned (Int.repr k))) = Int64.repr (Z.shiftr n k).
Proof.
  intros. rewrite Int.unsigned_repr by rep_lia. unfold Int64.shru. rewrite !Int64.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma bz_sum5 n a b c k : u64_ok n -> 0 <= a < 64 -> 0 <= b < 64 -> 0 <= c < 64 -> 0 <= k <= 100 ->
  Int64.add (Int64.add (Int64.add (Int64.add (Int64.repr n)
     (Int64.shru (Int64.repr n) (Int64.repr (Int.unsigned (Int.repr a)))))
     (Int64.shru (Int64.repr n) (Int64.repr (Int.unsigned (Int.repr b)))))
     (Int64.shru (Int64.repr n) (Int64.repr (Int.unsigned (Int.repr c)))))
     (Int64.repr (Int.signed (Int.repr k)))
  = Int64.repr (u64 (n + Z.shiftr n a + Z.shiftr n b + Z.shiftr n c + k)).
Proof.
  unfold u64_ok; intros. rewrite !bz_shr by lia. rewrite Int.signed_repr by rep_lia. rewrite !add64_repr.
  rewrite bz_repr_u64. reflexivity.
Qed.

Lemma bz_ltu a b : 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr a) (Int64.repr b) = true -> a < b.
Proof. intros. unfold Int64.ltu in *. rewrite !Int64.unsigned_repr in * by lia. destruct (zlt a b); [lia|discriminate]. Qed.
Lemma bz_nltu a b : 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr a) (Int64.repr b) = false -> a >= b.
Proof. intros. unfold Int64.ltu in *. rewrite !Int64.unsigned_repr in * by lia. destruct (zlt a b); [discriminate|lia]. Qed.

Definition bz_fixed (n : Z) : Z :=
  let f := u64 (n + Z.shiftr n 3 + Z.shiftr n 8 + Z.shiftr n 9 + 4) in if f <? n then UMAX64 else f.
Definition bz_store (n : Z) : Z :=
  let f := u64 (n + Z.shiftr n 5 + Z.shiftr n 7 + Z.shiftr n 11 + 7) in if f <? n then UMAX64 else f.

Lemma bz_fixed_range n : 0 <= bz_fixed n <= Int64.max_unsigned.
Proof. unfold bz_fixed. destruct (_ <? _); [unfold UMAX64; rep_lia | apply u64_range]. Qed.
Lemma bz_store_range n : 0 <= bz_store n <= Int64.max_unsigned.
Proof. unfold bz_store. destruct (_ <? _); [unfold UMAX64; rep_lia | apply u64_range]. Qed.

Definition bz_max (fl sl : Z) : Z := if fl >? sl then fl else sl.
Definition bz_add (b w : Z) : Z := if u64 (b + w) <? b then UMAX64 else u64 (b + w).

Lemma bz_none n : c_deflateBound_z None n = Some (bz_add (bz_max (bz_fixed n) (bz_store n)) 18).
Proof. reflexivity. Qed.
Lemma bz_bad s n : bad_state s = true ->
  c_deflateBound_z (Some s) n = Some (bz_add (bz_max (bz_fixed n) (bz_store n)) 18).
Proof. intros E. unfold c_deflateBound_z. rewrite E. reflexivity. Qed.

Lemma bz_add_range b w : 0 <= bz_add b w <= Int64.max_unsigned.
Proof. unfold bz_add. destruct (_ <? _); [unfold UMAX64; rep_lia | apply u64_range]. Qed.
Lemma bz_max_range n : 0 <= bz_max (bz_fixed n) (bz_store n) <= Int64.max_unsigned.
Proof. unfold bz_max. pose proof (bz_fixed_range n). pose proof (bz_store_range n). destruct (_ >? _); lia. Qed.

Lemma bz_add_lt b w : 0 <= b <= Int64.max_unsigned ->
  Int64.unsigned (Int64.repr (b + w)) < Int64.unsigned (Int64.repr b) -> vl (bz_add b w) = Vlong (Int64.repr (-1)).
Proof.
  intros Hb L. rewrite Int64.unsigned_repr_eq, (Int64.unsigned_repr b) in L by lia.
  unfold bz_add, u64. change 18446744073709551616 with Int64.modulus.
  rewrite (proj2 (Z.ltb_lt _ _) L). unfold vl. rewrite bz_UMAX64. reflexivity.
Qed.
Lemma bz_add_ge b w : 0 <= b <= Int64.max_unsigned ->
  Int64.unsigned (Int64.repr (b + w)) >= Int64.unsigned (Int64.repr b) -> vl (bz_add b w) = Vlong (Int64.repr (b + w)).
Proof.
  intros Hb L. rewrite Int64.unsigned_repr_eq, (Int64.unsigned_repr b) in L by lia.
  unfold bz_add. unfold u64 at 1. change 18446744073709551616 with Int64.modulus.
  destruct (_ <? _) eqn:E; [apply Z.ltb_lt in E; lia|]. unfold vl. rewrite bz_repr_u64. reflexivity.
Qed.

Lemma bz_add_lt' b w : 0 <= b <= Int64.max_unsigned ->
  Int64.ltu (Int64.add (Int64.repr b) (Int64.repr w)) (Int64.repr b) = true -> vl (bz_add b w) = Vlong (Int64.repr (-1)).
Proof.
  intros Hb L. apply bz_add_lt; auto. unfold Int64.ltu in L. rewrite add64_repr in L.
  destruct (zlt _ _); [auto|discriminate].
Qed.
Lemma bz_add_ge' b w : 0 <= b <= Int64.max_unsigned ->
  Int64.ltu (Int64.add (Int64.repr b) (Int64.repr w)) (Int64.repr b) = false ->
  vl (bz_add b w) = Vlong (Int64.add (Int64.repr b) (Int64.repr w)).
Proof.
  intros Hb L. rewrite add64_repr. apply bz_add_ge; auto. unfold Int64.ltu in L. rewrite add64_repr in L.
  destruct (zlt _ _); [discriminate|lia].
Qed.

Lemma bz_add_lt'' b w : 0 <= b <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr (b + w)) (Int64.repr b) = true -> vl (bz_add b w) = Vlong (Int64.repr (-1)).
Proof. intros Hb L. apply bz_add_lt; auto. unfold Int64.ltu in L. destruct (zlt _ _); [auto|discriminate]. Qed.
Lemma bz_add_ge'' b w : 0 <= b <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr (b + w)) (Int64.repr b) = false -> vl (bz_add b w) = Vlong (Int64.repr (b + w)).
Proof. intros Hb L. apply bz_add_ge; auto. unfold Int64.ltu in L. destruct (zlt _ _); [discriminate|lia]. Qed.

Ltac bz_addt := rewrite ?add64_repr in *;
  first [ solve [apply bz_add_lt; auto] | solve [apply bz_add_ge; auto]
        | solve [apply bz_add_lt''; auto] | solve [apply bz_add_ge''; auto] ].

(** The live-state path of the model, cut at the switch. *)
Definition bz_w (s : dstate) : option Z :=
  if d_wrap s <? 0 then let* _ := guard (in_int (- d_wrap s)) in Some (- d_wrap s) else Some (d_wrap s).

Definition bz_wlen (s : dstate) (w : Z) : option Z :=
  if w =? 0 then Some 0
  else if w =? 1 then Some (6 + (if d_strstart s =? 0 then 0 else 4))
  else if w =? 2 then
    match d_gzhead s with
    | None => Some 18
    | Some h =>
      let wl := 18 in
      let wl := match gz_extra h with
                | Some _ => u64 (wl + u32 (2 + gz_extra_len h))
                | None => wl end in
      let* wl := c_count_str (gz_name h) wl in
      let* wl := c_count_str (gz_comment h) wl in
      Some (if gz_hcrc h =? 0 then wl else u64 (wl + 2))
    end
  else Some 18.

Definition bz_tight (n wraplen : Z) : Z :=
  let bound := u64 (n + Z.shiftr n 12 + Z.shiftr n 14 + Z.shiftr n 25 + 13 - 6 + wraplen) in
  if bound <? n then UMAX64 else bound.

Definition bz_final (s : dstate) (n wraplen : Z) : Z :=
  if (negb (d_w_bits s =? 15) || negb (d_hash_bits s =? 8 + 7) ||
     ((d_strategy s =? Z_FIXED) && (d_level s >=? 1) && (d_level s <=? 3)))%bool then
    bz_add (if ((d_w_bits s <=? d_hash_bits s) && negb (d_level s =? 0))%bool then bz_fixed n else bz_store n) wraplen
  else bz_tight n wraplen.

Lemma bz_good s n : bad_state s = false ->
  c_deflateBound_z (Some s) n = let* w := bz_w s in let* wl := bz_wlen s w in Some (bz_final s n wl).
Proof.
  intros E. unfold c_deflateBound_z. rewrite E. unfold bz_w.
  destruct (d_wrap s <? 0); [destruct (in_int (- d_wrap s))|]; cbn [bind guard]; try reflexivity;
  (destruct (bz_wlen s _) eqn:W; unfold bz_wlen in W; rewrite W; cbn [bind];
   [unfold bz_final, bz_add, bz_tight, bz_fixed, bz_store; destruct (_ || _)%bool; reflexivity | reflexivity]).
Qed.

Lemma bz_w_ok s w : s32_ok (d_wrap s) -> bz_w s = Some w ->
  s32_ok w /\ w = (if d_wrap s <? 0 then - d_wrap s else d_wrap s) /\ (d_wrap s < 0 -> Int.min_signed < d_wrap s).
Proof.
  unfold bz_w, s32_ok. intros R. destruct (Z.ltb_spec (d_wrap s) 0).
  - destruct (in_int (- d_wrap s)) eqn:E; cbn [bind guard]; intros W; inv W. unfold in_int in E. apply andb_true_iff in E.
    destruct E as [E1 E2]; apply Z.leb_le in E1; apply Z.leb_le in E2. rep_lia.
  - intros W; inv W. rep_lia.
Qed.

Lemma bz_wlen_0 s wl : bz_wlen s 0 = Some wl -> wl = 0.
Proof. unfold bz_wlen. intros H; inv H; auto. Qed.
Lemma bz_wlen_1 s wl : bz_wlen s 1 = Some wl -> wl = 6 + (if d_strstart s =? 0 then 0 else 4).
Proof. unfold bz_wlen. intros H; inv H; auto. Qed.
Lemma bz_wlen_d s w wl : w <> 0 -> w <> 1 -> w <> 2 -> bz_wlen s w = Some wl -> wl = 18.
Proof.
  unfold bz_wlen. intros. rewrite (proj2 (Z.eqb_neq _ _) H), (proj2 (Z.eqb_neq _ _) H0), (proj2 (Z.eqb_neq _ _) H1) in H2.
  inv H2; auto.
Qed.

(** ** Taking the fields deflateBound_z reads out of the groups of the state (with a wand giving the group back) *)
Lemma bz_extract (P R F : mpred) : (P |-- R * F) -> (R * F |-- P) -> P |-- R * (R -* P).
Proof.
  intros H1 H2. eapply derives_trans; [exact H1|]. apply sepcon_derives; [auto|].
  apply wand_sepcon_adjoint. rewrite sepcon_comm. exact H2.
Qed.

Lemma bz_stat s p : stat_at s p |--
  (@field_at DCS.CS Ews t_ds (DOT _wrap) (vi (d_wrap s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _gzhead) (p_gzhead p) (p_s p)) *
  ((@field_at DCS.CS Ews t_ds (DOT _wrap) (vi (d_wrap s)) (p_s p) *
    @field_at DCS.CS Ews t_ds (DOT _gzhead) (p_gzhead p) (p_s p)) -* stat_at s p).
Proof.
  apply bz_extract with (F :=
   (@field_at DCS.CS Ews t_ds (DOT _status) (vi (d_status s)) (p_s p) *
    @field_at DCS.CS Ews t_ds (DOT _pending_buf_size) (vl (d_pending_buf_size s)) (p_s p) *
    @field_at DCS.CS Ews t_ds (DOT _pending_out) (offset_val (d_po s) (p_pbuf p)) (p_s p) *
    @field_at DCS.CS Ews t_ds (DOT _gzindex) (vl (d_gzindex s)) (p_s p) *
    @field_at DCS.CS Ews t_ds (DOT _method) (vi (d_method s)) (p_s p) *
    @field_at DCS.CS Ews t_ds (DOT _last_flush) (vi (d_last_flush s)) (p_s p))%logic);
  unfold stat_at; cancel.
Qed.

Lemma bz_match s p : match_at s p |--
  @field_at DCS.CS Ews t_ds (DOT _strstart) (vi (d_strstart s)) (p_s p) *
  (@field_at DCS.CS Ews t_ds (DOT _strstart) (vi (d_strstart s)) (p_s p) -* match_at s p).
Proof.
  apply bz_extract with (F :=
  (@field_at DCS.CS Ews t_ds (DOT _block_start) (vl (d_block_start s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _match_length) (vi (d_match_length s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _prev_match) (vi (d_prev_match s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _match_available) (vi (d_match_available s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _match_start) (vi (d_match_start s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _lookahead) (vi (d_lookahead s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _prev_length) (vi (d_prev_length s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _insert) (vi (d_insert s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _slid) (vi (d_slid s)) (p_s p))%logic);
  unfold match_at; cancel.
Qed.

Lemma bz_win s p : win_at s p |--
  @field_at DCS.CS Ews t_ds (DOT _w_bits) (vi (d_w_bits s)) (p_s p) *
  (@field_at DCS.CS Ews t_ds (DOT _w_bits) (vi (d_w_bits s)) (p_s p) -* win_at s p).
Proof.
  apply bz_extract with (F :=
  (@field_at DCS.CS Ews t_ds (DOT _window) (p_window p) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _window_size) (vl (d_window_size s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _w_size) (vi (d_w_size s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _w_mask) (vi (d_w_mask s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _high_water) (vl (d_high_water s)) (p_s p) *
  @data_at DCS.CS Ews (tarray tuchar (Zlength (mb_val (d_window s)))) (mb_vals (d_window s)) (p_window p))%logic);
  unfold win_at; cancel.
Qed.

Lemma bz_hash s p : hash_at s p |--
  @field_at DCS.CS Ews t_ds (DOT _hash_bits) (vi (d_hash_bits s)) (p_s p) *
  (@field_at DCS.CS Ews t_ds (DOT _hash_bits) (vi (d_hash_bits s)) (p_s p) -* hash_at s p).
Proof.
  apply bz_extract with (F :=
  (@field_at DCS.CS Ews t_ds (DOT _prev) (p_prev p) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _head) (p_head p) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _ins_h) (vi (d_ins_h s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _hash_size) (vi (d_hash_size s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _hash_mask) (vi (d_hash_mask s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _hash_shift) (vi (d_hash_shift s)) (p_s p) *
  @data_at DCS.CS Ews (tarray tushort (Zlength (d_prev s))) (map vi (d_prev s)) (p_prev p) *
  @data_at DCS.CS Ews (tarray tushort (Zlength (d_head s))) (map vi (d_head s)) (p_head p))%logic);
  unfold hash_at; cancel.
Qed.

Lemma bz_trees cs sp pbp strmp gv : trees_at cs sp pbp strmp gv |--
  lvl_at (fst cs) sp * (lvl_at (fst cs) sp -* trees_at cs sp pbp strmp gv).
Proof.
  apply bz_extract with (F :=
  (ltree_at (tr_ltree (fst cs)) sp * dtree_at (tr_dtree (fst cs)) sp * bltree_at (tr_bltree (fst cs)) sp *
   ldesc_at (field_address t_ds (DOT Zlib.trees.code._dyn_ltree) sp) (tr_lmax (fst cs)) (gv Zlib.trees.code._static_l_desc) sp *
   ddesc_at (field_address t_ds (DOT Zlib.trees.code._dyn_dtree) sp) (tr_dmax (fst cs)) (gv Zlib.trees.code._static_d_desc) sp *
   bldesc_at (field_address t_ds (DOT Zlib.trees.code._bl_tree) sp) (tr_blmax (fst cs)) (gv Zlib.trees.code._static_bl_desc) sp *
   work_at (tr_wk (fst cs)) sp * out_at (tr_out (fst cs)) (snd cs) sp pbp * sym_at (fst cs) sp pbp *
   dtype_at (fst cs) sp strmp)%logic);
  unfold trees_at; cancel.
Qed.

Ltac bz_bool := repeat match goal with
  | |- context [Int.eq (Int.repr ?a) Int.zero] =>
      change Int.zero with (Int.repr 0); rewrite (int_eq_s32 a 0) by (unfold s32_ok; rep_lia)
  | |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b)
  | |- context [Z.geb ?a ?b] => destruct (Z.geb_spec a b)
  | |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b)
  | |- context [zlt ?a ?b] => destruct (zlt a b)
  | |- context [zeq ?a ?b] => destruct (zeq a b)
  | |- context [zle ?a ?b] => destruct (zle a b)
  end; unfold Z_FIXED in *; try lia; try reflexivity; try contradiction;
  try (match goal with H : Int.repr _ = Int.zero |- _ => cbn in H; injection H; discriminate end);
  try (match goal with H : Int.repr _ <> Int.zero |- _ => exfalso; apply H; reflexivity end).

Lemma bz_close s p gv :
  Int.min_signed <= d_level s <= Int.max_signed -> Int.min_signed <= d_strategy s <= Int.max_signed ->
  (@field_at DCS.CS Ews t_ds (DOT Zlib.trees.code._level) (vi (d_level s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT Zlib.trees.code._strategy) (vi (d_strategy s)) (p_s p) *
   ((@field_at DCS.CS Ews t_ds (DOT Zlib.trees.code._level) (vi (d_level s)) (p_s p) *
     @field_at DCS.CS Ews t_ds (DOT Zlib.trees.code._strategy) (vi (d_strategy s)) (p_s p)) -*
    trees_at (d_trm s) (p_s p) (p_pbuf p) (p_strm p) gv) *
   @field_at DCS.CS Ews t_ds (DOT _hash_bits) (vi (d_hash_bits s)) (p_s p) *
   (@field_at DCS.CS Ews t_ds (DOT _hash_bits) (vi (d_hash_bits s)) (p_s p) -* hash_at s p) *
   @field_at DCS.CS Ews t_ds (DOT _w_bits) (vi (d_w_bits s)) (p_s p) *
   (@field_at DCS.CS Ews t_ds (DOT _w_bits) (vi (d_w_bits s)) (p_s p) -* win_at s p) *
   @field_at DCS.CS Ews t_ds (DOT _strstart) (vi (d_strstart s)) (p_s p) *
   (@field_at DCS.CS Ews t_ds (DOT _strstart) (vi (d_strstart s)) (p_s p) -* match_at s p) *
   @field_at DCS.CS Ews t_ds (DOT _wrap) (vi (d_wrap s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _gzhead) (p_gzhead p) (p_s p) *
   ((@field_at DCS.CS Ews t_ds (DOT _wrap) (vi (d_wrap s)) (p_s p) *
     @field_at DCS.CS Ews t_ds (DOT _gzhead) (p_gzhead p) (p_s p)) -* stat_at s p))
  |-- trees_at (d_trm s) (p_s p) (p_pbuf p) (p_strm p) gv * hash_at s p * win_at s p * match_at s p * stat_at s p.
Proof.
  intros.
  sep_apply (mp_wand (@field_at DCS.CS Ews t_ds (DOT Zlib.trees.code._level) (vi (d_level s)) (p_s p) *
     @field_at DCS.CS Ews t_ds (DOT Zlib.trees.code._strategy) (vi (d_strategy s)) (p_s p))%logic
     (trees_at (d_trm s) (p_s p) (p_pbuf p) (p_strm p) gv)).
  sep_apply (mp_wand (@field_at DCS.CS Ews t_ds (DOT _hash_bits) (vi (d_hash_bits s)) (p_s p)) (hash_at s p)).
  sep_apply (mp_wand (@field_at DCS.CS Ews t_ds (DOT _w_bits) (vi (d_w_bits s)) (p_s p)) (win_at s p)).
  sep_apply (mp_wand (@field_at DCS.CS Ews t_ds (DOT _strstart) (vi (d_strstart s)) (p_s p)) (match_at s p)).
  sep_apply (mp_wand (@field_at DCS.CS Ews t_ds (DOT _wrap) (vi (d_wrap s)) (p_s p) *
     @field_at DCS.CS Ews t_ds (DOT _gzhead) (p_gzhead p) (p_s p))%logic (stat_at s p)).
  cancel.
Qed.

Lemma bz_tight_eq n wl : u64_ok n -> 0 <= wl <= Int64.max_unsigned ->
  Int64.add (Int64.sub (Int64.add (Int64.add (Int64.add (Int64.add (Int64.repr n)
     (Int64.shru (Int64.repr n) (Int64.repr (Int.unsigned (Int.repr 12)))))
     (Int64.shru (Int64.repr n) (Int64.repr (Int.unsigned (Int.repr 14)))))
     (Int64.shru (Int64.repr n) (Int64.repr (Int.unsigned (Int.repr 25)))))
     (Int64.repr (Int.signed (Int.repr 13)))) (Int64.repr (Int.signed (Int.repr 6)))) (Int64.repr wl)
  = Int64.repr (u64 (n + Z.shiftr n 12 + Z.shiftr n 14 + Z.shiftr n 25 + 13 - 6 + wl)).
Proof.
  unfold u64_ok; intros. rewrite !bz_shr by lia. rewrite !Int.signed_repr by rep_lia. rewrite !add64_repr.
  rewrite sub64_repr, add64_repr, bz_repr_u64. reflexivity.
Qed.

Lemma bz_runs_range b a r : runs (strlen_body b) a r -> 0 <= r <= Int64.max_unsigned.
Proof.
  induction 1 as [a r H|a a' r H _ IH]; auto.
  destruct a as [i wl]. unfold strlen_body, rd in H. destruct (in_range i (Zlength b)); cbn [bind] in H; [|discriminate].
  destruct (Znth i b =? 0); inv H. apply u64_range.
Qed.

Lemma bz_count_range o wl r : 0 <= wl <= Int64.max_unsigned -> c_count_str o wl = Some r -> 0 <= r <= Int64.max_unsigned.
Proof. destruct o; cbn; intros H E; [apply loop_runs in E; eapply bz_runs_range; eauto | inv E; auto]. Qed.

Lemma bz_wlen_range s w wl : bz_wlen s w = Some wl -> 0 <= wl <= Int64.max_unsigned.
Proof.
  unfold bz_wlen. intros E.
  destruct (w =? 0); [inv E; rep_lia|]. destruct (w =? 1); [inv E; destruct (_ =? _); rep_lia|].
  destruct (w =? 2); [|inv E; rep_lia]. destruct (d_gzhead s) as [h|]; [|inv E; rep_lia].
  destruct (c_count_str (gz_name h) _) as [w1|] eqn:E1; cbn [bind] in E; [|discriminate].
  destruct (c_count_str (gz_comment h) w1) as [w2|] eqn:E2; cbn [bind] in E; [|discriminate].
  apply bz_count_range in E1; [|destruct (gz_extra h); [apply u64_range|rep_lia]].
  apply bz_count_range in E2; auto. inv E. destruct (_ =? _); [auto|apply u64_range].
Qed.

Lemma bz_true (c : bool) : Int.repr (if c then 1 else 0) <> Int.zero -> c = true.
Proof. destruct c; [reflexivity|]. intros H; exfalso; apply H; reflexivity. Qed.
Lemma bz_false (c : bool) : Int.repr (if c then 1 else 0) = Int.zero -> c = false.
Proof. destruct c; [|reflexivity]. intros H. cbn in H. injection H; discriminate. Qed.

Lemma bz_final_cons s n wl :
  (negb (d_w_bits s =? 15) || negb (d_hash_bits s =? 8 + 7) ||
   ((d_strategy s =? Z_FIXED) && (d_level s >=? 1) && (d_level s <=? 3)))%bool = true ->
  bz_final s n wl = bz_add (if ((d_w_bits s <=? d_hash_bits s) && negb (d_level s =? 0))%bool then bz_fixed n else bz_store n) wl.
Proof. intros E. unfold bz_final. rewrite E. reflexivity. Qed.
Lemma bz_final_tight s n wl :
  (negb (d_w_bits s =? 15) || negb (d_hash_bits s =? 8 + 7) ||
   ((d_strategy s =? Z_FIXED) && (d_level s >=? 1) && (d_level s <=? 3)))%bool = false ->
  bz_final s n wl = bz_tight n wl.
Proof. intros E. unfold bz_final. rewrite E. reflexivity. Qed.

Lemma bz_opt_open sh b p : opt_obj sh (Some b) p |--
  @data_at DCS.CS sh (tarray tuchar (Zlength b)) (map vi b) p *
  (@data_at DCS.CS sh (tarray tuchar (Zlength b)) (map vi b) p -* opt_obj sh (Some b) p).
Proof.
  apply derives_trans with (Q := (!! Forall (fun x => 0 <= x < 256) b && opt_obj sh (Some b) p)%logic).
  { apply andp_right; [unfold opt_obj; entailer! | apply derives_refl]. }
  Intros. apply bz_extract with (F := (if Zlength b =? 0 then @VST.floyd.library.malloc_token DCS.CS Ews (tarray tuchar 0) p else emp));
  unfold opt_obj; entailer!.
Qed.

(** ** The gzip header case *)
Definition bz_wl1 (h : gzh) : Z :=
  match gz_extra h with Some _ => u64 (18 + u32 (2 + gz_extra_len h)) | None => 18 end.

Lemma bz_wlen_2n s wl : d_gzhead s = None -> bz_wlen s 2 = Some wl -> wl = 18.
Proof. unfold bz_wlen. intros E H. rewrite E in H. inv H. auto. Qed.

Lemma bz_wlen_2 s h wl : d_gzhead s = Some h -> bz_wlen s 2 = Some wl ->
  exists w2 w3, c_count_str (gz_name h) (bz_wl1 h) = Some w2 /\ c_count_str (gz_comment h) w2 = Some w3 /\
                wl = (if gz_hcrc h =? 0 then w3 else u64 (w3 + 2)).
Proof.
  unfold bz_wlen. intros E H. rewrite E in H. change (2 =? 0) with false in H. change (2 =? 1) with false in H.
  change (2 =? 2) with true in H. cbv iota beta zeta in H. fold (bz_wl1 h) in H.
  destruct (c_count_str (gz_name h) (bz_wl1 h)) as [w2|] eqn:E2; cbn [bind] in H; [|discriminate].
  destruct (c_count_str (gz_comment h) w2) as [w3|] eqn:E3; cbn [bind] in H; [|discriminate].
  inv H. eauto.
Qed.

Lemma bz_wl1_range h : 0 <= bz_wl1 h <= Int64.max_unsigned.
Proof. unfold bz_wl1. destruct (gz_extra h); [apply u64_range|rep_lia]. Qed.

(** One iteration of the strlen loop, read off the model. *)
Lemma bz_step nb i wl r : runs (strlen_body nb) (i, wl) r ->
  0 <= i < Zlength nb /\ (Znth i nb = 0 -> r = u64 (wl + 1)) /\
  (Znth i nb <> 0 -> runs (strlen_body nb) (i + 1, u64 (wl + 1)) r).
Proof.
  intros H. apply runs_inv in H. unfold strlen_body, rd in H.
  destruct (in_range i (Zlength nb)) eqn:E; cbn [bind] in H.
  2:{ destruct H as [H|(a & H & _)]; discriminate. }
  unfold in_range in E. apply andb_true_iff in E. destruct E as [E1 E2].
  apply Z.leb_le in E1. apply Z.ltb_lt in E2. split; [lia|].
  destruct (Z.eqb_spec (Znth i nb) 0) as [Z0|Z0].
  - destruct H as [H|(a & H & _)]; [inv H|discriminate]. split; [auto|]. intros; contradiction.
  - destruct H as [H|(a & H & R)]; [discriminate|inv H]. split; [intros; contradiction|auto].
Qed.

Lemma bz_mid (A B C P : mpred) : P = (A * B * C)%logic -> P |-- B * (B -* P).
Proof. intros ->. apply bz_extract with (F := (A * C)%logic); cancel. Qed.

(** The byte at index [i] of a byte array, with a wand giving the array back. *)
Lemma bz_byte sh (l : list Z) p i : 0 <= i < Zlength l ->
  @data_at DCS.CS sh (tarray tuchar (Zlength l)) (map vi l) p |--
  @data_at DCS.CS sh tuchar (vi (Znth i l)) (offset_val i p) *
  (@data_at DCS.CS sh tuchar (vi (Znth i l)) (offset_val i p) -* @data_at DCS.CS sh (tarray tuchar (Zlength l)) (map vi l) p).
Proof.
  intros Hi. assert_PROP (field_compatible (tarray tuchar (Zlength l)) [] p) as FC by entailer!.
  eapply bz_mid.
  rewrite (split3_data_at_Tarray_tuchar sh (Zlength l) i (i + 1)) by (rewrite ?Zlength_map; lia).
  rewrite (sublist_one i (i + 1)) by (rewrite ?Zlength_map; lia). rewrite Znth_map by lia.
  replace (i + 1 - i) with 1 by lia.
  rewrite (data_at_singleton_array_eq sh tuchar (vi (Znth i l))) by reflexivity.
  rewrite (field_address0_offset (tarray tuchar (Zlength l)) [ArraySubsc i]) by auto with field_compatible.
  simpl nested_field_offset. replace (0 + 1 * i) with i by lia.
  reflexivity.
Qed.

Lemma bz_opt_valid sh b p : readable_share sh -> opt_obj sh (Some b) p |-- valid_pointer p.
Proof.
  intros Hsh. unfold opt_obj. apply andp_left2. destruct (Zlength b =? 0) eqn:E.
  - apply sepcon_valid_pointer2. apply VST.floyd.library.malloc_token_valid_pointer. simpl. lia.
  - apply sepcon_valid_pointer1. apply data_at_valid_ptr; [apply readable_nonidentity; auto|].
    apply Z.eqb_neq in E. pose proof (Zlength_nonneg b). simpl. rewrite Z.max_r by lia. lia.
Qed.

Lemma bz_opt_isptr sh b p : opt_obj sh (Some b) p |-- !! isptr p.
Proof. unfold opt_obj. entailer!. Qed.

Ltac bz_vp := first [ solve [apply field_at_valid_ptr0; auto; simpl; lia]
                    | apply sepcon_valid_pointer1; bz_vp | apply sepcon_valid_pointer2; bz_vp ].

Ltac bz_vpo := first [ solve [apply bz_opt_valid; auto]
                     | apply sepcon_valid_pointer1; bz_vpo | apply sepcon_valid_pointer2; bz_vpo ].

(** The byte fact of [opt_obj] (v6). *)
Definition opt_obj_bytes : Prop :=
  forall sh b p, opt_obj sh (Some b) p |-- !! Forall (fun x => 0 <= x < 256) b.

Lemma opt_obj_bytes_ok : opt_obj_bytes.
Proof. intros sh b p. unfold opt_obj. entailer!. Qed.

Lemma body_deflateBound_z_of (OB : opt_obj_bytes) : ob_deflateBound_z.
Proof.
  unfold ob_deflateBound_z. start_function.
  assert (Hn : 0 <= n <= Int64.max_unsigned) by (unfold u64_ok in H; lia).
  forward. rewrite bz_sum5 by (auto; lia).
  forward_if (PROP () LOCAL (temp _fixedlen (vl (bz_fixed n)); gvars gv; temp _strm strmp; temp _sourceLen (vl n))
    SEP (field_at Ews t_strm (DOT _next_in) ni strmp; dstream 2 os strmp ghp gv; hdr_at os ghp hx)).
  { forward. entailer!. apply bz_ltu in H1; [|apply u64_range|lia].
    unfold bz_fixed. rewrite (proj2 (Z.ltb_lt _ _) H1). unfold vl; rewrite bz_UMAX64. reflexivity. }
  { forward. entailer!. apply bz_nltu in H1; [|apply u64_range|lia].
    unfold bz_fixed. destruct (_ <? _) eqn:E; [apply Z.ltb_lt in E; lia|]. reflexivity. }
  forward. rewrite bz_sum5 by (auto; lia).
  forward_if (PROP () LOCAL (temp _storelen (vl (bz_store n)); temp _fixedlen (vl (bz_fixed n)); gvars gv; temp _strm strmp; temp _sourceLen (vl n))
    SEP (field_at Ews t_strm (DOT _next_in) ni strmp; dstream 2 os strmp ghp gv; hdr_at os ghp hx)).
  { forward. entailer!. apply bz_ltu in H1; [|apply u64_range|lia].
    unfold bz_store. rewrite (proj2 (Z.ltb_lt _ _) H1). unfold vl; rewrite bz_UMAX64. reflexivity. }
  { forward. entailer!. apply bz_nltu in H1; [|apply u64_range|lia].
    unfold bz_store. destruct (_ <? _) eqn:E; [apply Z.ltb_lt in E; lia|]. reflexivity. }
  pose proof (bz_fixed_range n). pose proof (bz_store_range n). pose proof (bz_max_range n).
  destruct os as [s|].
  2:{ rewrite bz_none in H0. inv H0. dcheck_none strmp gv.
      forward_if (PROP (False) LOCAL () SEP ()); [| inv H0 ].
      forward_if (temp _t'1 (vl (bz_max (bz_fixed n) (bz_store n)))).
      { forward. entailer!. unfold bz_max. destruct (Z.gtb_spec (bz_fixed n) (bz_store n)); [reflexivity|lia]. }
      { forward. entailer!. unfold bz_max. destruct (Z.gtb_spec (bz_fixed n) (bz_store n)); [lia|reflexivity]. }
      forward.
      forward_if (temp _t'2 (vl (bz_add (bz_max (bz_fixed n) (bz_store n)) 18))).
      { forward. entailer!. apply bz_add_lt; auto. }
      { forward. entailer!. apply bz_add_ge; auto. }
      forward. cancel. }
  dcheck_some s strmp gv.
  destruct (bad_state s) eqn:Hb.
  { rewrite bz_bad in H0 by auto. inv H0.
    assert (Hc : c_deflateStateCheck (Some s) = 1) by (unfold bad_state in Hb; apply Z.eqb_eq; auto).
    rewrite Hc.
    forward_if (PROP (False) LOCAL () SEP ()); [| inv H0 ].
    forward_if (temp _t'1 (vl (bz_max (bz_fixed n) (bz_store n)))).
    { forward. entailer!. unfold bz_max. destruct (Z.gtb_spec (bz_fixed n) (bz_store n)); [reflexivity|lia]. }
    { forward. entailer!. unfold bz_max. destruct (Z.gtb_spec (bz_fixed n) (bz_store n)); [lia|reflexivity]. }
    forward.
    forward_if (temp _t'2 (vl (bz_add (bz_max (bz_fixed n) (bz_store n)) 18))).
    { forward. entailer!. apply bz_add_lt; auto. }
    { forward. entailer!. apply bz_add_ge; auto. }
    forward. cancel. }
  assert (Hc : c_deflateStateCheck (Some s) = 0).
  { unfold bad_state in Hb. apply Z.eqb_neq in Hb. unfold c_deflateStateCheck in *. destruct (status_ok _); congruence. }
  rewrite Hc.
  forward_if (PROP () LOCAL (temp _storelen (vl (bz_store n)); temp _fixedlen (vl (bz_fixed n)); gvars gv; temp _strm strmp; temp _sourceLen (vl n))
    SEP (field_at Ews t_strm (DOT _next_in) ni strmp; dstream 2 (Some s) strmp ghp gv; hdr_at (Some s) ghp hx)).
  { contradiction. }
  { forward. entailer!. }
  rewrite bz_good in H0 by auto.
  destruct (bz_w s) as [w|] eqn:Hw; [|discriminate]. cbn [bind] in H0.
  destruct (bz_wlen s w) as [wl|] eqn:Hwl; [|discriminate]. cbn [bind] in H0. inv H0.
  rewrite dstream_some_eq. Intros p. rewrite dstate_at'_2; unfold dstate_at. Intros.
  match goal with HR : dstate_ranges s |- _ => rename HR into Hrs end.
  match goal with HR : p_strm p = strmp |- _ => rename HR into Hps end.
  match goal with HR : p_gzhead p = ghp |- _ => rename HR into Hpg end.
  match goal with HR : dsizes s |- _ => rename HR into Hsz end.
  assert (Hr : s32_ok (d_wrap s)) by drange Hrs.
  assert (Hss : u32_ok (d_strstart s)) by drange Hrs.
  assert (Hwb : u32_ok (d_w_bits s)) by drange Hrs.
  assert (Hhb : u32_ok (d_hash_bits s)) by drange Hrs.
  destruct (bz_w_ok s w Hr Hw) as (Hw1 & Hw2 & Hw3). unfold s32_ok in Hr, Hw1. unfold u32_ok in Hss, Hwb, Hhb.
  sep_apply (bz_stat s p). sep_apply (bz_match s p). sep_apply (bz_win s p). sep_apply (bz_hash s p).
  sep_apply (bz_trees (d_trm s) (p_s p) (p_pbuf p) (p_strm p) gv). unfold lvl_at. Intros.
  repeat flatten_sepcon_in_SEP.
  assert_PROP (isptr (p_s p)) by entailer!.
  forward. forward.
  forward_if (temp _t'4 (vi w)).
  { forward. forward.
    { entailer!. rewrite Int.signed_zero. specialize (Hw3 ltac:(assumption)). rep_lia. }
    entailer!. try rewrite Int.signed_repr in * by rep_lia. destruct (Z.ltb_spec (d_wrap s) 0); [|lia]. try (unfold vi; rewrite Int.neg_repr); reflexivity. }
  { forward. forward. entailer!. try rewrite Int.signed_repr in * by rep_lia. destruct (Z.ltb_spec (d_wrap s) 0); [lia|]. reflexivity. }
  clear Hw2 Hw3. pose proof (bz_wlen_range _ _ _ Hwl) as Hwlr.
  forward_if (temp _wraplen (vl wl)).
  { (* raw *)
    apply bz_wlen_0 in Hwl. subst wl. forward. forward. entailer!. }
  { (* zlib *)
    apply bz_wlen_1 in Hwl. subst wl. forward.
    forward_if (temp _t'5 (vi (if d_strstart s =? 0 then 0 else 4))).
    { forward. entailer!. destruct (Z.eqb_spec (d_strstart s) 0); [|reflexivity].
      exfalso. subst. contradiction. }
    { forward. entailer!. destruct (Z.eqb_spec (d_strstart s) 0); [reflexivity|].
      exfalso. match goal with Hx : Int.repr (d_strstart s) = _ |- _ =>
        apply repr_inj_unsigned in Hx; [lia|rep_lia|rep_lia] end. }
    assert (Ht5 : 0 <= (if d_strstart s =? 0 then 0 else 4) <= 4) by (destruct (_ =? _); lia).
    forget (if d_strstart s =? 0 then 0 else 4) as t5. forward. forward. entailer!. }
  { (* gzip *)
    forward.
    destruct hx as [[[hsh xp] np] cp].
    change (hdr_at (Some s) ghp (hsh, xp, np, cp)) with
      (match d_gzhead s with Some h => gzh_at hsh h ghp xp np cp | None => !! (ghp = nullval) && emp end)%logic.
    destruct (d_gzhead s) as [h|] eqn:Hgz.
    2:{ apply bz_wlen_2n in Hwl; auto. subst wl. Intros.
        assert (Hgn : p_gzhead p = nullval) by congruence. rewrite Hgn.
        forward. forward_if (temp _wraplen (vl 18)).
        { match goal with H : false = true |- _ => discriminate H end. }
        { forward. entailer!. }
        forward. entailer!. rewrite Hgn. unfold hdr_at. rewrite Hgz. entailer!. }
    destruct (bz_wlen_2 _ _ _ Hgz Hwl) as (w2 & w3 & E2 & E3 & Ewl). subst wl.
    pose proof (bz_wl1_range h) as Hw1r.
    unfold gzh_at. Intros vxf vem vnm vcm vdn. subst ghp.
    freeze [0;1;2;3;4;5;6;7;8;9;11;12;13;14;15;16;17;18;19;21;22;28;29;30;31;32] FR.
    assert_PROP (isptr (p_gzhead p)) as Hgp by entailer!.
    match goal with Hx : readable_share hsh /\ _ |- _ => destruct Hx as [Hrsh Hgok]
                  | Hx : readable_share hsh |- _ => rename Hx into Hrsh end.
    assert (Hnid : sepalg.nonidentity hsh) by (apply readable_nonidentity; auto).
    forward. forward_if (temp _wraplen (vl (if gz_hcrc h =? 0 then w3 else u64 (w3 + 2)))).
    { apply denote_tc_test_eq_split; [|apply valid_pointer_null]. bz_vp. }
    { (* user header *)
      forward.
      assert_PROP (gz_extra h = None -> xp = nullval) as Hxn.
      { destruct (gz_extra h); [entailer! | unfold opt_obj at 1; entailer!]. }
      assert_PROP (gz_extra h <> None -> isptr xp) as Hxs.
      { destruct (gz_extra h) as [xb|]; [|entailer!]. sep_apply (bz_opt_isptr hsh xb xp). entailer!. }
      assert (Hxpn : is_pointer_or_null xp).
      { destruct (gz_extra h).
        - assert (isptr xp) by (apply Hxs; discriminate). destruct xp; try contradiction; simpl; auto.
        - rewrite Hxn by reflexivity. simpl. auto. }
      forward.
      forward_if (temp _wraplen (vl (bz_wl1 h))).
      { destruct (gz_extra h) as [xb|] eqn:Hx.
        - apply denote_tc_test_eq_split; [|apply valid_pointer_null]. bz_vpo.
        - rewrite Hxn by reflexivity. apply denote_tc_test_eq_split; apply valid_pointer_null. }
      { destruct (gz_extra h) as [xb|] eqn:Hx.
        - forward. forward. forward. entailer!. unfold bz_wl1, vl, u32. rewrite Hx, bz_repr_u64, Int.unsigned_repr_eq. reflexivity.
        - exfalso. match goal with H0 : xp <> nullval |- _ => apply H0; apply Hxn; reflexivity end. }
      { destruct (gz_extra h) as [xb|] eqn:Hx.
        - exfalso. assert (isptr xp) by (apply Hxs; discriminate).
          match goal with H0 : xp = nullval |- _ => rewrite H0 in *; contradiction end.
        - forward. entailer!. unfold bz_wl1. rewrite Hx. reflexivity. }
      forward.
      assert_PROP (gz_name h = None -> np = nullval) as Hnn.
      { destruct (gz_name h); [entailer! | unfold opt_obj at 2; entailer!]. }
      assert_PROP (gz_name h <> None -> isptr np) as Hns.
      { destruct (gz_name h) as [nb|]; [|entailer!]. sep_apply (bz_opt_isptr hsh nb np). entailer!. }
      assert (Hnpn : is_pointer_or_null np).
      { destruct (gz_name h).
        - assert (isptr np) by (apply Hns; discriminate). destruct np; try contradiction; simpl; auto.
        - rewrite Hnn by reflexivity. simpl. auto. }
      forward.
      match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
        let Q' := remove_LOCAL2 constr:([temp _str Vundef; temp _wraplen Vundef]) Q in
        forward_if (PROPx P (LOCALx (temp _wraplen (vl w2) :: Q') (SEPx R))) end.
      { destruct (gz_name h) as [nb|] eqn:Hnm.
        - apply denote_tc_test_eq_split; [|apply valid_pointer_null]. bz_vpo.
        - rewrite Hnn by reflexivity. apply denote_tc_test_eq_split; apply valid_pointer_null. }
      { destruct (gz_name h) as [nb|] eqn:Hnm.
        2:{ exfalso. match goal with H0 : np <> nullval |- _ => apply H0; apply Hnn; reflexivity end. }
        try rewrite Hnm in E2. cbn [c_count_str] in E2. apply loop_runs in E2.
        assert_PROP (Forall (fun x => 0 <= x < 256) nb) as Hnb by (sep_apply (OB hsh nb np); entailer!).
        sep_apply (bz_opt_open hsh nb np). flatten_sepcon_in_SEP.
        assert (Hnp : isptr np) by (apply Hns; discriminate).
        match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
          let Q' := remove_LOCAL2 constr:([temp _str Vundef; temp _wraplen Vundef]) Q in
          forward_loop (EX i : Z, EX wl : Z, PROPx (runs (strlen_body nb) (i, wl) w2 :: P)
                          (LOCALx (temp _str (offset_val i np) :: temp _wraplen (vl wl) :: Q') (SEPx R)))
            continue: (EX i : Z, EX wl : Z, PROPx (runs (strlen_body nb) (i, wl) w2 :: P)
                          (LOCALx (temp _str (offset_val i np) :: temp _wraplen (vl (u64 (wl + 1))) :: Q') (SEPx R)))
            break: (PROPx P (LOCALx (temp _wraplen (vl w2) :: Q') (SEPx R)))
        end.
        { Exists 0 (bz_wl1 h). entailer!. }
        { Intros i wl. forward. Exists i wl. entailer!. unfold vl. rewrite bz_repr_u64. reflexivity. }
        { Intros i wl.
          match goal with Hr : runs (strlen_body nb) (i, wl) w2 |- _ => destruct (bz_step _ _ _ _ Hr) as (Hi & Hz & Hnz) end.
          assert (Hbi : 0 <= Znth i nb < 256) by (rewrite Forall_Znth in Hnb; apply Hnb; auto).
          assert (Hip : isptr (offset_val i np)) by (destruct np; try contradiction; simpl; auto).
          assert (Htc : tc_val tuchar (vi (Znth i nb))) by (unfold vi; simpl; rewrite Int.unsigned_repr by rep_lia; rep_lia).
          forward. forward.
          sep_apply (bz_byte hsh nb np i Hi). flatten_sepcon_in_SEP.
          forward.
          sep_apply (mp_wand (@data_at DCS.CS hsh tuchar (vi (Znth i nb)) (offset_val i np))
                             (@data_at DCS.CS hsh (tarray tuchar (Zlength nb)) (map vi nb) np)).
          forward_if (Znth i nb <> 0).
          { forward. entailer!. match goal with E : Znth i nb = 0 |- _ => rewrite E in * end.
            match goal with H0 : typed_true _ _ |- _ => inv H0 end. }
          { forward. entailer!.
            match goal with H0 : typed_false _ _ |- _ => rename H0 into Htf end.
            destruct (Z.eq_dec (Znth i nb) 0) as [Z0|Hne].
            2:{ exfalso. unfold typed_false, strict_bool_val in Htf. simpl in Htf.
                rewrite Int.eq_false in Htf; [discriminate|]. intro E. apply repr_inj_unsigned in E; rep_lia. }
            rewrite (Hz Z0). reflexivity. }
          Exists (i + 1) (u64 (wl + 1)). entailer!. }
        sep_apply (mp_wand (@data_at DCS.CS hsh (tarray tuchar (Zlength nb)) (map vi nb) np) (opt_obj hsh (Some nb) np)).
        unfold POSTCONDITION, abbreviate. simpl_ret_assert. entailer!. }
      { destruct (gz_name h) as [nb|] eqn:Hnm.
        - exfalso. assert (isptr np) by (apply Hns; rewrite ?Hnm; discriminate).
          match goal with H0 : np = nullval |- _ => rewrite H0 in *; contradiction end.
        - try rewrite Hnm in E2. cbn [c_count_str] in E2. inv E2. forward. entailer!. }
      forward.
      assert_PROP (gz_comment h = None -> cp = nullval) as Hcn.
      { destruct (gz_comment h); [entailer! | unfold opt_obj at 3; entailer!]. }
      assert_PROP (gz_comment h <> None -> isptr cp) as Hcs.
      { destruct (gz_comment h) as [cb|]; [|entailer!]. sep_apply (bz_opt_isptr hsh cb cp). entailer!. }
      assert (Hcpn : is_pointer_or_null cp).
      { destruct (gz_comment h).
        - assert (isptr cp) by (apply Hcs; discriminate). destruct cp; try contradiction; simpl; auto.
        - rewrite Hcn by reflexivity. simpl. auto. }
      forward.
      match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
        let Q' := remove_LOCAL2 constr:([temp _str Vundef; temp _wraplen Vundef]) Q in
        forward_if (PROPx P (LOCALx (temp _wraplen (vl w3) :: Q') (SEPx R))) end.
      { destruct (gz_comment h) as [cb|] eqn:Hcm.
        - apply denote_tc_test_eq_split; [|apply valid_pointer_null]. bz_vpo.
        - rewrite Hcn by reflexivity. apply denote_tc_test_eq_split; apply valid_pointer_null. }
      { destruct (gz_comment h) as [cb|] eqn:Hcm.
        2:{ exfalso. match goal with H0 : cp <> nullval |- _ => apply H0; apply Hcn; reflexivity end. }
        try rewrite Hcm in E3. cbn [c_count_str] in E3. apply loop_runs in E3.
        assert_PROP (Forall (fun x => 0 <= x < 256) cb) as Hcb by (sep_apply (OB hsh cb cp); entailer!).
        sep_apply (bz_opt_open hsh cb cp). flatten_sepcon_in_SEP.
        assert (Hcp : isptr cp) by (apply Hcs; discriminate).
        match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
          let Q' := remove_LOCAL2 constr:([temp _str Vundef; temp _wraplen Vundef]) Q in
          forward_loop (EX i : Z, EX wl : Z, PROPx (runs (strlen_body cb) (i, wl) w3 :: P)
                          (LOCALx (temp _str (offset_val i cp) :: temp _wraplen (vl wl) :: Q') (SEPx R)))
            continue: (EX i : Z, EX wl : Z, PROPx (runs (strlen_body cb) (i, wl) w3 :: P)
                          (LOCALx (temp _str (offset_val i cp) :: temp _wraplen (vl (u64 (wl + 1))) :: Q') (SEPx R)))
            break: (PROPx P (LOCALx (temp _wraplen (vl w3) :: Q') (SEPx R)))
        end.
        { Exists 0 w2. entailer!. }
        { Intros i wl. forward. Exists i wl. entailer!. unfold vl. rewrite bz_repr_u64. reflexivity. }
        { Intros i wl.
          match goal with Hr : runs (strlen_body cb) (i, wl) w3 |- _ => destruct (bz_step _ _ _ _ Hr) as (Hi & Hz & Hnz) end.
          assert (Hbi : 0 <= Znth i cb < 256) by (rewrite Forall_Znth in Hcb; apply Hcb; auto).
          assert (Hip : isptr (offset_val i cp)) by (destruct cp; try contradiction; simpl; auto).
          assert (Htc : tc_val tuchar (vi (Znth i cb))) by (unfold vi; simpl; rewrite Int.unsigned_repr by rep_lia; rep_lia).
          forward. forward.
          sep_apply (bz_byte hsh cb cp i Hi). flatten_sepcon_in_SEP.
          forward.
          sep_apply (mp_wand (@data_at DCS.CS hsh tuchar (vi (Znth i cb)) (offset_val i cp))
                             (@data_at DCS.CS hsh (tarray tuchar (Zlength cb)) (map vi cb) cp)).
          forward_if (Znth i cb <> 0).
          { forward. entailer!. match goal with E : Znth i cb = 0 |- _ => rewrite E in * end.
            match goal with H0 : typed_true _ _ |- _ => inv H0 end. }
          { forward. entailer!.
            match goal with H0 : typed_false _ _ |- _ => rename H0 into Htf end.
            destruct (Z.eq_dec (Znth i cb) 0) as [Z0|Hne].
            2:{ exfalso. unfold typed_false, strict_bool_val in Htf. simpl in Htf.
                rewrite Int.eq_false in Htf; [discriminate|]. intro E. apply repr_inj_unsigned in E; rep_lia. }
            rewrite (Hz Z0). reflexivity. }
          Exists (i + 1) (u64 (wl + 1)). entailer!. }
        sep_apply (mp_wand (@data_at DCS.CS hsh (tarray tuchar (Zlength cb)) (map vi cb) cp) (opt_obj hsh (Some cb) cp)).
        unfold POSTCONDITION, abbreviate. simpl_ret_assert. entailer!. }
      { destruct (gz_comment h) as [cb|] eqn:Hcm.
        - exfalso. assert (isptr cp) by (apply Hcs; rewrite ?Hcm; discriminate).
          match goal with H0 : cp = nullval |- _ => rewrite H0 in *; contradiction end.
        - try rewrite Hcm in E3. cbn [c_count_str] in E3. inv E3. forward. entailer!. }
      forward. forward.
      match goal with Hg : gzh_ok h |- _ => unfold gzh_ok in Hg end.
      forward_if (temp _wraplen (vl (if gz_hcrc h =? 0 then w3 else u64 (w3 + 2)))).
      { forward. entailer!. destruct (Z.eqb_spec (gz_hcrc h) 0) as [E0|E0].
        - exfalso. match goal with H0 : Int.repr (gz_hcrc h) <> _ |- _ => apply H0; rewrite E0; reflexivity end.
        - unfold vl. rewrite bz_repr_u64. reflexivity. }
      { forward. entailer!. destruct (Z.eqb_spec (gz_hcrc h) 0) as [E0|E0]; [reflexivity|].
        exfalso. match goal with H0 : Int.repr (gz_hcrc h) = _ |- _ => apply repr_inj_signed in H0; rep_lia end. }
      entailer!. }
    { match goal with Hx : p_gzhead p = nullval |- _ => rewrite Hx in Hgp; contradiction end. }
    forward. thaw FR. unfold hdr_at. rewrite Hgz. unfold gzh_at. Exists vdn vcm vnm vem vxf. entailer!. }
  { (* default *)
    assert (w <> 0 /\ w <> 1 /\ w <> 2) as (W0 & W1 & W2) by (repeat split; intro; subst; contradiction).
    apply (bz_wlen_d s w wl W0 W1 W2) in Hwl. subst wl. forward. forward. entailer!. }

  forward. forward_if (temp _t'11 (vi (if negb (d_w_bits s =? 15) || negb (d_hash_bits s =? 15) then 1 else 0))%bool).
  { forward. entailer!. destruct (Z.eqb_spec (d_w_bits s) 15); [subst; contradiction|reflexivity]. }
  { forward. forward. entailer!. destruct (Z.eqb_spec (d_w_bits s) 15); [|contradiction].
    destruct (zeq (d_hash_bits s) (8+7)); destruct (Z.eqb_spec (d_hash_bits s) 15); try lia; reflexivity. }
  change (tr_level (fst (d_trm s))) with (d_level s) in *.
  change (tr_strategy (fst (d_trm s))) with (d_strategy s) in *.
  forward_if (temp _t'12 (vi (if (negb (d_w_bits s =? 15) || negb (d_hash_bits s =? 15) ||
     ((d_strategy s =? Z_FIXED) && (d_level s >=? 1) && (d_level s <=? 3)))%bool then 1 else 0))).
  { forward. entailer!. destruct (negb _ || negb _)%bool; [reflexivity|contradiction]. }
  { forward.
    forward_if (temp _t'13 (vi (if ((d_strategy s =? Z_FIXED) && (d_level s >=? 1))%bool then 1 else 0))).
    { forward. forward. entailer!. bz_bool. }
    { forward. entailer!. bz_bool. }
    forward_if (temp _t'12 (vi (if (negb (d_w_bits s =? 15) || negb (d_hash_bits s =? 15) ||
     ((d_strategy s =? Z_FIXED) && (d_level s >=? 1) && (d_level s <=? 3)))%bool then 1 else 0))).
    { forward. forward. forward. entailer!. bz_bool. }
    { forward. entailer!. bz_bool. }
    entailer!. }
  forward_if ((negb (d_w_bits s =? 15) || negb (d_hash_bits s =? 15) ||
     ((d_strategy s =? Z_FIXED) && (d_level s >=? 1) && (d_level s <=? 3)))%bool = false).
  { (* conservative bound *)
    forward. forward.
    forward_if (temp _t'8 (vi (if ((d_w_bits s <=? d_hash_bits s) && negb (d_level s =? 0))%bool then 1 else 0))).
    { forward. forward. entailer!. bz_bool. }
    { forward. entailer!. bz_bool. }
    forward_if (temp _t'9 (vl (if ((d_w_bits s <=? d_hash_bits s) && negb (d_level s =? 0))%bool then bz_fixed n else bz_store n))).
    { forward. entailer!.
      destruct ((d_w_bits s <=? d_hash_bits s) && negb (d_level s =? 0))%bool eqn:Eb; [reflexivity|].
      try rewrite Eb in *. exfalso. match goal with Hx : _ <> _ |- _ => apply Hx; reflexivity end. }
    { forward. entailer!.
      destruct ((d_w_bits s <=? d_hash_bits s) && negb (d_level s =? 0))%bool eqn:Eb; [|reflexivity].
      try rewrite Eb in *. exfalso. match goal with Hx : Int.repr _ = Int.zero |- _ =>
        cbn in Hx; injection Hx; discriminate end. }
    forward.
    assert (HB : 0 <= (if ((d_w_bits s <=? d_hash_bits s) && negb (d_level s =? 0))%bool then bz_fixed n else bz_store n) <= Int64.max_unsigned)
      by (destruct ((d_w_bits s <=? d_hash_bits s) && negb (d_level s =? 0))%bool; auto).
    forward_if (temp _t'10 (vl (bz_add (if ((d_w_bits s <=? d_hash_bits s) && negb (d_level s =? 0))%bool then bz_fixed n else bz_store n) wl))).
    { forward. entailer!. bz_addt. }
    { forward. entailer!. bz_addt. }
    forward.
    sep_apply (bz_close s p gv ltac:(assumption) ltac:(assumption)).
    rewrite dstream_some_eq. Exists p. rewrite dstate_at'_2. unfold dstate_at.
    entailer!.
    rewrite bz_final_cons; [reflexivity | apply bz_true; assumption]. }
  { forward. entailer!.
    match goal with |- ?c = false => destruct c eqn:Ec; [|reflexivity] end. exfalso.
    match goal with Hx : Int.repr _ = Int.zero |- _ => try rewrite Ec in Hx; cbn in Hx; injection Hx; discriminate end. }
  forward. try rewrite bz_tight_eq by auto.
  forward_if (temp _t'14 (vl (bz_tight n wl))).
  { forward. entailer!. match goal with Hx : Int64.ltu _ _ = true |- _ => apply bz_ltu in Hx; [|apply u64_range|lia] end.
    unfold bz_tight. rewrite (proj2 (Z.ltb_lt _ _)) by assumption. unfold vl. rewrite bz_UMAX64. reflexivity. }
  { forward. entailer!. match goal with Hx : Int64.ltu _ _ = false |- _ => apply bz_nltu in Hx; [|apply u64_range|lia] end.
    unfold bz_tight. destruct (_ <? _) eqn:E; [apply Z.ltb_lt in E; lia|]. reflexivity. }
  forward.
  sep_apply (bz_close s p gv ltac:(assumption) ltac:(assumption)).
  rewrite dstream_some_eq. Exists p. rewrite dstate_at'_2. unfold dstate_at.
  entailer!.
  rewrite bz_final_tight; [reflexivity | assumption].
Qed.

Lemma body_deflateBound_z : ob_deflateBound_z.
Proof. exact (body_deflateBound_z_of opt_obj_bytes_ok). Qed.
