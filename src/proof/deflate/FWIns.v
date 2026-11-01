(** * fill_window, fragment S_ins (FWKit.v) against its model step. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.proof.deflate.FWKit.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

(** ** The fields the insertion touches, and the rest of the stream *)

Definition ins_part (s : dstate) (p : dptrs) : mpred :=
  (@field_at DCS.CS Ews t_ds (DOT _strstart) (vi (d_strstart s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _lookahead) (vi (d_lookahead s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _insert) (vi (d_insert s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _window) (p_window p) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _w_mask) (vi (d_w_mask s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _prev) (p_prev p) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _head) (p_head p) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _ins_h) (vi (d_ins_h s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _hash_mask) (vi (d_hash_mask s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _hash_shift) (vi (d_hash_shift s)) (p_s p) *
   @data_at DCS.CS Ews (tarray tuchar (Zlength (mb_val (d_window s)))) (mb_vals (d_window s)) (p_window p) *
   @data_at DCS.CS Ews (tarray tushort (Zlength (d_prev s))) (map vi (d_prev s)) (p_prev p) *
   @data_at DCS.CS Ews (tarray tushort (Zlength (d_head s))) (map vi (d_head s)) (p_head p))%logic.

Definition ins_rest (s : dstate) (z : strm) (p : dptrs) (pin : val) (ish : share) (msgv : val)
    (gv : globals) : mpred :=
  (trees_at (d_trm s) (p_s p) (p_pbuf p) (p_strm p) gv * cfg_at s p * stat_at s p *
   @field_at DCS.CS Ews t_ds (DOT _window_size) (vl (d_window_size s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _w_size) (vi (d_w_size s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _w_bits) (vi (d_w_bits s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _high_water) (vl (d_high_water s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _hash_size) (vi (d_hash_size s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _hash_bits) (vi (d_hash_bits s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _block_start) (vl (d_block_start s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _match_length) (vi (d_match_length s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _prev_match) (vi (d_prev_match s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _match_available) (vi (d_match_available s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _match_start) (vi (d_match_start s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _prev_length) (vi (d_prev_length s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _slid) (vi (d_slid s)) (p_s p) *
   strm_in_at z (p_s p) (p_strm p) pin msgv gv * in_obj ish z pin)%logic.

Lemma dfull_in_open s z p pin ish msgv gv :
  dfull_in s z p pin ish msgv gv =
  (!! (dstate_ranges s /\ strm_ranges z /\ msg_ok (z_msg z) msgv /\ readable_share ish) &&
   (ins_part s p * ins_rest s z p pin ish msgv gv))%logic.
Proof.
  unfold dfull_in, dstate_at, ins_part, ins_rest, win_at, hash_at, match_at.
  apply pred_ext.
  - Intros. entailer!.
  - Intros. entailer!.
Qed.


(** ** Model and arithmetic facts *)

Lemma Znth_dflt {A} (d1 d2 : A) i l : 0 <= i < Zlength l -> @Znth A d1 i l = @Znth A d2 i l.
Proof.
  intros H. unfold Znth. destruct (Z_lt_dec i 0); [lia|]. apply nth_indep.
  apply Nat2Z.inj_lt. rewrite Z2Nat.id, <- Zlength_correct; lia.
Qed.

Lemma mb_rd_inv b i c : mb_ok b -> mb_rd b i = Some c ->
  0 <= i < Zlength (mb_val b) /\ (forall d, @Znth val d i (mb_vals b) = vi c) /\ 0 <= c < 256.
Proof.
  intros [Hl Hd] H. unfold mb_rd, in_range in H.
  destruct (0 <=? i) eqn:E1; [|discriminate]. destruct (i <? Zlength (mb_val b)) eqn:E2; [|discriminate].
  destruct (Znth i (mb_def b)) eqn:E3; [|discriminate]. cbn in H. inversion H; subst; clear H.
  apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  split; [lia|]. split.
  - intros d. rewrite (Znth_dflt d Vundef) by (rewrite Zlength_mb_vals; auto; lia).
    unfold mb_vals. rewrite Znth_pb_vals by (auto; lia). rewrite E3. reflexivity.
  - apply Hd; auto.
Qed.

Lemma rd_inv l i h : rd l i = Some h -> 0 <= i < Zlength l /\ Znth i l = h.
Proof.
  unfold rd, in_range. destruct (0 <=? i) eqn:E1; [|discriminate].
  destruct (i <? Zlength l) eqn:E2; [|discriminate]. cbn. intros H; inversion H; subst.
  apply Z.leb_le in E1. apply Z.ltb_lt in E2. auto.
Qed.

Lemma wr_inv l i v l' : wr l i v = Some l' -> 0 <= i < Zlength l /\ l' = upd_Znth i l v.
Proof.
  unfold wr, in_range. destruct (0 <=? i) eqn:E1; [|discriminate].
  destruct (i <? Zlength l) eqn:E2; [|discriminate]. cbn. intros H; inversion H; subst.
  apply Z.leb_le in E1. apply Z.ltb_lt in E2. auto.
Qed.

Lemma xor_repr32 a b: Int.xor (Int.repr a) (Int.repr b) = Int.repr (Z.lxor a b).
Proof.
  apply Int.same_bits_eq. intros i Hi.
  rewrite Int.bits_xor by auto. rewrite !Int.testbit_repr by auto.
  rewrite Z.lxor_spec. reflexivity.
Qed.

Lemma repr_u32 x : Int.repr (u32 x) = Int.repr x.
Proof.
  unfold u32. change 4294967296 with Int.modulus. rewrite <- Int.unsigned_repr_eq. apply Int.repr_unsigned.
Qed.

Lemma u32_range x : 0 <= u32 x <= Int.max_unsigned.
Proof. unfold u32. pose proof (Z.mod_pos_bound x 4294967296). rep_lia. Qed.

Lemma unsigned_repr_u32 x : Int.unsigned (Int.repr x) = u32 x.
Proof. rewrite Int.unsigned_repr_eq. reflexivity. Qed.

Lemma update_hash_eq s h c :
  0 <= h <= Int.max_unsigned -> 0 <= d_hash_shift s < 32 ->
  Int.and (Int.xor (Int.shl (Int.repr h) (Int.repr (d_hash_shift s))) (Int.repr c)) (Int.repr (d_hash_mask s)) =
  Int.repr (update_hash s h c).
Proof.
  intros Hh Hs. unfold update_hash. rewrite repr_u32.
  unfold Int.shl. rewrite !Int.unsigned_repr by rep_lia.
  rewrite <- (repr_u32 (Z.shiftl h (d_hash_shift s))). rewrite xor_repr32, and_repr32. reflexivity.
Qed.

Lemma u32_small x : 0 <= x <= Int.max_unsigned -> u32 x = x.
Proof. intros. unfold u32. apply Z.mod_small. rep_lia. Qed.

Lemma update_hash_range s h c : 0 <= update_hash s h c <= Int.max_unsigned.
Proof. apply u32_range. Qed.

(** The states of the insertion: [s] with ins_h, prev, head, insert replaced. *)
Definition fwi (s : dstate) (ih : Z) (pv hd : list Z) (ins : Z) : dstate :=
  set_d_insert (set_d_head (set_d_prev (set_d_ins_h s ih) pv) hd) ins.

Definition same_rest (s t : dstate) : Prop := t = fwi s (d_ins_h t) (d_prev t) (d_head t) (d_insert t).

Lemma ins_rest_same s t z p pin ish msgv gv :
  same_rest s t -> ins_rest t z p pin ish msgv gv = ins_rest s z p pin ish msgv gv.
Proof. intros H. rewrite H. reflexivity. Qed.


Lemma ranges_ins s : dstate_ranges s ->
  mb_ok (d_window s) /\ Zlength (mb_val (d_window s)) <= Int.max_unsigned /\
  Forall (fun x => 0 <= x < 65536) (d_prev s) /\ Forall (fun x => 0 <= x < 65536) (d_head s) /\
  Zlength (d_prev s) <= Int.max_unsigned /\ Zlength (d_head s) <= Int.max_unsigned /\
  u32_ok (d_ins_h s) /\ u32_ok (d_hash_mask s) /\ u32_ok (d_hash_shift s) /\ u32_ok (d_strstart s) /\
  u32_ok (d_lookahead s) /\ u32_ok (d_insert s) /\ u32_ok (d_w_mask s).
Proof. unfold dstate_ranges. tauto. Qed.

Lemma ranges_fwi s ih pv hd ins : dstate_ranges s ->
  u32_ok ih -> Forall (fun x => 0 <= x < 65536) pv -> Forall (fun x => 0 <= x < 65536) hd ->
  Zlength pv <= Int.max_unsigned -> Zlength hd <= Int.max_unsigned -> u32_ok ins ->
  dstate_ranges (fwi s ih pv hd ins).
Proof. unfold dstate_ranges, fwi. cbn. tauto. Qed.


Lemma same_rest_fwi s t ih pv hd ins : same_rest s t -> same_rest s (fwi t ih pv hd ins).
Proof. unfold same_rest. intros ->. reflexivity. Qed.

Lemma runs_exit_eq {A B} (body : A -> option (A + B)) a r r' :
  runs body a r -> body a = Some (inr r') -> r = r'.
Proof. intros H E. destruct (runs_inv _ _ _ H) as [E'|(a' & E' & _)]; rewrite E in E'; congruence. Qed.

Lemma runs_step_eq {A B} (body : A -> option (A + B)) a a' r :
  runs body a r -> body a = Some (inl a') -> runs body a' r.
Proof.
  intros H E. destruct (runs_inv _ _ _ H) as [E'|(a'' & E' & H')]; rewrite E in E'; [discriminate|].
  inversion E'; subst; auto.
Qed.

(** One iteration of [while (s->insert)] with insert non-zero. *)
Lemma fw_body_step t str r : d_insert t <> 0 -> fw_insert_body (t, str) = Some r ->
  exists c h pv hd,
    d_hash_shift t < 32 /\ mb_rd (d_window t) (u32 (str + MIN_MATCH - 1)) = Some c /\
    rd (d_head t) (update_hash t (d_ins_h t) c) = Some h /\
    wr (d_prev t) (Z.land str (d_w_mask t)) h = Some pv /\
    wr (d_head t) (update_hash t (d_ins_h t) c) (u16 str) = Some hd /\
    r = if u32 (d_lookahead t + u32 (d_insert t - 1)) <? MIN_MATCH
        then inr (fwi t (update_hash t (d_ins_h t) c) pv hd (u32 (d_insert t - 1)))
        else inl (fwi t (update_hash t (d_ins_h t) c) pv hd (u32 (d_insert t - 1)), u32 (str + 1)).
Proof.
  intros Hn H. unfold fw_insert_body in H.
  destruct (d_insert t =? 0) eqn:E; [apply Z.eqb_eq in E; contradiction|].
  inv_bind H. destruct x. apply guard_inv, Z.ltb_lt in Ha.
  inv_bind H. inv_bind H. inv_bind H. inv_bind H.
  exists x, x0, x1, x2. split; [exact Ha|]. split; [exact Ha0|]. split; [exact Ha1|]. split; [exact Ha2|].
  split; [exact Ha3|].
  destruct (_ <? MIN_MATCH); inversion H; reflexivity.
Qed.

(** A load of a defined window byte [Hv : forall d, Znth i (mb_vals ..) = vi c]. *)
Ltac ld_side Hv :=
  lazymatch goal with
  | |- ENTAIL _, _ |-- _ =>
      go_lower; apply prop_right; first [ lia | rewrite Hv; apply tc_val_tuchar_repr; rep_lia ]
  | |- _ => idtac
  end.
Ltac ld_byte Hv := forward; ld_side Hv; rewrite Hv.

Lemma fw_ins : fw_ins_triple.
Proof.
  unfold fw_ins_triple; intros. show_fw_stmt.
  rewrite dfull_in_open. unfold ins_part. Intros.
  fwd. fwd.
  forward_if.
  2: { forward. rewrite unsigned_repr_u32 in H4.
       unfold c_fw_insert in H. destruct (_ >=? _) eqn:Ec in H; [unfold MIN_MATCH in Ec; lia|].
       inversion H; subst s'; clear H.
       rewrite dfull_in_open. unfold ins_part. entailer!. }
  rewrite unsigned_repr_u32 in H4.
  unfold c_fw_insert in H. destruct (_ >=? _) eqn:Ec in H; [|unfold MIN_MATCH in Ec; lia].
  inv_bind H. inv_bind H. inv_bind H. destruct x0. apply guard_inv, Z.ltb_lt in Ha0.
  cbn [d_hash_shift d_window set_d_ins_h] in Ha0, Ha1.
  fwd. fwd. fwd.
  rewrite sub_repr32, <- repr_u32. set (str0 := u32 (d_strstart s - d_insert s)) in *.
  pose proof (ranges_ins s H0) as (Hmb & Hwl & Hpv & Hhd & Hpl & Hhl & Rih & Rhm & Rhs & Rss & Rla & Rin & Rwm).
  unfold u32_ok in Rih, Rhm, Rhs, Rss, Rla, Rin, Rwm.
  destruct (mb_rd_inv _ _ _ Hmb Ha) as (Hi0 & Hv0 & Hc0).
  fwd.
  ld_byte Hv0. fwd.
  destruct (mb_rd_inv _ _ _ Hmb Ha1) as (Hi1 & Hv1 & Hc1).
  rewrite (u32_small (str0 + 1)) in Hi1, Hv1 by rep_lia.
  fwd. fwd. fwd.
  ld_byte Hv1. fwd.
  forward.
  rewrite (update_hash_eq s) by rep_lia.
  assert (Hs1 : set_d_ins_h (set_d_ins_h s x) (update_hash (set_d_ins_h s x) (d_ins_h (set_d_ins_h s x)) x1) =
                fwi s (update_hash s x x1) (d_prev s) (d_head s) (d_insert s)) by reflexivity.
  rewrite Hs1 in H; clear Hs1. apply loop_runs in H.
  forward_loop (EX t : dstate, EX str : Z,
    PROP (runs fw_insert_body (t, str) s'; same_rest s t; dstate_ranges t; 0 <= str; str + 2 <= Int.max_unsigned)
    LOCAL (temp _str (vi str); temp _wsize (vi w); temp _s (p_s p); gvars gv)
    SEP (ins_part t p; ins_rest s z p pin ish msgv gv; deflate_globals gv))
   break: (PROP (dstate_ranges s'; same_rest s s')
    LOCAL (temp _wsize (vi w); temp _s (p_s p); gvars gv)
    SEP (ins_part s' p; ins_rest s z p pin ish msgv gv; deflate_globals gv)).
  { Exists (fwi s (update_hash s x x1) (d_prev s) (d_head s) (d_insert s)) str0.
    unfold ins_part. cbn [fwi set_d_insert set_d_head set_d_prev set_d_ins_h d_strstart d_lookahead d_insert
      d_w_mask d_ins_h d_hash_mask d_hash_shift d_window d_prev d_head].
    entailer!.
    apply ranges_fwi; auto; first [apply update_hash_range | unfold u32_ok; lia]. }
  2: { Intros. rewrite dfull_in_open, (ins_rest_same s s') by auto. entailer!. }
  Intros t str. unfold ins_part. Intros.
  rename H5 into Hrun, H6 into Hsr, H7 into Htr, H8 into Hs0, H9 into Hs2.
  clear Hi0 Hv0 Hc0 Hi1 Hv1 Hc1 Ha Ha1 H.
  pose proof (ranges_ins t Htr) as (Tmb & Twl & Tpv & Thd & Tpl & Thl & Tih & Thm & Ths & Tss & Tla & Tin & Twm).
  unfold u32_ok in Tih, Thm, Ths, Tss, Tla, Tin, Twm.
  fwd. forward_if.
  2: { assert (Hz : d_insert t = 0).
       { apply (f_equal Int.unsigned) in H. rewrite Int.unsigned_repr in H by rep_lia. exact H. }
       assert (Ht : s' = t).
       { eapply runs_exit_eq; [exact Hrun|]. unfold fw_insert_body. rewrite Hz. reflexivity. }
       subst s'. forward. unfold ins_part. entailer!. }
  assert (exists r, fw_insert_body (t, str) = Some r) as (r & Hb)
    by (destruct (runs_inv _ _ _ Hrun) as [?|(? & ? & _)]; eauto).
  destruct (fw_body_step _ _ _ H' Hb) as (c & h & pv & hd & Hsh & Hc & Hh & Hpv' & Hhd' & Hr).
  unfold MIN_MATCH in Hc, Hr. rewrite (u32_small (str + 3 - 1)) in Hc by lia.
  destruct (mb_rd_inv _ _ _ Tmb Hc) as (Hi & Hv & Hcr).
  fwd. fwd. fwd. ld_byte Hv. fwd. forward.
  rewrite (update_hash_eq t) by rep_lia.
  set (ih := update_hash t (d_ins_h t) c) in *.
  destruct (rd_inv _ _ _ Hh) as (Hih & Hhv).
  destruct (wr_inv _ _ _ _ Hpv') as (Hpi & ->).
  destruct (wr_inv _ _ _ _ Hhd') as (_ & ->).
  assert (Hhr : 0 <= Znth ih (d_head t) < 65536) by (apply Forall_Znth; auto).
  fwd. fwd. fwd. fwd. fwd. rewrite Hhv. forward.
  fwd. fwd. forward. forward. fwd. forward. fwd. fwd.
  assert (Hin1 : u32 (d_insert t - 1) = d_insert t - 1) by (apply u32_small; lia).
  assert (Hst1 : u32 (str + 1) = str + 1) by (apply u32_small; lia).
  rewrite Hin1, Hst1 in Hr.
  rewrite sub_repr32, add_repr32, !zext16_repr, Zmod_mod, (Z.mod_small h) by lia.
  change (Vint (Int.repr h)) with (vi h). change (Vint (Int.repr (str mod 65536))) with (vi (u16 str)).
  rewrite !upd_Znth_map.
  set (t' := fwi t ih (upd_Znth (Z.land str (d_w_mask t)) (d_prev t) h) (upd_Znth ih (d_head t) (u16 str))
               (d_insert t - 1)) in Hr.
  assert (Hsr' : same_rest s t') by (apply same_rest_fwi; auto).
  assert (Htr' : dstate_ranges t').
  { apply ranges_fwi; auto.
    all: unfold u32_ok; try rewrite upd_Znth_Zlength by lia.
    all: first [ lia | apply update_hash_range | apply Forall_upd_Znth; [assumption|] ].
    all: first [ rewrite <- Hhv; lia | unfold u16; apply Z.mod_pos_bound; lia ]. }
  forward_if.
  - rewrite unsigned_repr_u32 in H5.
    assert (Hs' : s' = t').
    { eapply runs_exit_eq; [exact Hrun|]. rewrite Hb, Hr.
      replace (u32 (d_lookahead t + (d_insert t - 1)) <? 3) with true; [reflexivity|].
      symmetry. apply Z.ltb_lt. exact H5. }
    subst s'. forward. unfold ins_part, t', fwi.
    cbn [set_d_insert set_d_head set_d_prev set_d_ins_h d_strstart d_lookahead d_insert
      d_w_mask d_ins_h d_hash_mask d_hash_shift d_window d_prev d_head].
    rewrite !upd_Znth_Zlength by lia.
    entailer!.
  - rewrite unsigned_repr_u32 in H5.
    assert (Hrun' : runs fw_insert_body (t', str + 1) s').
    { eapply runs_step_eq; [exact Hrun|]. rewrite Hb, Hr.
      replace (u32 (d_lookahead t + (d_insert t - 1)) <? 3) with false; [reflexivity|].
      symmetry. apply Z.ltb_ge. lia. }
    forward. Exists t' (str + 1). unfold ins_part, t', fwi.
    cbn [set_d_insert set_d_head set_d_prev set_d_ins_h d_strstart d_lookahead d_insert
      d_w_mask d_ins_h d_hash_mask d_hash_shift d_window d_prev d_head].
    rewrite !upd_Znth_Zlength by lia.
    entailer!.
Qed.
