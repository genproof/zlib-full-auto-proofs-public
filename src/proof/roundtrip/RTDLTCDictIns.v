(** * deflateSetDictionary: the insertion loop of deflateSetDictionary
    ([do { UPDATE_HASH; prev[str & w_mask] = head[ins_h]; head[ins_h] = str; str++; } while (--n);])
    for positions below w_size. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDLTCDictKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.


(** ** Helpers *)
Definition sdT (s : dstate) (h : Z) (P H : list Z) : dstate := set_d_head (set_d_prev (set_d_ins_h s h) P) H.

Lemma sdT_window s h P H : d_window (sdT s h P H) = d_window s. Proof. destruct s; reflexivity. Qed.
Lemma sdT_hash_shift s h P H : d_hash_shift (sdT s h P H) = d_hash_shift s. Proof. destruct s; reflexivity. Qed.
Lemma sdT_hash_mask s h P H : d_hash_mask (sdT s h P H) = d_hash_mask s. Proof. destruct s; reflexivity. Qed.
Lemma sdT_w_mask s h P H : d_w_mask (sdT s h P H) = d_w_mask s. Proof. destruct s; reflexivity. Qed.
Lemma sdT_ins_h s h P H : d_ins_h (sdT s h P H) = h. Proof. destruct s; reflexivity. Qed.

Lemma sdT_step_states s h P H ih P2 H2 :
  set_d_head (set_d_prev (set_d_ins_h (sdT s h P H) ih) P2) H2 = sdT s ih P2 H2 /\
  d_head (set_d_ins_h (sdT s h P H) ih) = H /\ d_ins_h (set_d_ins_h (sdT s h P H) ih) = ih /\
  d_prev (set_d_ins_h (sdT s h P H) ih) = P /\
  d_head (set_d_prev (set_d_ins_h (sdT s h P H) ih) P2) = H /\
  d_ins_h (set_d_prev (set_d_ins_h (sdT s h P H) ih) P2) = ih /\
  d_window (set_d_ins_h (sdT s h P H) ih) = d_window s /\
  d_w_mask (set_d_ins_h (sdT s h P H) ih) = d_w_mask s.
Proof. destruct s; repeat split; reflexivity. Qed.

Lemma update_hash_sdT s h P H x c : update_hash (sdT s h P H) x c = update_hash s x c.
Proof. unfold update_hash. rewrite sdT_hash_shift, sdT_hash_mask. reflexivity. Qed.

Lemma update_hash_range s x c : prm s -> 0 <= update_hash s x c < d_hash_size s.
Proof.
  intros Hp. destruct Hp as (_ & _ & _ & Hhb & Hhs & Hhm & _).
  unfold update_hash. rewrite Hhm, Hhs.
  replace (2 ^ d_hash_bits s - 1) with (Z.ones (d_hash_bits s)) by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_ones by lia.
  assert (0 <= 2 ^ d_hash_bits s <= 2 ^ 16) by (split; [lia| apply Z.pow_le_mono_r; lia]).
  unfold u32. rewrite (Z.mod_small (_ mod _)).
  - apply Z.mod_pos_bound; lia.
  - pose proof (Z.mod_pos_bound (Z.lxor (Z.shiftl x (d_hash_shift s) mod 4294967296) c) (2 ^ d_hash_bits s)
      ltac:(lia)). lia.
Qed.

Lemma land_small_mask s p : prm s -> 0 <= p < d_w_size s -> Z.land p (d_w_mask s) = p.
Proof.
  intros Hp Hr. destruct Hp as (Hwb & Hws & Hwm & _).
  rewrite Hwm, Hws in *.
  replace (2 ^ d_w_bits s - 1) with (Z.ones (d_w_bits s)) by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

Lemma w_size_bound s : prm s -> d_w_size s <= 32768.
Proof.
  intros Hp. destruct Hp as (Hwb & Hws & _). rewrite Hws.
  change 32768 with (2 ^ 15). apply Z.pow_le_mono_r; lia.
Qed.

Lemma hash_shift_lt s : prm s -> d_hash_shift s < 32.
Proof.
  intros Hp. destruct Hp as (_ & _ & _ & Hhb & _ & _ & Hsh & _). rewrite Hsh.
  apply Z.div_lt_upper_bound; lia.
Qed.

(** One iteration of the insertion loop at position [p] below w_size. *)
Lemma sd_step s h P H p m :
  prm s -> wstruct s -> 0 <= p -> p + 2 < d_w_size s -> 1 <= m <= d_w_size s ->
  Zlength P = Zlength (d_prev s) -> Zlength H = Zlength (d_head s) ->
  Znth (p + 2) (mb_def (d_window s)) = true ->
  let ih := update_hash s h (Znth (p + 2) (mb_val (d_window s))) in
  sd_insert_body (sdT s h P H, p, m) =
    Some (if m - 1 =? 0 then inr (sdT s ih (upd_Znth p P (Znth ih H)) (upd_Znth ih H p), p + 1)
          else inl (sdT s ih (upd_Znth p P (Znth ih H)) (upd_Znth ih H p), p + 1, m - 1)).
Proof.
  intros Hp Hw H0 Hpw Hm HP HH Hdef ih.
  pose proof (w_size_bound s Hp) as Hwb.
  destruct Hw as (Hwl & Hwok & _ & Hpl & Hhl).
  unfold sd_insert_body.
  rewrite sdT_hash_shift. pose proof (hash_shift_lt s Hp) as Hsh.
  replace (d_hash_shift s <? 32) with true by (symmetry; apply Z.ltb_lt; lia).
  cbn [bind guard].
  rewrite sdT_window.
  replace (u32 (p + (MIN_MATCH - 1))) with (p + 2) by (unfold u32, MIN_MATCH; rewrite Z.mod_small; lia).
  unfold mb_rd. rewrite Hdef.
  replace (in_range (p + 2) (Zlength (mb_val (d_window s)))) with true
    by (symmetry; unfold in_range; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
  cbn [andb bind].
  rewrite update_hash_sdT, sdT_ins_h. fold ih.
  pose proof (update_hash_range s h (Znth (p + 2) (mb_val (d_window s))) Hp) as Hih. fold ih in Hih.
  destruct (sdT_step_states s h P H ih (upd_Znth p P (Znth ih H)) (upd_Znth ih H p))
    as (Est & Eh1 & Ei1 & Ep1 & Eh2 & Ei2 & Ewin & Ewm).
  rewrite Eh1, Ei1, Ep1, Ewm.
  unfold rd. replace (in_range ih (Zlength H)) with true
    by (symmetry; unfold in_range; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
  cbn [bind].
  rewrite (land_small_mask s p Hp) by lia.
  unfold wr. replace (in_range p (Zlength P)) with true
    by (symmetry; unfold in_range; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
  cbn [bind].
  rewrite Eh2, Ei2.
  replace (in_range ih (Zlength H)) with true
    by (symmetry; unfold in_range; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
  cbn [bind].
  replace (u16 p) with p by (unfold u16; rewrite Z.mod_small; lia).
  rewrite Est.
  replace (u32 (p + 1)) with (p + 1) by (unfold u32; rewrite Z.mod_small; lia).
  replace (u32 (m - 1)) with (m - 1) by (unfold u32; rewrite Z.mod_small; lia).
  destruct (m - 1 =? 0); reflexivity.
Qed.

(** The master lemma: all properties at once, with a generic predicate on the head entries. *)
Lemma sd_ins_all : forall s str nn (Q : Z -> Prop),
  prm s -> wstruct s -> 0 <= str -> 1 <= nn -> str + nn + 2 <= d_w_size s ->
  (forall i, 0 <= i < str + nn + 2 -> Znth i (mb_def (d_window s)) = true) ->
  exists h P H,
    loop FUEL sd_insert_body (s, str, nn) = Some (sdT s h P H, str + nn) /\
    Zlength P = Zlength (d_prev s) /\ Zlength H = Zlength (d_head s) /\
    (heads_lt (d_w_size s) (d_head s) -> heads_lt (d_w_size s) H) /\
    (chains str (d_head s) (d_prev s) -> chains (str + nn) H P) /\
    ((forall i, 0 <= i < Zlength (d_head s) -> Q (Znth i (d_head s))) -> (forall p, str <= p < str + nn -> Q p) ->
     forall i, 0 <= i < Zlength H -> Q (Znth i H)).
Proof.
  intros s str nn Q Hp Hw Hs Hn Hb Hdef.
  pose proof (w_size_bound s Hp) as Hwb.
  set (QH := fun H : list Z => forall i, 0 <= i < Zlength H -> Q (Znth i H)).
  set (inv := fun a : dstate * Z * Z => let '(s', p, m) := a in
    exists h P H, s' = sdT s h P H /\ p + m = str + nn /\ str <= p /\ 1 <= m /\
      Zlength P = Zlength (d_prev s) /\ Zlength H = Zlength (d_head s) /\
      (heads_lt (d_w_size s) (d_head s) -> heads_lt (d_w_size s) H) /\
      (chains str (d_head s) (d_prev s) -> chains p H P) /\
      (QH (d_head s) -> (forall q, str <= q < str + nn -> Q q) -> QH H)).
  set (Post := fun b : dstate * Z => exists h P H, b = (sdT s h P H, str + nn) /\
      Zlength P = Zlength (d_prev s) /\ Zlength H = Zlength (d_head s) /\
      (heads_lt (d_w_size s) (d_head s) -> heads_lt (d_w_size s) H) /\
      (chains str (d_head s) (d_prev s) -> chains (str + nn) H P) /\
      (QH (d_head s) -> (forall q, str <= q < str + nn -> Q q) -> QH H)).
  assert (Hloop : exists b, loop FUEL sd_insert_body (s, str, nn) = Some b /\ Post b).
  { apply (loop_measure sd_insert_body inv Post (fun a => let '(_, _, m) := a in m) FUEL).
    - intros [[s' p] m] (h & P & H & _ & _ & _ & Hm & _). lia.
    - intros [[s' p] m] (h & P & H & -> & Hpm & Hsp & Hm & HP & HH & Hlt & Hch & HQ).
      assert (Hd : Znth (p + 2) (mb_def (d_window s)) = true) by (apply Hdef; lia).
      rewrite (sd_step s h P H p m Hp Hw ltac:(lia) ltac:(lia) ltac:(lia) HP HH Hd).
      set (ih := update_hash s h (Znth (p + 2) (mb_val (d_window s)))).
      pose proof (update_hash_range s h (Znth (p + 2) (mb_val (d_window s))) Hp) as Hih. fold ih in Hih.
      destruct Hw as (_ & _ & _ & Hpl & Hhl).
      assert (Hih' : 0 <= ih < Zlength H) by lia.
      assert (Hpp : 0 <= p < Zlength P) by lia.
      set (P2 := upd_Znth p P (Znth ih H)). set (H2 := upd_Znth ih H p).
      assert (LP : Zlength P2 = Zlength (d_prev s)) by (unfold P2; rewrite upd_Znth_Zlength; lia).
      assert (LH : Zlength H2 = Zlength (d_head s)) by (unfold H2; rewrite upd_Znth_Zlength; lia).
      assert (Lt2 : heads_lt (d_w_size s) (d_head s) -> heads_lt (d_w_size s) H2).
      { intros Hl i Hi. specialize (Hlt Hl). unfold H2 in *. rewrite upd_Znth_Zlength in Hi by lia.
        destruct (Z.eq_dec i ih) as [->|Hne].
        - rewrite upd_Znth_same by lia. lia.
        - rewrite upd_Znth_diff by lia. apply Hlt. lia. }
      assert (Ch2 : chains str (d_head s) (d_prev s) -> chains (p + 1) H2 P2).
      { intros Hc. destruct (Hch Hc) as [Ch Cp]. split.
        - intros i Hi. unfold H2 in *. rewrite upd_Znth_Zlength in Hi by lia.
          destruct (Z.eq_dec i ih) as [->|Hne].
          + rewrite upd_Znth_same by lia. unfold inG. lia.
          + rewrite upd_Znth_diff by lia. specialize (Ch i ltac:(lia)). unfold inG in *. lia.
        - intros q Hq. unfold P2.
          destruct (Z.eq_dec q p) as [->|Hne].
          + rewrite upd_Znth_same by lia. specialize (Ch ih Hih'). unfold inG in *. lia.
          + rewrite upd_Znth_diff by lia. specialize (Cp q ltac:(lia)). unfold inG in *. lia. }
      assert (Q2 : QH (d_head s) -> (forall q, str <= q < str + nn -> Q q) -> QH H2).
      { intros Q0 Qi i Hi. specialize (HQ Q0 Qi). unfold H2 in *. rewrite upd_Znth_Zlength in Hi by lia.
        destruct (Z.eq_dec i ih) as [->|Hne].
        - rewrite upd_Znth_same by lia. apply Qi. lia.
        - rewrite upd_Znth_diff by lia. apply HQ. lia. }
      destruct (Z.eqb_spec (m - 1) 0) as [E|E].
      + eexists. split; [reflexivity|].
        exists ih, P2, H2. split; [f_equal; lia|].
        split; [exact LP|]. split; [exact LH|]. split; [exact Lt2|].
        split; [replace (str + nn) with (p + 1) by lia; exact Ch2|exact Q2].
      + eexists. split; [reflexivity|]. split; [|lia].
        exists ih, P2, H2. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|].
        split; [exact LP|]. split; [exact LH|]. split; [exact Lt2|]. split; [exact Ch2|exact Q2].
    - exists (d_ins_h s), (d_prev s), (d_head s). split.
      + unfold sdT. destruct s; reflexivity.
      + split; [lia|]. split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
        split; [auto|]. split; [auto|]. auto.
    - cbn [inv]. unfold FUEL. assert (2 ^ 15 < 2 ^ Z.of_nat 40) by (apply Z.pow_lt_mono_r; lia). lia. }
  destruct Hloop as (b & E & h & P & H & -> & HP & HH & Hlt & Hch & HQ).
  exists h, P, H. split; [exact E|]. split; [exact HP|]. split; [exact HH|]. split; [exact Hlt|].
  split; [exact Hch|]. exact HQ.
Qed.

(** Needed for level 0 with a pending slide (heads only known to be <= w_size, possibly
    negative): every final head entry is an initial head entry or an inserted position. *)
Lemma sd_ins_heads : forall s str nn (Q : Z -> Prop),
  prm s -> wstruct s -> 0 <= str -> 1 <= nn -> str + nn + 2 <= d_w_size s ->
  (forall i, 0 <= i < str + nn + 2 -> Znth i (mb_def (d_window s)) = true) ->
  (forall i, 0 <= i < Zlength (d_head s) -> Q (Znth i (d_head s))) -> (forall p, str <= p < str + nn -> Q p) ->
  exists h P H,
    loop FUEL sd_insert_body (s, str, nn) = Some (set_d_head (set_d_prev (set_d_ins_h s h) P) H, str + nn) /\
    (forall i, 0 <= i < Zlength H -> Q (Znth i H)).
Proof.
  intros s str nn Q Hp Hw Hs Hn Hb Hdef HQ0 HQi.
  destruct (sd_ins_all s str nn Q Hp Hw Hs Hn Hb Hdef) as (h & P & H & E & _ & _ & _ & _ & HQ).
  exists h, P, H. split; [exact E|]. exact (HQ HQ0 HQi).
Qed.

Lemma sd_ins_ok : forall s str nn,
  prm s -> wstruct s -> 0 <= str -> 1 <= nn -> str + nn + 2 <= d_w_size s ->
  (forall i, 0 <= i < str + nn + 2 -> Znth i (mb_def (d_window s)) = true) ->
  exists h P H,
    loop FUEL sd_insert_body (s, str, nn) = Some (set_d_head (set_d_prev (set_d_ins_h s h) P) H, str + nn) /\
    Zlength P = Zlength (d_prev s) /\ Zlength H = Zlength (d_head s) /\
    (heads_lt (d_w_size s) (d_head s) -> heads_lt (d_w_size s) H) /\
    (chains str (d_head s) (d_prev s) -> chains (str + nn) H P).
Proof.
  intros s str nn Hp Hw Hs Hn Hb Hdef.
  destruct (sd_ins_all s str nn (fun _ => True) Hp Hw Hs Hn Hb Hdef) as (h & P & H & E & HP & HH & Hlt & Hch & _).
  exists h, P, H. split; [exact E|]. split; [exact HP|]. split; [exact HH|]. split; [exact Hlt|exact Hch].
Qed.
