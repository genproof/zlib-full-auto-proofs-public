(** Copy of LTBStatic.v (its proof, under this module name), for LTBEvent.v. *)
(** * deflate_bound theory: the static-code cost of a block

    [DynSum.stat_data syms]: the bits of the block's symbols and END_BLOCK under the static trees (RFC 1951
    3.2.6: literals 0..143 8 bits, 144..255 9 bits, length codes 7 or 8 bits plus extra bits, distance codes 5
    bits plus extra bits). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.huffman.Model Zlib.proof.huffman.Bits Zlib.proof.huffman.BlockBound
               Zlib.proof.huffman.DynSum.
Require Zlib.proof.deflate.DState.
Import ListNotations.
Local Open Scope Z_scope.

Definition syms_valid (syms : list (Z * Z)) : Prop := forall x, In x syms -> valid_sym (fst x) (snd x).

(** ** Helpers *)

Definition sp_lcost (lc : Z) : Z :=
  Znth (Znth lc length_code_tab + 257) static_ltree_len + Znth (Znth lc length_code_tab) extra_lbits.
Definition sp_xd (d : Z) : Z := Znth (d_code d) extra_dbits.

Definition sp_l_ok (lc : Z) : bool :=
  (Znth lc static_ltree_len <=? 9) && (sp_lcost lc <=? 13) && implb (lc =? 0) (sp_lcost lc <=? 7) &&
  (sp_lcost lc <=? 5 * lc + 8) && (sp_lcost lc <=? 9 * lc + 9) && ((lc =? 0) || (2 * sp_lcost lc <=? 13 * lc + 8)).
Definition sp_d_ok (d : Z) : bool :=
  (Znth (d_code d) static_dtree_len =? 5) && (0 <=? sp_xd d) && (sp_xd d <=? 13) &&
  implb (d <=? 4095) (sp_xd d <=? 10) && (2 ^ (sp_xd d + 1) <=? d + 262).

Lemma sp_l_all : check_from sp_l_ok 0 (Z.to_nat 256) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sp_d_all : check_from sp_d_ok 0 (Z.to_nat 32768) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sp_l : forall lc, 0 <= lc <= 255 ->
  Znth lc static_ltree_len <= 9 /\ sp_lcost lc <= 13 /\ (lc = 0 -> sp_lcost lc <= 7) /\ sp_lcost lc <= 5 * lc + 8 /\
  sp_lcost lc <= 9 * lc + 9 /\ (lc <> 0 -> 2 * sp_lcost lc <= 13 * lc + 8).
Proof.
  intros lc Hlc. assert (H := check_from_spec _ _ _ sp_l_all lc ltac:(rewrite Z2Nat.id; lia)).
  unfold sp_l_ok, implb in H. repeat rewrite andb_true_iff in H. destruct H as [[[[[H1 H2] H3] H4] H5] H6].
  rewrite Z.leb_le in H1, H2, H4, H5. split; [lia|]. split; [lia|]. split; [|split; [lia|split; [lia|]]].
  - intros ->. simpl in H3. apply Z.leb_le in H3. exact H3.
  - intros Hne. apply orb_true_iff in H6. destruct H6 as [H6|H6]; [apply Z.eqb_eq in H6; lia|].
    apply Z.leb_le in H6. exact H6.
Qed.

Lemma sp_d : forall d, 0 <= d <= 32767 ->
  Znth (d_code d) static_dtree_len = 5 /\ 0 <= sp_xd d <= 13 /\ (d <= 4095 -> sp_xd d <= 10) /\
  2 ^ (sp_xd d + 1) <= d + 262.
Proof.
  intros d Hd. assert (H := check_from_spec _ _ _ sp_d_all d ltac:(rewrite Z2Nat.id; lia)).
  unfold sp_d_ok, implb in H. repeat rewrite andb_true_iff in H. destruct H as [[[[H1 H2] H3] H4] H5].
  rewrite Z.eqb_eq in H1. rewrite Z.leb_le in H2, H3, H5. split; [lia|]. split; [lia|]. split; [|lia].
  intros Hle. apply Z.leb_le in Hle. rewrite Hle in H4. apply Z.leb_le in H4. exact H4.
Qed.

Lemma sp_cost_match : forall d lc, valid_sym d lc -> d <> 0 ->
  sym_cost static_ltree_len static_dtree_len d lc = sp_lcost lc + 5 + sp_xd (d - 1).
Proof.
  intros d lc [Hl Hd] Hne. unfold sym_cost. destruct (Z.eqb_spec d 0); [lia|].
  destruct (sp_d (d - 1) ltac:(lia)) as [E _]. unfold sp_lcost, sp_xd. rewrite E. lia.
Qed.

Lemma sp_stat_cost : forall syms, syms_valid syms ->
  stat_data syms = cost_sum static_ltree_len static_dtree_len syms + 7.
Proof.
  intros syms Hv. change 7 with (Znth END_BLOCK static_ltree_len).
  rewrite (dc_cost_regroup syms static_ltree_len static_dtree_len Hv). unfold stat_data. f_equal.
Qed.

Lemma sp_sum : forall (a b c : Z) syms,
  (forall x, In x syms -> a * sym_cost static_ltree_len static_dtree_len (fst x) (snd x) <= b * sym_len x + c) ->
  a * cost_sum static_ltree_len static_dtree_len syms <= b * blk_len syms + c * Zlength syms.
Proof.
  intros a b c syms. induction syms as [|[d l] r IH]; intros H.
  - unfold blk_len. simpl. rewrite Zlength_nil. lia.
  - unfold blk_len in *. cbn [cost_sum map]. rewrite Zlength_cons.
    assert (H1 := H (d, l) (or_introl eq_refl)). cbn [fst snd] in H1.
    assert (IH' := IH (fun x Hx => H x (or_intror Hx))).
    cbn [CT.hsum]. lia.
Qed.

Record static_facts : Prop := {
  st_blk_len_ge : forall syms, syms_valid syms -> Zlength syms <= blk_len syms;
  st_stat_9 : forall syms, syms_valid syms -> stat_data syms <= 9 * blk_len syms + 7;
  st_stat_far : forall syms, syms_valid syms ->
  (forall x, In x syms -> fst x <> 0 -> fst x <= 32506) ->
  (forall x, In x syms -> fst x <> 0 -> snd x = 0 -> fst x <= DState.TOO_FAR) ->
  Zlength syms <= 16383 -> 32507 <= blk_len syms ->
  stat_data syms <= 8 * blk_len syms + 37;
  st_stat_win : forall syms wb, syms_valid syms -> 9 <= wb <= 15 ->
  (forall x, In x syms -> fst x <> 0 -> fst x <= 2 ^ wb - 262) ->
  4 * (Zlength syms + 1) <= 2 ^ wb -> 2 ^ wb - 262 < blk_len syms ->
  stat_data syms <= 8 * blk_len syms + 37
}.

Lemma sp_len_ge : forall syms, syms_valid syms -> Zlength syms <= blk_len syms.
Proof.
  induction syms as [|[d l] r IH]; intros Hv.
  - unfold blk_len. simpl. rewrite Zlength_nil. lia.
  - unfold blk_len in *. cbn [map]. rewrite Zlength_cons.
    assert (IH' := IH (fun x Hx => Hv x (or_intror Hx))).
    destruct (Hv (d, l) (or_introl eq_refl)) as [Hl Hd]. cbn [fst snd] in Hl, Hd.
    cbn [CT.hsum]. unfold sym_len at 1. cbn [fst snd]. destruct (d =? 0); lia.
Qed.

Theorem static_proof : static_facts.
Proof.
  constructor.
  - exact sp_len_ge.
  - intros syms Hv. rewrite sp_stat_cost by exact Hv.
    assert (H := sp_sum 1 9 0 syms). cut (1 * cost_sum static_ltree_len static_dtree_len syms <= 9 * blk_len syms + 0 * Zlength syms); [lia|].
    apply H. intros [d l] Hx. destruct (Hv _ Hx) as [Hl Hd]. cbn [fst snd] in *.
    destruct (sp_l l Hl) as [L1 [L2 [L3 [L4 [L5 L6]]]]].
    unfold sym_len. cbn [fst]. destruct (Z.eqb_spec d 0) as [E|E].
    + unfold sym_cost. subst d. rewrite Z.eqb_refl. cbn [snd]. lia.
    + rewrite sp_cost_match by (unfold valid_sym; lia). destruct (sp_d (d - 1) ltac:(lia)) as [D1 [D2 [D3 D4]]].
      cbn [snd]. destruct (Z.eq_dec l 0) as [->|]; [specialize (L3 eq_refl)|]; lia.
  - intros syms Hv Hfar Htoo Hn HB. rewrite sp_stat_cost by exact Hv.
    assert (H := sp_sum 2 13 5 syms).
    cut (2 * cost_sum static_ltree_len static_dtree_len syms <= 13 * blk_len syms + 5 * Zlength syms); [lia|].
    apply H. intros [d l] Hx. destruct (Hv _ Hx) as [Hl Hd]. cbn [fst snd] in *.
    destruct (sp_l l Hl) as [L1 [L2 [L3 [L4 [L5 L6]]]]].
    unfold sym_len. cbn [fst]. destruct (Z.eqb_spec d 0) as [E|E].
    + unfold sym_cost. subst d. rewrite Z.eqb_refl. cbn [snd]. lia.
    + rewrite sp_cost_match by (unfold valid_sym; lia). destruct (sp_d (d - 1) ltac:(lia)) as [D1 [D2 [D3 D4]]].
      cbn [snd]. destruct (Z.eq_dec l 0) as [->|Hl0].
      * specialize (L3 eq_refl). assert (Ht := Htoo _ Hx E eq_refl). cbn [fst] in Ht.
        unfold DState.TOO_FAR in Ht. specialize (D3 ltac:(lia)). lia.
      * specialize (L6 Hl0). lia.
  - intros syms wb Hv Hwb Hfar Hn HB. rewrite sp_stat_cost by exact Hv.
    assert (H := sp_sum 1 5 (wb - 4) syms).
    cut (1 * cost_sum static_ltree_len static_dtree_len syms <= 5 * blk_len syms + (wb - 4) * Zlength syms).
    2:{ apply H. intros [d l] Hx. destruct (Hv _ Hx) as [Hl Hd]. cbn [fst snd] in *.
      destruct (sp_l l Hl) as [L1 [L2 [L3 [L4 [L5 L6]]]]].
      unfold sym_len. cbn [fst]. destruct (Z.eqb_spec d 0) as [E|E].
      + unfold sym_cost. subst d. rewrite Z.eqb_refl. cbn [snd]. lia.
      + rewrite sp_cost_match by (unfold valid_sym; lia). destruct (sp_d (d - 1) ltac:(lia)) as [D1 [D2 [D3 D4]]].
        assert (Hf := Hfar _ Hx E). cbn [fst] in Hf.
        assert (Hx2 : sp_xd (d - 1) + 1 < wb).
        { apply (Z.pow_lt_mono_r_iff 2); [lia|lia|]. lia. }
        cbn [snd]. lia. }
    intros Hc. assert (Hz : 0 <= Zlength syms) by apply Zlength_nonneg.
    assert (wb = 9 \/ wb = 10 \/ wb = 11 \/ wb = 12 \/ wb = 13 \/ wb = 14 \/ wb = 15) as Hw by lia.
    destruct Hw as [->|[->|[->|[->|[->|[->| ->]]]]]]; simpl (2 ^ _) in *; lia.
Qed.

Lemma blk_len_ge : forall syms, syms_valid syms -> Zlength syms <= blk_len syms.
Proof. exact (st_blk_len_ge static_proof). Qed.

Lemma stat_9 : forall syms, syms_valid syms -> stat_data syms <= 9 * blk_len syms + 7.
Proof. exact (st_stat_9 static_proof). Qed.

Lemma stat_far : forall syms, syms_valid syms ->
  (forall x, In x syms -> fst x <> 0 -> fst x <= 32506) ->
  (forall x, In x syms -> fst x <> 0 -> snd x = 0 -> fst x <= DState.TOO_FAR) ->
  Zlength syms <= 16383 -> 32507 <= blk_len syms ->
  stat_data syms <= 8 * blk_len syms + 37.
Proof. exact (st_stat_far static_proof). Qed.

Lemma stat_win : forall syms wb, syms_valid syms -> 9 <= wb <= 15 ->
  (forall x, In x syms -> fst x <> 0 -> fst x <= 2 ^ wb - 262) ->
  4 * (Zlength syms + 1) <= 2 ^ wb -> 2 ^ wb - 262 < blk_len syms ->
  stat_data syms <= 8 * blk_len syms + 37.
Proof. exact (st_stat_win static_proof). Qed.


(** At most 9 bits per byte, plus END_BLOCK. *)

(** memLevel 8 at levels 4..9 (Z_FIXED with buf = NULL): length-3 matches at most TOO_FAR away, at most 16383
    symbols spanning at least 32507 bytes. *)

(** w_bits > hash_bits (so at most w_size / 4 - 1 symbols) with buf = NULL (more than w_size - 262 bytes),
    distances at most w_size - 262. *)
