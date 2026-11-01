(** * The deflateBound accounting for the short laws: deflateBound on the model

    LTBDBound.v's [hdr_bytes_len] / [deflateBound_val] for the gzip headers [hdr_ok_w] (an extra field of up to
    65535 bytes, a name and a comment of up to 2^32-2 bytes: [c_count_str] runs up to 2^32 - 1 times) and any
    n <= 2^63-1 (deflateBound computes in uLong: no wrap-around below 2^64). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTWBDefs.
Require Import Zlib.proof.deflate.LTBDBound.
Import ListNotations.
Local Open Scope Z_scope.

Record dbound_w_facts : Prop := {
  dw_hdr_bytes_len : forall s a, gzh_ok_w s -> 0 <= Zlength (hdr_bytes s a) <= 17179869184;
  dw_deflateBound_val : forall s n a,
    prm s -> status_ok (d_status s) = true -> 0 <= d_wrap s <= 2 -> gzh_ok_w s -> 0 <= n <= 9223372036854775807 ->
    c_deflateBound (Some s) n = Some (Zlength (hdr_bytes s a) + body (bcls_of s) n + tlen (d_wrap s))
}.

(** ** Helpers *)

(** [loop FUEL] runs up to [2 ^ FUEL] iterations: a loop that ends within [2 ^ FUEL] steps gives its result. *)
Lemma loop_dgo_w {A B : Type} (bd : A -> option (A + B)) :
  forall n x r, dgo bd n x = Some (inr r) -> (n <= Nat.pow 2 FUEL)%nat -> loop FUEL bd x = Some r.
Proof.
  intros n x r H Hle. unfold loop. rewrite loop2_dgo.
  rewrite (dgo_mono bd n (Nat.pow 2 FUEL) x r H) by lia. reflexivity.
Qed.

(** [c_count_str] over a name or a comment of [cstr_ok_w] adds its length (with the zero byte). *)
Lemma count_str_val_w : forall o wl, cstr_ok_w o -> 0 <= wl <= 17179869184 ->
  c_count_str o wl = Some (wl + Zlength (cstr_bytes o)).
Proof.
  intros [l|] wl Ho Hwl; simpl; [|rewrite Zlength_nil; f_equal; lia].
  destruct (Ho l eq_refl) as (l0 & -> & Hlen & Hf).
  pose proof (Zlength_nonneg l0).
  apply (loop_dgo_w _ (S (Z.to_nat (Zlength l0)))).
  - rewrite (count_str_dgo l0 (Z.to_nat (Zlength l0)) 0 wl) by (try exact Hf; lia).
    rewrite Zlength_app, Zlength_cons, Zlength_nil. f_equal. f_equal. lia.
  - assert (Z.of_nat (S (Z.to_nat (Zlength l0))) <= Z.of_nat (Nat.pow 2 FUEL)).
    { rewrite Nat2Z.inj_pow. unfold FUEL. simpl (Z.of_nat 2). simpl (Z.of_nat 40). lia. }
    lia.
Qed.

Lemma cstr_len_w : forall o, cstr_ok_w o -> 0 <= Zlength (cstr_bytes o) <= 4294967295.
Proof.
  intros [l|] Ho; simpl; [|rewrite Zlength_nil; lia].
  destruct (Ho l eq_refl) as (l0 & -> & Hlen & _).
  rewrite Zlength_app, Zlength_cons, Zlength_nil. pose proof (Zlength_nonneg l0). lia.
Qed.

(** The length of a gzip header of [hdr_ok_w]. *)
Lemma gz_hdr_len_w : forall h x, hdr_ok_w h ->
  Zlength (gz_hdr_bytes (Some h) x) =
  10 + exlen h + Zlength (cstr_bytes (gz_name h)) + Zlength (cstr_bytes (gz_comment h)) +
  (if gz_hcrc h =? 0 then 0 else 2).
Proof.
  intros h x (_ & _ & _ & _ & Hxl & Hx & _ & _).
  unfold gz_hdr_bytes, gz_body, exlen, gz_extra_bytes.
  rewrite !Zlength_app.
  replace (Zlength (gz_pre h x)) with 10 by reflexivity.
  destruct (gz_hcrc h =? 0);
  [replace (Zlength (@nil Z)) with 0 by reflexivity
  |match goal with |- context [Zlength [?a; ?b]] => replace (Zlength [a; b]) with 2 by reflexivity end];
  (destruct (gz_extra h) as [l|] eqn:E;
   [destruct (Hx l eq_refl) as [Hl _];
    rewrite Zlength_app, Zlength_map; replace (Zlength [Z.land (gz_extra_len h) 255;
      Z.land (Z.shiftr (gz_extra_len h) 8) 255]) with 2 by reflexivity;
    replace (Z.land (gz_extra_len h) 65535) with (gz_extra_len h)
      by (symmetry; change 65535 with (Z.ones 16); rewrite Z.land_ones by lia; apply Z.mod_small; lia);
    rewrite Zlength_sublist by lia; lia
   | rewrite Zlength_nil; lia]).
Qed.

Lemma hdr_len_le_w : forall s a, gzh_ok_w s -> 0 <= Zlength (hdr_bytes s a) <= 17179869184.
Proof.
  intros s a Hg. unfold hdr_bytes.
  destruct (d_wrap s =? 1).
  { unfold zlib_hdr_bytes, msb2. destruct (d_strstart s =? 0); reflexivity || (split; discriminate). }
  destruct (d_wrap s =? 2); [|rewrite Zlength_nil; lia].
  destruct (d_gzhead s) as [h|] eqn:E; [|split; discriminate].
  pose proof (Hg h E) as Hh. rewrite gz_hdr_len_w by exact Hh.
  destruct Hh as (_ & Hc & _ & _ & Hxl & _ & Hn & Hm).
  pose proof (cstr_len_w _ Hn). pose proof (cstr_len_w _ Hm).
  unfold exlen. destruct (gz_extra h), (gz_hcrc h =? 0); lia.
Qed.

(** [n >> k] is at most [n / 2^k]: the sums of deflateBound stay below [2^64] for [n <= 2^63-1]. *)
Lemma shiftr_mul_w : forall n k p, 0 <= n -> 0 <= k -> p = 2 ^ k -> 0 <= Z.shiftr n k /\ p * Z.shiftr n k <= n.
Proof.
  intros n k p Hn Hk ->. rewrite Z.shiftr_div_pow2 by lia.
  assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia].
Qed.

Theorem dbound_w_proof : dbound_w_facts.
Proof.
  constructor.
  - exact hdr_len_le_w.
  - intros s n a Hp Hst Hw Hg Hn.
    unfold c_deflateBound, c_deflateBound_z, bad_state, c_deflateStateCheck. rewrite Hst.
    cbn [Z.eqb Pos.eqb negb]. replace (d_wrap s <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
    cbv beta iota. cbn [bind].
    pose proof (shiftr_mul_w n 3 8 ltac:(lia) ltac:(lia) eq_refl).
    pose proof (shiftr_mul_w n 5 32 ltac:(lia) ltac:(lia) eq_refl).
    pose proof (shiftr_mul_w n 7 128 ltac:(lia) ltac:(lia) eq_refl).
    pose proof (shiftr_mul_w n 8 256 ltac:(lia) ltac:(lia) eq_refl).
    pose proof (shiftr_mul_w n 9 512 ltac:(lia) ltac:(lia) eq_refl).
    pose proof (shiftr_mul_w n 11 2048 ltac:(lia) ltac:(lia) eq_refl).
    pose proof (shiftr_mul_w n 12 4096 ltac:(lia) ltac:(lia) eq_refl).
    pose proof (shiftr_mul_w n 14 16384 ltac:(lia) ltac:(lia) eq_refl).
    pose proof (shiftr_mul_w n 25 33554432 ltac:(lia) ltac:(lia) eq_refl).
    replace (u64 (n + Z.shiftr n 3 + Z.shiftr n 8 + Z.shiftr n 9 + 4))
      with (n + Z.shiftr n 3 + Z.shiftr n 8 + Z.shiftr n 9 + 4) by (unfold u64; symmetry; apply Z.mod_small; lia).
    replace (u64 (n + Z.shiftr n 5 + Z.shiftr n 7 + Z.shiftr n 11 + 7))
      with (n + Z.shiftr n 5 + Z.shiftr n 7 + Z.shiftr n 11 + 7) by (unfold u64; symmetry; apply Z.mod_small; lia).
    rewrite (proj2 (Z.ltb_ge (n + Z.shiftr n 3 + Z.shiftr n 8 + Z.shiftr n 9 + 4) n)) by lia.
    rewrite (proj2 (Z.ltb_ge (n + Z.shiftr n 5 + Z.shiftr n 7 + Z.shiftr n 11 + 7) n)) by lia.
    match goal with |- bind ?X _ = _ =>
      assert (HW : X = Some (Zlength (hdr_bytes s a) + tlen (d_wrap s))) end.
    { unfold hdr_bytes, tlen.
      assert (Hw3 : d_wrap s = 0 \/ d_wrap s = 1 \/ d_wrap s = 2) by lia.
      destruct Hw3 as [-> | [-> | ->]]; cbn [Z.eqb Pos.eqb]; [reflexivity| |].
      - unfold zlib_hdr_bytes, msb2. destruct (d_strstart s =? 0); reflexivity.
      - destruct (d_gzhead s) as [h|] eqn:E; [|reflexivity].
        pose proof (Hg h E) as Hh. rewrite gz_hdr_len_w by exact Hh.
        destruct Hh as (_ & Hc & _ & _ & Hxl & _ & Hnm & Hcm).
        pose proof (cstr_len_w _ Hnm). pose proof (cstr_len_w _ Hcm).
        assert (Hx : match gz_extra h with Some _ => u64 (18 + u32 (2 + gz_extra_len h)) | None => 18 end
                     = 18 + exlen h).
        { unfold exlen. destruct (gz_extra h); [|lia]. unfold u64, u32.
          rewrite (Z.mod_small (2 + gz_extra_len h)) by lia. rewrite Z.mod_small by lia. lia. }
        rewrite Hx. assert (0 <= exlen h <= 65537) by (unfold exlen; destruct (gz_extra h); lia).
        rewrite count_str_val_w by (auto; lia). cbn [bind].
        rewrite count_str_val_w by (auto; lia). cbn [bind].
        f_equal. destruct (gz_hcrc h =? 0); [lia|].
        unfold u64. rewrite Z.mod_small by lia. lia. }
    rewrite HW. cbn [bind].
    assert (HL : 0 <= Zlength (hdr_bytes s a) + tlen (d_wrap s) <= 17179869300).
    { pose proof (hdr_len_le_w s a Hg). unfold tlen.
      destruct (d_wrap s =? 1); [lia|]. destruct (d_wrap s =? 2); lia. }
    replace (Zlength (hdr_bytes s a) + body (bcls_of s) n + tlen (d_wrap s))
      with (body (bcls_of s) n + (Zlength (hdr_bytes s a) + tlen (d_wrap s))) by ring.
    revert HL. generalize (Zlength (hdr_bytes s a) + tlen (d_wrap s)). intros wl HL.
    unfold bcls_of, tight_b, body.
    destruct (d_w_bits s =? 15), (d_hash_bits s =? 8 + 7),
      ((d_strategy s =? Z_FIXED) && (d_level s >=? 1) && (d_level s <=? 3)),
      ((d_w_bits s <=? d_hash_bits s) && negb (d_level s =? 0)); cbn [negb orb andb];
      unfold u64; rewrite Z.mod_small by lia; rewrite (proj2 (Z.ltb_ge _ _)) by lia; f_equal; lia.
Qed.

Lemma hdr_bytes_len_w : forall s a, gzh_ok_w s -> 0 <= Zlength (hdr_bytes s a) <= 17179869184.
Proof. exact (dw_hdr_bytes_len dbound_w_proof). Qed.

Lemma deflateBound_val_w : forall s n a,
  prm s -> status_ok (d_status s) = true -> 0 <= d_wrap s <= 2 -> gzh_ok_w s -> 0 <= n <= 9223372036854775807 ->
  c_deflateBound (Some s) n = Some (Zlength (hdr_bytes s a) + body (bcls_of s) n + tlen (d_wrap s)).
Proof. exact (dw_deflateBound_val dbound_w_proof). Qed.
