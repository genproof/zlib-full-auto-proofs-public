(** * deflate_bound theory: deflateBound and compressBound on the model

    wraplen = the header bytes deflate() writes ([hdr_bytes], LTDefs) + the trailer ([tlen]); the gzip loops
    [c_count_str] over the name and the comment of the harness's header (hdr_ok: zero-free with one zero byte). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTBArith.
Import ListNotations.
Local Open Scope Z_scope.

Record dbound_facts : Prop := {
  db_hdr_bytes_len : forall s a, gzh_ok s -> 0 <= Zlength (hdr_bytes s a) <= 16384;
  db_deflateBound_val : forall s n a,
  prm s -> status_ok (d_status s) = true -> 0 <= d_wrap s <= 2 -> gzh_ok s -> 0 <= n <= 1048576 ->
  c_deflateBound (Some s) n = Some (Zlength (hdr_bytes s a) + body (bcls_of s) n + tlen (d_wrap s));
  db_compressBound_val : forall n, 0 <= n <= 1048576 -> c_compressBound n = body BTight n + 6;
  db_hdr_bytes_zlib_nodict : forall s a, d_wrap s = 1 -> d_strstart s = 0 -> Zlength (hdr_bytes s a) = 2
}.

(** ** Helpers *)

(** [loop2] as [2 ^ d] iterations. *)
Section Go.
Context {A B : Type} (bd : A -> option (A + B)).

Fixpoint dgo (n : nat) (x : A) : option (A + B) :=
  match n with
  | O => Some (inl x)
  | S n' => match bd x with Some (inl x') => dgo n' x' | r => r end
  end.

Lemma dgo_add : forall n m x, dgo (n + m) x = match dgo n x with Some (inl x') => dgo m x' | r => r end.
Proof.
  induction n as [|n IH]; intros m x; simpl; [reflexivity|].
  destruct (bd x) as [[x'|r]|]; auto.
Qed.

Lemma loop2_dgo : forall d x, loop2 d bd x = dgo (Nat.pow 2 d) x.
Proof.
  induction d as [|d IH]; intros x.
  - simpl. destruct (bd x) as [[x'|r]|]; reflexivity.
  - change (Nat.pow 2 (S d)) with (Nat.pow 2 d + (Nat.pow 2 d + 0))%nat.
    rewrite Nat.add_0_r, dgo_add. simpl. rewrite IH.
    destruct (dgo (Nat.pow 2 d) x) as [[x'|r]|]; auto.
Qed.

Lemma dgo_mono : forall n m x r, dgo n x = Some (inr r) -> (n <= m)%nat -> dgo m x = Some (inr r).
Proof.
  intros n m x r H Hle. replace m with (n + (m - n))%nat by lia. rewrite dgo_add, H. reflexivity.
Qed.

Lemma loop_dgo : forall n x r, dgo n x = Some (inr r) -> (n <= Nat.pow 2 13)%nat -> loop FUEL bd x = Some r.
Proof.
  intros n x r H Hle. unfold loop. rewrite loop2_dgo.
  assert (Hp : (Nat.pow 2 13 <= Nat.pow 2 FUEL)%nat) by (apply Nat.pow_le_mono_r; unfold FUEL; lia).
  rewrite (dgo_mono n (Nat.pow 2 FUEL) x r H) by lia. reflexivity.
Qed.
End Go.

Lemma count_str_dgo : forall l0 k i wl,
  Forall (fun b => 0 < b < 256) l0 -> 0 <= i -> i + Z.of_nat k = Zlength l0 -> 0 <= wl ->
  wl + Z.of_nat k + 1 < 18446744073709551616 ->
  dgo (strlen_body (l0 ++ [0])) (S k) (i, wl) = Some (inr (wl + Z.of_nat k + 1)).
Proof.
  intros l0 k. induction k as [|k IH]; intros i wl Hf Hi Hk Hwl Hb.
  - simpl. unfold strlen_body, rd, in_range. unfold u64. rewrite Z.mod_small by lia.
    replace (Zlength (l0 ++ [0])) with (Zlength l0 + 1) by (rewrite Zlength_app; reflexivity).
    match goal with |- context [ (0 <=? i) && ?X ] => replace ((0 <=? i) && X) with true
      by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia) end.
    simpl. rewrite app_Znth2 by lia. replace (i - Zlength l0) with 0 by lia. simpl.
    f_equal. f_equal. lia.
  - cbn [dgo]. unfold strlen_body at 1, rd, in_range. unfold u64. rewrite Z.mod_small by lia.
    replace (Zlength (l0 ++ [0])) with (Zlength l0 + 1) by (rewrite Zlength_app; reflexivity).
    match goal with |- context [ (0 <=? i) && ?X ] => replace ((0 <=? i) && X) with true
      by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia) end.
    simpl. rewrite app_Znth1 by lia.
    assert (Hnz : 0 < Znth i l0 < 256) by (apply (Forall_Znth _ _ i) in Hf; [exact Hf | lia]).
    replace (Znth i l0 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    change (dgo (strlen_body (l0 ++ [0])) (S k) (i + 1, wl + 1) = Some (inr (wl + Z.of_nat (S k) + 1))).
    rewrite Nat2Z.inj_succ in *. rewrite (IH (i + 1) (wl + 1)) by (auto; lia). f_equal. f_equal. lia.
Qed.

Lemma count_str_val : forall o wl, cstr_ok o -> 0 <= wl <= 1000000 ->
  c_count_str o wl = Some (wl + Zlength (cstr_bytes o)).
Proof.
  intros [l|] wl Ho Hwl; simpl; [|rewrite Zlength_nil; f_equal; lia].
  destruct (Ho l eq_refl) as (l0 & -> & Hlen & Hf).
  pose proof (Zlength_nonneg l0).
  apply (loop_dgo _ (S (Z.to_nat (Zlength l0)))).
  - rewrite (count_str_dgo l0 (Z.to_nat (Zlength l0)) 0 wl) by (try exact Hf; lia).
    rewrite Zlength_app, Zlength_cons, Zlength_nil. f_equal. f_equal. lia.
  - assert (Z.of_nat (S (Z.to_nat (Zlength l0))) <= Z.of_nat (Nat.pow 2 13)).
    { rewrite Nat2Z.inj_pow. simpl (Z.of_nat 2). simpl (Z.of_nat 13). lia. }
    lia.
Qed.

Lemma shiftr_rng : forall n k, 0 <= n -> 0 <= k -> 0 <= Z.shiftr n k <= n.
Proof.
  intros n k Hn Hk. rewrite Z.shiftr_div_pow2 by lia.
  assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; nia.
Qed.

Definition exlen (h : gzh) : Z := match gz_extra h with Some _ => 2 + gz_extra_len h | None => 0 end.

Lemma cstr_len : forall o, cstr_ok o -> 0 <= Zlength (cstr_bytes o) <= 4097.
Proof.
  intros [l|] Ho; simpl; [|rewrite Zlength_nil; lia].
  destruct (Ho l eq_refl) as (l0 & -> & Hlen & _).
  rewrite Zlength_app, Zlength_cons, Zlength_nil. pose proof (Zlength_nonneg l0). lia.
Qed.

Lemma gz_hdr_len : forall h x, hdr_ok h ->
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

Lemma hdr_len_le : forall s a, gzh_ok s -> 0 <= Zlength (hdr_bytes s a) <= 16384.
Proof.
  intros s a Hg. unfold hdr_bytes.
  destruct (d_wrap s =? 1).
  { unfold zlib_hdr_bytes, msb2. destruct (d_strstart s =? 0); reflexivity || (split; discriminate). }
  destruct (d_wrap s =? 2); [|rewrite Zlength_nil; lia].
  destruct (d_gzhead s) as [h|] eqn:E; [|split; discriminate].
  pose proof (Hg h E) as Hh. rewrite gz_hdr_len by exact Hh.
  destruct Hh as (_ & Hc & _ & _ & Hxl & _ & Hn & Hm).
  pose proof (cstr_len _ Hn). pose proof (cstr_len _ Hm).
  unfold exlen. destruct (gz_extra h), (gz_hcrc h =? 0); lia.
Qed.

Theorem dbound_proof : dbound_facts.
Proof.
  constructor.
  - exact hdr_len_le.
  - intros s n a Hp Hst Hw Hg Hn.
    unfold c_deflateBound, c_deflateBound_z, bad_state, c_deflateStateCheck. rewrite Hst.
    cbn [Z.eqb Pos.eqb negb]. replace (d_wrap s <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
    cbv beta iota. cbn [bind].
    pose proof (shiftr_rng n 3). pose proof (shiftr_rng n 8). pose proof (shiftr_rng n 9).
    pose proof (shiftr_rng n 5). pose proof (shiftr_rng n 7). pose proof (shiftr_rng n 11).
    pose proof (shiftr_rng n 12). pose proof (shiftr_rng n 14). pose proof (shiftr_rng n 25).
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
        pose proof (Hg h E) as Hh. rewrite gz_hdr_len by exact Hh.
        destruct Hh as (_ & Hc & _ & _ & Hxl & _ & Hnm & Hcm).
        pose proof (cstr_len _ Hnm). pose proof (cstr_len _ Hcm).
        assert (Hx : match gz_extra h with Some _ => u64 (18 + u32 (2 + gz_extra_len h)) | None => 18 end
                     = 18 + exlen h).
        { unfold exlen. destruct (gz_extra h); [|lia]. unfold u64, u32.
          rewrite (Z.mod_small (2 + gz_extra_len h)) by lia. rewrite Z.mod_small by lia. lia. }
        rewrite Hx. assert (0 <= exlen h <= 4098) by (unfold exlen; destruct (gz_extra h); lia).
        rewrite count_str_val by (auto; lia). cbn [bind].
        rewrite count_str_val by (auto; lia). cbn [bind].
        f_equal. destruct (gz_hcrc h =? 0); [lia|].
        unfold u64. rewrite Z.mod_small by lia. lia. }
    rewrite HW. cbn [bind].
    assert (HL : 0 <= Zlength (hdr_bytes s a) + tlen (d_wrap s) <= 20000).
    { pose proof (hdr_len_le s a Hg). unfold tlen.
      destruct (d_wrap s =? 1); [lia|]. destruct (d_wrap s =? 2); lia. }
    replace (Zlength (hdr_bytes s a) + body (bcls_of s) n + tlen (d_wrap s))
      with (body (bcls_of s) n + (Zlength (hdr_bytes s a) + tlen (d_wrap s))) by ring.
    revert HL. generalize (Zlength (hdr_bytes s a) + tlen (d_wrap s)). intros wl HL.
    unfold bcls_of, tight_b, body.
    destruct (d_w_bits s =? 15), (d_hash_bits s =? 8 + 7),
      ((d_strategy s =? Z_FIXED) && (d_level s >=? 1) && (d_level s <=? 3)),
      ((d_w_bits s <=? d_hash_bits s) && negb (d_level s =? 0)); cbn [negb orb andb];
      unfold u64; rewrite Z.mod_small by lia; rewrite (proj2 (Z.ltb_ge _ _)) by lia; f_equal; lia.
  - intros n Hn. unfold c_compressBound, compressBound_z, body, u64.
    pose proof (shiftr_rng n 12). pose proof (shiftr_rng n 14). pose proof (shiftr_rng n 25).
    rewrite Z.mod_small by lia. destruct (_ <? n) eqn:E; [apply Z.ltb_lt in E; lia|lia].
  - intros s a Hw Hs. unfold hdr_bytes, zlib_hdr_bytes. rewrite Hw, Hs. reflexivity.
Qed.

Lemma hdr_bytes_len : forall s a, gzh_ok s -> 0 <= Zlength (hdr_bytes s a) <= 16384.
Proof. exact (db_hdr_bytes_len dbound_proof). Qed.

Lemma deflateBound_val : forall s n a,
  prm s -> status_ok (d_status s) = true -> 0 <= d_wrap s <= 2 -> gzh_ok s -> 0 <= n <= 1048576 ->
  c_deflateBound (Some s) n = Some (Zlength (hdr_bytes s a) + body (bcls_of s) n + tlen (d_wrap s)).
Proof. exact (db_deflateBound_val dbound_proof). Qed.

Lemma compressBound_val : forall n, 0 <= n <= 1048576 -> c_compressBound n = body BTight n + 6.
Proof. exact (db_compressBound_val dbound_proof). Qed.

Lemma hdr_bytes_zlib_nodict : forall s a, d_wrap s = 1 -> d_strstart s = 0 -> Zlength (hdr_bytes s a) = 2.
Proof. exact (db_hdr_bytes_zlib_nodict dbound_proof). Qed.




(** The zlib header without a dictionary: 2 bytes. *)
