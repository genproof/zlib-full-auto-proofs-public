(* Adler-32: the reference of the harnesses and the exact result of zlib's adler32_z.

   ref_adler32 is harness/zlib_common.h's ref_adler32, transcribed: s1 = a & 0xffff, s2 = (a >> 16) & 0xffff,
   then for each byte s1 = (s1 + b) % 65521 and s2 = (s2 + s1) % 65521; the result is (s2 << 16) | s1.

   adler32_z_val is what adler32_z returns for ANY initial value (any 64-bit unsigned long) and a non-null
   buffer: for a valid initial value (both halves below 65521) it is ref_adler32 (adler32_z_val_ref); for
   any initial value its halves are congruent mod 65521 to the reference from the reduced halves
   (adler32_z_val_lo_mod, adler32_z_val_hi_mod).  The one-byte fast path is the only case where the
   result is not fully reduced (the high half of an invalid initial value plus s1 can exceed 2 * 65521).

   Bytes are Z values in 0..255 (Bytes.v: bytes_rep, the representation of nondet_bytes). *)
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.adler32.Bytes.

Definition ADLER_BASE : Z := 65521.

Definition adler_lo (a: Z) : Z := a mod 65536.
Definition adler_hi (a: Z) : Z := (a / 65536) mod 65536.
Definition adler_pack (s: Z * Z) : Z := snd s * 65536 + fst s.

(* A valid Adler-32 checksum: 32 bits, both halves below 65521. *)
Definition adler_valid (a: Z) : Prop :=
  0 <= a < 2 ^ 32 /\ adler_lo a < ADLER_BASE /\ adler_hi a < ADLER_BASE.

(* The reference: one byte, reduced at every step. *)
Definition adler_ref_step (s: Z * Z) (b: Z) : Z * Z :=
  let s1 := (fst s + b) mod ADLER_BASE in (s1, (snd s + s1) mod ADLER_BASE).

Definition ref_adler32 (a: Z) (data: list Z) : Z :=
  adler_pack (fold_left adler_ref_step data (adler_lo a, adler_hi a)).

(* The sums without reduction (what the C code accumulates between two reductions). *)
Definition adler_sum_step (s: Z * Z) (b: Z) : Z * Z := (fst s + b, snd s + (fst s + b)).

Definition adler_sums (s: Z * Z) (data: list Z) : Z * Z := fold_left adler_sum_step data s.

(* The result of adler32_z(a, buf, len) for a non-null buffer holding data (len = Zlength data). *)
Definition adler32_z_val (a: Z) (data: list Z) : Z :=
  match data with
  | [b] =>
      let s1 := (adler_lo a + b) mod ADLER_BASE in
      let t := adler_hi a + s1 in
      (if t <? ADLER_BASE then t else t - ADLER_BASE) * 65536 + s1
  | _ =>
      let s := adler_sums (adler_lo a, adler_hi a) data in
      (snd s mod ADLER_BASE) * 65536 + fst s mod ADLER_BASE
  end.

(* adler32_combine's algebra (RFC 1950 sums): the checksum of a concatenation whose second part has length
   len2, from the checksums x of the first part and y of the second. *)
Definition adler32_combine_val (x y len2: Z) : Z :=
  let x1 := adler_lo x in let x2 := adler_hi x in
  let y1 := adler_lo y in let y2 := adler_hi y in
  let s1 := (x1 + y1 + ADLER_BASE - 1) mod ADLER_BASE in
  let s2 := (x2 + y2 + (len2 mod ADLER_BASE) * ((x1 + ADLER_BASE - 1) mod ADLER_BASE)) mod ADLER_BASE in
  s2 * 65536 + s1.

(* ---------------------------------------------------------------------- *)
(* Facts                                                                   *)
(* ---------------------------------------------------------------------- *)

Lemma adler_lo_range a: 0 <= adler_lo a < 65536.
Proof. unfold adler_lo. apply Z.mod_pos_bound. lia. Qed.

Lemma adler_hi_range a: 0 <= adler_hi a < 65536.
Proof. unfold adler_hi. apply Z.mod_pos_bound. lia. Qed.

Lemma adler_lo_pack s1 s2: 0 <= s1 < 65536 -> adler_lo (s2 * 65536 + s1) = s1.
Proof.
  intros. unfold adler_lo. rewrite Z.add_comm, Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma adler_hi_pack s1 s2: 0 <= s1 < 65536 -> 0 <= s2 < 65536 -> adler_hi (s2 * 65536 + s1) = s2.
Proof.
  intros. unfold adler_hi. rewrite Z.add_comm, Z.div_add by lia.
  rewrite Z.div_small by lia. rewrite Z.add_0_l. apply Z.mod_small. lia.
Qed.

Lemma adler_pack_range s1 s2: 0 <= s1 < 65536 -> 0 <= s2 < 65536 -> 0 <= s2 * 65536 + s1 < 2 ^ 32.
Proof. intros. change (2 ^ 32) with (65536 * 65536). nia. Qed.

Lemma adler_valid_pack s1 s2: 0 <= s1 < ADLER_BASE -> 0 <= s2 < ADLER_BASE -> adler_valid (s2 * 65536 + s1).
Proof.
  unfold adler_valid, ADLER_BASE. intros. split; [apply adler_pack_range; lia | ].
  rewrite adler_lo_pack, adler_hi_pack by lia. lia.
Qed.

(* The reference state stays reduced. *)
Lemma adler_ref_fold_range: forall data s,
  0 <= fst s < ADLER_BASE -> 0 <= snd s < ADLER_BASE ->
  let s' := fold_left adler_ref_step data s in 0 <= fst s' < ADLER_BASE /\ 0 <= snd s' < ADLER_BASE.
Proof.
  induction data as [|b data IH]; intros s H1 H2; simpl; auto.
  apply IH; unfold adler_ref_step; simpl; apply Z.mod_pos_bound; unfold ADLER_BASE; lia.
Qed.

Lemma ref_adler32_valid a data: adler_valid a -> adler_valid (ref_adler32 a data).
Proof.
  intros (_ & Hlo & Hhi). unfold ref_adler32, adler_pack.
  pose proof (adler_lo_range a). pose proof (adler_hi_range a).
  destruct (adler_ref_fold_range data (adler_lo a, adler_hi a)) as [A B]; simpl; try lia.
  apply adler_valid_pack; auto.
Qed.

Lemma ref_adler32_app a d1 d2:
  adler_valid a -> ref_adler32 (ref_adler32 a d1) d2 = ref_adler32 a (d1 ++ d2).
Proof.
  intros (_ & Hlo & Hhi). unfold ref_adler32 at 2 3. rewrite fold_left_app.
  pose proof (adler_lo_range a). pose proof (adler_hi_range a).
  destruct (adler_ref_fold_range d1 (adler_lo a, adler_hi a)) as [A B]; simpl; try lia.
  unfold ref_adler32, adler_pack.
  destruct (fold_left adler_ref_step d1 (adler_lo a, adler_hi a)) as [s1 s2] eqn:E. simpl in *.
  unfold ADLER_BASE in *.
  rewrite adler_lo_pack, adler_hi_pack by lia. reflexivity.
Qed.

Lemma add_mod_cong m x y z w: x mod m = y mod m -> z mod m = w mod m -> (x + z) mod m = (y + w) mod m.
Proof. intros A B. rewrite Zplus_mod, A, B, <- Zplus_mod. reflexivity. Qed.

(* The unreduced sums agree with the reduced reference modulo 65521. *)
Lemma adler_sums_mod: forall data s t,
  fst s mod ADLER_BASE = fst t mod ADLER_BASE -> snd s mod ADLER_BASE = snd t mod ADLER_BASE ->
  fst (adler_sums s data) mod ADLER_BASE = fst (adler_sums t data) mod ADLER_BASE /\
  snd (adler_sums s data) mod ADLER_BASE = snd (adler_sums t data) mod ADLER_BASE.
Proof.
  unfold adler_sums. induction data as [|b data IH]; intros s t H1 H2; simpl; auto.
  apply IH; unfold adler_sum_step; simpl.
  - apply add_mod_cong; auto.
  - apply add_mod_cong; auto. apply add_mod_cong; auto.
Qed.

Lemma adler_ref_sums: forall data s t,
  0 <= fst s < ADLER_BASE -> 0 <= snd s < ADLER_BASE ->
  fst s = fst t mod ADLER_BASE -> snd s = snd t mod ADLER_BASE ->
  fold_left adler_ref_step data s =
    (fst (adler_sums t data) mod ADLER_BASE, snd (adler_sums t data) mod ADLER_BASE).
Proof.
  unfold adler_sums. induction data as [|b data IH]; intros s t R1 R2 H1 H2; simpl.
  - destruct s; simpl in *; congruence.
  - apply IH; unfold adler_ref_step, adler_sum_step; simpl;
      try (apply Z.mod_pos_bound; unfold ADLER_BASE; lia).
    + rewrite H1, Zplus_mod_idemp_l. reflexivity.
    + apply add_mod_cong.
      * rewrite H2, Zmod_mod. reflexivity.
      * rewrite Zmod_mod, H1, Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma ref_adler32_sums a data:
  ref_adler32 a data =
    adler_pack (fst (adler_sums (adler_lo a mod ADLER_BASE, adler_hi a mod ADLER_BASE) data) mod ADLER_BASE,
                snd (adler_sums (adler_lo a mod ADLER_BASE, adler_hi a mod ADLER_BASE) data) mod ADLER_BASE)
  \/ data = [].
Proof.
  destruct data as [|b data]; [right; reflexivity | left].
  unfold ref_adler32. simpl fold_left.
  rewrite (adler_ref_sums data _ (adler_sum_step (adler_lo a mod ADLER_BASE, adler_hi a mod ADLER_BASE) b));
    unfold adler_ref_step, adler_sum_step; simpl; try (apply Z.mod_pos_bound; unfold ADLER_BASE; lia).
  - reflexivity.
  - rewrite Zplus_mod_idemp_l. reflexivity.
  - apply add_mod_cong.
    + rewrite Zmod_mod. reflexivity.
    + rewrite Zmod_mod, Zplus_mod_idemp_l. reflexivity.
Qed.

(* For a valid initial value, adler32_z computes the reference. *)
Lemma adler32_z_val_ref a data: adler_valid a -> adler32_z_val a data = ref_adler32 a data.
Proof.
  intros (_ & Hlo & Hhi).
  pose proof (adler_lo_range a). pose proof (adler_hi_range a).
  destruct data as [|b [|b2 data]].
  - unfold adler32_z_val, ref_adler32, adler_pack, adler_sums; simpl.
    rewrite !Z.mod_small by lia. lia.
  - unfold adler32_z_val, ref_adler32, adler_pack, adler_ref_step; simpl.
    set (s1 := (adler_lo a + b) mod ADLER_BASE).
    assert (0 <= s1 < ADLER_BASE) by (apply Z.mod_pos_bound; unfold ADLER_BASE; lia).
    destruct (Z.ltb_spec (adler_hi a + s1) ADLER_BASE).
    + rewrite Z.mod_small by lia. reflexivity.
    + rewrite (Z.mod_eq _ ADLER_BASE) by (unfold ADLER_BASE; lia).
      replace ((adler_hi a + s1) / ADLER_BASE) with 1. lia.
      apply Z.div_unique with (adler_hi a + s1 - ADLER_BASE); lia.
  - destruct (ref_adler32_sums a (b :: b2 :: data)) as [E|E]; [ | discriminate].
    rewrite E. unfold adler32_z_val, adler_pack. simpl fst; simpl snd.
    rewrite (Z.mod_small (adler_lo a)), (Z.mod_small (adler_hi a)) by lia. lia.
Qed.

Lemma adler32_z_val_long a data: (forall b, data <> [b]) ->
  adler32_z_val a data =
    let s := adler_sums (adler_lo a, adler_hi a) data in (snd s mod ADLER_BASE) * 65536 + fst s mod ADLER_BASE.
Proof. intros H. destruct data as [|x [|y l]]; auto. exfalso; eapply H; eauto. Qed.

(* For any initial value: the halves are congruent to the reference from the reduced halves. *)
Definition adler_reduce (a: Z) : Z := (adler_hi a mod ADLER_BASE) * 65536 + adler_lo a mod ADLER_BASE.

Lemma adler_reduce_valid a: adler_valid (adler_reduce a).
Proof. apply adler_valid_pack; apply Z.mod_pos_bound; unfold ADLER_BASE; lia. Qed.

Lemma adler32_z_val_range a data: is_bytes data -> 0 <= adler32_z_val a data < 2 ^ 32 /\
  0 <= adler_lo (adler32_z_val a data) < ADLER_BASE /\ adler_hi (adler32_z_val a data) < 65536.
Proof.
  intros HB. pose proof (adler_lo_range a). pose proof (adler_hi_range a).
  destruct data as [|b [|b2 data]].
  - unfold adler32_z_val.
    assert (0 <= snd (adler_sums (adler_lo a, adler_hi a) []) mod ADLER_BASE < ADLER_BASE)
      by (apply Z.mod_pos_bound; unfold ADLER_BASE; lia).
    assert (0 <= fst (adler_sums (adler_lo a, adler_hi a) []) mod ADLER_BASE < ADLER_BASE)
      by (apply Z.mod_pos_bound; unfold ADLER_BASE; lia).
    unfold ADLER_BASE in *.
    rewrite adler_lo_pack, adler_hi_pack by lia. split; [apply adler_pack_range | ]; lia.
  - unfold adler32_z_val.
    set (s1 := (adler_lo a + b) mod ADLER_BASE).
    assert (0 <= s1 < ADLER_BASE) by (apply Z.mod_pos_bound; unfold ADLER_BASE; lia).
    unfold ADLER_BASE in *.
    destruct (Z.ltb_spec (adler_hi a + s1) 65521);
      rewrite adler_lo_pack, ?adler_hi_pack by lia; (split; [apply adler_pack_range | ]; lia).
  - unfold adler32_z_val.
    set (s := adler_sums _ _).
    assert (0 <= snd s mod ADLER_BASE < ADLER_BASE) by (apply Z.mod_pos_bound; unfold ADLER_BASE; lia).
    assert (0 <= fst s mod ADLER_BASE < ADLER_BASE) by (apply Z.mod_pos_bound; unfold ADLER_BASE; lia).
    unfold ADLER_BASE in *.
    rewrite adler_lo_pack, adler_hi_pack by lia. split; [apply adler_pack_range | ]; lia.
Qed.

Lemma adler32_z_val_mod a data:
  adler_lo (adler32_z_val a data) mod ADLER_BASE = adler_lo (ref_adler32 (adler_reduce a) data) /\
  adler_hi (adler32_z_val a data) mod ADLER_BASE = adler_hi (ref_adler32 (adler_reduce a) data).
Proof.
  pose proof (adler_lo_range a). pose proof (adler_hi_range a).
  assert (Rl: 0 <= adler_lo a mod ADLER_BASE < ADLER_BASE) by (apply Z.mod_pos_bound; unfold ADLER_BASE; lia).
  assert (Rh: 0 <= adler_hi a mod ADLER_BASE < ADLER_BASE) by (apply Z.mod_pos_bound; unfold ADLER_BASE; lia).
  assert (Lr: adler_lo (adler_reduce a) = adler_lo a mod ADLER_BASE)
    by (unfold adler_reduce, ADLER_BASE in *; apply adler_lo_pack; lia).
  assert (Hr: adler_hi (adler_reduce a) = adler_hi a mod ADLER_BASE)
    by (unfold adler_reduce, ADLER_BASE in *; apply adler_hi_pack; lia).
  rewrite <- adler32_z_val_ref by apply adler_reduce_valid.
  destruct data as [|b [|b2 data]].
  - unfold adler32_z_val, adler_sums; simpl fold_left; simpl fst; simpl snd.
    rewrite Lr, Hr, !Zmod_mod. unfold ADLER_BASE in *.
    rewrite !adler_lo_pack, !adler_hi_pack by lia. rewrite !Zmod_mod. auto.
  - unfold adler32_z_val. rewrite Lr, Hr.
    rewrite Zplus_mod_idemp_l.
    set (s1 := (adler_lo a + b) mod ADLER_BASE).
    assert (0 <= s1 < ADLER_BASE) by (apply Z.mod_pos_bound; unfold ADLER_BASE; lia).
    assert (E: forall t,
              (if t <? ADLER_BASE then t else t - ADLER_BASE) mod ADLER_BASE = t mod ADLER_BASE).
    { intros t. destruct (Z.ltb_spec t ADLER_BASE); auto.
      rewrite <- (Z.mod_add _ 1) by (unfold ADLER_BASE; lia). f_equal. lia. }
    set (t1 := adler_hi a + s1). set (t2 := adler_hi a mod ADLER_BASE + s1).
    assert (Ht1: 0 <= (if t1 <? ADLER_BASE then t1 else t1 - ADLER_BASE) < 65536).
    { unfold t1, ADLER_BASE in *. destruct (Z.ltb_spec (adler_hi a + s1) 65521); lia. }
    assert (Ht2: 0 <= (if t2 <? ADLER_BASE then t2 else t2 - ADLER_BASE) < 65536).
    { unfold t2, ADLER_BASE in *. destruct (Z.ltb_spec (adler_hi a mod 65521 + s1) 65521); lia. }
    unfold ADLER_BASE in *.
    rewrite !adler_lo_pack, !adler_hi_pack by lia.
    rewrite Z.mod_small by lia. split; auto.
    rewrite E.
    rewrite <- (Z.mod_small (if t2 <? 65521 then t2 else t2 - 65521) 65521)
      by (destruct (Z.ltb_spec t2 65521); unfold t2 in *; lia).
    rewrite E. unfold t1, t2. apply add_mod_cong; [rewrite Zmod_mod | ]; reflexivity.
  - rewrite !adler32_z_val_long by (intros ? X; discriminate X). cbv zeta. rewrite Lr, Hr.
    destruct (adler_sums_mod (b :: b2 :: data) (adler_lo a, adler_hi a)
                (adler_lo a mod ADLER_BASE, adler_hi a mod ADLER_BASE)) as [A B];
      try (cbn [fst snd]; rewrite Zmod_mod; reflexivity).
    set (u := adler_sums (adler_lo a, adler_hi a) _) in *.
    set (v := adler_sums (adler_lo a mod ADLER_BASE, adler_hi a mod ADLER_BASE) _) in *.
    assert (0 <= snd u mod ADLER_BASE < ADLER_BASE) by (apply Z.mod_pos_bound; unfold ADLER_BASE; lia).
    assert (0 <= fst u mod ADLER_BASE < ADLER_BASE) by (apply Z.mod_pos_bound; unfold ADLER_BASE; lia).
    assert (0 <= snd v mod ADLER_BASE < ADLER_BASE) by (apply Z.mod_pos_bound; unfold ADLER_BASE; lia).
    assert (0 <= fst v mod ADLER_BASE < ADLER_BASE) by (apply Z.mod_pos_bound; unfold ADLER_BASE; lia).
    unfold ADLER_BASE in *.
    rewrite !adler_lo_pack, !adler_hi_pack by lia. rewrite !Zmod_mod. auto.
Qed.
