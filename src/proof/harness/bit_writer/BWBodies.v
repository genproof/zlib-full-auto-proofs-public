(* The bodies of put_bits and put_literal (harness/rj_bad_block.c, rj_far_back.c) against BWSpec.v. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.rfc1951.Format.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.harness.bit_writer.BWSpec.

#[local] Existing Instance Zlib.units.Adler32.CS.

(* ---------------------------------------------------------------------------------------------- *)
(* Pure facts: the machine integers of one step of put_bits, and the bits it writes                *)

(* a number below 2^n has no bit at n or above *)
Lemma testbit_small : forall z n i, 0 <= z < 2 ^ n -> n <= i -> Z.testbit z i = false.
Proof.
  intros z n i Hz Hi.
  destruct (Z.eq_dec z 0) as [->|Hnz]; [apply Z.testbit_0_l|].
  apply Z.bits_above_log2; [lia|].
  assert (Z.log2 z < n) by (apply Z.log2_lt_pow2; lia). lia.
Qed.

(* conversely, a nonnegative number without bits at 8 or above is a byte *)
Lemma byte_of_bits : forall z, 0 <= z -> (forall j, 8 <= j -> Z.testbit z j = false) -> z < 256.
Proof.
  intros z Hz Hb.
  assert (z = Z.land z (Z.ones 8)).
  { apply Z.bits_inj'; intros j Hj. rewrite Z.land_spec.
    destruct (zlt j 8).
    - rewrite Z.ones_spec_low by lia. rewrite andb_true_r. reflexivity.
    - rewrite Hb by lia. reflexivity. }
  rewrite H, Z.land_ones by lia. pose proof (Z.mod_pos_bound z (2 ^ 8) ltac:(lia)).
  change (2 ^ 8) with 256 in *. lia.
Qed.

Lemma zext8_repr : forall z, 0 <= z < 256 -> Int.zero_ext 8 (Int.repr z) = Int.repr z.
Proof.
  intros z Hz. apply Int.same_bits_eq; intros j Hj.
  rewrite Int.bits_zero_ext by lia. rewrite !Int.testbit_repr by lia.
  destruct (zlt j 8); auto. symmetry; apply (testbit_small z 8); [change (2 ^ 8) with 256|]; lia.
Qed.

(* mask = (unsigned char) (1u << bit % 8), bit the current position *)
Lemma mask_eq : forall q, 0 <= q <= Int64.max_unsigned ->
  Int.zero_ext 8 (Int.zero_ext 8 (Int.shl (Int.repr 1)
     (Int64.loword (Int64.modu (Int64.repr q) (Int64.repr (Int.signed (Int.repr 8))))))) =
  Int.repr (2 ^ (q mod 8)).
Proof.
  intros q Hq.
  pose proof (Z.mod_pos_bound q 8 ltac:(lia)).
  assert (Hm : Int64.loword (Int64.modu (Int64.repr q) (Int64.repr (Int.signed (Int.repr 8)))) =
               Int.repr (q mod 8)).
  { unfold Int64.modu, Int64.loword. rewrite Int.signed_repr by rep_lia.
    rewrite (Int64.unsigned_repr q), (Int64.unsigned_repr 8) by rep_lia.
    rewrite Int64.unsigned_repr by rep_lia. reflexivity. }
  rewrite Hm. unfold Int.shl. rewrite (Int.unsigned_repr 1), (Int.unsigned_repr (q mod 8)) by rep_lia.
  rewrite Z.shiftl_1_l.
  assert (0 < 2 ^ (q mod 8) < 256).
  { split. apply Z.pow_pos_nonneg; lia. change 256 with (2 ^ 8). apply Z.pow_lt_mono_r; lia. }
  rewrite !zext8_repr by lia. reflexivity.
Qed.

(* one = (value >> shift) & 1 is the bit shift of value *)
Lemma one_eq : forall v s, 0 <= v <= Int.max_unsigned -> 0 <= s < 32 ->
  Int.and (Int.shru (Int.repr v) (Int.repr s)) (Int.repr 1) = if Z.testbit v s then Int.one else Int.zero.
Proof.
  intros v s Hv Hs. apply Int.same_bits_eq; intros j Hj.
  rewrite Int.bits_and, Int.bits_shru by lia. rewrite (Int.unsigned_repr s) by rep_lia.
  change (Int.repr 1) with Int.one. rewrite Int.bits_one.
  change Int.zwordsize with 32 in *.
  destruct (zeq j 0).
  - subst. destruct (zlt (0 + s) 32); [|lia].
    rewrite Int.testbit_repr by (change Int.zwordsize with 32; lia). rewrite Z.add_0_l.
    destruct (Z.testbit v s); reflexivity.
  - rewrite andb_false_r. destruct (Z.testbit v s).
    + rewrite Int.bits_one. destruct (zeq j 0); [lia|reflexivity].
    + rewrite Int.bits_zero. reflexivity.
Qed.

(* the stored byte: (unsigned char) ((x & ~mask) | (one ? mask : 0)) *)
Lemma byte_eq : forall x m (b : bool), 0 <= x < 256 -> 0 <= m < 256 ->
  Int.zero_ext 8 (Int.or (Int.and (Int.repr x) (Int.not (Int.repr m))) (if b then Int.repr m else Int.repr 0)) =
  Int.repr (Z.lor (Z.land x (Z.lnot m)) (if b then m else 0)).
Proof.
  intros x m b Hx Hm. apply Int.same_bits_eq; intros j Hj.
  rewrite Int.bits_zero_ext by lia. rewrite (Int.testbit_repr _ j) by lia.
  rewrite Z.lor_spec, Z.land_spec, Z.lnot_spec by lia.
  destruct (zlt j 8).
  - destruct b; rewrite Int.bits_or, Int.bits_and, Int.bits_not by lia; rewrite !Int.testbit_repr by lia;
      reflexivity.
  - destruct b; [|rewrite Z.testbit_0_l];
      rewrite (testbit_small x 8 j), (testbit_small m 8 j) by (change (2 ^ 8) with 256; lia); reflexivity.
Qed.

Lemma byte_range : forall x m (b : bool), 0 <= x < 256 -> 0 <= m < 256 ->
  0 <= Z.lor (Z.land x (Z.lnot m)) (if b then m else 0) < 256.
Proof.
  intros x m b Hx Hm.
  assert (0 <= Z.lor (Z.land x (Z.lnot m)) (if b then m else 0)).
  { apply Z.lor_nonneg. split; [apply Z.land_nonneg; lia | destruct b; lia]. }
  split; auto. apply byte_of_bits; auto. intros j Hj.
  rewrite Z.lor_spec, Z.land_spec, Z.lnot_spec by lia.
  destruct b; [|rewrite Z.testbit_0_l];
    rewrite (testbit_small x 8 j), (testbit_small m 8 j) by (change (2 ^ 8) with 256; lia); reflexivity.
Qed.

(* set_bit keeps the length and the byte range *)
Lemma set_bit_bytes : forall bytes q b, is_bytes bytes -> 0 <= q < 8 * Zlength bytes ->
  Zlength (set_bit bytes q b) = Zlength bytes /\ is_bytes (set_bit bytes q b).
Proof.
  intros bytes q b Hb Hq. unfold set_bit.
  assert (0 <= q / 8 < Zlength bytes) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  pose proof (Z.mod_pos_bound q 8 ltac:(lia)).
  assert (0 < 2 ^ (q mod 8) < 256).
  { split. apply Z.pow_pos_nonneg; lia. change 256 with (2 ^ 8). apply Z.pow_lt_mono_r; lia. }
  assert (0 <= Znth (q / 8) bytes <= Byte.max_unsigned).
  { apply (proj1 (Forall_Znth _ _) Hb); lia. }
  split.
  - apply upd_Znth_Zlength; lia.
  - apply Forall_upd_Znth; auto.
    pose proof (byte_range (Znth (q / 8) bytes) (2 ^ (q mod 8)) b). rep_lia.
Qed.

Lemma write_bits_snoc : forall bs bytes q b,
  write_bits bytes q (bs ++ [b]) = set_bit (write_bits bytes q bs) (q + Zlength bs) b.
Proof.
  induction bs as [|c bs IH]; intros bytes q b; simpl.
  - rewrite Z.add_0_r. reflexivity.
  - rewrite IH, Zlength_cons. f_equal. lia.
Qed.

Lemma bits_le_len : forall v n, 0 <= n -> Zlength (bits_le v n) = n.
Proof.
  intros. unfold bits_le. rewrite Zlength_map, Zlength_correct, seq_length. lia.
Qed.

Lemma bits_le_nth : forall v n i, 0 <= i < n -> Znth i (bits_le v n) = Z.testbit v i.
Proof.
  intros v n i Hi. unfold bits_le.
  rewrite Znth_map by (rewrite Zlength_correct, seq_length; lia).
  unfold Znth. destruct (Z_lt_dec i 0); [lia|].
  rewrite seq_nth by lia. simpl. rewrite Z2Nat.id by lia. reflexivity.
Qed.

(* bit i of pb_bits is bit shift of value, shift = huffman ? count - 1 - i : i *)
Lemma pb_bits_nth : forall v n h i, 0 <= i < n ->
  Zlength (pb_bits v n h) = n /\ Znth i (pb_bits v n h) = Z.testbit v (if h =? 0 then i else n - 1 - i).
Proof.
  intros v n h i Hi. unfold pb_bits, bits_msb. destruct (h =? 0).
  - split; [apply bits_le_len; lia | apply bits_le_nth; lia].
  - rewrite Zlength_rev, bits_le_len by lia. split; auto.
    rewrite Znth_rev by (rewrite bits_le_len; lia). rewrite bits_le_len by lia.
    replace (n - 1 - i) with (n - i - 1) by lia. apply bits_le_nth; lia.
Qed.

(* put_literal: one call of put_bits with the 8- or 9-bit fixed code, most significant bit first *)
Lemma body_put_literal :
  @semax_body Vprog_bw Gprog_put_literal Zlib.units.Adler32.CS BWC.f_put_literal put_literal_spec.
Proof.
  start_function.
  unfold put_literal_m, lit_len in *.
  forward_if.
  - rewrite (proj2 (Z.ltb_lt lit 144)) in * by lia.
    forward_call (sh, stream, shb, bitp, bytes, bit, 48 + lit, 8, 1).
    rewrite (proj2 (Z.ltb_lt lit 144)) by lia. entailer!.
  - rewrite (proj2 (Z.ltb_ge lit 144)) in * by lia.
    forward_call (sh, stream, shb, bitp, bytes, bit, 400 + lit - 144, 9, 1).
    rewrite (proj2 (Z.ltb_ge lit 144)) by lia. entailer!.
Qed.

(* The loop invariant: after i iterations the first i bits of pb_bits are written from position bit on, and
   *bit = bit + i. *)
Lemma body_put_bits :
  @semax_body Vprog_bw Gprog_put_bits Zlib.units.Adler32.CS BWC.f_put_bits put_bits_spec.
Proof.
  start_function.
  set (bs := pb_bits value count huffman).
  forward_for_simple_bound count
    (EX i : Z,
     PROP (Zlength (write_bits bytes bit (sublist 0 i bs)) = Zlength bytes;
           is_bytes (write_bits bytes bit (sublist 0 i bs)))
     LOCAL (temp BWC._stream stream; temp BWC._bit bitp; temp BWC._value (Vint (Int.repr value));
            temp BWC._count (Vint (Int.repr count)); temp BWC._huffman (Vint (Int.repr huffman)))
     SEP (data_at sh (tarray tuchar (Zlength bytes)) (bytes_rep (write_bits bytes bit (sublist 0 i bs))) stream;
          data_at shb tulong (Vlong (Int64.repr (bit + i))) bitp)).
  - entailer!. apply derives_refl.
  - assert (Hsh : 0 <= (if huffman =? 0 then i else count - 1 - i) < count)
      by (destruct (huffman =? 0); lia).
    forward_if
      (PROP (Zlength (write_bits bytes bit (sublist 0 i bs)) = Zlength bytes;
             is_bytes (write_bits bytes bit (sublist 0 i bs)))
       LOCAL (temp BWC._t'1 (Vint (Int.repr (if huffman =? 0 then i else count - 1 - i)));
              temp BWC._i (Vint (Int.repr i)); temp BWC._stream stream;
              temp BWC._bit bitp; temp BWC._value (Vint (Int.repr value));
              temp BWC._count (Vint (Int.repr count)); temp BWC._huffman (Vint (Int.repr huffman)))
       SEP (data_at sh (tarray tuchar (Zlength bytes)) (bytes_rep (write_bits bytes bit (sublist 0 i bs))) stream;
            data_at shb tulong (Vlong (Int64.repr (bit + i))) bitp)).
    + forward.
      destruct (Z.eqb_spec huffman 0); [subst; contradiction|].
      entailer!.
    + forward.
      assert (huffman = 0) as ->.
      { rewrite <- (Int.signed_repr huffman) by rep_lia. rewrite H8. reflexivity. }
      entailer!.
    + forward.
      forward.
      { entailer!. change (Int.unsigned Int.iwordsize) with 32. lia. }
      forward.
      forward.
      { entailer!. rewrite !Int64.Z_mod_modulus_eq.
        match goal with |- (?a mod 8) mod _ < _ =>
          pose proof (Z.mod_pos_bound a 8 ltac:(lia)); rewrite (Z.mod_small (a mod 8)) by rep_lia; lia end. }
      rewrite mask_eq by lia.
      rewrite one_eq by (rep_lia || lia).
      set (W := write_bits bytes bit (sublist 0 i bs)) in *.
      set (b := Z.testbit value (if huffman =? 0 then i else count - 1 - i)).
      forward_if
        (PROP ()
         LOCAL (temp BWC._t'2 (Vint (if b then Int.repr (2 ^ ((bit + i) mod 8)) else Int.repr 0));
                temp BWC._mask (Vint (Int.repr (2 ^ ((bit + i) mod 8))));
                temp BWC._i (Vint (Int.repr i)); temp BWC._stream stream;
                temp BWC._bit bitp; temp BWC._value (Vint (Int.repr value));
                temp BWC._count (Vint (Int.repr count)); temp BWC._huffman (Vint (Int.repr huffman)))
         SEP (data_at sh (tarray tuchar (Zlength bytes)) (bytes_rep W) stream;
              data_at shb tulong (Vlong (Int64.repr (bit + i))) bitp)).
      * destruct b; [|contradiction].
        forward. entailer!.
      * destruct b; [discriminate|].
        forward. entailer!.
      * assert (Hk : 0 <= (bit + i) / 8 < Zlength bytes)
          by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
        assert (Hx := is_bytes_Znth W ((bit + i) / 8) H9 ltac:(lia)).
        forward.
        forward.
        forward.
        { rewrite Znth_bytes_rep by lia. entailer!.
          change (let (q, _) := Z.div_eucl (bit + i) 8 in q) with ((bit + i) / 8).
          rewrite Int.unsigned_repr by rep_lia. lia. }
        rewrite Znth_bytes_rep by lia.
        forward.
        forward.
        forward.
        (* the loop invariant for i + 1: the step wrote bit i of pb_bits at position bit + i *)
        assert (Hlen := proj1 (pb_bits_nth value count huffman i H7)). fold bs in Hlen.
        assert (Hstep : write_bits bytes bit (sublist 0 (i + 1) bs) = set_bit W (bit + i) b).
        { rewrite (sublist_split 0 i (i + 1)) by lia. rewrite sublist_len_1 by lia.
          rewrite write_bits_snoc, Zlength_sublist by lia.
          replace (bit + (i - 0)) with (bit + i) by lia.
          unfold bs; rewrite (proj2 (pb_bits_nth value count huffman i H7)). reflexivity. }
        destruct (set_bit_bytes W (bit + i) b H9 ltac:(lia)) as [Hl1 Hb1].
        change (let (q, _) := Z.div_eucl (bit + i) 8 in q) with ((bit + i) / 8).
        pose proof (Z.mod_pos_bound (bit + i) 8 ltac:(lia)).
        assert (0 < 2 ^ ((bit + i) mod 8) < 256).
        { split. apply Z.pow_pos_nonneg; lia. change 256 with (2 ^ 8). apply Z.pow_lt_mono_r; lia. }
        assert (Hx' : 0 <= Znth ((bit + i) / 8) W < 256) by (change Byte.max_unsigned with 255 in Hx; lia).
        pose proof (byte_range (Znth ((bit + i) / 8) W) (2 ^ ((bit + i) mod 8)) b Hx' ltac:(lia)).
        rewrite byte_eq by lia. rewrite zext8_repr by lia.
        assert (Hrep : upd_Znth ((bit + i) / 8) (bytes_rep W)
                  (Vint (Int.repr (Z.lor (Z.land (Znth ((bit + i) / 8) W) (Z.lnot (2 ^ ((bit + i) mod 8))))
                                         (if b then 2 ^ ((bit + i) mod 8) else 0)))) =
                       bytes_rep (set_bit W (bit + i) b)).
        { unfold set_bit, bytes_rep. rewrite <- upd_Znth_map. reflexivity. }
        rewrite Hrep, Hstep.
        rewrite Int.signed_repr by rep_lia. rewrite add64_repr.
        replace (bit + i + 1) with (bit + (i + 1)) by lia.
        entailer!.
  - assert (Zlength bs = count).
    { unfold bs, pb_bits, bits_msb. destruct (huffman =? 0); [|rewrite Zlength_rev]; apply bits_le_len; lia. }
    rewrite sublist_same by lia. unfold put_bits_m. entailer!.
Qed.

Lemma bit_writer_bodies : bit_writer_ok.
Proof.
  split; [apply body_put_bits | apply body_put_literal].
Qed.
