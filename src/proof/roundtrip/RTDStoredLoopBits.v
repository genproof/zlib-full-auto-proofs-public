(* RT-D part STORED LOOP: bit-level helpers (stored-block encoding, the patched LEN/NLEN bytes,
   runs of blocks). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDStoredKit.
Import ListNotations.
Local Open Scope Z_scope.

(** ** bits_le *)

Lemma Zlength_bits_le v n : 0 <= n -> Zlength (F.bits_le v n) = n.
Proof.
  intros Hn. unfold F.bits_le. rewrite Zlength_map, Zlength_correct, seq_length. lia.
Qed.

Lemma Zlength_bytes_bits l : Zlength (F.bytes_bits l) = 8 * Zlength l.
Proof.
  induction l as [|b r IH]; [reflexivity|].
  unfold F.bytes_bits in *. cbn [flat_map]. rewrite Zlength_app, IH, Zlength_bits_le, Zlength_cons by lia. lia.
Qed.

Lemma bytes_bits_app l1 l2 : F.bytes_bits (l1 ++ l2) = F.bytes_bits l1 ++ F.bytes_bits l2.
Proof. unfold F.bytes_bits. apply flat_map_app. Qed.

Lemma bits_le_ext a b n : (forall i, 0 <= i < n -> Z.testbit a i = Z.testbit b i) -> F.bits_le a n = F.bits_le b n.
Proof.
  intros H. unfold F.bits_le. apply map_ext_in. intros i Hi. apply in_seq in Hi. apply H. lia.
Qed.

Lemma bits_le_0 v : F.bits_le v 0 = [].
Proof. reflexivity. Qed.

Lemma seq_shift_add (n m : nat) : seq n m = map (Nat.add n) (seq 0 m).
Proof.
  induction m as [|m IH]; [reflexivity|].
  rewrite !seq_S, map_app, IH. cbn [map]. f_equal.
Qed.

Lemma bits_le_split v n m : 0 <= n -> 0 <= m ->
  F.bits_le v (n + m) = F.bits_le v n ++ F.bits_le (Z.shiftr v n) m.
Proof.
  intros Hn Hm. unfold F.bits_le. rewrite Z2Nat.inj_add by lia. rewrite seq_app, map_app. f_equal.
  rewrite seq_shift_add, map_map. apply map_ext_in. intros i Hi. apply in_seq in Hi.
  rewrite Z.shiftr_spec by lia. f_equal. lia.
Qed.

Lemma bits_le_mod v n : 0 <= n -> F.bits_le (v mod 2 ^ n) n = F.bits_le v n.
Proof.
  intros Hn. apply bits_le_ext. intros i Hi. apply Z.mod_pow2_bits_low. lia.
Qed.

(** The 4 bytes deflate_stored patches into the header of the empty stored block. *)
Lemma len_bytes_bits len : 0 <= len <= 65535 ->
  F.bytes_bits [u8 len; u8 (Z.shiftr len 8); u8 (u32 (Z.lnot len)); u8 (Z.shiftr (u32 (Z.lnot len)) 8)] =
  F.bits_le len 16 ++ F.bits_le (65535 - len) 16.
Proof.
  intros Hl. unfold F.bytes_bits. cbn [flat_map]. rewrite app_nil_r.
  assert (U8 : forall x, F.bits_le (u8 x) 8 = F.bits_le x 8)
    by (intros x; unfold u8; change 256 with (2 ^ 8); apply bits_le_mod; lia).
  rewrite !U8.
  assert (S : forall x, F.bits_le x 8 ++ F.bits_le (Z.shiftr x 8) 8 = F.bits_le x 16)
    by (intros x; rewrite <- bits_le_split by lia; reflexivity).
  rewrite app_assoc, S, S. f_equal.
  rewrite <- (bits_le_mod (u32 (Z.lnot len)) 16) by lia.
  f_equal. unfold u32. rewrite Z.lnot_eq_pred_opp.
  change (2 ^ 16) with 65536.
  rewrite <- Znumtheory.Zmod_div_mod by (try lia; exists 65536; reflexivity).
  replace (- len - 1) with (65535 - len + (-1) * 65536) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small; lia.
Qed.

(** ** Stored blocks *)

Lemma pad8_spec q : 0 <= F.pad8 q < 8 /\ (q + F.pad8 q) mod 8 = 0.
Proof. unfold F.pad8. split; [apply Z.mod_pos_bound; lia|]. Z.div_mod_to_equations. lia. Qed.

Lemma enc_stored_eq p fin d :
  F.enc_block p fin (F.Stored d) =
  [fin; false; false] ++ F.zeros (F.pad8 (p + 3)) ++
  F.bits_le (Zlength d) 16 ++ F.bits_le (65535 - Zlength d) 16 ++ F.bytes_bits d.
Proof. reflexivity. Qed.

Lemma Zlength_zeros n : 0 <= n -> Zlength (F.zeros n) = n.
Proof. intros H. unfold F.zeros. rewrite Zlength_correct, repeat_length. lia. Qed.

Lemma Zlength_enc_stored p fin d :
  Zlength (F.enc_block p fin (F.Stored d)) = 3 + F.pad8 (p + 3) + 32 + 8 * Zlength d.
Proof.
  rewrite enc_stored_eq. pose proof (pad8_spec (p + 3)).
  rewrite !Zlength_app, Zlength_zeros, !Zlength_bits_le, Zlength_bytes_bits by lia.
  change (Zlength [fin; false; false]) with 3. lia.
Qed.

Lemma enc_stored_align p fin d : (p + Zlength (F.enc_block p fin (F.Stored d))) mod 8 = 0.
Proof.
  rewrite Zlength_enc_stored. pose proof (pad8_spec (p + 3)) as [_ H].
  replace (p + (3 + F.pad8 (p + 3) + 32 + 8 * Zlength d)) with (p + 3 + F.pad8 (p + 3) + (4 + Zlength d) * 8) by lia.
  rewrite Z.mod_add by lia. exact H.
Qed.

(** ** Runs of blocks *)

Lemma enc_from_snoc p bs b fin :
  enc_from p (bs ++ [b]) fin = enc_from p bs false ++ F.enc_block (p + Zlength (enc_from p bs false)) fin b.
Proof.
  revert p. induction bs as [|c r IH]; intros p.
  - cbn [app enc_from]. rewrite andb_true_r, app_nil_r, Zlength_nil, Z.add_0_r. reflexivity.
  - cbn [app enc_from]. replace (match r ++ [b] with [] => true | _ :: _ => false end) with false
      by (destruct r; reflexivity).
    rewrite andb_false_r. cbn [andb]. rewrite IH. rewrite <- app_assoc. f_equal. f_equal. f_equal.
    rewrite Zlength_app. lia.
Qed.

Lemma enc_out_false p bs : enc_out p bs false = enc_from p bs false.
Proof. reflexivity. Qed.

(* the final stored block ends on a byte boundary: no padding after it *)
Lemma enc_out_stored_last p bs d :
  enc_out p (bs ++ [F.Stored d]) true = enc_from p bs false ++
    F.enc_block (p + Zlength (enc_from p bs false)) true (F.Stored d).
Proof.
  unfold enc_out. rewrite enc_from_snoc.
  match goal with |- ?A ++ F.zeros ?n = _ => replace n with 0; [rewrite app_nil_r; reflexivity|] end.
  rewrite Zlength_app. unfold F.pad8.
  set (q := p + Zlength (enc_from p bs false)).
  replace (p + (Zlength (enc_from p bs false) + Zlength (F.enc_block q true (F.Stored d))))
    with (q + Zlength (F.enc_block q true (F.Stored d))) by (unfold q; lia).
  rewrite enc_stored_align. reflexivity.
Qed.

Lemma enc_from_stored_snoc_align p bs d fin :
  (p + Zlength (enc_from p (bs ++ [F.Stored d]) fin)) mod 8 = 0.
Proof.
  rewrite enc_from_snoc, Zlength_app.
  set (q := p + Zlength (enc_from p bs false)).
  replace (p + (Zlength (enc_from p bs false) + Zlength (F.enc_block q fin (F.Stored d))))
    with (q + Zlength (F.enc_block q fin (F.Stored d))) by (unfold q; lia).
  apply enc_stored_align.
Qed.
