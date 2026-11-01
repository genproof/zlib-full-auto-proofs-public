(* Law rfc_stored: the layout of a stream of stored blocks (RSSimKit.rs_lay_stmt).  Every block is stored, so
   each block starts on a byte boundary and is 5 + n bytes long: BFINAL, BTYPE and five zero padding bits, LEN,
   NLEN, then its n bytes; the blocks follow the header in order and the deflate stream ends after the last
   one. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.harness.rfc_stored.RSSimKit.
Require Import Zlib.proof.rfc1951.DecKit Zlib.proof.rfc1951.DecType.
Import ListNotations.
Local Open Scope Z_scope.

(* a stored block at a byte boundary is 40 + 8 n bits long *)
Lemma rsl_stored_len p f b : p mod 8 = 0 -> Zlength (enc_block p f (Stored b)) = 40 + 8 * Zlength b.
Proof.
  intros Hp. rewrite dt_stored_len.
  assert (P : pad8 (p + 3) = 5) by (unfold pad8; Z.to_euclidean_division_equations; lia). lia.
Qed.

(* the position of a block never precedes the start *)
Lemma rsl_epos_ge bs : forall p k, p <= epos p bs k.
Proof.
  induction bs as [|b r IH]; intros p k; destruct k as [|k]; cbn [epos]; try lia.
  pose proof (IH (p + Zlength (enc_block p false b)) k). pose proof (Zlength_nonneg (enc_block p false b)). lia.
Qed.

(* stored blocks from a byte boundary: every block starts on a byte boundary, and each one is at least
   40 bits after the previous ones *)
Lemma rsl_epos_stored bs : Forall (fun b => exists l, b = Stored l) bs -> forall p, p mod 8 = 0 ->
  (forall k, epos p bs k mod 8 = 0) /\
  (forall j k, (j < k)%nat -> (k <= length bs)%nat -> epos p bs j + 40 <= epos p bs k).
Proof.
  induction bs as [|b r IH]; intros HF p Hp.
  - split; [intros k; destruct k; exact Hp | intros j k Hjk Hk; cbn in Hk; lia].
  - inversion HF as [|? ? [l E] HF']; subst b.
    assert (Hp' : (p + (40 + 8 * Zlength l)) mod 8 = 0).
    { replace (p + (40 + 8 * Zlength l)) with (p + (5 + Zlength l) * 8) by ring. rewrite Z_mod_plus_full. exact Hp. }
    destruct (IH HF' _ Hp') as [IA IM]. split.
    + intros k. destruct k as [|k]; cbn [epos]; [exact Hp|]. rewrite rsl_stored_len by exact Hp. apply IA.
    + intros j k Hjk Hk. cbn [length] in Hk. destruct k as [|k]; [lia|]. cbn [epos].
      rewrite rsl_stored_len by exact Hp. pose proof (Zlength_nonneg l).
      destruct j as [|j]; cbn [epos].
      * pose proof (rsl_epos_ge r (p + (40 + 8 * Zlength l)) k). lia.
      * apply IM; lia.
Qed.

(* the source starts with the header and the deflate stream (dctx_ok7a: DecKit.dkit_sbits for streams of
   any length) *)
Lemma rsl_sbits G : dctx_ok7a G -> exists R,
  sbits G = bytes_bits (hdr_bytes (dc_w G)) ++ deflate_bits (dc_bs G) ++ R.
Proof.
  intros (_ & _ & _ & _ & Hs & _ & _ & Heq).
  assert (HR : exists R,
    dc_src G = hdr_bytes (dc_w G) ++ deflate_bytes (dc_bs G) ++ dkit_trl (dc_w G) (data (dc_hist G) (dc_bs G)) ++ R).
  { exists (sublist (slen G) (Zlength (dc_src G)) (dc_src G)).
    rewrite <- (sublist_same 0 (Zlength (dc_src G)) (dc_src G)) at 1 by lia.
    assert (0 <= slen G) by (unfold slen; apply Zlength_nonneg).
    rewrite <- (sublist_rejoin 0 (slen G) (Zlength (dc_src G))) by lia.
    rewrite Heq, dkit_stream_split, <- !app_assoc. reflexivity. }
  destruct HR as [R HR].
  unfold sbits. rewrite HR, !dkit_bytes_bits_app. unfold deflate_bytes.
  rewrite dkit_pack_bits by apply dkit_deflate_bits_len.
  eexists. reflexivity.
Qed.

(* block k of the source (DecKit's dk_blk under dctx_ok7a) *)
Lemma rsl_blk G k : dctx_ok7a G -> 0 <= k < nblk G ->
  bpos G (k + 1) = bpos G k + Zlength (enc_block (bpos G k - D0 G) (lastflag G k =? 1) (blk G k)) /\
  sublist (bpos G k) (bpos G (k + 1)) (sbits G) = enc_block (bpos G k - D0 G) (lastflag G k =? 1) (blk G k).
Proof.
  intros HG Hk. unfold nblk in Hk. unfold bpos, blk, lastflag, nblk.
  assert (Hn: (Z.to_nat k < length (dc_bs G))%nat) by (rewrite <- ZtoNat_Zlength; apply Z2Nat.inj_lt; lia).
  replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by (rewrite Z2Nat.inj_add by lia; simpl; lia).
  rewrite (dkit_epos_S _ _ 0 (Stored []) Hn).
  replace (D0 G + epos 0 (dc_bs G) (Z.to_nat k) - D0 G) with (epos 0 (dc_bs G) (Z.to_nat k)) by ring.
  replace ((if k =? Zlength (dc_bs G) - 1 then 1 else 0) =? 1) with (Nat.eqb (S (Z.to_nat k)) (length (dc_bs G))).
  2: { rewrite <- ZtoNat_Zlength.
       destruct (Z.eqb_spec k (Zlength (dc_bs G) - 1));
       destruct (Nat.eqb_spec (S (Z.to_nat k)) (Z.to_nat (Zlength (dc_bs G)))); simpl; auto; lia. }
  rewrite (dkit_enc_block_len _ false (Nat.eqb (S (Z.to_nat k)) (length (dc_bs G)))). split; [ring|].
  destruct (rsl_sbits G HG) as [R HR].
  destruct (dkit_enc_blocks_at (dc_bs G) 0 (Z.to_nat k) (Stored []) Hn) as [A [B [HE HA]]].
  replace (D0 G + (epos 0 (dc_bs G) (Z.to_nat k) +
            Zlength (enc_block (epos 0 (dc_bs G) (Z.to_nat k)) (S (Z.to_nat k) =? length (dc_bs G))%nat
               (nth (Z.to_nat k) (dc_bs G) (Stored [])))))
    with (Zlength (bytes_bits (hdr_bytes (dc_w G)) ++ A) +
            Zlength (enc_block (epos 0 (dc_bs G) (Z.to_nat k)) (S (Z.to_nat k) =? length (dc_bs G))%nat
               (nth (Z.to_nat k) (dc_bs G) (Stored []))))
    by (rewrite Zlength_app, HA, dkit_D0_len; ring).
  replace (D0 G + epos 0 (dc_bs G) (Z.to_nat k)) with (Zlength (bytes_bits (hdr_bytes (dc_w G)) ++ A))
    by (rewrite Zlength_app, HA, dkit_D0_len; ring).
  rewrite HR. unfold deflate_bits. rewrite HE. rewrite <- !app_assoc. rewrite (app_assoc (bytes_bits _) A).
  apply dkit_sublist_mid.
Qed.

Lemma rsl_D0_mod G : D0 G mod 8 = 0.
Proof. unfold D0. rewrite Z.mul_comm. apply Z.mod_mul. lia. Qed.

Lemma rsl_align G k : rs_stored_only G -> bpos G k mod 8 = 0.
Proof.
  intros HS. unfold bpos. destruct (rsl_epos_stored _ HS 0 eq_refl) as [IA _].
  rewrite Zplus_mod, rsl_D0_mod, IA. reflexivity.
Qed.

Lemma rsl_mono G j k : rs_stored_only G -> 0 <= j < k -> k <= nblk G -> bpos G j + 40 <= bpos G k.
Proof.
  intros HS Hj Hk. unfold bpos. destruct (rsl_epos_stored _ HS 0 eq_refl) as [_ IM].
  unfold nblk in Hk. rewrite Zlength_correct in Hk.
  enough (epos 0 (dc_bs G) (Z.to_nat j) + 40 <= epos 0 (dc_bs G) (Z.to_nat k)) by lia.
  apply IM; lia.
Qed.

Lemma rsl_end G : rs_stored_only G -> endpos G = bpos G (nblk G).
Proof.
  intros HS. unfold endpos, bpos, nblk. rewrite ZtoNat_Zlength, dkit_epos_end.
  destruct (dkit_deflate_bits_len (dc_bs G)) as [HL _]. rewrite HL.
  destruct (rsl_epos_stored _ HS 0 eq_refl) as [IA _].
  specialize (IA (length (dc_bs G))). rewrite dkit_epos_end in IA.
  assert (P : pad8 (Zlength (enc_blocks 0 (dc_bs G))) = 0).
  { unfold pad8. rewrite Z.add_0_l in IA. rewrite IA. reflexivity. }
  rewrite P. ring.
Qed.

Lemma rs_lay : rs_lay_stmt.
Proof.
  constructor.
  - (* rl_stored *)
    intros G k HS Hk. unfold blk. unfold nblk in Hk.
    assert (Hn : (Z.to_nat k < length (dc_bs G))%nat) by (rewrite Zlength_correct in Hk; lia).
    destruct (proj1 (Forall_forall _ _) HS (nth (Z.to_nat k) (dc_bs G) (Stored [])) (nth_In _ _ Hn)) as [l E].
    exists l. exact E.
  - (* rl_D0 *)
    intros G k _. unfold bpos. pose proof (rsl_epos_ge (dc_bs G) 0 (Z.to_nat k)). lia.
  - (* rl_align *)
    intros G k HS _. apply rsl_align, HS.
  - (* rl_blk *)
    intros G k bytes HG HS Hk E.
    destruct (rsl_blk G k HG Hk) as [H1 H2]. rewrite E in H1, H2.
    assert (Ha : (bpos G k - D0 G) mod 8 = 0).
    { rewrite Zminus_mod, rsl_align, rsl_D0_mod by exact HS. reflexivity. }
    rewrite rsl_stored_len in H1 by exact Ha.
    split; [lia|]. split; [|split; [|exact H2]].
    + destruct HG as ((_ & _ & _ & (_ & _ & Hb)) & _).
      apply (dt_blocks_nth _ _ _ (Z.to_nat k) _ Hb); [|exact E]. unfold nblk in Hk. rewrite Zlength_correct in Hk. lia.
    + pose proof (dt_endpos_slen G). rewrite rsl_end in H by exact HS.
      destruct (Z.eq_dec (k + 1) (nblk G)) as [Eq|Ne]; [rewrite Eq; lia|].
      pose proof (rsl_mono G (k + 1) (nblk G) HS ltac:(lia) ltac:(lia)). lia.
  - (* rl_mono *)
    intros G j k HS Hj Hk. apply rsl_mono; auto.
  - (* rl_end *)
    intros G HS. apply rsl_end, HS.
Qed.
