(** * Core part of the deflate law theory: small shared lemmas (streams, outok, flush_pre) *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDLTCSpecs.
Require Zlib.proof.crc32.Combine.
Require Import compcert.lib.Integers.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Lemma bytes_is_bytes l : bytes l -> Zlib.proof.adler32.Bytes.is_bytes l.
Proof.
  unfold bytes, Zlib.proof.adler32.Bytes.is_bytes. intros H. eapply Forall_impl; [|exact H].
  intros a Ha. cbv beta in *. replace Byte.max_unsigned with 255 by reflexivity. lia.
Qed.

Lemma bytes_sublist l lo hi : bytes l -> bytes (sublist lo hi l).
Proof.
  unfold bytes. intros H. apply Forall_forall. intros x Hx.
  apply sublist_In in Hx. rewrite Forall_forall in H. auto.
Qed.

Lemma zin_ok_zall z : zin_ok z -> zall z.
Proof.
  unfold zin_ok, zall, zin_in, zout_ok. intros (? & ? & ? & ? & ? & ? & ?). repeat split; auto; lia.
Qed.

Lemma adler_upd_nil w a : adler_ok w a -> adler_upd w a [] = a.
Proof.
  intros [H1 H2]. unfold adler_upd.
  destruct (Z.eqb_spec w 1) as [->|N1].
  - destruct (H1 eq_refl) as (Ha & _ & _).
    unfold Zlib.proof.adler32.Model.ref_adler32, Zlib.proof.adler32.Model.adler_pack,
      Zlib.proof.adler32.Model.adler_lo, Zlib.proof.adler32.Model.adler_hi. cbn [fold_left fst snd].
    rewrite (Z.mod_small (a / 65536)) by (split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]).
    pose proof (Z.div_mod a 65536 ltac:(lia)). lia.
  - destruct (Z.eqb_spec w 2) as [->|N2]; [|reflexivity].
    specialize (H2 eq_refl).
    unfold Zlib.proof.crc32.Model.ref_crc32. cbn [fold_left].
    rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r. apply Z.mod_small. lia.
Qed.

Lemma u64_id x : 0 <= x < 18446744073709551616 -> u64 x = x.
Proof. intros H. unfold u64. apply Z.mod_small. exact H. Qed.

Lemma zstep_refl w z : zall z -> adler_ok w (z_adler z) -> zstep w z z 0 [].
Proof.
  intros [(Hb & Hn & Ha & Hl & Ht) (Ho & Hto & Hs)] Hd.
  unfold zstep. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [rewrite Z.add_0_r; symmetry; apply u64_id; lia|].
  split; [rewrite Z.add_0_r, sublist_nil, adler_upd_nil; auto|].
  split; [rewrite app_nil_r; reflexivity|]. split; [cbn; lia|]. split; [cbn; lia|].
  split; [cbn; rewrite Z.add_0_r; symmetry; apply u64_id; lia|]. reflexivity.
Qed.

Lemma zout_only_zstep w z z' x :
  zall z -> adler_ok w (z_adler z) -> zout_only z z' x -> 0 <= z_avail_out z' -> zstep w z z' 0 x.
Proof.
  intros [(Hb & Hn & Ha & Hl & Ht) (Ho & Hto & Hs)] Hd (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9) Hz'.
  unfold zstep. split; [auto|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [rewrite E4, Z.add_0_r; symmetry; apply u64_id; lia|].
  split; [rewrite E5, Z.add_0_r, sublist_nil, adler_upd_nil; auto|].
  split; [auto|]. split; [lia|]. split; [auto|].
  pose proof (Zlength_nonneg x). split; [rewrite E9; symmetry; apply u64_id; lia|]. auto.
Qed.

Lemma adler_ok_upd w a d : bytes d -> adler_ok w a -> adler_ok w (adler_upd w a d).
Proof.
  intros Hb [H1 H2]. unfold adler_upd. split; intros ->; cbn.
  - apply Zlib.proof.adler32.Model.ref_adler32_valid. auto.
  - pose proof (Zlib.proof.crc32.Combine.ref_crc32_range a d (bytes_is_bytes d Hb)) as R.
    unfold Zlib.proof.crc32.GF2.is32 in R. lia.
Qed.

Lemma adler_upd_app w a d1 d2 :
  bytes d1 -> adler_ok w a -> adler_upd w (adler_upd w a d1) d2 = adler_upd w a (d1 ++ d2).
Proof.
  intros Hb [H1 H2]. unfold adler_upd.
  destruct (Z.eqb_spec w 1) as [->|N1].
  - apply Zlib.proof.adler32.Model.ref_adler32_app. auto.
  - destruct (Z.eqb_spec w 2) as [->|N2]; [|reflexivity].
    apply Zlib.proof.crc32.Combine.ref_crc32_app. apply bytes_is_bytes. auto.
Qed.

Lemma u64_add_u64 a b : u64 (u64 a + b) = u64 (a + b).
Proof. unfold u64. rewrite Zplus_mod_idemp_l. reflexivity. Qed.

Lemma zstep_trans w z1 z2 z3 k1 x1 k2 x2 :
  zin_in z1 -> adler_ok w (z_adler z1) ->
  zstep w z1 z2 k1 x1 -> zstep w z2 z3 k2 x2 -> zstep w z1 z3 (k1 + k2) (x1 ++ x2).
Proof.
  intros (Hb & Hn & Ha & Hl & Ht) Hd
    (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A7x & A8 & A9 & A10)
    (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B7x & B8 & B9 & B10).
  rewrite A8 in B7x.
  unfold zstep. rewrite B1, B3, B4, B5, B6, B7, B8, B9, B10, A1, A3, A4, A5, A6, A7, A8, A9, A10.
  rewrite A1, A3 in *. rewrite A4 in B2.
  rewrite app_assoc, u64_add_u64, u64_add_u64, Zlength_app.
  rewrite adler_upd_app by (auto; apply bytes_sublist; auto).
  replace (z_next_in z1 + k1 + k2) with (z_next_in z1 + (k1 + k2)) by lia.
  rewrite <- (sublist_split (z_next_in z1) (z_next_in z1 + k1) (z_next_in z1 + (k1 + k2))) by lia.
  repeat split; auto; try lia; f_equal; lia.
Qed.

Lemma zall_zstep w z z' k x : zall z -> zstep w z z' k x -> 0 <= z_avail_out z' -> zall z'.
Proof.
  intros [(Hb & Hn & Ha & Hl & Ht) (Ho & Hto & Hs)] (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A7x & A8 & A9 & A10) Hz.
  unfold zall, zin_in, zout_ok. rewrite A1, A3, A4, A5, A9.
  pose proof (Zlength_nonneg x). rewrite (u64_id (z_total_out z + Zlength x)) by lia.
  repeat split; auto; try lia; unfold u64; apply Z.mod_pos_bound; lia.
Qed.

(** outok after a step that keeps pending_out, pending and the buffer size and only grows pending_buf. *)
Lemma outok_grow s s' :
  outok s -> pb_grow (tr_out (d_tr s)) (d_pbm s) (tr_out (d_tr s')) (d_pbm s') ->
  d_po s' = d_po s -> d_pending s' = d_pending s -> d_pending_buf_size s' = d_pending_buf_size s ->
  bits_ok (tr_out (d_tr s')) -> outok s'.
Proof.
  unfold outok, d_pb. intros (Hm & Hb & Hp0 & Hp1 & [Hd0 [Hd1 Hd2]] & Hz) (G1 & G2 & G3 & G4) E1 E2 E3 Hb'.
  rewrite E1, E2, E3. cbn [mb_val mb_def] in *.
  split; [apply G4, Hm|]. split; [exact Hb'|]. split; [lia|]. split; [lia|].
  split; [split; [lia|split; [cbn; lia|intros i Hi; cbn; apply G3, Hd2; lia]]|]. exact Hz.
Qed.

(** The precondition of lemma (i) from the parts of [W], outok and quiet. *)
Lemma flush_pre_of s syms :
  prm s -> tree_ok (d_tr s) (d_pbm s) syms -> Zlength syms <= d_L s - 1 -> outok s -> quiet s ->
  flush_pre (d_tr s) syms.
Proof.
  intros Hp (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10) HL Ho (Q1 & Q2 & Q3).
  destruct Hp as (_ & _ & _ & Hhb & _ & _ & _ & HLe & _).
  unfold d_L in *.
  constructor.
  - exists (d_hash_bits s - 7). split; [lia|]. rewrite HLe. f_equal. lia.
  - destruct Ho as (_ & Hb & _). unfold d_pending, d_bi_valid in *. split; [exact Hb|]. split; [exact Q1|]. split; [exact Q3|]. exact T1.
  - refine (conj T3 (conj HL (conj T4 _))).
    intros i Hi. assert (E := f_equal (Znth i) T5).
    rewrite Znth_sublist in E by lia. rewrite Z.add_comm. exact E.
  - exact T7.
  - exact T8.
  - exact T9.
  - exact T10.
Qed.
