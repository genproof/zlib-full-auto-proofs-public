(* Law inflate_dict, theory part: the harness's stream is a decode context of the decode theory (rfc1951/DecodeDefs.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_dict.ITTheoryDefs.
Import ListNotations.
Local Open Scope Z_scope.

Lemma itc_bval_range l : 0 <= bval l < 2 ^ Zlength l.
Proof.
  induction l as [|b r IH]; simpl.
  - rewrite ?Zlength_nil. simpl. lia.
  - rewrite Zlength_cons, Z.pow_succ_r by (pose proof (Zlength_nonneg r); lia).
    destruct b; simpl; lia.
Qed.

Lemma itc_pack_ok bs : bytes_ok (pack bs).
Proof.
  unfold bytes_ok, pack. apply Forall_map, Forall_forall. intros k _.
  set (l := sublist (8 * Z.of_nat k) (8 * Z.of_nat k + 8) bs). pose proof (itc_bval_range l).
  assert (Zlength l <= 8).
  { unfold l, sublist. rewrite Zlength_correct, length_skipn, length_firstn. lia. }
  assert (2 ^ Zlength l <= 2 ^ 8) by (apply Z.pow_le_mono_r; [lia | pose proof (Zlength_nonneg l); lia]).
  unfold Basics.compose; cbv beta; fold l. change (2 ^ 8) with 256 in *. rep_lia.
Qed.

Lemma itc_le_ok v n : bytes_ok (le_bytes v n).
Proof.
  unfold bytes_ok, le_bytes. apply Forall_map, Forall_forall. intros i _.
  pose proof (Z.mod_pos_bound (Z.shiftr v (8 * Z.of_nat i)) 256 ltac:(lia)). unfold Basics.compose; cbv beta. rep_lia.
Qed.

Lemma itc_be_ok v n : bytes_ok (be_bytes v n).
Proof. unfold be_bytes, bytes_ok. apply Forall_rev, itc_le_ok. Qed.

Lemma itc_hdr_ok wb fl fd : 8 <= wb <= 15 -> 0 <= fl <= 3 -> bytes_ok (zlib_hdr wb fl fd).
Proof.
  intros. unfold bytes_ok, zlib_hdr.
  set (c := (31 - _ mod 31) mod 31).
  assert (0 <= c < 31) by (apply Z.mod_pos_bound; lia).
  repeat constructor; destruct fd; rep_lia.
Qed.

Lemma itc_ok : forall G, it_ok G -> dctx_ok (itd G).
Proof.
  intros G (Hwb & Hfl & _ & _ & Hsrc & _ & Hso & Hiw).
  assert (Hb: bytes_ok (it_src G)).
  { unfold it_src, it_wrapper, stream_bytes, deflate_bytes. destruct (g_zlib G).
    - unfold bytes_ok. rewrite !Forall_app. repeat split.
      + apply itc_hdr_ok; auto. pose proof (Z.land_ones (g_flevel G) 2 ltac:(lia)) as E.
        change (Z.ones 2) with 3 in E. rewrite E.
        pose proof (Z.mod_pos_bound (g_flevel G) (2 ^ 2) ltac:(lia)). change (2 ^ 2) with 4 in *. lia.
      + apply itc_be_ok.
      + apply itc_pack_ok.
      + apply itc_be_ok.
    - apply itc_pack_ok. }
  unfold dctx_ok, itd, slen, accepts; simpl. fold (it_src G).
  split; [auto|]. split; [unfold it_wrapper; destruct (g_zlib G); auto|].
  split; [unfold it_wrapper; destruct (g_zlib G); discriminate|].
  split; [intros ? ? ? Hw; unfold it_wrapper in Hw; destruct (g_zlib G); inv Hw; right; reflexivity|].
  split; [lia|]. split; [lia|]. split; [auto|].
  rewrite sublist_same by lia. reflexivity.
Qed.
