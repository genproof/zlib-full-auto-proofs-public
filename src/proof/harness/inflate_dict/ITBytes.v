(* Law inflate_dict: the stream and the data of a well-formed ghost (ITFacts.v it_ok) are bytes (0..255). *)
From Coq Require Import ZArith List Lia.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.harness.inflate_dict.ITFacts.
Import ListNotations.
Local Open Scope Z_scope.

Local Lemma itb_Znth_byte (l: list Z) i : Forall byte_ok l -> byte_ok (Znth i l).
Proof.
  intros H. destruct (zlt i 0); [rewrite Znth_underflow by lia; unfold byte_ok, default, Inhabitant_Z; lia|].
  destruct (zlt i (Zlength l)); [|rewrite Znth_overflow by lia; unfold byte_ok, default, Inhabitant_Z; lia].
  eapply Forall_forall in H; [exact H|]. apply Znth_In. lia.
Qed.

Local Lemma itb_lz_copy n dist out : Forall byte_ok out -> Forall byte_ok (lz_copy n dist out).
Proof.
  revert out; induction n; intros out H; simpl; auto.
  apply IHn. apply Forall_app; split; auto. constructor; auto. apply itb_Znth_byte; auto.
Qed.

Local Lemma itb_syms wmax ll dl syms : forall out,
  syms_ok wmax ll dl out syms -> Forall byte_ok out -> Forall byte_ok (syms_data out syms).
Proof.
  induction syms as [|s r IH]; intros out Hok H; simpl; auto.
  destruct Hok as [Hs Hr]. apply IH; auto.
  destruct s; simpl in *.
  - apply Forall_app; split; auto. constructor; [tauto|constructor].
  - apply itb_lz_copy; auto.
Qed.

Local Lemma itb_blocks wmax bs : forall out,
  blocks_ok wmax out bs -> Forall byte_ok out -> Forall byte_ok (fold_left block_data bs out).
Proof.
  induction bs as [|b r IH]; intros out Hok H; simpl; auto.
  destruct Hok as [Hb Hr]. apply IH; auto.
  destruct b; simpl in *.
  - apply Forall_app; split; tauto.
  - eapply itb_syms; eauto.
  - eapply itb_syms; [apply Hb|auto].
Qed.

Local Lemma itb_is_bytes l : Forall byte_ok l -> is_bytes l.
Proof.
  unfold is_bytes, byte_ok. intros H. eapply Forall_impl; [|exact H]. simpl. rep_lia.
Qed.

Local Lemma itb_sublist lo hi l : Forall byte_ok l -> Forall byte_ok (sublist lo hi l).
Proof.
  intros H. unfold sublist. apply Forall_skipn, Forall_firstn, H.
Qed.

Local Lemma itb_bval bs : 0 <= bval bs < 2 ^ Z.of_nat (length bs).
Proof.
  induction bs as [|b r IH]; cbn [bval length]; [simpl; lia|].
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. destruct b; simpl; lia.
Qed.

Local Lemma itb_pack bs : Forall byte_ok (pack bs).
Proof.
  unfold pack. apply Forall_forall. intros x Hx. apply in_map_iff in Hx. destruct Hx as [k [<- _]].
  set (s := sublist _ _ bs). pose proof (itb_bval s).
  assert (length s <= 8)%nat.
  { subst s. unfold sublist. rewrite skipn_length, firstn_length. lia. }
  red. split; [lia|].
  assert (2 ^ Z.of_nat (length s) <= 2 ^ 8) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Local Lemma itb_be v n : Forall byte_ok (be_bytes v n).
Proof.
  unfold be_bytes, le_bytes. apply Forall_rev. apply Forall_forall. intros x Hx.
  apply in_map_iff in Hx. destruct Hx as [k [<- _]]. red. apply Z.mod_pos_bound. lia.
Qed.

Local Lemma itb_hdr wb fl fd : 8 <= wb <= 15 -> 0 <= fl <= 3 -> Forall byte_ok (zlib_hdr wb fl fd).
Proof.
  intros Hw Hf. unfold zlib_hdr.
  set (c := (wb - 8) * 16 + 8). set (f := fl * 64 + (if fd then 32 else 0)).
  assert (0 <= f <= 224) by (subst f; destruct fd; lia).
  pose proof (Z.mod_pos_bound (c * 256 + f) 31 ltac:(lia)).
  pose proof (Z.mod_pos_bound (31 - (c * 256 + f) mod 31) 31 ltac:(lia)).
  repeat constructor; unfold byte_ok; subst c; lia.
Qed.

Lemma it_bytes G : it_ok G -> is_bytes (it_data G) /\ is_bytes (it_src G).
Proof.
  intros (Hwb & Hfl & _ & _ & _ & _ & Hs & _).
  destruct Hs as (_ & _ & _ & _ & Hh & Hbs).
  assert (Hd: Forall byte_ok (it_data G)).
  { unfold it_data, data, expand. apply itb_sublist. eapply itb_blocks; eauto. }
  split; [apply itb_is_bytes; auto|].
  apply itb_is_bytes. unfold it_src, stream_bytes, it_wrapper. destruct (g_zlib G).
  - assert (0 <= Z.land (g_flevel G) 3 <= 3).
    { replace (Z.land (g_flevel G) 3) with (g_flevel G mod 4)
        by (symmetry; apply (Z.land_ones (g_flevel G) 2); lia).
      pose proof (Z.mod_pos_bound (g_flevel G) 4 ltac:(lia)). lia. }
    cbv beta iota zeta. unfold deflate_bytes.
    apply Forall_app; split; [apply itb_hdr; lia|].
    apply Forall_app; split; [apply itb_be|].
    apply Forall_app; split; [apply itb_pack|apply itb_be].
  - cbv beta iota zeta. unfold deflate_bytes. apply itb_pack.
Qed.
