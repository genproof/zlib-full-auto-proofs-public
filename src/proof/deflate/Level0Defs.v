(** * The output of deflate at level 0: definitions

    zlib.h, deflateInit: level 0 "gives no compression at all (the input data is simply copied a block at a
    time)".  One deflate(Z_FINISH) on a fresh level-0 stream that is offered all of its data and enough output
    space writes the wrapper header (raw: none; zlib: 2 bytes; gzip: 10), then the data as RFC 1951 stored
    blocks (3.2.4) of 65535 bytes but the last, then the trailer (raw: none; zlib: 4 bytes; gzip: 8).

    [stored_block last d] is one stored block holding [d]: the byte of the three header bits BFINAL = [last],
    BTYPE = 00 padded to a byte boundary, LEN and NLEN = ~LEN (two bytes each, least significant first), the
    bytes of [d].  [stored_blocks d] is the sequence of blocks deflate_stored makes of [d] when the output space
    allows blocks of the maximum size: [l0_blocks (Zlength d)] blocks, all of 65535 bytes but the last, only
    the last with BFINAL set (one empty block for empty data).  [l0_hlen], [l0_tlen], [l0_size] are the
    harness's head_len, trailer_len and size of harness/rfc_level0_size.c. *)
From Coq Require Import ZArith List Lia.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LawFacts.
Import ListNotations.
Local Open Scope Z_scope.

Definition MAX_STORED_LEN : Z := 65535.

(** The wrapper's header and trailer lengths by windowBits (negative: raw; 0..15: zlib; above: gzip). *)
Definition l0_hlen (wbits : Z) : Z := if wbits <? 0 then 0 else if wbits >? 15 then 10 else 2.
Definition l0_tlen (wbits : Z) : Z := if wbits <? 0 then 0 else if wbits >? 15 then 8 else 4.

(** The number of stored blocks of [n] bytes: max(1, ceil(n / 65535)). *)
Definition l0_blocks (n : Z) : Z := if n =? 0 then 1 else (n + 65534) / 65535.

(** Everything deflate writes for [n] bytes of data. *)
Definition l0_size (wbits n : Z) : Z := l0_hlen wbits + 5 * l0_blocks n + n + l0_tlen wbits.

Definition stored_block (last : Z) (d : list Z) : list Z :=
  [last; Zlength d mod 256; Zlength d / 256; (65535 - Zlength d) mod 256; (65535 - Zlength d) / 256] ++ d.

(** At most [k] blocks of [d]. *)
Fixpoint sblocks (k : nat) (d : list Z) : list Z :=
  match k with
  | O => []
  | S k' =>
      if Zlength d <=? MAX_STORED_LEN then stored_block 1 d
      else stored_block 0 (sublist 0 MAX_STORED_LEN d) ++ sblocks k' (sublist MAX_STORED_LEN (Zlength d) d)
  end.

Definition stored_blocks (d : list Z) : list Z := sblocks (Z.to_nat (l0_blocks (Zlength d))) d.

(** ** Basic facts *)

Lemma l0_blocks_pos n : 0 <= n -> 1 <= l0_blocks n.
Proof.
  intros H. unfold l0_blocks. destruct (Z.eqb_spec n 0); [lia|].
  apply Z.div_le_lower_bound; lia.
Qed.

(** A block more than the data after the first 65535 bytes. *)
Lemma l0_blocks_step n : 65535 < n -> l0_blocks n = l0_blocks (n - 65535) + 1.
Proof.
  intros H. unfold l0_blocks.
  destruct (Z.eqb_spec n 0); [lia|]. destruct (Z.eqb_spec (n - 65535) 0); [lia|].
  replace (n + 65534) with ((n - 65535 + 65534) + 1 * 65535) by lia.
  rewrite Z.div_add by lia. reflexivity.
Qed.

Lemma l0_blocks_one n : 0 <= n <= 65535 -> l0_blocks n = 1.
Proof.
  intros H. unfold l0_blocks. destruct (Z.eqb_spec n 0); [reflexivity|].
  symmetry. apply Z.div_unique with (n - 1); lia.
Qed.

Lemma sblocks_enough k d :
  (l0_blocks (Zlength d) <= Z.of_nat k)%Z ->
  sblocks k d = if Zlength d <=? MAX_STORED_LEN then stored_block 1 d
                else stored_block 0 (sublist 0 MAX_STORED_LEN d) ++
                     sblocks (Z.to_nat (l0_blocks (Zlength d - MAX_STORED_LEN))) (sublist MAX_STORED_LEN (Zlength d) d).
Proof.
  revert d. induction k as [|k IH]; intros d Hk.
  - pose proof (l0_blocks_pos (Zlength d) (Zlength_nonneg d)). lia.
  - cbn [sblocks]. unfold MAX_STORED_LEN in *.
    destruct (Z.leb_spec (Zlength d) 65535) as [Hle|Hgt]; [reflexivity|].
    f_equal.
    set (d' := sublist 65535 (Zlength d) d).
    assert (Hl : Zlength d' = Zlength d - 65535) by (subst d'; rewrite Zlength_sublist; lia).
    rewrite l0_blocks_step in Hk by lia.
    (* both sides are the blocks of d': at least l0_blocks of it steps of fuel give the same list *)
    assert (Hfuel : forall j m (e : list Z), (l0_blocks (Zlength e) <= Z.of_nat j)%Z ->
                      (l0_blocks (Zlength e) <= Z.of_nat m)%Z -> sblocks j e = sblocks m e).
    { induction j as [|j IHj]; intros m e Hj Hm.
      - pose proof (l0_blocks_pos (Zlength e) (Zlength_nonneg e)). lia.
      - destruct m as [|m]; [pose proof (l0_blocks_pos (Zlength e) (Zlength_nonneg e)); lia|].
        cbn [sblocks]. unfold MAX_STORED_LEN.
        destruct (Z.leb_spec (Zlength e) 65535); [reflexivity|]. f_equal.
        rewrite l0_blocks_step in Hj, Hm by lia.
        apply IHj; rewrite Zlength_sublist by lia; lia. }
    apply Hfuel; rewrite Hl; [lia|].
    rewrite Z2Nat.id by (pose proof (l0_blocks_pos (Zlength d - 65535)); lia). lia.
Qed.

(** One block, then the blocks of the rest. *)
Lemma stored_blocks_eq d :
  stored_blocks d =
    if Zlength d <=? MAX_STORED_LEN then stored_block 1 d
    else stored_block 0 (sublist 0 MAX_STORED_LEN d) ++ stored_blocks (sublist MAX_STORED_LEN (Zlength d) d).
Proof.
  unfold stored_blocks at 1. rewrite sblocks_enough.
  - unfold MAX_STORED_LEN. destruct (Z.leb_spec (Zlength d) 65535); [reflexivity|].
    unfold stored_blocks. rewrite Zlength_sublist by lia. reflexivity.
  - rewrite Z2Nat.id by (pose proof (l0_blocks_pos (Zlength d) (Zlength_nonneg d)); lia). lia.
Qed.

Lemma Zlength_stored_block last d : Zlength (stored_block last d) = 5 + Zlength d.
Proof. unfold stored_block. rewrite Zlength_app. reflexivity. Qed.

Lemma Zlength_stored_blocks d : Zlength (stored_blocks d) = 5 * l0_blocks (Zlength d) + Zlength d.
Proof.
  remember (Z.to_nat (Zlength d / 65535)) as k eqn:Ek.
  revert d Ek. induction k as [|k IH]; intros d Ek.
  - rewrite stored_blocks_eq. unfold MAX_STORED_LEN.
    destruct (Z.leb_spec (Zlength d) 65535) as [H|H].
    + rewrite Zlength_stored_block, l0_blocks_one by (pose proof (Zlength_nonneg d); lia). lia.
    + exfalso. assert (1 <= Zlength d / 65535) by (apply Z.div_le_lower_bound; lia). lia.
  - rewrite stored_blocks_eq. unfold MAX_STORED_LEN.
    destruct (Z.leb_spec (Zlength d) 65535) as [H|H].
    + rewrite Zlength_stored_block, l0_blocks_one by (pose proof (Zlength_nonneg d); lia). lia.
    + rewrite Zlength_app, Zlength_stored_block, IH.
      * rewrite !Zlength_sublist by lia. rewrite (l0_blocks_step (Zlength d)) by lia. lia.
      * rewrite Zlength_sublist by lia.
        replace (Zlength d - 65535) with ((Zlength d) + (-1) * 65535) by lia.
        rewrite Z.div_add by lia. lia.
Qed.
