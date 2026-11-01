(** * deflate_stored's second-phase stored block leaves at most 65535 window bytes unwritten
    ([LTWClipKit.blk2_ub_stmt]): with left = strstart - block_start <= 65536 and
    have = MIN(pending_buf_size - header, 65535) >= 506, a block of min(left, have) bytes is written when
    left >= min_block = MIN(have, w_size), and otherwise left < min_block <= 65535.  strstart and lookahead are
    unchanged (_tr_stored_block and flush_pending only touch the output part of the state). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.deflate.LTWClipKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** flush_pending only moves pending bytes to the output: strstart, block_start and lookahead are kept. *)
Lemma flush_pending_keep_pos s z s' z' :
  c_flush_pending s z = Some (s', z') ->
  d_strstart s' = d_strstart s /\ d_block_start s' = d_block_start s /\ d_lookahead s' = d_lookahead s.
Proof.
  unfold c_flush_pending. intros H.
  destruct (c_tr_flush_bits (d_out s)) as [o|]; cbn in H; [|discriminate].
  destruct (_ =? 0).
  - injection H as <- <-. destruct s; repeat split.
  - destruct (mb_read _ _ _) as [b|]; cbn in H; [|discriminate].
    destruct (out_put _ _) as [z1|]; cbn in H; [|discriminate].
    injection H as <- <-. destruct s; cbn.
    destruct (_ =? 0); repeat split.
Qed.

(** The header size of a stored block: at most 6 bytes when bi_valid <= 7. *)
Lemma stored_hdr_small s : 0 <= d_bi_valid s <= 7 -> 0 <= stored_hdr s <= 6.
Proof.
  intros H. unfold stored_hdr, d_bi_valid, u32 in *.
  rewrite (Z.mod_small (o_bi_valid _) 4294967296) by lia.
  rewrite (Z.mod_small (_ + 42) 4294967296) by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  split; [apply Z.div_pos; lia | apply Z.lt_succ_r, Z.div_lt_upper_bound; lia].
Qed.

Theorem blk2_ub_ok : blk2_ub_stmt.
Proof.
  intros A s z flush K r H Hbv Hpbs Hl.
  pose proof (stored_hdr_small s Hbv) as Hh.
  unfold ds_blk2 in H.
  set (hdr := stored_hdr s) in *.
  set (have := u32 (let a := u64 (d_pending_buf_size s - hdr) in if a >? MAX_STORED then MAX_STORED else a)) in *.
  assert (Hhave : 506 <= have <= 65535).
  { unfold have, u32, u64, MAX_STORED.
    rewrite (Z.mod_small (_ - hdr) 18446744073709551616) by lia.
    destruct (Z.gtb_spec (d_pending_buf_size s - hdr) 65535);
      rewrite Z.mod_small by lia; lia. }
  clearbody have.
  destruct (in_long (d_strstart s - d_block_start s)); cbn in H; [|discriminate].
  assert (Hleft : u32 (d_strstart s - d_block_start s) = d_strstart s - d_block_start s)
    by (unfold u32; apply Z.mod_small; lia).
  rewrite Hleft in H.
  set (left := d_strstart s - d_block_start s) in *.
  set (min_block := if have >? d_w_size s then d_w_size s else have) in *.
  assert (Hmb : min_block <= have) by (unfold min_block; destruct (Z.gtb_spec have (d_w_size s)); lia).
  clearbody min_block.
  destruct (_ || _) eqn:Hc.
  - (* a block of min(left, have) bytes is written: left' = left - min(left, have) <= 65536 - 506 *)
    set (len := if left >? have then have else left) in *.
    assert (Hlen : len = Z.min left have) by (unfold len; destruct (Z.gtb_spec left have); lia).
    clearbody len. subst len.
    destruct (if _ =? 0 then Some [] else _) as [buf|]; cbn in H; [|discriminate].
    destruct (c_tr_stored_block _ _ _ _) as [o|]; cbn in H; [|discriminate].
    destruct (in_long _); cbn in H; [|discriminate].
    destruct (c_flush_pending _ _) as [[s1 z1]|] eqn:Hf; cbn in H; [|discriminate].
    apply flush_pending_keep_pos in Hf. destruct Hf as (E1 & E2 & E3).
    destruct s; cbn in *.
    eexists _, _, _; split; [exact H|]. rewrite E1, E2, E3. cbn.
    unfold left in *. repeat split; try reflexivity; lia.
  - (* nothing is written: left < min_block <= have *)
    apply orb_false_iff in Hc as [Hc _]. destruct (Z.geb_spec left min_block); [discriminate|].
    cbn in H. eexists _, _, _; split; [exact H|]. unfold left in *. repeat split; lia.
Qed.
