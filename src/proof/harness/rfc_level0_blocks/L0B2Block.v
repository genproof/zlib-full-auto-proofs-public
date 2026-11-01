(* Law rfc_level0_blocks (data of any length), main (harness/rfc_level0_blocks.c): block i of the check of the
   stored blocks after its header byte (L0B2Blocks.blk_rest): the gp_asserts on LEN and NLEN, bytes_eq of the
   block's data with the next len bytes of the copy of the data, then `at += 5 + len; done += len`. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.Rep Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.deflate.Level0Defs.
Require Import Zlib.proof.harness.rfc_level0_blocks.L0B2MainStmt.
Require Import Zlib.proof.harness.rfc_level0_blocks.L0B2Kit.
Require Import Zlib.proof.harness.rfc_level0_size.L0Kit2.
Require Import Zlib.proof.harness.rfc_level0_blocks.L0B2Blocks.
Require Zlib.contracts.rfc_level0_blocks.
Require Import Zlib.harness.rfc_level0_blocks.code.
#[local] Existing Instance DCS.CS.

Lemma block_rest {Espec : OracleKind} (gv : globals) (vs ep cp : val) (n hl room tot B i len : Z)
    (C Dv : list val) (d : list Z) (Fr : mpred) :
  isptr ep -> isptr cp -> blk_ok n hl room B i len C Dv d ->
  semax Delta_l0 (blk_P gv vs ep cp n hl room tot B i len C Dv Fr) blk_rest
    (normal_ret_assert (blk_Q gv vs ep cp n hl room tot B i len C Dv Fr)).
Proof.
  intros Pep Pcp (Hn & Hhl & Hi & HB & Hlen & Hlen' & Hroom & Hrm & E1 & E2 & E3 & E4 & Edata & Hd & Hdbytes & Hdb).
  unfold blk_rest, blk_P, blk_Q.
  abbreviate_semax.
  (* LEN and NLEN, two bytes each, least significant first *)
  assert (Hby : 0 <= len mod 256 < 256 /\ 0 <= len / 256 < 256 /\ 0 <= (65535 - len) mod 256 < 256 /\
               0 <= (65535 - len) / 256 < 256).
  { repeat split; try apply Z.mod_pos_bound; try lia;
      first [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia. }
  assert (Hlh : len mod 256 + 256 * (len / 256) = len) by (pose proof (Z.div_mod len 256); lia).
  assert (Hlh' : (65535 - len) mod 256 + 256 * ((65535 - len) / 256) = 65535 - len)
    by (pose proof (Z.div_mod (65535 - len) 256); lia).
  set (lo := len mod 256) in *. set (hi := len / 256) in *.
  set (lo' := (65535 - len) mod 256) in *. set (hi' := (65535 - len) / 256) in *.
  clearbody lo hi lo' hi'.
  assert_PROP (Zlength C = room /\ Zlength Dv = n) as HCD by (entailer!; list_solve).
  destruct HCD as [HC HD].
  unfold vl. forward.
  { entailer!. setoid_rewrite E1. apply is_int_vi_byte. lia. }
  forward.
  { entailer!. setoid_rewrite E2. apply is_int_vi_byte. lia. }
  setoid_rewrite E1. setoid_rewrite E2.
  forward_call Int.one.
  { entailer!. rewrite Hlh, Int64.eq_true. reflexivity. }
  forward.
  { entailer!. setoid_rewrite E3. apply is_int_vi_byte. lia. }
  forward.
  { entailer!. setoid_rewrite E4. apply is_int_vi_byte. lia. }
  setoid_rewrite E3. setoid_rewrite E4.
  forward_call Int.one.
  { entailer!. rewrite Hlh', Int64.eq_true. reflexivity. }
  (* the LEN bytes of the block are the next bytes of the data *)
  rewrite <- !l0_bytes_cs.
  forward_call (offset_val (hl + 5 * i + 65535 * i + 5) cp, Ews, cp, hl + 5 * i + 65535 * i + 5, room,
                C, d, offset_val (65535 * i) ep, Ews, ep, 65535 * i, n, Dv, d, len).
  { split; unfold cbuf_ok; repeat split; auto; try lia. }
  destruct (list_eq_dec Z.eq_dec d d) as [_ | Cn]; [| congruence].
  rewrite !l0_bytes_cs.
  forward_call Int.one.
  forward. forward.
  entailer!. unfold vl. f_equal; f_equal; lia.
Qed.
