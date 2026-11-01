(* Law rfc_level0_blocks (data of any length), main (harness/rfc_level0_blocks.c): the check of the stored
   blocks, from `at = head_len` (after `if (code != Z_STREAM_END) return 0;`) to main's end ([part_loop]),
   from the state [A_loop] of L0B2Blocks.v.  Block i: its length, the gp_assert on the header byte here, the
   rest by L0B2Block.block_rest. *)
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
Require Import Zlib.proof.harness.rfc_level0_blocks.L0B2Block.
Require Zlib.contracts.rfc_level0_blocks.
Require Import Zlib.harness.rfc_level0_blocks.code.
#[local] Existing Instance DCS.CS.

Lemma part_loop {Espec : OracleKind} (gv : globals) (vs ep cp : val) (n hl room tot : Z) (inb H T : list Z)
    (junk : list val) (Fr : mpred) :
  (field_at Ews t_strm (DOT _total_out) (vl tot) vs * Fr |-- data_at_ Tsh t_strm vs * TT)%logic ->
  semax Delta_l0 (A_loop gv vs ep cp n hl room tot inb H T junk Fr) l0_seg24 POST_B.
Proof.
  intros HC.
  unfold l0_seg24, A_loop, POST_B.
  abbreviate_semax.
  Intros.
  forward. forward.
  pose proof (l0_blocks_pos n ltac:(lia)) as HB1. pose proof (l0_blocks_range n H0) as HB17.
  pose proof (l0_blocks_cover n ltac:(lia)) as HBc.
  set (B := l0_blocks n) in *.
  forward_for_simple_bound B
    (EX i : Z,
     PROP ()
     LOCAL (temp _at (vl (hl + 5 * i + Z.min n (65535 * i))); temp _done (vl (Z.min n (65535 * i)));
            temp _data_len (vl n); temp _blocks (vl B); temp _head_len (vl hl);
            temp _expected ep; temp _compressed cp; lvar _strm t_strm vs; gvars gv)
     SEP (data_at Ews (tarray tuchar room) (map vi (H ++ stored_blocks inb ++ T) ++ junk) cp;
          data_at Ews (tarray tuchar n) (map vi inb) ep;
          field_at Ews t_strm (DOT _total_out) (vl tot) vs; Fr))%assert%logic.
  { entailer!. rewrite Z.mul_0_r, Z.min_r by lia. unfold vl; split; do 2 f_equal; lia. }
  - (* block i *)
    assert (Hmin : Z.min n (65535 * i) = 65535 * i)
      by (destruct (l0_blocks_lt n i ltac:(lia) ltac:(lia)) as [| ->]; lia).
    rewrite Hmin.
    destruct (block_at inb i ltac:(rewrite H1; lia)) as (X & Y & HX & EB).
    rewrite H1 in EB.
    set (len := blen n i) in *. set (last := blast n i) in *.
    assert (Hlen : 0 <= len <= 65535 /\ 65535 * i + len <= n) by (subst len; unfold blen; lia).
    (* the five header bytes of block i and its data in the output object *)
    set (d := sublist (65535 * i) (65535 * i + len) inb) in *.
    assert (Hd : Zlength d = len) by (subst d; rewrite Zlength_sublist; lia).
    assert (EC : map vi (H ++ stored_blocks inb ++ T) ++ junk =
                 map vi ((H ++ X) ++ stored_block last d ++ (Y ++ T)) ++ junk)
      by (rewrite EB, <- !app_assoc; reflexivity).
    assert (HHX : Zlength (H ++ X) = hl + 5 * i + 65535 * i) by (rewrite Zlength_app; lia).
    assert (Ehd : forall k, 0 <= k < 5 ->
              Znth (hl + 5 * i + 65535 * i + k) (map vi (H ++ stored_blocks inb ++ T) ++ junk) =
              vi (Znth k [last; len mod 256; len / 256; (65535 - len) mod 256; (65535 - len) / 256])).
    { intros k Hk. rewrite EC, <- HHX, znth_mid by (rewrite Zlength_stored_block, Hd; lia).
      unfold stored_block. rewrite Znth_app1 by list_solve. rewrite Hd. reflexivity. }
    assert (Edata : sublist (hl + 5 * i + 65535 * i + 5) (hl + 5 * i + 65535 * i + 5 + len)
                      (map vi (H ++ stored_blocks inb ++ T) ++ junk) = map vi d).
    { replace (hl + 5 * i + 65535 * i + 5 + len) with (Zlength (H ++ X) + (5 + len)) by lia.
      replace (hl + 5 * i + 65535 * i + 5) with (Zlength (H ++ X) + 5) by lia.
      rewrite EC, sublist_mid by (rewrite ?Zlength_stored_block; lia).
      unfold stored_block. rewrite sublist_app2 by list_solve. f_equal. list_solve. }
    assert (Hsb : Zlength (stored_blocks inb) >= 65540 * i + 5 + len).
    { rewrite EB, !Zlength_app, Zlength_stored_block. pose proof (Zlength_nonneg Y). lia. }
    assert (Hend : hl + 5 * i + 65535 * i + 5 + len <= tot) by lia.
    assert (Hroom : hl + 5 * i + 65535 * i + 5 + len <= room)
      by (rewrite <- H6, !Zlength_app; pose proof (Zlength_nonneg T); pose proof (Zlength_nonneg junk); lia).
    assert (Hlast : last = 1 <-> i + 1 = B) by (subst last; unfold blast; fold B; destruct (Z.eqb_spec (i + 1) B); lia).
    assert (Hdb : sublist (65535 * i) (65535 * i + len) (map vi inb) = map vi d)
      by (subst d; rewrite sublist_map; reflexivity).
    assert (Hdbytes : is_bytes d).
    { subst d. unfold bytes in H2. unfold is_bytes. apply Forall_sublist.
      eapply Forall_impl; [| exact H2]. cbv beta. intros. rep_lia. }
    clearbody d. clear EC HHX EB.
    assert (E0 : Znth (hl + 5 * i + 65535 * i) (map vi (H ++ stored_blocks inb ++ T) ++ junk) = vi last)
      by (rewrite <- (Z.add_0_r (hl + 5 * i + 65535 * i)), Ehd by lia; reflexivity).
    assert (E1 : Znth (hl + 5 * i + 65535 * i + 1) (map vi (H ++ stored_blocks inb ++ T) ++ junk) =
                 vi (len mod 256)) by (rewrite Ehd by lia; reflexivity).
    assert (E2 : Znth (hl + 5 * i + 65535 * i + 2) (map vi (H ++ stored_blocks inb ++ T) ++ junk) =
                 vi (len / 256)) by (rewrite Ehd by lia; reflexivity).
    assert (E3 : Znth (hl + 5 * i + 65535 * i + 3) (map vi (H ++ stored_blocks inb ++ T) ++ junk) =
                 vi ((65535 - len) mod 256)) by (rewrite Ehd by lia; reflexivity).
    assert (E4 : Znth (hl + 5 * i + 65535 * i + 4) (map vi (H ++ stored_blocks inb ++ T) ++ junk) =
                 vi ((65535 - len) / 256)) by (rewrite Ehd by lia; reflexivity).
    clear Ehd.
    assert (Hlast01 : last = 0 \/ last = 1) by (subst last; unfold blast; destruct (_ =? _); auto).
    clearbody last.
    forward.
    forward_if (temp _len (vl len)).
    { rewrite sub64_repr in H9. rewrite !Int64.unsigned_repr in H9 by rep_lia.
      forward. entailer!. unfold vl, blen; rewrite Z.min_r by lia; reflexivity. }
    { rewrite sub64_repr in H9 |- *. rewrite !Int64.unsigned_repr in H9 by rep_lia.
      forward. entailer!. unfold vl, blen; rewrite Z.min_l by lia; reflexivity. }
    forward.
    (* the header byte: BFINAL = 1 on the last block only, BTYPE = 00 *)
    forward_if (temp _t'15 (Vint Int.one)).
    { unfold vl. forward.
      - entailer!. setoid_rewrite E0. destruct Hlast01 as [-> | ->]; compute; congruence.
      - setoid_rewrite E0. forward. entailer!. unfold Int64.cmpu.
        destruct (Z.eq_dec (i + 1) B) as [E|E].
        + assert (last = 1) as -> by (apply Hlast; exact E). rewrite E, Int64.eq_true. reflexivity.
        + assert (last = 0) as -> by (destruct Hlast01; [auto | exfalso; apply E, Hlast; auto]).
          rewrite Int64.eq_false; [reflexivity|].
          intros E'. apply (f_equal Int64.unsigned) in E'. rewrite !Int64.unsigned_repr in E' by rep_lia. lia. }
    { rewrite !add64_repr, !Int64.unsigned_repr in H9 by rep_lia. lia. }
    forward_call Int.one.
    (* the rest of block i: L0B2Block.block_rest *)
    assert (Hnext : Z.min n (65535 * (i + 1)) = 65535 * i + len).
    { subst len; unfold blen.
      destruct (Z.min_spec n (65535 * (i + 1))), (Z.min_spec (n - 65535 * i) 65535); lia. }
    assert (Hok : blk_ok n hl room B i len (map vi (H ++ stored_blocks inb ++ T) ++ junk) (map vi inb) d)
      by (unfold blk_ok; repeat split; auto; lia).
    eapply semax_post_flipped;
      [ eapply semax_pre;
        [| apply (block_rest gv vs ep cp n hl room tot B i len _ _ d Fr Pep Pcp Hok)] | .. ].
    { unfold blk_P. entailer!. }
    { unfold blk_Q, for_ret_assert, POST_l0; simpl RA_normal. entailer!.
      rewrite Hnext. unfold vl. f_equal; f_equal; lia. }
    all: intros; apply andp_left2; simpl; normalize.
  - (* after the last block: return 0, the local z_stream back *)
    forward.
    sep_apply HC. entailer!. Exists (Int.repr 0). entailer!.
Qed.
