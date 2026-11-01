(** * deflate_stored at level 0: the second-phase stored block without a flush_pending hypothesis
    (RTDLTCFlushKit.fpend_ok: bi_valid = 0 after _tr_stored_block).  Proof: with the lemmas of
    RTDLTCStoredBlk2.v, the flush_pending step by fpend_ok. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDLTCStoredKit Zlib.proof.roundtrip.RTDLTCFlushKit.
Require Import Zlib.proof.roundtrip.RTDLTCStoredBlk2.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Theorem blk2_ok2 : sblk_stmt -> blk2_stmt.
Proof.
  intros Hsb s z flush HW Ho Hq Hl Hz Ha Hf Hfin.
  pose proof HW as HW0. pose proof Ho as Ho0. pose proof Hz as Hz0.
  destruct HW as (Hp & Hws & Hwp & Hww & _ & _ & Hl0 & _).
  destruct (Hl0 Hl) as [Hla Hbs0].
  destruct Hp as (P1&P2&P3&P4&P5&P6&P7&P8&P9&P10&P11&P12&P13&P14&P15).
  destruct Hws as (S1&S2&S3&S4&S5).
  destruct Hwp as (A1&A2&A3&A4&A5&A6&A7&A8&A9).
  destruct Hq as (Q1&Q2&Q3).
  destruct Ho as (O1&O2&O3&O4&O5&O6).
  assert (HL : 128 <= d_L s).
  { rewrite P8. replace 128 with (2 ^ 7) by reflexivity. apply Z.pow_le_mono_r; lia. }
  assert (HLu : d_L s <= 32768).
  { rewrite P8. replace 32768 with (2 ^ 15) by reflexivity. apply Z.pow_le_mono_r; lia. }
  assert (HW15 : d_w_size s <= 32768).
  { rewrite P2. replace 32768 with (2 ^ 15) by reflexivity. apply Z.pow_le_mono_r; lia. }
  clear P1 P2 P3 P4 P5 P6 P7 P8 P12 P13 P14 P15 S4 S5 A6 A7 A8 A9 O3 O4 O5 O6 Hl0.
  assert (Hbv : 0 <= d_bi_valid s <= 7) by (destruct O2 as (B1 & _); unfold d_bi_valid in *; lia).
  set (hdr := (d_bi_valid s + 42) / 8).
  assert (Hhdr5 : 5 <= hdr < 7) by (unfold hdr; split; [apply Z.div_le_lower_bound|apply Z.div_lt_upper_bound]; lia).
  assert (Hhdr : stored_hdr s = hdr).
  { unfold stored_hdr, hdr, d_bi_valid, u32 in *. rewrite Z.shiftr_div_pow2 by lia.
    rewrite (Z.mod_small (o_bi_valid _)) by lia. rewrite Z.mod_small by lia. reflexivity. }
  set (have := Z.min (d_pending_buf_size s - hdr) 65535).
  assert (Hhave : u32 (if u64 (d_pending_buf_size s - hdr) >? MAX_STORED then MAX_STORED
                       else u64 (d_pending_buf_size s - hdr)) = have).
  { rewrite u64_id by lia. unfold have, MAX_STORED, u32.
    destruct (Z.gtb_spec (d_pending_buf_size s - hdr) 65535); rewrite Z.mod_small by lia; lia. }
  set (left := d_strstart s - d_block_start s).
  assert (Hlong : in_long left = true) by (unfold in_long, left; rewrite andb_true_iff, !Z.leb_le; lia).
  assert (Hleft : u32 left = left) by (unfold u32, left; apply Z.mod_small; lia).
  assert (Hhv : have = Z.min (d_pending_buf_size s - hdr) 65535) by reflexivity.
  set (mb := if have >? d_w_size s then d_w_size s else have).
  set (len := if left >? have then have else left).
  set (last := if (flush =? Z_FINISH) && (z_avail_in z =? 0) && (len =? left) then 1 else 0).
  set (cnd := (left >=? mb) ||
      ((negb (left =? 0) || (flush =? Z_FINISH)) && negb (flush =? Z_NO_FLUSH) &&
       (z_avail_in z =? 0) && (left <=? have))).
  destruct cnd eqn:Hcnd.
  2:{ exists s, z, 0, [], []. split.
      { intros A K. unfold ds_blk2. cbv zeta. rewrite Hhdr, Hhave. fold left. rewrite Hlong. cbn [guard bind].
        rewrite Hleft. fold mb. fold cnd. rewrite Hcnd. reflexivity. }
      split; [exact HW0|]. split; [exact Ho0|]. split; [reflexivity|].
      split; [apply zstep_refl; auto|]. split; [constructor|].
      split; [cbn [sum_len fold_right]; lia|]. split; [reflexivity|]. split; [constructor|].
      left. split; [reflexivity|split; [constructor|exact Q3]]. }
  assert (Hlen : 0 <= len <= left /\ len <= have /\ (left <= have -> len = left))
    by (unfold len; destruct (Z.gtb_spec left have); lia).
  assert (Hlast : (last = 1 /\ flush = Z_FINISH /\ z_avail_in z = 0 /\ len = left) \/
                  (last = 0 /\ ~ (flush = Z_FINISH /\ z_avail_in z = 0 /\ len = left))).
  { unfold last. destruct (Z.eqb_spec flush Z_FINISH), (Z.eqb_spec (z_avail_in z) 0), (Z.eqb_spec len left);
      cbn [andb]; (left; repeat split; assumption) || (right; split; [reflexivity|tauto]). }
  set (buf := sublist (d_block_start s) (d_block_start s + len) (mb_val (d_window s))).
  assert (Hbuf : (if len =? 0 then Some [] else mb_read (d_window s) (d_block_start s) len) = Some buf).
  { destruct (Z.eqb_spec len 0) as [E|E].
    - unfold buf. rewrite E, Z.add_0_r, sublist_nil. reflexivity.
    - apply mb_read_ok; [|lia]. split; [lia|]. split; [rewrite S1; lia|].
      intros i Hi. apply Hww. lia. }
  assert (Hbl : Zlength buf = len) by (unfold buf; rewrite Zlength_sublist; lia).
  assert (Hbb : bytes buf).
  { unfold bytes. apply Forall_forall. intros v Hv. apply In_Znth in Hv. destruct Hv as (j & Hj & <-).
    unfold buf in *. rewrite Zlength_sublist in Hj by lia. rewrite Znth_sublist by lia.
    destruct S2 as [S2a S2b]. apply S2b; [lia|]. apply Hww. lia. }
  destruct (Hsb (tr_out (d_tr s)) (d_pbm s) buf len last) as (o' & m' & Hst & Sp & Sbv & Sbo & Sbp & Sg & Sd).
  { exact O2. }
  { destruct Hlast as [(-> & _)|(-> & _)]; lia. }
  { lia. }
  { unfold MAX_STORED. lia. }
  { exact Hbb. }
  { lia. }
  { change (o_pending (tr_out (d_tr s))) with (d_pending s).
    change ((o_bi_valid (tr_out (d_tr s)) + 42) / 8) with hdr. lia. }
  change (o_pending (tr_out (d_tr s))) with (d_pending s) in Sp, Sd.
  change ((o_bi_valid (tr_out (d_tr s)) + 42) / 8) with hdr in Sp.
  unfold bitpos in Sbp. change (o_bi_valid (tr_out (d_tr s))) with (d_bi_valid s) in Sbp.
  change (o_pending (tr_out (d_tr s))) with (d_pending s) in Sbp.
  rewrite Q1, Z.mul_0_r, Z.add_0_l in Sbp. rewrite Q1, Z.add_0_l in Sp.
  destruct Sg as (G1 & G2 & G3 & G4).
  assert (Hlong2 : in_long (d_block_start s + len) = true)
    by (unfold in_long; rewrite andb_true_iff, !Z.leb_le; lia).
  set (s2 := set_d_block_start (set_d_out s (o', m')) (d_block_start s + len)).
  assert (Hos2 : outok s2).
  { unfold outok, d_pb. change (tr_out (d_tr s2)) with o'. change (d_pbm s2) with m'.
    change (d_po s2) with (d_po s). change (d_pending s2) with (o_pending o').
    change (d_pending_buf_size s2) with (d_pending_buf_size s). rewrite Q2.
    split; [apply G4, O1|]. split; [exact Sbo|]. split; [lia|]. split; [lia|].
    split; [|intros; reflexivity].
    split; [lia|]. split; [cbn [mb_val]; lia|]. intros i Hi. cbn [mb_def]. apply Sd. lia. }
  assert (Hr2 : fp_room s2) by (left; change (d_bi_valid s2) with (o_bi_valid o'); lia).
  assert (Hpb2 : d_pending_buf_size s2 = Zlength (o_buf (tr_out (d_tr s2)))).
  { change (d_pending_buf_size s2) with (d_pending_buf_size s). change (tr_out (d_tr s2)) with o'. lia. }
  assert (Hpb3 : d_pending_buf_size s2 <= 131072).
  { change (d_pending_buf_size s2) with (d_pending_buf_size s). lia. }
  destruct (fpend_ok s2 z Hpb2 Hpb3 Hos2 (proj2 Hz) Hr2) as (s' & z' & x & Hfe & Hzo & Hxb & Hxl & Hpend & Hbv' & Hos' & HGb & Hfk & Hpg).
  change (d_pending s2) with (o_pending o') in Hxl, Hpend.
  change (d_bi_valid s2) with (o_bi_valid o') in Hxl, Hbv'.
  rewrite Sbv in Hxl, Hbv'. rewrite Z.div_0_l, Z.add_0_r in Hxl by lia. rewrite Z.mod_0_l in Hbv' by lia.
  destruct (fp_fields _ _ Hfk) as (F1 & F2 & F3).
  change (d_block_start s2) with (d_block_start s + len) in F1.
  change (d_strstart s2) with (d_strstart s) in F2.
  change (d_lookahead s2) with (d_lookahead s) in F3.
  assert (Hob : ob_keep s' = ob_keep s).
  { rewrite (ob_keep_fp _ _ Hfk). reflexivity. }
  pose proof Hzo as Hzo'.
  destruct Hzo as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9).
  exists s', z', last, [DStored (Gb s (z_total_out z)) len last], x. split.
  { intros A K. unfold ds_blk2. cbv zeta. rewrite Hhdr, Hhave. fold left. rewrite Hlong. cbn [guard bind].
    rewrite Hleft. fold mb len. fold last. fold cnd. rewrite Hcnd. rewrite Hbuf. cbn [bind].
    change (d_out s) with (tr_out (d_tr s), d_pbm s). rewrite Hst. cbn [bind].
    change (d_block_start (set_d_out s (o', m'))) with (d_block_start s). rewrite Hlong2. cbn [guard bind].
    fold s2. rewrite Hfe. cbn [bind]. reflexivity. }
  assert (Hleq : left = d_strstart s - d_block_start s) by reflexivity.
  assert (Hao : 0 <= z_avail_out z) by (destruct Hz as [_ [? _]]; lia).
  destruct Hpg as (H1 & H2 & H3 & H4).
  split.
  { apply (W_ob s s' HW0 Hl Hob).
    - rewrite H1. exact G1.
    - rewrite H2. exact G2.
    - rewrite F1. lia. }
  split; [exact Hos'|]. split; [exact Hob|].
  split; [apply zout_only_zstep; [exact Hz|exact Ha|exact Hzo'|lia]|].
  split; [exact Hxb|].
  split; [unfold ub; cbn [sum_len fold_right ev_len]; rewrite F1, F2, F3; lia|].
  split.
  { cbn [ev_chain ev_g ev_after]. split; [reflexivity|].
    rewrite HGb. unfold Gb. change (d_pending s2) with (o_pending o'). change (d_bi_valid s2) with (o_bi_valid o').
    rewrite Q1, Sbv.
    replace (8 * (z_total_out z + 0) + d_bi_valid s + 10) with ((d_bi_valid s + 10) + z_total_out z * 8) by ring.
    rewrite Z.div_add by lia. lia. }
  split.
  { constructor; [|constructor]. cbn [ev_ok]. split; [exact Hl|]. split; [unfold MAX_STORED; lia|].
    destruct Hlast as [(E1 & E2 & E3 & E4)|(E1 & E2)]; rewrite E1.
    - split; [lia|]. split; [auto|]. intros; lia.
    - split; [lia|]. split; [intros; lia|]. intros _.
      apply orb_true_iff in Hcnd. destruct Hcnd as [Hc|Hc].
      + right. apply Z.geb_le in Hc. clear - Hc Hhv Hhdr5 HW15. unfold mb in Hc. unfold len.
        destruct (Z.gtb_spec have (d_w_size s)), (Z.gtb_spec left have); lia.
      + left. rewrite !andb_true_iff in Hc. destruct Hc as (((Hc1 & Hc2) & Hc3) & Hc4).
        apply negb_true_iff, Z.eqb_neq in Hc2. apply Z.eqb_eq in Hc3. apply Z.leb_le in Hc4.
        split; [exact Hc2|]. intros Ef. apply E2. split; [exact Ef|]. split; [exact Hc3|]. apply Hlen; exact Hc4. }
  destruct Hlast as [(E1 & E2 & E3 & E4)|(E1 & E2)].
  - right. split; [exact E1|].
    split; [exists [], (DStored (Gb s (z_total_out z)) len last); split; [reflexivity|];
            split; [cbn; exact E1|constructor]|].
    split; [exact E2|]. split; [exact E3|]. split; [unfold ub; rewrite F1, F2, F3; lia|]. split; [exact Hbv'|].
    rewrite Z8, Hxl. specialize (Hfin E2). rewrite Hhdr, E3 in Hfin. rewrite Sp. lia.
  - left. split; [exact E1|]. split; [constructor; [cbn; exact E1|constructor]|lia].
Qed.
