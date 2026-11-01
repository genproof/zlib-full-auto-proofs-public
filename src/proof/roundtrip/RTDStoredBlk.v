(* RT-D part STORED: the second-phase stored block ds_blk2 (statement: RTDStoredKit.v).
   Proof: the safety proof RTDLTCStoredBlk2b.blk2_ok2 redone with the run given, plus the bits of
   _tr_stored_block (stored_block_fspec) and of flush_pending (fpend_fspec2). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDStoredKit.
Require Import Zlib.proof.roundtrip.RTDLTCFlushKit Zlib.proof.roundtrip.RTDLTCStoredBlk2 Zlib.proof.roundtrip.RTDLTCStoredSblk.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Lemma rtdsb_Zlength_bits_le v n : 0 <= n -> Zlength (F.bits_le v n) = n.
Proof. intros H. unfold F.bits_le. rewrite Zlength_map, Zlength_correct, seq_length. lia. Qed.

Lemma rtdsb_Zlength_zeros n : 0 <= n -> Zlength (F.zeros n) = n.
Proof. intros H. unfold F.zeros. rewrite Zlength_correct, repeat_length. lia. Qed.

Lemma rtdsb_Zlength_bytes_bits l : Zlength (F.bytes_bits l) = 8 * Zlength l.
Proof.
  induction l as [|b l IH]; [reflexivity|].
  unfold F.bytes_bits in *. cbn [flat_map]. rewrite Zlength_app, IH, Zlength_cons, rtdsb_Zlength_bits_le by lia.
  lia.
Qed.

Lemma rtdsb_pad8_range q : 0 <= F.pad8 q < 8 /\ (q + F.pad8 q) mod 8 = 0.
Proof. unfold F.pad8. split; Z.div_mod_to_equations; lia. Qed.

Lemma rtdsb_enc_out1 p fin buf :
  enc_out p [F.Stored buf] fin = F.enc_block p fin (F.Stored buf).
Proof.
  unfold enc_out. cbn [enc_from]. rewrite andb_true_r, app_nil_r.
  destruct fin; [|reflexivity].
  replace (F.pad8 (p + Zlength (F.enc_block p true (F.Stored buf)))) with 0; [change (F.zeros 0) with (@nil bool); apply app_nil_r|].
  unfold F.enc_block. rewrite Zlength_cons, !Zlength_app, rtdsb_Zlength_zeros, !rtdsb_Zlength_bits_le,
    rtdsb_Zlength_bytes_bits by (try lia; apply rtdsb_pad8_range).
  destruct (rtdsb_pad8_range (p + 3)) as [R1 R2].
  set (q := F.pad8 (p + 3)) in *. clearbody q. change (Zlength [false; false]) with 2. unfold F.pad8.
  Z.div_mod_to_equations; lia.
Qed.

Theorem rtds_blk_ok : stored_block_fspec -> fpend_fspec2 -> fblk2_stmt.
Proof.
  intros Hsf Hfp s z flush s0 z0 lst p HW Ho Hq Hl Hz Ha Hf Hfin Hds Hp0 Hpm0.
  pose proof sblk_ok as Hsb.
  pose proof (Hds _ (fun a b c => Some (a, b, c))) as Hrun. cbv beta in Hrun. clear Hds.
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
  2:{ unfold ds_blk2 in Hrun. cbv zeta in Hrun. rewrite Hhdr, Hhave in Hrun. fold left in Hrun.
      rewrite Hlong in Hrun. cbn [guard bind] in Hrun.
      rewrite Hleft in Hrun. fold mb in Hrun. fold cnd in Hrun. rewrite Hcnd in Hrun. cbn [bind] in Hrun.
      injection Hrun as <- <- <-.
      exists [], []. split; [apply zstep_refl; auto|]. split; [constructor|].
      split; [rewrite sublist_nil; reflexivity|].
      split; [|discriminate].
      unfold pend. rewrite Q1, Z.add_0_r, sublist_nil.
      change (enc_out p (map F.Stored []) (0 =? 1)) with (@nil bool). rewrite app_nil_r. symmetry. apply app_nil_r. }
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
  destruct (Hsf (tr_out (d_tr s)) (d_pbm s) buf len last o' m' p) as (_ & _ & Hob').
  { exact O2. }
  { destruct Hlast as [(-> & _)|(-> & _)]; lia. }
  { lia. }
  { right. lia. }
  { rewrite sublist_same by lia. exact Hbb. }
  { exact Hp0. }
  { exact Hpm0. }
  { exact Hst. }
  rewrite sublist_same in Hob' by lia.
  change (o_pending (tr_out (d_tr s))) with (d_pending s) in Sp, Sd.
  change ((o_bi_valid (tr_out (d_tr s)) + 42) / 8) with hdr in Sp.
  rewrite Q1, Z.add_0_l in Sp.
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
  destruct (fpend_ok s2 z Hpb2 Hpb3 Hos2 (proj2 Hz) Hr2)
    as (s1 & z1 & x & Hfe & Hzo & Hxb & Hxl & Hpend & Hbv' & Hos' & HGb & Hfk & Hpg).
  change (d_pending s2) with (o_pending o') in Hxl, Hpend.
  change (d_bi_valid s2) with (o_bi_valid o') in Hxl, Hbv'.
  rewrite Sbv in Hxl, Hbv'. rewrite Z.div_0_l, Z.add_0_r in Hxl by lia.
  destruct (fp_fields _ _ Hfk) as (F1 & F2 & F3).
  change (d_block_start s2) with (d_block_start s + len) in F1.
  unfold ds_blk2 in Hrun. cbv zeta in Hrun. rewrite Hhdr, Hhave in Hrun. fold left in Hrun.
  rewrite Hlong in Hrun. cbn [guard bind] in Hrun.
  rewrite Hleft in Hrun. fold mb len in Hrun. fold last in Hrun. fold cnd in Hrun. rewrite Hcnd in Hrun.
  rewrite Hbuf in Hrun. cbn [bind] in Hrun.
  change (d_out s) with (tr_out (d_tr s), d_pbm s) in Hrun. rewrite Hst in Hrun. cbn [bind] in Hrun.
  change (d_block_start (set_d_out s (o', m'))) with (d_block_start s) in Hrun. rewrite Hlong2 in Hrun.
  cbn [guard bind] in Hrun.
  fold s2 in Hrun. rewrite Hfe in Hrun. cbn [bind] in Hrun.
  injection Hrun as <- <- <-.
  assert (Hbv2 : d_bi_valid s2 < 8 \/ d_po s2 = 0) by (left; change (d_bi_valid s2) with (o_bi_valid o'); lia).
  destruct (Hfp s2 z s1 z1 Hos2 (proj2 Hz) Hbv2 Hfe) as (x' & Hzo2 & Hbits).
  assert (Hxx : x' = x).
  { destruct Hzo as (_ & _ & _ & _ & _ & _ & E1 & _). destruct Hzo2 as (_ & _ & _ & _ & _ & _ & E2 & _).
    rewrite E1 in E2. apply app_inv_head in E2. auto. }
  subst x'.
  pose proof Hzo as Hzo'.
  destruct Hzo as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9).
  exists x, [buf]. split.
  { apply zout_only_zstep; [exact Hz|exact Ha|exact Hzo'|]. rewrite Z8, Hxl. destruct Hz as [_ [? _]]. lia. }
  split; [constructor; [lia|constructor]|].
  split; [cbn [concat]; rewrite app_nil_r, F1; reflexivity|].
  split; [|intros _; discriminate].
  rewrite Hbits. cbn [map]. rewrite rtdsb_enc_out1.
  assert (E2 : F.bytes_bits (pend s2) ++ bibits s2 = obits o').
  { unfold pend, bibits, obits. change (d_po s2) with (d_po s). change (d_pending s2) with (o_pending o').
    change (tr_out (d_tr s2)) with o'. change (d_bi_valid s2) with (o_bi_valid o'). rewrite Q2, Z.add_0_l.
    reflexivity. }
  rewrite E2, Hob'. unfold obits, bibits.
  change (o_pending (tr_out (d_tr s))) with (d_pending s). rewrite Q1, sublist_nil.
  reflexivity.
Qed.
