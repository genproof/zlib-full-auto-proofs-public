(** * Level 0 over several deflate() calls: deflate_stored in one call

    deflate_stored on a level-0 state with nothing pending, an empty bit buffer and nothing left in the window
    (strstart = block_start), as in every call of the harnesses' loop after the header:
    - [l0c_stored_nf]: with Z_NO_FLUSH, offered [k] whole blocks of 65535 bytes and room for them, it writes [k]
      non-final stored blocks straight from next_in, keeps the last w_size bytes in the window (strstart =
      block_start again) and returns need_more;
    - [l0c_stored_fin]: with Z_FINISH, offered the rest of the data (at most 2^32 - 1 bytes) and room for its
      stored blocks, it writes them, the last one final, and returns finish_done.
    Both leave nothing pending and the configuration of the state ([LTCStored2.cp]: status, wrap, gzip header,
    level, ...) unchanged. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.Level0CallsIter.
Require Import Zlib.proof.deflate.LTCStored2.
Require Import Zlib.proof.deflate.LTCStoredLoopLib.
Require Zlib.proof.wide.deflate.LTCStoredWin.
Require Zlib.proof.deflate.LTCStoredChain.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Lemma ob_ob_set_g s0 b u m : ob s0 b u m = ob_set s0 (mkOut b 0 0 0 u) m 0 (d_block_start s0).
Proof. reflexivity. Qed.

Lemma min_block_pos s : prm s -> 0 < ds_min_block s.
Proof.
  intros Hp. destruct (prm_pbsize s Hp) as [E1 E2].
  destruct Hp as (Hwb & Hws & _ & Hhb & _ & _ & _ & HL & Hps & _).
  assert (2 ^ 7 <= 2 ^ (d_hash_bits s - 1)) by (apply Z.pow_le_mono_r; lia).
  assert (2 ^ 9 <= 2 ^ d_w_bits s <= 2 ^ 15) by (split; apply Z.pow_le_mono_r; lia).
  unfold ds_min_block. cbv zeta. rewrite (u64_id (d_pending_buf_size s - 5)) by lia.
  rewrite min_if', u32_id by lia. lia.
Qed.

(** The second-phase refill does nothing when no input is left. *)
Lemma fill2_none {A} s z (K : dstate -> strm -> option A) :
  z_avail_in z = 0 -> ds_fill2 s z K = K (upd_high_water s) z.
Proof.
  intros H. unfold ds_fill2. rewrite H.
  set (h := u32 (u64 (d_window_size s - d_strstart s))).
  assert (Hh : 0 <= h) by (unfold h, u32; apply Z.mod_pos_bound; lia).
  replace (0 >? h) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
  cbn [andb bind].
  replace (if h >? 0 then 0 else h) with 0 by (destruct (Z.gtb_spec h 0); lia).
  reflexivity.
Qed.

(** The second-phase block with Z_NO_FLUSH and nothing in the window ([left = 0]) is not written. *)
Lemma blk2_nf {A} s z (K : dstate -> strm -> Z -> option A) :
  d_strstart s = d_block_start s -> 0 < d_w_size s -> 0 <= stored_hdr s < d_pending_buf_size s ->
  d_pending_buf_size s < 4294967296 ->
  ds_blk2 s z Z_NO_FLUSH K = K s z 0.
Proof.
  intros Hss Hw Hh Hp. unfold ds_blk2. rewrite Hss, Z.sub_diag.
  change (in_long 0) with true. change (u32 0) with 0. cbn [bind guard].
  rewrite (u64_id (d_pending_buf_size s - stored_hdr s)) by lia.
  set (h := u32 (if d_pending_buf_size s - stored_hdr s >? MAX_STORED then MAX_STORED
                 else d_pending_buf_size s - stored_hdr s)).
  assert (Hh0 : 0 < h).
  { unfold h, MAX_STORED. destruct (Z.gtb_spec (d_pending_buf_size s - stored_hdr s) 65535);
      rewrite u32_id; lia. }
  replace (0 >=? (if h >? d_w_size s then d_w_size s else h)) with false
    by (symmetry; rewrite Z.geb_leb; apply Z.leb_gt; destruct (Z.gtb_spec h (d_w_size s)); lia).
  reflexivity.
Qed.

Lemma uhw_pos s : d_strstart (upd_high_water s) = d_strstart s /\ d_block_start (upd_high_water s) = d_block_start s.
Proof. unfold upd_high_water. destruct (_ <? _); split; reflexivity. Qed.

(** The state before the loop, with its output part as [ob] describes it. *)
Lemma l0c_state s :
  W s -> outok s -> d_pending s = 0 -> d_po s = 0 -> d_bi_valid s = 0 ->
  s = ob s (o_buf (tr_out (d_tr s))) (o_bi_used (tr_out (d_tr s))) (d_pbm s) /\
  5 <= Zlength (o_buf (tr_out (d_tr s))) /\ Zlength (d_pbm s) = Zlength (o_buf (tr_out (d_tr s))) /\
  mb_ok (mkMB (o_buf (tr_out (d_tr s))) (d_pbm s)) /\ 0 < ds_min_block s <= 32768 /\
  0 < d_w_size s /\ d_pending_buf_size s = Zlength (o_buf (tr_out (d_tr s))) /\
  512 <= d_pending_buf_size s <= 131072.
Proof.
  intros HW Hok Hp Hpo Hbv.
  pose proof HW as (Hprm & _).
  destruct (prm_pbsize s Hprm) as [Epb Hpb].
  pose proof (min_block_pos s Hprm). pose proof (min_block_le s Hprm).
  pose proof Hprm as (Hwb & Hws & _ & Hhb & _ & _ & _ & HL & Hps & Hlb & Hlm & _).
  assert (2 ^ 7 <= 2 ^ (d_hash_bits s - 1)) by (apply Z.pow_le_mono_r; lia).
  assert (2 ^ 9 <= 2 ^ d_w_bits s) by (apply Z.pow_le_mono_r; lia).
  pose proof Hok as (Hmb & (Hv1 & Hv2 & Hv3) & _).
  assert (Hbb : o_bi_buf (tr_out (d_tr s)) = 0)
    by (unfold d_bi_valid in Hbv; rewrite Hbv in Hv2; change (2 ^ 0) with 1 in Hv2; lia).
  split; [exact (ob_init s Hp Hpo Hbv Hbb)|].
  split; [lia|]. split; [lia|]. split; [exact Hmb|]. split; [lia|]. split; [lia|]. split; lia.
Qed.

(** The output part after the loop is sane. *)
Lemma outok_ob s B U M :
  mb_ok (mkMB B M) -> 0 <= d_pending_buf_size s -> outok (ob s B U M).
Proof.
  intros Hok Hp. unfold outok, d_pb, d_pending, d_po, d_pending_buf_size.
  cbn [ob set_d_po set_d_out set_d_pbm set_d_tr set_out d_tr d_pbm d_po tr_out fst snd
       o_buf o_pending o_bi_buf o_bi_valid o_bi_used].
  split; [exact Hok|]. split; [unfold bits_ok; cbn; lia|].
  split; [lia|]. split; [change (0 + 0 <= d_pending_buf_size s); lia|].
  split; [unfold mb_defined; cbn [mb_val mb_def]; split; [lia|split; [pose proof (Zlength_nonneg B); lia|intros; lia]]|].
  intros _. reflexivity.
Qed.

Theorem l0c_stored_nf s z k :
  W s -> outok s -> d_pending s = 0 -> d_po s = 0 -> d_bi_valid s = 0 -> d_level s = 0 ->
  d_strstart s = d_block_start s ->
  zall_w z -> adler_ok (d_wrap s) (z_adler z) ->
  z_avail_in z = 65535 * Z.of_nat k -> (1 <= k)%nat ->
  65540 * Z.of_nat k + 5 <= z_avail_out z <= 4294967295 ->
  exists s' z',
    c_deflate_stored s z Z_NO_FLUSH = Some (s', z', need_more) /\
    zstep (d_wrap s) z z' (65535 * Z.of_nat k) (nblocks (z_next_in z) k (z_in z)) /\
    W s' /\ outok s' /\ d_pending s' = 0 /\ d_po s' = 0 /\ d_bi_valid s' = 0 /\
    d_strstart s' = d_block_start s' /\ cp s' = cp s.
Proof.
  intros HW Hok Hp Hpo Hbv Hlev Hss Hz Ha Hai Hk Hao.
  destruct (l0c_state s HW Hok Hp Hpo Hbv) as (Es & Hb5 & Hm & Hmb & Hmin & Hws & Epb & Hpb).
  destruct (nf_loop s (ds_min_block s) z k _ (o_bi_used (tr_out (d_tr s))) _ Hss Hmin Hz Ha Hb5 Hm Hmb Hai Hao)
    as (B & U & M & z1 & E & LB & LM & OK & Hst).
  rewrite <- Es in E.
  pose proof Hz as [(Hzb & Hn0 & _ & Hn1 & _) _].
  pose proof Hst as (A1 & A2 & A3 & A4 & _).
  rewrite c_deflate_stored_eq. cbv zeta. rewrite E. cbn [bind].
  rewrite A4. replace (u32 (z_avail_in z - (z_avail_in z - 65535 * Z.of_nat k))) with (65535 * Z.of_nat k)
    by (rewrite u32_id; lia).
  destruct (Zlib.proof.wide.deflate.LTCStoredWin.dswin_ok_w LTCStoredChain.chain_parts_ok
              (ob s B U M) z1 (65535 * Z.of_nat k)) as (s2 & Ew & HW2 & Hk2 & Hub2).
  { rewrite ob_ob_set_g. apply W_ob; [exact HW|exact Hlev|cbn; lia|cbn; lia|lia]. }
  { exact Hlev. }
  { rewrite A1. exact Hzb. }
  { lia. }
  { rewrite A1, A3. lia. }
  { lia. }
  { intros _. change (d_block_start s = d_strstart s). lia. }
  rewrite Ew. cbn [bind].
  change (negb (0 =? 0)) with false. cbv iota.
  change (negb (Z_NO_FLUSH =? Z_NO_FLUSH)) with false. cbn [andb].
  rewrite fill2_none by (rewrite A4; lia).
  pose proof (op_win_eq _ _ Hk2) as Eop. pose proof (cp_win_eq _ _ Hk2) as Ecp.
  destruct (cp_fields _ _ Ecp) as (_ & _ & Elv & Epbs & Ews & _).
  destruct (op_fields _ _ Eop Epbs) as (Ho2 & _ & _ & Ebv2 & Eh2 & Ep2).
  assert (Hss2 : d_strstart s2 = d_block_start s2).
  { destruct (W_level0 s2 HW2 ltac:(rewrite Elv; exact Hlev)) as (Hla & _).
    unfold ub in Hub2. rewrite Hla in Hub2.
    change (d_strstart s2 - d_block_start s2 + 0 = d_strstart s - d_block_start s + d_lookahead s) in Hub2.
    destruct (W_level0 s HW Hlev) as (Hla0 & _). lia. }
  set (s4 := upd_high_water (upd_high_water s2)).
  assert (Ecp4 : cp s4 = cp s) by (unfold s4; rewrite !cp_uhw; exact Ecp).
  assert (Eop4 : op s4 = op (ob s B U M)) by (unfold s4; rewrite !op_uhw; exact Eop).
  destruct (cp_fields _ _ Ecp4) as (_ & _ & Elv4 & Epbs4 & Ews4 & _).
  destruct (op_fields _ _ Eop4 ltac:(rewrite Epbs4; reflexivity)) as (Ho4 & _ & _ & Ebv4 & Eh4 & Ep4).
  assert (Hst4 : d_strstart s4 = d_block_start s4)
    by (unfold s4; destruct (uhw_pos (upd_high_water s2)) as [P1 P2]; destruct (uhw_pos s2) as [P3 P4];
        rewrite P1, P2, P3, P4; exact Hss2).
  rewrite blk2_nf; cycle 1.
  { exact Hst4. }
  { lia. }
  { rewrite Eh4. change (stored_hdr (ob s B U M)) with 5. lia. }
  { lia. }
  cbn [Z.eqb]. exists s4, z1. split; [reflexivity|].
  split; [exact Hst|].
  split; [unfold s4; apply W_hw, W_hw, HW2|].
  split; [apply Ho4, outok_ob; [exact OK|lia]|].
  unfold op in Eop4. injection Eop4 as Eo4 Em4 Epo4.
  split; [unfold d_pending; rewrite Eo4; reflexivity|].
  split; [exact Epo4|].
  split; [unfold d_bi_valid; rewrite Eo4; reflexivity|].
  split; [exact Hst4|exact Ecp4].
Qed.

Theorem l0c_stored_fin s z :
  W s -> outok s -> d_pending s = 0 -> d_po s = 0 -> d_bi_valid s = 0 -> d_level s = 0 ->
  d_strstart s = d_block_start s ->
  zall_w z -> adler_ok (d_wrap s) (z_adler z) ->
  5 * l0_blocks (z_avail_in z) + z_avail_in z <= z_avail_out z <= 4294967295 ->
  exists s' z',
    c_deflate_stored s z Z_FINISH = Some (s', z', finish_done) /\
    zstep (d_wrap s) z z' (z_avail_in z)
      (stored_blocks (sublist (z_next_in z) (z_next_in z + z_avail_in z) (z_in z))) /\
    outok s' /\ d_pending s' = 0 /\ d_po s' = 0 /\ d_bi_valid s' = 0 /\ cp s' = cp s /\
    Zlength (o_buf (tr_out (d_tr s'))) = Zlength (o_buf (tr_out (d_tr s))) /\ d_lookahead s' = 0.
Proof.
  intros HW Hok Hp Hpo Hbv Hlev Hss Hz Ha Hao.
  destruct (l0c_state s HW Hok Hp Hpo Hbv) as (Es & Hb5 & Hm & Hmb & Hmin & Hws & Epb & Hpb).
  destruct (fin_loop s (ds_min_block s) z _ (o_bi_used (tr_out (d_tr s))) _ Hss Hmin Hz Ha Hb5 Hm Hmb Hao)
    as (B & M & z1 & E & LB & LM & OK & Hst).
  rewrite <- Es in E.
  pose proof Hz as [(Hzb & Hn0 & Hai & Hn1 & _) _].
  pose proof Hst as (A1 & A2 & A3 & A4 & _).
  rewrite c_deflate_stored_eq. cbv zeta. rewrite E. cbn [bind].
  rewrite A4. rewrite Z.sub_diag, Z.sub_0_r, u32_id by lia.
  destruct (Zlib.proof.wide.deflate.LTCStoredWin.dswin_ok_w LTCStoredChain.chain_parts_ok
              (ob s B 3 M) z1 (z_avail_in z)) as (s2 & Ew & HW2 & Hk2 & Hub2).
  { rewrite ob_ob_set_g. apply W_ob; [exact HW|exact Hlev|cbn; lia|cbn; lia|lia]. }
  { exact Hlev. }
  { rewrite A1. exact Hzb. }
  { lia. }
  { rewrite A1, A3. lia. }
  { lia. }
  { intros _. change (d_block_start s = d_strstart s). lia. }
  rewrite Ew. cbn [bind].
  change (negb (1 =? 0)) with true. cbv iota.
  pose proof (op_win_eq _ _ Hk2) as Eop. pose proof (cp_win_eq _ _ Hk2) as Ecp.
  set (s4 := set_d_bi_used (upd_high_water s2) 8).
  assert (Ecp4 : cp s4 = cp s) by (unfold s4; rewrite cp_bu, cp_uhw; exact Ecp).
  destruct (cp_fields _ _ Ecp4) as (_ & _ & _ & Epbs4 & _).
  assert (Eop3 : op (upd_high_water s2) = op (ob s B 3 M)) by (rewrite op_uhw; exact Eop).
  assert (Ecp3 : cp (upd_high_water s2) = cp (ob s B 3 M)) by (rewrite cp_uhw; exact Ecp).
  destruct (cp_fields _ _ Ecp3) as (_ & _ & _ & Epbs3 & _).
  destruct (op_fields _ _ Eop3 Epbs3) as (Ho3 & _ & _ & Ebv3 & _ & Ep3).
  exists s4, z1. split; [reflexivity|].
  split; [exact Hst|].
  unfold op in Eop3. injection Eop3 as Eo3 Em3 Epo3.
  split; [apply (proj1 (bu_fields _)), Ho3, outok_ob; [exact OK|lia]|].
  split; [unfold s4, d_pending; cbn [set_d_bi_used d_tr set_d_tr set_out tr_out o_pending]; rewrite Eo3; reflexivity|].
  split; [exact Epo3|].
  split; [unfold s4, d_bi_valid; cbn [set_d_bi_used d_tr set_d_tr set_out tr_out o_bi_valid]; rewrite Eo3; reflexivity|].
  split; [exact Ecp4|].
  split; [unfold s4; cbn [set_d_bi_used d_tr set_d_tr set_out tr_out o_buf]; rewrite Eo3; cbn [o_buf]; exact LB|].
  (* nothing is left to compress: level 0 keeps lookahead at 0 *)
  destruct (cp_fields _ _ Ecp) as (_ & _ & Elv2 & _).
  destruct (W_level0 s2 HW2 ltac:(rewrite Elv2; exact Hlev)) as (Hla2 & _).
  unfold s4, upd_high_water. destruct (d_high_water s2 <? d_strstart s2); exact Hla2.
Qed.
