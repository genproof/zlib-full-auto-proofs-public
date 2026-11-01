(** * Level 0 over several deflate() calls: one iteration of deflate_stored's first loop

    [Level0Stored.ds_iter] follows one iteration of the first-phase loop ([ds_body]) of deflate_stored with
    Z_FINISH on a fresh stream (strstart = block_start = 0, at most 2^20 bytes, 32-bit counters).  Here the same
    iteration in the situation of every call of the harnesses' loop: any flush among Z_NO_FLUSH (then a whole
    block of input is offered) and Z_FINISH, strstart = block_start of any value (nothing is left in the window:
    [left = 0]), avail_in up to 2^32 - 1 and total_out up to 2^64 - 1.  The effect on the stream is stated with
    [zstep]: the block's input bytes are consumed (total_in and the checksum follow) and the stored block holding
    them is written. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.Level0Stored.
Require Export Zlib.proof.wide.deflate.LTCStoredKit.
Require Export Zlib.proof.wide.deflate.LTCLib.
Require Export Zlib.proof.deflate.Level0CallsBlocks.
Require Import Zlib.proof.deflate.LTCStoredLoopLib.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** The copy from next_in at the end of [ds_body], with the 64-bit counters. *)
Lemma incopy_w s z len :
  zall_w z -> adler_ok (d_wrap s) (z_adler z) -> 0 <= len <= z_avail_in z -> len <= z_avail_out z <= 4294967295 ->
  exists z2,
    (if len =? 0 then Some z else
     let* (z, data) := c_read_buf s z len in
     let* _ := guard (Zlength data =? len) in
     let* z := out_put z data in
     let z := set_z_avail_out z (u32 (z_avail_out z - len)) in
     Some (set_z_total_out z (u64 (z_total_out z + len)))) = Some z2 /\
    zstep (d_wrap s) z z2 len (sublist (z_next_in z) (z_next_in z + len) (z_in z)).
Proof.
  intros Hz Ha Hl Ho. pose proof Hz as [(Hb & Hni & Hai & Hn & Hti) (Hao & Hto & Hs)].
  destruct (Z.eqb_spec len 0) as [->|N].
  - exists z. split; [reflexivity|]. rewrite Z.add_0_r, sublist_nil. apply zstep_refl_w; auto.
  - destruct (read_buf_ok_w s z len Hz Ha ltac:(lia)) as (z1 & E & Hs1 & Ho1 & Hao1 & Hto1).
    rewrite Z.min_l in E, Hs1 by lia. rewrite E. cbn [bind].
    rewrite Zlength_sublist by lia.
    replace (z_next_in z + len - z_next_in z =? len) with true by (symmetry; apply Z.eqb_eq; lia).
    cbn [bind guard]. unfold out_put. rewrite Zlength_sublist by lia.
    replace (z_next_in z + len - z_next_in z <=? z_avail_out z1) with true by (symmetry; apply Z.leb_le; lia).
    cbn [bind]. eexists. split; [reflexivity|].
    destruct Hs1 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11).
    unfold zstep. cbn [z_in z_next_in z_avail_in z_total_in z_adler z_out z_avail_out z_total_out z_msg
                       set_z_out set_z_avail_out set_z_total_out].
    rewrite Zlength_sublist by lia. rewrite Ho1, Hao1, Hto1.
    replace (z_next_in z + len - z_next_in z) with len by lia. rewrite u32_id by lia.
    repeat split; auto; lia.
Qed.

(** The checksum stays valid across a step of the stream. *)
Lemma adler_ok_zstep_l0 w z z' k x : zall_w z -> adler_ok w (z_adler z) -> zstep w z z' k x -> adler_ok w (z_adler z').
Proof.
  intros [(Hb & _) _] Ha (_ & _ & _ & _ & _ & E & _). rewrite E. apply adler_ok_upd; auto.
  apply bytes_sublist; auto.
Qed.

(** ** One iteration

    [len = min 65535 avail_in] bytes from next_in as one stored block, final when the flush is Z_FINISH and the
    block takes the rest of the input; with Z_NO_FLUSH at least a whole block is offered. *)
Definition it_len (z : strm) : Z := Z.min 65535 (z_avail_in z).
Definition it_last (flush : Z) (z : strm) : Z := if (flush =? Z_FINISH) && (z_avail_in z <=? 65535) then 1 else 0.

Lemma ds_iter_g s0 b u m z mb flush :
  d_strstart s0 = d_block_start s0 -> 5 <= Zlength b -> Zlength m = Zlength b -> 0 < mb <= 32768 ->
  (flush = Z_NO_FLUSH /\ 65535 <= z_avail_in z \/ flush = Z_FINISH) ->
  zall_w z -> adler_ok (d_wrap s0) (z_adler z) ->
  5 + it_len z <= z_avail_out z <= 4294967295 ->
  exists B M z',
    ds_body flush mb (ob s0 b u m, z) =
      Some (if it_last flush z =? 0 then inl (ob s0 B 3 M, z') else inr (ob s0 B 3 M, z', 1)) /\
    Zlength B = Zlength b /\ Zlength M = Zlength m /\ (mb_ok (mkMB b m) -> mb_ok (mkMB B M)) /\
    zstep (d_wrap s0) z z' (it_len z)
      (stored_block (it_last flush z) (sublist (z_next_in z) (z_next_in z + it_len z) (z_in z))).
Proof.
  intros Hss Hb Hm Hmb Hfl Hz Ha Hao.
  pose proof Hz as [(Hzb & Hni & Hai & Hn & Hti) (Hao0 & Hto & Hs)].
  unfold it_len, it_last in *.
  unfold ds_body. cbv beta iota zeta.
  change (stored_hdr (ob s0 b u m)) with 5.
  change (d_strstart (ob s0 b u m)) with (d_strstart s0). change (d_block_start (ob s0 b u m)) with (d_block_start s0).
  rewrite Hss, Z.sub_diag.
  change (u32 0) with 0. change (in_long 0) with true. rewrite Z.add_0_l.
  set (ai := z_avail_in z) in *. set (A := z_avail_out z) in *.
  unfold MAX_STORED. try rewrite (u64_id ai) by lia. try rewrite (u32_id ai) by lia.
  rewrite (u32_id (A - 5)) by lia.
  rewrite (min_if 65535 ai), (min_if (Z.min 65535 ai) (A - 5)), (Z.min_l (Z.min 65535 ai)) by lia.
  replace (A <? 5) with false by (symmetry; apply Z.ltb_ge; lia).
  cbn [andb orb negb guard bind].
  assert (Hlen : 0 <= Z.min 65535 ai <= 65535 /\ Z.min 65535 ai <= ai) by lia.
  set (len := Z.min 65535 ai) in *.
  match goal with |- context [if (len <? mb) && ?r then _ else _] =>
    replace ((len <? mb) && r) with false
      by (destruct Hfl as [[-> H65] | ->];
          [destruct (Z.ltb_spec len mb); [subst len; lia|reflexivity]
          |subst len; destruct (Z.ltb_spec (Z.min 65535 ai) mb); destruct (Z.eqb_spec (Z.min 65535 ai) ai);
           destruct (Z.min 65535 ai =? 0); cbn [andb orb negb Z.eqb Pos.eqb Z_FINISH Z_NO_FLUSH]; lia]) end.
  replace (len =? ai) with (ai <=? 65535)
    by (subst len; destruct (Z.eqb_spec (Z.min 65535 ai) ai); destruct (Z.leb_spec ai 65535); lia).
  set (lst := if (flush =? Z_FINISH) && (ai <=? 65535) then 1 else 0).
  assert (Hlst : 0 <= lst <= 1) by (subst lst; destruct (_ && _); lia).
  change (d_out (ob s0 b u m)) with (mkOut b 0 0 0 u, m).
  rewrite sblk_empty by assumption. cbn [bind].
  rewrite ob_obs, obs_out.
  rewrite d_pending_obs. cbn [o_pending]. change (u64 (5 - 4)) with 1.
  rewrite pb_wr_obs by (rewrite ?Zlength_upd_Znth_any; lia). cbn [bind].
  rewrite d_pending_obs. cbn [o_pending]. change (u64 (5 - 3)) with 2.
  rewrite pb_wr_obs by (rewrite ?Zlength_upd_Znth_any; lia). cbn [bind].
  rewrite d_pending_obs. cbn [o_pending]. change (u64 (5 - 2)) with 3.
  rewrite pb_wr_obs by (rewrite ?Zlength_upd_Znth_any; lia). cbn [bind].
  rewrite d_pending_obs. cbn [o_pending]. change (u64 (5 - 1)) with 4.
  rewrite pb_wr_obs by (rewrite ?Zlength_upd_Znth_any; lia). cbn [bind].
  rewrite fp_obs by first [rewrite ?Zlength_upd_Znth_any; lia | intros; apply mask5; lia]. cbn [bind].
  change (0 =? 0) with true. cbv iota. cbn [bind].
  match goal with |- context [set_z_out z (z_out z ++ ?h)] => set (H5 := h) in * end.
  assert (LH5 : Zlength H5 = 5) by (unfold H5; rewrite Zlength_sublist by (rewrite ?Zlength_upd_Znth_any; lia); lia).
  match goal with |- context [c_read_buf ?s1 ?z1 len] =>
    assert (Hz1 : zall_w z1 /\ adler_ok (d_wrap s1) (z_adler z1) /\ zstep (d_wrap s0) z z1 0 H5);
    [|destruct (incopy_w s1 z1 len) as (z2 & E2 & Z2)] end.
  { split; [|split].
    - unfold zall_w, zin_in_w, zout_ok_w in *.
      cbn [z_in z_next_in z_avail_in z_total_in z_adler z_msg z_out z_avail_out z_total_out
           set_z_out set_z_avail_out set_z_total_out].
      rewrite u64_id by lia. fold A ai. repeat split; try lia; auto.
    - exact Ha.
    - apply zout_only_zstep_w; auto.
      + unfold zout_only.
        cbn [z_in z_next_in z_avail_in z_total_in z_adler z_msg z_out z_avail_out z_total_out
             set_z_out set_z_avail_out set_z_total_out].
        rewrite u64_id by lia. repeat split; lia.
      + cbn [z_avail_out set_z_out set_z_avail_out set_z_total_out]. lia. }
  { destruct Hz1 as (H1 & _). exact H1. }
  { destruct Hz1 as (_ & H2 & _). exact H2. }
  { cbn [z_avail_in set_z_out set_z_avail_out set_z_total_out]. subst len. lia. }
  { cbn [z_avail_out set_z_out set_z_avail_out set_z_total_out]. lia. }
  cbv zeta in E2. rewrite E2. cbn [bind].
  match goal with |- context [obs s0 (mkOut ?B 0 0 0 3) ?M 0] => exists B, M, z2 end.
  split; [rewrite <- !ob_obs; unfold lst; destruct (_ && _); reflexivity|].
  split; [rewrite !Zlength_upd_Znth_any; reflexivity|].
  split; [rewrite !Zlength_upd_Znth_any; reflexivity|].
  split.
  { intros Hok. pose proof (u8_range len). pose proof (u8_range (Z.shiftr len 8)).
    pose proof (u8_range (u32 (Z.lnot len))). pose proof (u8_range (Z.shiftr (u32 (Z.lnot len)) 8)).
    repeat (apply mb_ok_upd; [|rewrite ?Zlength_upd_Znth_any; lia|lia]). exact Hok. }
  destruct Hz1 as (_ & _ & Z1).
  match type of Z2 with zstep (d_wrap ?s1) _ _ _ _ => change (d_wrap s1) with (d_wrap s0) in Z2 end.
  cbn [z_in z_next_in set_z_out set_z_avail_out set_z_total_out] in Z2.
  pose proof (zstep_trans_w _ _ _ _ _ _ _ _ (proj1 Hz) Ha Z1 Z2) as Z3.
  rewrite Z.add_0_l in Z3.
  replace (stored_block lst (sublist (z_next_in z) (z_next_in z + len) (z_in z)))
    with (H5 ++ sublist (z_next_in z) (z_next_in z + len) (z_in z)); [exact Z3|].
  unfold H5. rewrite hdr5 by lia. unfold stored_block.
  rewrite Zlength_sublist by lia. replace (z_next_in z + len - z_next_in z) with len by lia.
  rewrite <- len_bytes by lia. reflexivity.
Qed.

(** With Z_NO_FLUSH and no input left, the loop leaves at once ([len = 0] is below min_block). *)
Lemma ds_brk_nf s0 b u m z mb :
  d_strstart s0 = d_block_start s0 -> 0 < mb -> z_avail_in z = 0 -> 5 <= z_avail_out z <= 4294967295 ->
  ds_body Z_NO_FLUSH mb (ob s0 b u m, z) = Some (inr (ob s0 b u m, z, 0)).
Proof.
  intros Hss Hmb Hai Hao.
  unfold ds_body. cbv beta iota zeta.
  change (stored_hdr (ob s0 b u m)) with 5.
  change (d_strstart (ob s0 b u m)) with (d_strstart s0). change (d_block_start (ob s0 b u m)) with (d_block_start s0).
  rewrite Hss, Z.sub_diag, Hai.
  change (u32 0) with 0. change (in_long 0) with true.
  replace (z_avail_out z <? 5) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite (u32_id (z_avail_out z - 5)) by lia.
  cbn [bind guard].
  replace ((if (if MAX_STORED >? u64 (0 + 0) then u32 (0 + 0) else MAX_STORED) >? z_avail_out z - 5
            then z_avail_out z - 5 else if MAX_STORED >? u64 (0 + 0) then u32 (0 + 0) else MAX_STORED)) with 0
    by (cbn; destruct (Z.gtb_spec 0 (z_avail_out z - 5)); lia).
  replace (0 <? mb) with true by (symmetry; apply Z.ltb_lt; lia).
  reflexivity.
Qed.

(** ** The loop with Z_NO_FLUSH, offered [j] whole blocks and room for them: [j] non-final stored blocks, then
    the loop leaves with nothing consumed from the window ([last = 0]). *)
Section NoFlush.
Variables (s0 : dstate) (mb : Z) (z0 : strm) (j0 : nat).

Definition nf_inv (a : dstate * strm) : Prop :=
  let '(s, z) := a in
  exists i b u m, s = ob s0 b u m /\ (i <= j0)%nat /\
    5 <= Zlength b /\ Zlength m = Zlength b /\ mb_ok (mkMB b m) /\
    zall_w z /\ adler_ok (d_wrap s0) (z_adler z) /\
    z_avail_in z = 65535 * Z.of_nat (j0 - i) /\ 65540 * Z.of_nat (j0 - i) + 5 <= z_avail_out z <= 4294967295 /\
    zstep (d_wrap s0) z0 z (65535 * Z.of_nat i) (nblocks (z_next_in z0) i (z_in z0)).

Definition nf_post (L : Z) (r : dstate * strm * Z) : Prop :=
  let '(s, z, last) := r in
  last = 0 /\ exists B U M, s = ob s0 B U M /\ Zlength B = L /\ Zlength M = L /\ mb_ok (mkMB B M) /\
    zstep (d_wrap s0) z0 z (65535 * Z.of_nat j0) (nblocks (z_next_in z0) j0 (z_in z0)).

Lemma nf_step L a :
  d_strstart s0 = d_block_start s0 -> 0 < mb <= 32768 -> zall_w z0 -> adler_ok (d_wrap s0) (z_adler z0) ->
  nf_inv a -> Zlength (o_buf (tr_out (d_tr (fst a)))) = L ->
  exists r, ds_body Z_NO_FLUSH mb a = Some r /\
    match r with
    | inl a' => (nf_inv a' /\ Zlength (o_buf (tr_out (d_tr (fst a')))) = L) /\ 0 <= z_avail_in (snd a') < z_avail_in (snd a)
    | inr e => nf_post L e
    end.
Proof.
  intros Hss Hmb Hz0 Ha0. destruct a as [s z].
  intros (i & b & u & m & -> & Hi & Hb & Hm & Hok & Hz & Ha & Hai & Hao & Hst) HL.
  change (Zlength b = L) in HL.
  destruct (Nat.eq_dec i j0) as [->|Ne].
  - exists (inr (ob s0 b u m, z, 0)). split.
    + apply ds_brk_nf; [exact Hss|lia|rewrite Hai, Nat.sub_diag; reflexivity|rewrite Nat.sub_diag in Hao; lia].
    + split; [reflexivity|]. exists b, u, m. split; [reflexivity|]. split; [exact HL|]. split; [lia|]. auto.
  - assert (Hj : (1 <= j0 - i)%nat) by lia.
    assert (Hj' : 1 <= Z.of_nat (j0 - i)) by lia.
    destruct (ds_iter_g s0 b u m z mb Z_NO_FLUSH Hss Hb Hm Hmb
                ltac:(left; split; [reflexivity|lia]) Hz Ha)
      as (B & M & z' & E & LB & LM & OK & Hst');
      [unfold it_len; lia|].
    assert (El : it_last Z_NO_FLUSH z = 0) by reflexivity.
    assert (En : it_len z = 65535) by (unfold it_len; lia).
    rewrite El in E, Hst'. rewrite En in Hst'. cbn [Z.eqb] in E.
    exists (inl (ob s0 B 3 M, z')). split; [exact E|].
    pose proof Hst as (A1 & A2 & A3 & A4 & _).
    pose proof Hst' as (C1 & C2 & C3 & C4 & _ & _ & _ & _ & C9 & _).
    pose proof Hz as [(_ & Hn0 & _ & Hn1 & _) _].
    rewrite Zlength_stored_block, Zlength_sublist in C9 by lia.
    split; [split|cbn [snd]; lia].
    + exists (S i), B, 3, M. split; [reflexivity|]. split; [lia|].
      split; [lia|]. split; [lia|]. split; [auto|].
      split; [apply (zall_zstep_w _ _ _ _ _ Hz Hst'); lia|].
      split; [apply (adler_ok_zstep_l0 _ _ _ _ _ Hz Ha Hst')|].
      split; [rewrite C4, Hai; lia|].
      split; [rewrite C9; lia|].
      pose proof (zstep_trans_w _ _ _ _ _ _ _ _ (proj1 Hz0) Ha0 Hst Hst') as Z3.
      rewrite nblocks_S. rewrite A1, A3 in Z3.
      replace (65535 * Z.of_nat (S i)) with (65535 * Z.of_nat i + 65535) by lia. exact Z3.
    + change (Zlength B = L). lia.
Qed.

Lemma nf_loop b u m :
  d_strstart s0 = d_block_start s0 -> 0 < mb <= 32768 -> zall_w z0 -> adler_ok (d_wrap s0) (z_adler z0) ->
  5 <= Zlength b -> Zlength m = Zlength b -> mb_ok (mkMB b m) ->
  z_avail_in z0 = 65535 * Z.of_nat j0 -> 65540 * Z.of_nat j0 + 5 <= z_avail_out z0 <= 4294967295 ->
  exists B U M z',
    loop FUEL (ds_body Z_NO_FLUSH mb) (ob s0 b u m, z0) = Some (ob s0 B U M, z', 0) /\
    Zlength B = Zlength b /\ Zlength M = Zlength b /\ mb_ok (mkMB B M) /\
    zstep (d_wrap s0) z0 z' (65535 * Z.of_nat j0) (nblocks (z_next_in z0) j0 (z_in z0)).
Proof.
  intros Hss Hmb Hz0 Ha0 Hb Hm Hok Hai Hao.
  set (L := Zlength b).
  destruct (loop_meas (ds_body Z_NO_FLUSH mb)
              (fun a => nf_inv a /\ Zlength (o_buf (tr_out (d_tr (fst a)))) = L) (nf_post L)
              (fun a => z_avail_in (snd a))
              (fun a Ha => nf_step L a Hss Hmb Hz0 Ha0 (proj1 Ha) (proj2 Ha))
              (ob s0 b u m, z0))
    as ([[s1 z1] last] & E & (-> & B & U & M & -> & LB & LM & OK & Hst)).
  { split; [|reflexivity]. exists O, b, u, m. rewrite Nat.sub_0_r.
    split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hok|].
    split; [exact Hz0|]. split; [exact Ha0|]. split; [exact Hai|]. split; [exact Hao|].
    rewrite Z.mul_0_r. cbn [nblocks]. apply zstep_refl_w; auto. }
  { cbn [snd]. lia. }
  exists B, U, M, z1. split; [exact E|]. split; [exact LB|]. split; [lia|]. auto.
Qed.
End NoFlush.

(** ** The loop with Z_FINISH and room for every block: the stored blocks of all the input, the last one final *)
Section Finish.
Variables (s0 : dstate) (mb : Z) (z0 : strm).

Definition fin_data : list Z := sublist (z_next_in z0) (z_next_in z0 + z_avail_in z0) (z_in z0).

Definition fin_inv (a : dstate * strm) : Prop :=
  let '(s, z) := a in
  exists i b u m, s = ob s0 b u m /\ (i = O \/ 65535 * Z.of_nat i < z_avail_in z0) /\
    5 <= Zlength b /\ Zlength m = Zlength b /\ mb_ok (mkMB b m) /\
    zall_w z /\ adler_ok (d_wrap s0) (z_adler z) /\
    z_avail_in z = z_avail_in z0 - 65535 * Z.of_nat i /\
    5 * l0_blocks (z_avail_in z) + z_avail_in z <= z_avail_out z <= 4294967295 /\
    zstep (d_wrap s0) z0 z (65535 * Z.of_nat i) (nblocks (z_next_in z0) i (z_in z0)).

Definition fin_post (L : Z) (r : dstate * strm * Z) : Prop :=
  let '(s, z, last) := r in
  last = 1 /\ exists B M, s = ob s0 B 3 M /\ Zlength B = L /\ Zlength M = L /\ mb_ok (mkMB B M) /\
    zstep (d_wrap s0) z0 z (z_avail_in z0) (stored_blocks fin_data).

Lemma fin_step L a :
  d_strstart s0 = d_block_start s0 -> 0 < mb <= 32768 -> zall_w z0 -> adler_ok (d_wrap s0) (z_adler z0) ->
  fin_inv a -> Zlength (o_buf (tr_out (d_tr (fst a)))) = L ->
  exists r, ds_body Z_FINISH mb a = Some r /\
    match r with
    | inl a' => (fin_inv a' /\ Zlength (o_buf (tr_out (d_tr (fst a')))) = L) /\ 0 <= z_avail_in (snd a') < z_avail_in (snd a)
    | inr e => fin_post L e
    end.
Proof.
  intros Hss Hmb Hz0 Ha0. destruct a as [s z].
  intros (i & b & u & m & -> & Hi & Hb & Hm & Hok & Hz & Ha & Hai & Hao & Hst) HL.
  change (Zlength b = L) in HL.
  pose proof Hz0 as [(_ & Hn00 & Ha00 & Hn01 & _) _].
  pose proof Hz as [(_ & Hn0 & Ha0' & Hn1 & _) _].
  pose proof Hst as (A1 & A2 & A3 & A4 & _).
  pose proof (l0_blocks_pos (z_avail_in z) ltac:(lia)) as Hbl.
  destruct (ds_iter_g s0 b u m z mb Z_FINISH Hss Hb Hm Hmb ltac:(right; reflexivity) Hz Ha)
    as (B & M & z' & E & LB & LM & OK & Hst'); [unfold it_len; lia|].
  pose proof Hst' as (C1 & C2 & C3 & C4 & _ & _ & _ & _ & C9 & _).
  unfold it_len in *.
  rewrite Zlength_stored_block, Zlength_sublist in C9 by lia.
  pose proof (zstep_trans_w _ _ _ _ _ _ _ _ (proj1 Hz0) Ha0 Hst Hst') as Z3.
  rewrite A1, A3 in Z3.
  destruct (Z.leb_spec (z_avail_in z) 65535) as [Hle|Hgt].
  - assert (El : it_last Z_FINISH z = 1) by (unfold it_last; rewrite (proj2 (Z.leb_le _ _) Hle); reflexivity).
    rewrite El in E, Z3. cbn [Z.eqb Pos.eqb] in E.
    exists (inr (ob s0 B 3 M, z', 1)). split; [exact E|].
    split; [reflexivity|]. exists B, M. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [auto|].
    rewrite Z.min_r in Z3 by lia.
    replace (65535 * Z.of_nat i + z_avail_in z) with (z_avail_in z0) in Z3 by lia.
    replace (stored_blocks fin_data) with
      (nblocks (z_next_in z0) i (z_in z0) ++
       stored_block 1 (sublist (z_next_in z0 + 65535 * Z.of_nat i)
                         (z_next_in z0 + 65535 * Z.of_nat i + z_avail_in z) (z_in z0))); [exact Z3|].
    unfold fin_data.
    rewrite (stored_blocks_split i) by (rewrite Zlength_sublist by lia; lia).
    rewrite nblocks_sublist by lia. f_equal.
    rewrite Zlength_sublist, sublist_sublist by lia.
    rewrite stored_blocks_eq. unfold MAX_STORED_LEN.
    rewrite Zlength_sublist by lia.
    replace (_ <=? 65535) with true by (symmetry; apply Z.leb_le; lia).
    f_equal. f_equal; lia.
  - assert (El : it_last Z_FINISH z = 0) by (unfold it_last; rewrite (proj2 (Z.leb_gt _ _) Hgt); reflexivity).
    rewrite El in E, Z3. cbn [Z.eqb Pos.eqb] in E.
    rewrite Z.min_l in Z3, C2, C3, C4, C9 by lia.
    exists (inl (ob s0 B 3 M, z')). split; [exact E|].
    split; [split|cbn [snd]; lia].
    + exists (S i), B, 3, M. split; [reflexivity|]. split; [right; lia|].
      split; [lia|]. split; [lia|]. split; [auto|].
      split; [apply (zall_zstep_w _ _ _ _ _ Hz Hst'); lia|].
      split; [apply (adler_ok_zstep_l0 _ _ _ _ _ Hz Ha Hst')|].
      split; [rewrite C4, Hai; lia|].
      split; [rewrite C9, C4; rewrite (l0_blocks_step (z_avail_in z)) in Hao by lia; lia|].
      rewrite nblocks_S.
      replace (65535 * Z.of_nat (S i)) with (65535 * Z.of_nat i + 65535) by lia. exact Z3.
    + change (Zlength B = L). lia.
Qed.

Lemma fin_loop b u m :
  d_strstart s0 = d_block_start s0 -> 0 < mb <= 32768 -> zall_w z0 -> adler_ok (d_wrap s0) (z_adler z0) ->
  5 <= Zlength b -> Zlength m = Zlength b -> mb_ok (mkMB b m) ->
  5 * l0_blocks (z_avail_in z0) + z_avail_in z0 <= z_avail_out z0 <= 4294967295 ->
  exists B M z',
    loop FUEL (ds_body Z_FINISH mb) (ob s0 b u m, z0) = Some (ob s0 B 3 M, z', 1) /\
    Zlength B = Zlength b /\ Zlength M = Zlength b /\ mb_ok (mkMB B M) /\
    zstep (d_wrap s0) z0 z' (z_avail_in z0) (stored_blocks fin_data).
Proof.
  intros Hss Hmb Hz0 Ha0 Hb Hm Hok Hao.
  set (L := Zlength b).
  destruct (loop_meas (ds_body Z_FINISH mb)
              (fun a => fin_inv a /\ Zlength (o_buf (tr_out (d_tr (fst a)))) = L) (fin_post L)
              (fun a => z_avail_in (snd a))
              (fun a Ha => fin_step L a Hss Hmb Hz0 Ha0 (proj1 Ha) (proj2 Ha))
              (ob s0 b u m, z0))
    as ([[s1 z1] last] & E & (-> & B & M & -> & LB & LM & OK & Hst)).
  { split; [|reflexivity]. exists O, b, u, m.
    split; [reflexivity|]. split; [left; reflexivity|]. split; [lia|]. split; [lia|]. split; [exact Hok|].
    split; [exact Hz0|]. split; [exact Ha0|]. split; [lia|]. split; [exact Hao|].
    rewrite Z.mul_0_r. cbn [nblocks]. apply zstep_refl_w; auto. }
  { cbn [snd]. pose proof Hz0 as [(_ & _ & ? & _) _]. lia. }
  exists B, M, z1. split; [exact E|]. split; [exact LB|]. split; [lia|]. auto.
Qed.
End Finish.
