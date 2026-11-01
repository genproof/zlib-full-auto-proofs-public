(** * The output of deflate at level 0: [l0_stored_stmt] (see Level0Stmts.v) *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.zlist.list_solver.
Require Export Zlib.proof.deflate.Level0Stmts.
Require Import Zlib.proof.deflate.LTCStored2 Zlib.proof.deflate.LTCStoredLoopLib.
Require Zlib.proof.deflate.LTCStoredWin Zlib.proof.deflate.LTCStoredChain.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** The proof follows deflate_stored(s, Z_FINISH) on a state with an empty window (strstart = block_start = 0),
    nothing pending and an empty bit buffer: every iteration of the first-phase loop ([ds_body]) skips the copy
    from the window, writes an empty stored block header into pending_buf, overwrites its LEN / NLEN bytes,
    flushes the five header bytes to next_out and copies [min 65535 avail_in] bytes from next_in; the loop
    leaves after the block that takes the rest of the input, with BFINAL set. *)

(** ** The state during the loop: the initial state with another pending_buf, and nothing pending *)

Definition ob (s0 : dstate) (b : list Z) (u : Z) (m : list bool) : dstate :=
  set_d_po (set_d_out s0 (mkOut b 0 0 0 u, m)) 0.

(** The state with any output part. *)
Definition obs (s0 : dstate) (o : outbuf) (m : list bool) (po : Z) : dstate :=
  set_d_po (set_d_out s0 (o, m)) po.

Lemma obs_out s0 o m po o' m' : set_d_out (obs s0 o m po) (o', m') = obs s0 o' m' po.
Proof. destruct s0 as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? [] ?]. reflexivity. Qed.

Lemma obs_po s0 o m po po' : set_d_po (obs s0 o m po) po' = obs s0 o m po'.
Proof. destruct s0 as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? [] ?]. reflexivity. Qed.

Lemma ob_obs s0 b u m : ob s0 b u m = obs s0 (mkOut b 0 0 0 u) m 0.
Proof. reflexivity. Qed.

(** The initial state is of this form. *)
Lemma ob_init s0 :
  d_pending s0 = 0 -> d_po s0 = 0 -> d_bi_valid s0 = 0 -> o_bi_buf (tr_out (d_tr s0)) = 0 ->
  s0 = ob s0 (o_buf (tr_out (d_tr s0))) (o_bi_used (tr_out (d_tr s0))) (d_pbm s0).
Proof.
  destruct s0 as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? [? ? ? ? ? ? ? [] ? ? ? ? ? ? ?] ?].
  unfold d_pending, d_bi_valid. cbn. intros -> -> -> ->. reflexivity.
Qed.

(** ** Pieces of [ds_body] on such a state *)

Lemma wr_ok l i v : 0 <= i < Zlength l -> wr l i v = Some (upd_Znth i l v).
Proof.
  intros H. unfold wr, in_range.
  replace ((0 <=? i) && (i <? Zlength l)) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
  reflexivity.
Qed.

Lemma mb_ok_upd b m i v :
  mb_ok (mkMB b m) -> 0 <= i < Zlength b -> 0 <= v < 256 -> mb_ok (mkMB (upd_Znth i b v) (upd_Znth i m true)).
Proof.
  unfold mb_ok; cbn [mb_val mb_def]. intros [H1 H2] Hi Hv. rewrite !upd_Znth_Zlength by lia. split; [lia|].
  intros j Hj Hd. destruct (Z.eq_dec j i) as [->|N].
  - rewrite upd_Znth_same by lia. exact Hv.
  - rewrite upd_Znth_diff by lia. rewrite upd_Znth_diff in Hd by lia. apply H2; auto.
Qed.

(** The empty stored block of the first phase with an empty bit buffer: the byte [last], LEN = 0, NLEN = 0xffff
    at pending_buf[0 .. 5). *)
Lemma sblk_empty b m u last :
  5 <= Zlength b -> Zlength m = Zlength b -> 0 <= last <= 1 ->
  c_tr_stored_block (mkOut b 0 0 0 u, m) [] 0 last =
  Some (mkOut (upd_Znth 4 (upd_Znth 3 (upd_Znth 2 (upd_Znth 1 (upd_Znth 0 b last) 0) 0) 255) 255) 5 0 0 3,
        upd_Znth 4 (upd_Znth 3 (upd_Znth 2 (upd_Znth 1 (upd_Znth 0 m true) true) true) true) true).
Proof.
  intros Hb Hm Hl.
  unfold c_tr_stored_block, c_send_bits, c_bi_windup, c_put_short, c_put_byte. cbn -[upd_Znth Zlength].
  assert (E : u16 (u16 (0 + last)) = last) by (assert (last = 0 \/ last = 1) as [-> | ->] by lia; reflexivity).
  assert (E' : u8 last = last) by (assert (last = 0 \/ last = 1) as [-> | ->] by lia; reflexivity).
  rewrite E, E'.
  repeat (rewrite wr_ok by (rewrite ?Zlength_upd_Znth_any; lia);
          cbn [bind o_buf o_pending o_bi_buf o_bi_valid o_bi_used]).
  reflexivity.
Qed.

Lemma d_pending_obs s0 o m po : d_pending (obs s0 o m po) = o_pending o. Proof. reflexivity. Qed.
Lemma d_out_obs s0 o m po : d_out (obs s0 o m po) = (o, m). Proof. reflexivity. Qed.

(** A byte store into pending_buf. *)
Lemma pb_wr_obs s0 b p bb bv u m po i v :
  0 <= i < Zlength b ->
  c_pb_wr (obs s0 (mkOut b p bb bv u) m po) i v =
  Some (obs s0 (mkOut (upd_Znth i b v) p bb bv u) (upd_Znth i m true) po).
Proof.
  intros Hi. unfold c_pb_wr, mb_wr.
  change (d_pb (obs s0 (mkOut b p bb bv u) m po)) with (mkMB b m). cbn [mb_val mb_def].
  replace (in_range i (Zlength b)) with true
    by (unfold in_range; symmetry; apply andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
  cbn [bind].
  destruct s0 as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? [] ?]. reflexivity.
Qed.

(** flush_pending with the five header bytes pending and room for them. *)
Lemma fp_obs s0 B M u z :
  5 <= Zlength B -> Zlength M = Zlength B -> (forall i, 0 <= i < 5 -> Znth i M = true) -> 5 <= z_avail_out z ->
  c_flush_pending (obs s0 (mkOut B 5 0 0 u) M 0) z =
  Some (obs s0 (mkOut B 0 0 0 u) M 0,
        set_z_avail_out (set_z_total_out (set_z_out z (z_out z ++ sublist 0 5 B)) (u64 (z_total_out z + 5)))
                        (z_avail_out z - 5)).
Proof.
  intros Hb Hm Hd Ha. unfold c_flush_pending. rewrite d_out_obs.
  cbn [c_tr_flush_bits c_bi_flush o_bi_valid Z.eqb Z.geb Z.compare bind]. rewrite obs_out, d_pending_obs.
  cbn [o_pending].
  replace (5 >? z_avail_out z) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
  change (u32 5 =? 0) with false. cbv iota.
  change (mkMB (o_buf (tr_out (d_tr (obs s0 (mkOut B 5 0 0 u) M 0)))) (d_pbm (obs s0 (mkOut B 5 0 0 u) M 0)))
    with (mkMB B M).
  change (d_po (obs s0 (mkOut B 5 0 0 u) M 0)) with 0. change (u32 5) with 5.
  rewrite mb_read_some
    by first [lia | split; [lia|]; split; [cbn [mb_val]; lia|]; intros i Hi; cbn [mb_def]; apply Hd; lia].
  cbn [bind mb_val]. unfold out_put. rewrite Zlength_sublist by lia.
  replace (5 - 0 <=? z_avail_out z) with true by (symmetry; apply Z.leb_le; lia). cbn [bind].
  rewrite obs_po. change (0 + 5) with 5.
  change (tr_out (d_tr (obs s0 (mkOut B 5 0 0 u) M 5))) with (mkOut B 5 0 0 u).
  change (d_pbm (obs s0 (mkOut B 5 0 0 u) M 5)) with M. cbn [o_buf o_pending o_bi_buf o_bi_valid o_bi_used].
  rewrite obs_out, d_pending_obs. cbn [o_pending]. rewrite obs_po.
  replace (5 - 0 <=? z_avail_out z) with true by (symmetry; apply Z.leb_le; lia). cbn [bind].
  reflexivity.
Qed.

(** read_buf of [n] bytes, all available. *)
Lemma rb_ok s z n :
  0 < n <= z_avail_in z -> 0 <= z_next_in z -> z_next_in z + z_avail_in z <= Zlength (z_in z) ->
  exists z1, c_read_buf s z n = Some (z1, sublist (z_next_in z) (z_next_in z + n) (z_in z)) /\
    z_in z1 = z_in z /\ z_next_in z1 = z_next_in z + n /\ z_avail_in z1 = z_avail_in z - n /\
    z_out z1 = z_out z /\ z_avail_out z1 = z_avail_out z /\ z_total_out z1 = z_total_out z /\ z_msg z1 = z_msg z.
Proof.
  intros Hn Hi Hl. unfold c_read_buf.
  replace (if z_avail_in z >? n then n else z_avail_in z) with n by (destruct (Z.gtb_spec (z_avail_in z) n); lia).
  replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  unfold rds. cbn [z_in z_next_in set_z_avail_in].
  replace ((0 <=? z_next_in z) && (0 <=? n) && (z_next_in z + n <=? Zlength (z_in z))) with true
    by (symmetry; rewrite !andb_true_iff, !Z.leb_le; lia).
  cbn [bind].
  destruct (d_wrap s =? 1); [|destruct (d_wrap s =? 2)]; eexists; (split; [reflexivity|]); cbn; repeat split; lia.
Qed.

(** The copy from next_in, verbatim from [ds_body]. *)
Lemma incopy_ok s z len :
  0 <= len <= z_avail_in z -> 0 <= z_next_in z -> z_next_in z + z_avail_in z <= Zlength (z_in z) ->
  len <= z_avail_out z < 4294967296 -> 0 <= z_total_out z < 4294967296 ->
  exists z2,
    (if len =? 0 then Some z else
     let* (z, data) := c_read_buf s z len in
     let* _ := guard (Zlength data =? len) in
     let* z := out_put z data in
     let z := set_z_avail_out z (u32 (z_avail_out z - len)) in
     Some (set_z_total_out z (u64 (z_total_out z + len)))) = Some z2 /\
    z_in z2 = z_in z /\ z_next_in z2 = z_next_in z + len /\ z_avail_in z2 = z_avail_in z - len /\
    z_out z2 = z_out z ++ sublist (z_next_in z) (z_next_in z + len) (z_in z) /\
    z_avail_out z2 = z_avail_out z - len /\ z_total_out z2 = z_total_out z + len /\ z_msg z2 = z_msg z.
Proof.
  intros Hl Hi Hn Ha Ht. destruct (Z.eqb_spec len 0) as [->|N].
  - exists z. rewrite Z.add_0_r, sublist_nil, app_nil_r. repeat split; lia.
  - destruct (rb_ok s z len ltac:(lia) Hi Hn) as (z1 & E & A1 & A2 & A3 & A4 & A5 & A6 & A7).
    rewrite E. cbn [bind]. rewrite Zlength_sublist by lia.
    replace (z_next_in z + len - z_next_in z =? len) with true by (symmetry; apply Z.eqb_eq; lia).
    cbn [bind guard]. unfold out_put. rewrite Zlength_sublist by lia.
    replace (z_next_in z + len - z_next_in z <=? z_avail_out z1) with true by (symmetry; apply Z.leb_le; lia).
    cbn [bind]. eexists. split; [reflexivity|]. cbn.
    rewrite u32_id by lia. rewrite u64_id by lia. rewrite A4. repeat split; try lia; assumption.
Qed.

(** The LEN / NLEN bytes deflate_stored writes are those of [stored_block]. *)
Lemma len_bytes len :
  0 <= len <= 65535 ->
  [u8 len; u8 (Z.shiftr len 8); u8 (u32 (Z.lnot len)); u8 (Z.shiftr (u32 (Z.lnot len)) 8)] =
  [len mod 256; len / 256; (65535 - len) mod 256; (65535 - len) / 256].
Proof.
  intros H. unfold u8, u32.
  assert (E : Z.lnot len mod 4294967296 = 65535 - len + 16776960 * 256)
    by (rewrite Z.lnot_eq_pred_opp; symmetry; apply Z.mod_unique with (q := -1); [left|]; lia).
  rewrite E, !Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
  rewrite Z.mod_add by lia. rewrite Z.div_add by lia.
  rewrite (Z.mod_small (len / 256)) by (split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia).
  rewrite Z.add_mod by lia. change (16776960 mod 256) with 0. rewrite Z.add_0_r, Z.mod_mod by lia.
  rewrite (Z.mod_small ((65535 - len) / 256)) by (split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia).
  reflexivity.
Qed.

Lemma hdr5 (b : list Z) (v0 v1 v2 v3 v4 w1 w2 w3 w4 : Z) :
  5 <= Zlength b ->
  sublist 0 5 (upd_Znth 4 (upd_Znth 3 (upd_Znth 2 (upd_Znth 1
    (upd_Znth 4 (upd_Znth 3 (upd_Znth 2 (upd_Znth 1 (upd_Znth 0 b v0) v1) v2) v3) v4) w1) w2) w3) w4) =
  [v0; w1; w2; w3; w4].
Proof. intros H. list_solve. Qed.

Lemma mask5 (m : list bool) i :
  5 <= Zlength m -> 0 <= i < 5 ->
  Znth i (upd_Znth 4 (upd_Znth 3 (upd_Znth 2 (upd_Znth 1
    (upd_Znth 4 (upd_Znth 3 (upd_Znth 2 (upd_Znth 1 (upd_Znth 0 m true) true) true) true) true) true) true) true)
    true) = true.
Proof. intros H Hi. list_solve. Qed.

(** ** One iteration of the first-phase loop

    With [ai] bytes available: a stored block of [min 65535 ai] bytes from next_in, the last one (BFINAL set,
    the loop leaves) when [ai <= 65535]. *)
Lemma ds_iter s0 b u m z mb :
  d_strstart s0 = 0 -> d_block_start s0 = 0 -> 5 <= Zlength b -> Zlength m = Zlength b -> mb <= 32768 ->
  0 <= z_next_in z -> 0 <= z_avail_in z <= 1048576 -> z_next_in z + z_avail_in z <= Zlength (z_in z) ->
  5 + Z.min 65535 (z_avail_in z) <= z_avail_out z ->
  0 <= z_total_out z -> z_total_out z + z_avail_out z < 4294967296 ->
  exists B M z',
    ds_body Z_FINISH mb (ob s0 b u m, z) =
      Some (if z_avail_in z <=? 65535 then inr (ob s0 B 3 M, z', 1) else inl (ob s0 B 3 M, z')) /\
    Zlength B = Zlength b /\ Zlength M = Zlength m /\ (mb_ok (mkMB b m) -> mb_ok (mkMB B M)) /\
    z_in z' = z_in z /\ z_next_in z' = z_next_in z + Z.min 65535 (z_avail_in z) /\
    z_avail_in z' = z_avail_in z - Z.min 65535 (z_avail_in z) /\
    z_out z' = z_out z ++ stored_block (if z_avail_in z <=? 65535 then 1 else 0)
                 (sublist (z_next_in z) (z_next_in z + Z.min 65535 (z_avail_in z)) (z_in z)) /\
    z_avail_out z' = z_avail_out z - (5 + Z.min 65535 (z_avail_in z)) /\
    z_total_out z' = z_total_out z + (5 + Z.min 65535 (z_avail_in z)) /\
    z_msg z' = z_msg z.
Proof.
  intros Hss Hbs Hb Hm Hmb Hni Hai Hn Hao Hto Hta.
  unfold ds_body. cbv beta iota zeta.
  change (stored_hdr (ob s0 b u m)) with 5.
  change (d_strstart (ob s0 b u m)) with (d_strstart s0). change (d_block_start (ob s0 b u m)) with (d_block_start s0).
  rewrite Hss, Hbs.
  set (ai := z_avail_in z) in *. set (A := z_avail_out z) in *.
  change (u32 (0 - 0)) with 0. change (in_long (0 - 0)) with true. rewrite Z.add_0_l.
  unfold MAX_STORED. rewrite (u64_id ai), (u32_id ai), (u32_id (A - 5)) by lia.
  rewrite (min_if 65535 ai), (min_if (Z.min 65535 ai) (A - 5)), (Z.min_l (Z.min 65535 ai)) by lia.
  replace (A <? 5) with false by (symmetry; apply Z.ltb_ge; lia).
  change (Z_FINISH =? Z_FINISH) with true. change (Z_FINISH =? Z_NO_FLUSH) with false.
  cbn [andb orb negb guard bind].
  set (len := Z.min 65535 ai) in *.
  match goal with |- context [if (len <? mb) && ?r then _ else _] =>
    replace ((len <? mb) && r) with false
      by (subst len; destruct (Z.ltb_spec (Z.min 65535 ai) mb); destruct (Z.eqb_spec (Z.min 65535 ai) ai);
          destruct (Z.min 65535 ai =? 0); cbn [andb orb negb]; lia) end.
  replace (len =? ai) with (ai <=? 65535)
    by (subst len; destruct (Z.eqb_spec (Z.min 65535 ai) ai); destruct (Z.leb_spec ai 65535); lia).
  set (lst := if ai <=? 65535 then 1 else 0).
  assert (Hlst : 0 <= lst <= 1) by (subst lst; destruct (ai <=? 65535); lia).
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
  match goal with |- context [c_read_buf ?s ?z1 len] =>
    destruct (incopy_ok s z1 len) as (z2 & E2 & C1 & C2 & C3 & C4 & C5 & C6 & C7);
    [cbn [z_avail_in set_z_avail_out set_z_total_out set_z_out]; lia
    |cbn [z_next_in set_z_avail_out set_z_total_out set_z_out]; lia
    |cbn [z_in z_next_in z_avail_in set_z_avail_out set_z_total_out set_z_out]; lia
    |cbn [z_avail_out set_z_avail_out set_z_total_out set_z_out]; lia
    |cbn [z_total_out set_z_avail_out set_z_total_out set_z_out]; rewrite u64_id by lia; lia
    |] end.
  cbv zeta in E2. rewrite E2. cbn [bind].
  cbn [z_in z_next_in z_avail_in z_out z_avail_out z_total_out z_msg set_z_avail_out set_z_total_out set_z_out]
    in C1, C2, C3, C4, C5, C6, C7.
  rewrite u64_id in C6 by lia.
  rewrite hdr5 in C4 by lia. rewrite <- app_assoc in C4.
  match goal with |- context [obs s0 (mkOut ?B 0 0 0 3) ?M 0] => exists B, M, z2 end.
  assert (Hlen : 0 <= len <= 65535) by lia.
  assert (Hdata : Zlength (sublist (z_next_in z) (z_next_in z + len) (z_in z)) = len)
    by (rewrite Zlength_sublist; lia).
  split; [unfold lst; destruct (ai <=? 65535); reflexivity|].
  split; [rewrite !Zlength_upd_Znth_any; reflexivity|].
  split; [rewrite !Zlength_upd_Znth_any; reflexivity|].
  split.
  { intros Hok. pose proof (u8_range len). pose proof (u8_range (Z.shiftr len 8)).
    pose proof (u8_range (u32 (Z.lnot len))). pose proof (u8_range (Z.shiftr (u32 (Z.lnot len)) 8)).
    repeat (apply mb_ok_upd; [|rewrite ?Zlength_upd_Znth_any; lia|lia]). exact Hok. }
  split; [exact C1|]. split; [exact C2|]. split; [exact C3|].
  split; [rewrite C4; unfold stored_block; rewrite Hdata, <- len_bytes by lia; reflexivity|].
  split; [lia|]. split; [lia|]. exact C7.
Qed.

(** ** The loop

    [lp]: the loop state is [ob s0 ..] with a pending_buf of [L] bytes; the input is [inb] from [Zlength inb -
    avail_in] on; the output written so far followed by the stored blocks of the rest of the input is the
    whole output; room for the blocks of the rest; total_out + avail_out = [T]; total_out counts the bytes
    written after [O] from [tout]. *)
Definition lp (s0 : dstate) (inb O : list Z) (T L tout : Z) (msg : option Z) (a : dstate * strm) : Prop :=
  let '(s, z) := a in
  exists b u m, s = ob s0 b u m /\ Zlength b = L /\ Zlength m = L /\ mb_ok (mkMB b m) /\
  z_in z = inb /\ 0 <= z_avail_in z <= Zlength inb /\ z_next_in z = Zlength inb - z_avail_in z /\
  z_out z ++ stored_blocks (sublist (z_next_in z) (Zlength inb) inb) = O ++ stored_blocks inb /\
  5 * l0_blocks (z_avail_in z) + z_avail_in z <= z_avail_out z /\
  0 <= z_total_out z /\ z_total_out z + z_avail_out z = T /\
  z_total_out z - Zlength (z_out z) = tout - Zlength O /\ z_msg z = msg.

(** The exit of the loop: last = 1, all input consumed, all blocks written. *)
Definition lq (s0 : dstate) (inb O : list Z) (T L tout : Z) (msg : option Z) (r : dstate * strm * Z)
    : Prop :=
  let '(s, z, last) := r in
  last = 1 /\
  exists b u m, s = ob s0 b u m /\ Zlength b = L /\ Zlength m = L /\ mb_ok (mkMB b m) /\
  z_in z = inb /\ z_avail_in z = 0 /\ z_next_in z = Zlength inb /\
  z_out z = O ++ stored_blocks inb /\ z_total_out z + z_avail_out z = T /\
  z_total_out z - Zlength (z_out z) = tout - Zlength O /\ z_msg z = msg.

Lemma lp_step s0 inb O T L tout msg mb a :
  d_strstart s0 = 0 -> d_block_start s0 = 0 -> 5 <= L -> mb <= 32768 -> Zlength inb <= 1048576 ->
  T < 4294967296 ->
  lp s0 inb O T L tout msg a ->
  exists r, ds_body Z_FINISH mb a = Some r /\
    match r with
    | inl a' => lp s0 inb O T L tout msg a' /\ 0 <= z_avail_in (snd a') < z_avail_in (snd a)
    | inr b => lq s0 inb O T L tout msg b
    end.
Proof.
  intros Hss Hbs HL Hmb Hn HT.
  destruct a as [s z].
  intros (b & u & m & -> & Lb & Lm & Hok & Hin & Hai & Hni & Hout & Hroom & Hto & Hta & Hacc & Hmsg).
  set (n := Zlength inb) in *. set (ai := z_avail_in z) in *.
  pose proof (l0_blocks_pos ai ltac:(lia)) as Hbl.
  destruct (ds_iter s0 b u m z mb Hss Hbs ltac:(lia) ltac:(lia) Hmb ltac:(lia) ltac:(lia) ltac:(rewrite Hin; lia)
              ltac:(lia) Hto ltac:(lia))
    as (B & M & z' & E & LB & LM & OK & C1 & C2 & C3 & C4 & C5 & C6 & C7).
  fold ai in E, C2, C3, C4, C5, C6.
  rewrite Hin, Hni in C4. rewrite Hni in C2. rewrite Hni in Hout.
  exists (if ai <=? 65535 then inr (ob s0 B 3 M, z', 1) else inl (ob s0 B 3 M, z')).
  split; [exact E|].
  assert (Lrest : Zlength (sublist (n - ai) n inb) = ai) by (rewrite Zlength_sublist; lia).
  pose proof (stored_blocks_eq (sublist (n - ai) n inb)) as Esb. rewrite Lrest in Esb. unfold MAX_STORED_LEN in Esb.
  destruct (Z.leb_spec ai 65535) as [Hle|Hgt].
  - rewrite Z.min_r in C2, C3, C4, C5, C6 by lia.
    replace (ai <=? 65535) with true in Esb by (symmetry; apply Z.leb_le; lia).
    replace (n - ai + ai) with n in C4 by lia. rewrite <- Esb in C4.
    split; [reflexivity|]. exists B, 3, M.
    split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [auto|].
    split; [congruence|]. split; [lia|]. split; [lia|].
    split; [rewrite C4; exact Hout|].
    split; [lia|].
    split; [rewrite C4, Zlength_app, Zlength_stored_blocks, Lrest, l0_blocks_one by lia; lia|]. congruence.
  - rewrite Z.min_l in C2, C3, C4, C5, C6 by lia.
    replace (ai <=? 65535) with false in Esb by (symmetry; apply Z.leb_gt; lia).
    split; [|cbn [snd]; lia].
    exists B, 3, M.
    split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [auto|].
    split; [congruence|]. split; [lia|]. split; [lia|].
    split.
    { rewrite C4, C2, <- app_assoc. rewrite <- Hout, Esb.
      rewrite sublist_sublist by lia. rewrite sublist_sublist by lia.
      do 3 f_equal; f_equal; lia. }
    split; [rewrite C3, C5; rewrite (l0_blocks_step ai) in Hroom by lia; lia|].
    split; [lia|]. split; [lia|].
    split; [rewrite C4, Zlength_app, Zlength_stored_block, Zlength_sublist by lia; lia|]. congruence.
Qed.

(** ** After the loop *)

Lemma ob_ob_set s0 b u m : d_block_start s0 = 0 -> ob s0 b u m = ob_set s0 (mkOut b 0 0 0 u) m 0 0.
Proof.
  destruct s0 as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? [] ?].
  cbn. intros ->. reflexivity.
Qed.

Lemma min_block_le s : prm s -> ds_min_block s <= 32768.
Proof.
  intros Hp. destruct (prm_pbsize s Hp) as [E1 E2].
  destruct Hp as (Hwb & Hws & _ & Hhb & _ & _ & _ & HL & Hps & _).
  assert (2 ^ 7 <= 2 ^ (d_hash_bits s - 1)) by (apply Z.pow_le_mono_r; lia).
  assert (2 ^ 9 <= 2 ^ d_w_bits s <= 2 ^ 15) by (split; apply Z.pow_le_mono_r; lia).
  unfold ds_min_block. cbv zeta. rewrite (u64_id (d_pending_buf_size s - 5)) by lia.
  rewrite min_if', u32_id by lia. lia.
Qed.

Theorem l0_stored : l0_stored_stmt.
Proof.
  intros s inb O tin aout tout adler msg HW Hok Hp Hpo Hbv Hlev Hss Hbs Hbytes Hn Hroom Ht Hta.
  pose proof (Zlength_nonneg inb) as Hn0.
  set (n := Zlength inb) in *.
  pose proof HW as (Hprm & _).
  destruct (prm_pbsize s Hprm) as [Epb Hpb].
  pose proof Hprm as (_ & _ & _ & Hhb & _ & _ & _ & HL & Hps & Hlb & Hlm & _).
  assert (2 ^ 7 <= 2 ^ (d_hash_bits s - 1)) by (apply Z.pow_le_mono_r; lia).
  set (L := Zlength (o_buf (tr_out (d_tr s)))) in *.
  assert (HL5 : 5 <= L) by lia.
  pose proof Hok as (Hmb & (Hv1 & Hv2 & Hv3) & _).
  assert (Hbb : o_bi_buf (tr_out (d_tr s)) = 0)
    by (unfold d_bi_valid in Hbv; rewrite Hbv in Hv2; change (2 ^ 0) with 1 in Hv2; lia).
  pose proof (ob_init s Hp Hpo Hbv Hbb) as Es.
  set (b0 := o_buf (tr_out (d_tr s))) in *. set (u0 := o_bi_used (tr_out (d_tr s))) in *.
  set (m0 := d_pbm s) in *.
  set (z0 := mkST inb 0 n tin O aout tout adler msg).
  pose proof (l0_blocks_pos n ltac:(lia)) as Hbl.
  destruct (loop_meas (ds_body Z_FINISH (ds_min_block s)) (lp s inb O (tout + aout) L tout msg)
              (lq s inb O (tout + aout) L tout msg) (fun a => z_avail_in (snd a))
              (fun a Ha => lp_step s inb O (tout + aout) L tout msg (ds_min_block s) a Hss Hbs HL5
                             (min_block_le s Hprm) Hn ltac:(lia) Ha)
              (s, z0))
    as ([[s1 z1] last] & Eloop & Hq).
  { cbn [lp]. exists b0, u0, m0. split; [exact Es|]. split; [reflexivity|]. split; [lia|].
    split; [exact Hmb|]. unfold z0; cbn [z_in z_next_in z_avail_in z_out z_avail_out z_total_out z_msg].
    fold n. replace (n - n) with 0 by lia. rewrite sublist_same by lia.
    repeat split; try lia. }
  { cbn [snd z0 z_avail_in]. lia. }
  destruct Hq as (-> & b & u & m & -> & Lb & Lm & Hok1 & Hin & Hai & Hni & Hout & Htt & Hacc & Hmsg).
  fold n in Hni.
  rewrite c_deflate_stored_eq. cbv zeta. fold z0. rewrite Eloop. cbn [bind].
  change (z_avail_in z0) with n. rewrite Hai, Z.sub_0_r, u32_id by lia.
  destruct (LTCStoredWin.dswin_ok LTCStoredChain.chain_parts_ok (ob s b u m) z1 n)
    as (s2 & Ew & HW2 & Hk2 & _).
  { rewrite ob_ob_set by exact Hbs. apply W_ob; [exact HW|exact Hlev|cbn; exact Lb|cbn; transitivity L; [exact Lm|]; change (L = Zlength m0); lia|lia]. }
  { exact Hlev. }
  { rewrite Hin. exact Hbytes. }
  { lia. }
  { rewrite Hni, Hin. fold n. lia. }
  { lia. }
  { intros _. change (d_block_start s = d_strstart s). lia. }
  rewrite Ew. cbn [bind]. change (negb (1 =? 0)) with true. cbv iota.
  exists (set_d_bi_used (upd_high_water s2) 8), z1. split; [reflexivity|].
  pose proof (op_win_eq _ _ Hk2) as Eop. rewrite <- (op_uhw s2) in Eop.
  pose proof (cp_win_eq _ _ Hk2) as Ecp. rewrite <- (cp_uhw s2) in Ecp.
  set (s3 := upd_high_water s2) in *. clearbody s3.
  unfold op in Eop. cbn [ob set_d_po set_d_out set_d_pbm set_d_tr set_out d_tr d_pbm d_po tr_out fst snd] in Eop.
  injection Eop as Eo3 Em3 Ep3.
  unfold cp in Ecp. injection Ecp as _ Ew3 _ _ _ _ _ _ _ _ Epbs3 _ _.
  assert (Lout : Zlength (O ++ stored_blocks inb) = Zlength O + (5 * l0_blocks n + n))
    by (rewrite Zlength_app, Zlength_stored_blocks; reflexivity).
  rewrite Hout in Hacc. rewrite Lout in Hacc.
  split; [exact Hout|].
  split; [lia|]. split; [lia|]. split; [exact Hai|]. split; [exact Hmsg|].
  unfold outok, d_pb, d_pending, d_bi_valid, d_po, d_wrap, d_pending_buf_size.
  cbn [set_d_bi_used d_tr d_pbm set_d_tr set_out tr_out o_buf o_pending o_bi_buf o_bi_valid o_bi_used].
  fold (d_pending_buf_size s3) (d_wrap s3) (d_po s3). rewrite Eo3, Em3, Ep3, Epbs3, Ew3.
  cbn [o_buf o_pending o_bi_buf o_bi_valid o_bi_used ob set_d_po set_d_out set_d_pbm set_d_tr set_out d_tr
       d_pbm d_po d_wrap tr_out fst snd d_pending_buf_size].
  split; [|split; [reflexivity|split; [reflexivity|split; [reflexivity|split; [reflexivity|unfold L; lia]]]]].
  split; [exact Hok1|].
  split; [unfold bits_ok; cbn; lia|].
  split; [lia|]. split; [lia|]. split; [unfold mb_defined; cbn [mb_val mb_def]; split; [lia|split; [lia|intros; lia]]|].
  intros _. reflexivity.
Qed.
