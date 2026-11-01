(** * Kit for LTCLive2.v: the first phase of deflate_stored with Z_FINISH and room for everything
    ends with last = 1.  Invariant [linv] of the [ds_body] loop; one iteration keeps it or leaves with last = 1. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTCSpecs2.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** Boolean comparisons by lia. *)
Ltac zb := unfold Buf_size in *; repeat match goal with
  | |- context [Z.gtb ?a ?b] => rewrite (Z.gtb_ltb a b)
  | |- context [Z.geb ?a ?b] => rewrite (Z.geb_leb a b)
  | |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec a b)
  | |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b)
  | |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b)
  end; cbn [andb orb negb]; try reflexivity; try lia.

(** ** Byte writes into pending_buf, read backwards from a successful run *)

Lemma put_byte_inv o m c o' m' :
  Zlength m = Zlength (o_buf o) -> c_put_byte (o, m) c = Some (o', m') ->
  wr_region o m o' m' 1 /\ o_bi_valid o' = o_bi_valid o /\ o_bi_buf o' = o_bi_buf o.
Proof.
  intros Hm H.
  assert (Hr : 0 <= o_pending o < Zlength (o_buf o)).
  { unfold c_put_byte, wr, in_range in H.
    destruct ((0 <=? o_pending o) && (o_pending o <? Zlength (o_buf o))) eqn:E; [|discriminate].
    apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia. }
  rewrite c_put_byte_ok in H by assumption. inversion H; subst; clear H.
  split; [apply wr_region_put; assumption|]. split; reflexivity.
Qed.

Lemma wr_region_len o m o' m' k :
  Zlength m = Zlength (o_buf o) -> wr_region o m o' m' k -> Zlength m' = Zlength (o_buf o').
Proof. intros Hm (W1 & W2 & _). congruence. Qed.

Lemma put_short_inv o m w o' m' :
  Zlength m = Zlength (o_buf o) -> c_put_short (o, m) w = Some (o', m') ->
  wr_region o m o' m' 2 /\ o_bi_valid o' = o_bi_valid o /\ o_bi_buf o' = o_bi_buf o.
Proof.
  intros Hm H. unfold c_put_short in H.
  destruct (c_put_byte (o, m) (Z.land w 255)) as [[o1 m1]|] eqn:E1; [|discriminate]. cbn [bind] in H.
  destruct (put_byte_inv _ _ _ _ _ Hm E1) as (W1 & V1 & B1).
  destruct (put_byte_inv _ _ _ _ _ (wr_region_len _ _ _ _ _ Hm W1) H) as (W2 & V2 & B2).
  split; [|split; congruence].
  change 2 with (1 + 1). eapply wr_region_trans; [lia|lia|exact W1|exact W2].
Qed.

(** The tail of the empty stored block after bi_windup: the two length words. *)
Lemma sblk_tail o m bv o' m' :
  Zlength m = Zlength (o_buf o) ->
  (let* om := c_put_short (mkOut (o_buf o) (o_pending o) 0 0 bv, m) (u16 0) in
   let* (o, m) := c_put_short om (u16 (Z.lnot 0)) in
   let* (b, m) := (if negb (0 =? 0) then None else Some (o_buf o, m)) in
   Some (mkOut b (o_pending o + 0) (o_bi_buf o) (o_bi_valid o) (o_bi_used o), m)) = Some (o', m') ->
  wr_region o m o' m' 4 /\ o_bi_valid o' = 0 /\ o_bi_buf o' = 0.
Proof.
  intros Hm H.
  destruct (c_put_short (mkOut (o_buf o) (o_pending o) 0 0 bv, m) (u16 0)) as [[o4 m4]|] eqn:E4;
    cbn [bind] in H; [|discriminate].
  destruct (put_short_inv (mkOut (o_buf o) (o_pending o) 0 0 bv) m _ _ _ Hm E4) as (W4 & V4 & B4).
  destruct (c_put_short (o4, m4) (u16 (Z.lnot 0))) as [[o5 m5]|] eqn:E5; cbn [bind] in H; [|discriminate].
  destruct (put_short_inv _ _ _ _ _ (wr_region_len _ _ _ _ _ Hm W4) E5) as (W5 & V5 & B5).
  cbn [negb Z.eqb bind] in H. inversion H; subst o' m'; clear H.
  cbn [o_bi_valid o_bi_buf] in *. split; [|split; congruence].
  assert (Wt : wr_region (mkOut (o_buf o) (o_pending o) 0 0 bv) m o5 m5 (2 + 2))
    by (eapply wr_region_trans; [lia|lia|exact W4|exact W5]).
  destruct Wt as (A1 & A2 & A3 & A4 & A5). cbn [o_buf o_pending] in *.
  unfold wr_region; cbn [o_buf o_pending]. rewrite Z.add_0_r. auto 6.
Qed.

(** The empty stored block of the first phase: [(bi_valid + 42) / 8] bytes at pending, bit buffer emptied. *)
Lemma sblk0_inv o m last o' m' :
  Zlength m = Zlength (o_buf o) -> 0 <= o_bi_valid o <= 7 -> 0 <= last <= 1 ->
  c_tr_stored_block (o, m) [] 0 last = Some (o', m') ->
  wr_region o m o' m' ((o_bi_valid o + 42) / 8) /\ o_bi_valid o' = 0 /\ o_bi_buf o' = 0.
Proof.
  intros Hm Hv Hl H. unfold c_tr_stored_block, c_send_bits in H.
  replace ((0 <=? o_bi_valid o) && (o_bi_valid o <=? Buf_size)) with true in H
    by zb.
  cbn [bind guard] in H.
  replace (o_bi_valid o >? Buf_size - 3) with false in H
    by zb.
  cbn [bind] in H.
  set (o1 := set_bits o _ (o_bi_valid o + 3)) in H.
  assert (W1 : wr_region o m o1 m 0) by (apply wr_region_0; reflexivity).
  assert (V1 : o_bi_valid o1 = o_bi_valid o + 3) by reflexivity.
  clearbody o1.
  unfold c_bi_windup in H.
  replace ((0 <=? o_bi_valid o1) && (o_bi_valid o1 <=? 16)) with true in H
    by zb.
  cbn [bind guard] in H.
  assert (Hm1 : Zlength m = Zlength (o_buf o1)) by (destruct W1 as (A & _); congruence).
  destruct (o_bi_valid o1 >? 8) eqn:G8.
  - destruct (c_put_short (o1, m) (o_bi_buf o1)) as [[o2 m2]|] eqn:E; cbn [bind] in H; [|discriminate].
    destruct (put_short_inv _ _ _ _ _ Hm1 E) as (W2 & _).
    destruct (sblk_tail o2 m2 _ o' m' (wr_region_len _ _ _ _ _ Hm1 W2) H) as (W3 & V3 & B3).
    split; [|split; assumption].
    replace ((o_bi_valid o + 42) / 8) with (0 + 2 + 4) by (apply Z.gtb_lt in G8; Z.div_mod_to_equations; lia).
    eapply wr_region_trans; [lia|lia| |exact W3]. eapply wr_region_trans; [lia|lia|exact W1|exact W2].
  - destruct (o_bi_valid o1 >? 0) eqn:G0; [|rewrite Z.gtb_ltb in G0; apply Z.ltb_ge in G0; lia].
    destruct (c_put_byte (o1, m) (o_bi_buf o1)) as [[o2 m2]|] eqn:E; cbn [bind] in H; [|discriminate].
    destruct (put_byte_inv _ _ _ _ _ Hm1 E) as (W2 & _).
    destruct (sblk_tail o2 m2 _ o' m' (wr_region_len _ _ _ _ _ Hm1 W2) H) as (W3 & V3 & B3).
    split; [|split; assumption].
    replace ((o_bi_valid o + 42) / 8) with (0 + 1 + 4)
      by (rewrite Z.gtb_ltb in G8; apply Z.ltb_ge in G8; Z.div_mod_to_equations; lia).
    eapply wr_region_trans; [lia|lia| |exact W3]. eapply wr_region_trans; [lia|lia|exact W1|exact W2].
Qed.

(** ** The invariant of the first-phase loop *)

Lemma u32_id x : 0 <= x < 4294967296 -> u32 x = x.
Proof. intros H. unfold u32. apply Z.mod_small. exact H. Qed.

Lemma stored_hdr_eq s : 0 <= d_bi_valid s <= 7 -> stored_hdr s = (d_bi_valid s + 42) / 8.
Proof.
  intros H. unfold stored_hdr, d_bi_valid in *. rewrite (u32_id (o_bi_valid _)) by lia.
  rewrite u32_id by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

(** ** Pieces of [ds_body] *)

Lemma min_eq L h : 0 <= L <= h ->
  (if (if 65535 >? L then L else 65535) >? h then h else if 65535 >? L then L else 65535) = Z.min 65535 L.
Proof.
  intros H. rewrite (Z.gtb_ltb 65535 L). destruct (Z.ltb_spec L 65535) as [E|E].
  - rewrite (Z.gtb_ltb L h). destruct (Z.ltb_spec h L); lia.
  - rewrite (Z.gtb_ltb 65535 h). destruct (Z.ltb_spec h 65535); lia.
Qed.

Lemma pb_wr_inv s i v s' :
  c_pb_wr s i v = Some s' ->
  0 <= i < Zlength (o_buf (tr_out (d_tr s))) /\
  s' = set_d_out s (mkOut (upd_Znth i (o_buf (tr_out (d_tr s))) v) (d_pending s) (o_bi_buf (tr_out (d_tr s)))
                          (d_bi_valid s) (o_bi_used (tr_out (d_tr s))), upd_Znth i (d_pbm s) true).
Proof.
  unfold c_pb_wr, mb_wr, d_pb. cbn [mb_val mb_def].
  destruct (in_range i (Zlength (o_buf (tr_out (d_tr s))))) eqn:E; [|discriminate].
  cbn [bind]. intros H. inversion H; subst s'; clear H.
  unfold in_range in E. apply andb_true_iff in E. destruct E as [E1 E2].
  apply Z.leb_le in E1. apply Z.ltb_lt in E2. split; [lia|reflexivity].
Qed.

Lemma outok_wr s i v :
  outok s -> 0 <= i < Zlength (o_buf (tr_out (d_tr s))) -> 0 <= v < 256 ->
  outok (set_d_out s (mkOut (upd_Znth i (o_buf (tr_out (d_tr s))) v) (d_pending s) (o_bi_buf (tr_out (d_tr s)))
                          (d_bi_valid s) (o_bi_used (tr_out (d_tr s))), upd_Znth i (d_pbm s) true)).
Proof.
  intros (Hmb & Hbits & Hpo & Hpe & Hdef & Hp0) Hi Hv.
  unfold outok, d_pb, d_pending, d_bi_valid in *. pj.
  destruct Hmb as [Hm1 Hm2]. cbn [mb_val mb_def o_buf o_pending o_bi_valid o_bi_buf] in *.
  split; [|split; [exact Hbits|split; [exact Hpo|split; [exact Hpe|split; [|exact Hp0]]]]].
  - unfold mb_ok; cbn [mb_val mb_def]. rewrite !upd_Znth_Zlength by lia. split; [lia|].
    intros j Hj Hd. destruct (Z.eq_dec j i) as [->|N].
    + rewrite upd_Znth_same by lia. exact Hv.
    + rewrite upd_Znth_diff by lia. rewrite upd_Znth_diff in Hd by lia. apply Hm2; auto.
  - destruct Hdef as (D1 & D2 & D3). unfold mb_defined; cbn [mb_val mb_def] in *.
    rewrite upd_Znth_Zlength by lia. split; [lia|split; [lia|]].
    intros j Hj. destruct (Z.eq_dec j i) as [->|N].
    + rewrite upd_Znth_same by lia. reflexivity.
    + rewrite upd_Znth_diff by lia. apply D3. lia.
Qed.

Lemma u8_range x : 0 <= u8 x < 256.
Proof. unfold u8. apply Z.mod_pos_bound. lia. Qed.

Lemma mb_read_len b lo len l : mb_read b lo len = Some l -> 0 <= lo -> Zlength l = len.
Proof.
  unfold mb_read, mb_definedb. intros H Hlo.
  destruct ((0 <=? len) && (((0 <=? lo) && (lo + len <=? Zlength (mb_val b))) && _)) eqn:E; [|discriminate].
  inversion H; subst l. apply andb_true_iff in E. destruct E as [E1 E2].
  apply andb_true_iff in E2. destruct E2 as [E2 _]. apply andb_true_iff in E2. destruct E2 as [_ E2].
  apply Z.leb_le in E1. apply Z.leb_le in E2. rewrite Zlength_sublist by lia. lia.
Qed.

(** The copy from the window, verbatim from [ds_body]. *)
Lemma win_copy_inv (s : dstate) (z : strm) (len left : Z) s1 z1 len1 :
  (if left =? 0 then Some (s, z, len) else
     let left := if left >? len then len else left in
     let* bytes := mb_read (d_window s) (d_block_start s) left in
     let* z := out_put z bytes in
     let z := set_z_avail_out z (u32 (z_avail_out z - left)) in
     let z := set_z_total_out z (u64 (z_total_out z + left)) in
     let* _ := guard (in_long (d_block_start s + left)) in
     let s := set_d_block_start s (d_block_start s + left) in
     Some (s, z, u32 (len - left))) = Some (s1, z1, len1) ->
  0 <= left -> 0 <= len < 4294967296 -> 0 <= d_block_start s -> 0 <= z_avail_out z < 4294967296 ->
  0 <= z_total_out z -> z_total_out z + z_avail_out z < 18446744073709551616 ->
  s1 = set_d_block_start s (d_block_start s + Z.min left len) /\
  Z.min left len <= z_avail_out z /\
  z_avail_out z1 = z_avail_out z - Z.min left len /\ z_total_out z1 = z_total_out z + Z.min left len /\
  z_avail_in z1 = z_avail_in z /\ len1 = len - Z.min left len.
Proof.
  intros H Hl Hn Hb Ha Ht Hta.
  destruct (Z.eqb_spec left 0) as [->|N].
  - inversion H; subst. rewrite Z.min_l by lia. rewrite Z.add_0_r, Z.sub_0_r.
    split; [match goal with |- ?x = _ => destruct x; reflexivity end|]. repeat split; lia.
  - assert (Ek : (if left >? len then len else left) = Z.min left len)
      by (rewrite Z.gtb_ltb; destruct (Z.ltb_spec len left); lia).
    rewrite Ek in H. cbv zeta in H.
    destruct (mb_read (d_window s) (d_block_start s) (Z.min left len)) as [bytes|] eqn:E1; cbn [bind] in H;
      [|discriminate].
    apply mb_read_len in E1; [|exact Hb].
    unfold out_put in H. destruct (Z.leb_spec (Zlength bytes) (z_avail_out z)) as [Lo|Lo]; [|discriminate].
    cbn [bind] in H.
    destruct (in_long _); cbn [bind guard] in H; [|discriminate].
    inversion H; subst s1 z1 len1; clear H. cbn [set_z_total_out set_z_avail_out set_z_out z_avail_out z_total_out z_avail_in].
    rewrite E1 in Lo.
    rewrite (u32_id (z_avail_out z - Z.min left len)) by lia.
    rewrite (u64_id (z_total_out z + Z.min left len)) by lia.
    rewrite (u32_id (len - Z.min left len)) by lia.
    split; [reflexivity|]. repeat split; lia.
Qed.

(** The copy from next_in, verbatim from [ds_body]. *)
Lemma in_copy_inv (s : dstate) (z : strm) (len : Z) z2 :
  (if len =? 0 then Some z else
     let* (z, data) := c_read_buf s z len in
     let* _ := guard (Zlength data =? len) in
     let* z := out_put z data in
     let z := set_z_avail_out z (u32 (z_avail_out z - len)) in
     Some (set_z_total_out z (u64 (z_total_out z + len)))) = Some z2 ->
  0 <= len <= z_avail_in z -> 0 <= z_avail_out z < 4294967296 ->
  0 <= z_total_out z -> z_total_out z + z_avail_out z < 18446744073709551616 ->
  len <= z_avail_out z /\
  z_avail_out z2 = z_avail_out z - len /\ z_total_out z2 = z_total_out z + len /\
  z_avail_in z2 = z_avail_in z - len.
Proof.
  intros H Hl Ha Ht Hta.
  destruct (Z.eqb_spec len 0) as [->|N].
  - inversion H; subst. repeat split; lia.
  - unfold c_read_buf in H.
    replace (if z_avail_in z >? len then len else z_avail_in z) with len in H
      by (rewrite Z.gtb_ltb; destruct (Z.ltb_spec len (z_avail_in z)); lia).
    replace (len =? 0) with false in H by (symmetry; apply Z.eqb_neq; exact N).
    destruct (rds _ _ _) as [data|] eqn:E1; cbn [bind] in H; [|discriminate].
    destruct (Z.eqb_spec (Zlength data) len) as [Ed|Ed]; cbn [bind guard] in H; [|
      destruct (d_wrap s =? 1); [|destruct (d_wrap s =? 2)]; cbn [bind guard] in H; discriminate].
    destruct (d_wrap s =? 1); [|destruct (d_wrap s =? 2)]; cbn [bind guard] in H;
    unfold out_put in H; cbn [z_avail_out set_z_total_in set_z_next_in set_z_adler set_z_avail_in] in H;
    (destruct (Zlength data <=? z_avail_out z) eqn:Lo; [|discriminate]); apply Z.leb_le in Lo;
    cbn [bind] in H; inversion H; subst z2; clear H; cbn;
    rewrite (u32_id (z_avail_out z - len)) by lia;
    rewrite (u64_id (z_total_out z + len)) by lia; repeat split; lia.
Qed.

Lemma pb_wr_facts s i v s' :
  c_pb_wr s i v = Some s' ->
  0 <= i < Zlength (o_buf (tr_out (d_tr s))) /\ fp_keep s' = fp_keep s /\ d_pending s' = d_pending s /\
  d_bi_valid s' = d_bi_valid s /\ d_po s' = d_po s /\
  Zlength (o_buf (tr_out (d_tr s'))) = Zlength (o_buf (tr_out (d_tr s))) /\
  (outok s -> 0 <= v < 256 -> outok s').
Proof.
  intros H. destruct (pb_wr_inv _ _ _ _ H) as [Hi ->].
  split; [exact Hi|]. split; [apply fp_keep_set_d_out|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [cbn [tr_out d_tr set_d_out set_d_pbm set_d_tr set_out fst o_buf]; apply upd_Znth_Zlength; lia|].
  intros Ho Hv. apply outok_wr; assumption.
Qed.

Definition lrest (s : dstate) (z : strm) : Z := d_strstart s - d_block_start s + z_avail_in z.

Definition linv (s : dstate) (z : strm) : Prop :=
  d_pending_buf_size s = Zlength (o_buf (tr_out (d_tr s))) /\ d_pending_buf_size s <= 131072 /\
  outok s /\ quiet s /\
  0 <= d_block_start s <= d_strstart s /\ d_strstart s - d_block_start s <= 16777216 /\
  zout_ok z /\ 0 <= z_avail_in z <= 1073741824 /\ z_avail_out z <= 1073741824 /\
  stored_hdr s + 5 * (lrest s z / MAX_STORED) + lrest s z <= z_avail_out z.

Lemma ds_step mb s z r :
  mb < MAX_STORED -> linv s z -> ds_body Z_FINISH mb (s, z) = Some r ->
  match r with inl (s', z') => linv s' z' | inr (_, _, last) => last <> 0 end.
Proof.
  intros Hmb (Hps & Hps2 & Hok & (Hq1 & Hq2 & Hq3) & Hb & Hl & Hz & Hai & Hao & Hroom) H.
  assert (Hbv : 0 <= d_bi_valid s) by (destruct Hok as (_ & (? & _) & _); unfold d_bi_valid; lia).
  rewrite stored_hdr_eq in Hroom by lia. unfold lrest in Hroom.
  unfold ds_body in H. cbv beta iota in H.
  assert (Ehdr : stored_hdr s = (d_bi_valid s + 42) / 8) by (apply stored_hdr_eq; lia).
  rewrite Ehdr in H. unfold MAX_STORED in *.
  set (hdr := (d_bi_valid s + 42) / 8) in *.
  assert (Hhdr : 5 <= hdr <= 6) by (subst hdr; Z.div_mod_to_equations; lia).
  set (left := d_strstart s - d_block_start s) in *.
  set (A := z_avail_out z) in *. set (ai := z_avail_in z) in *.
  assert (Hdiv : 0 <= (left + ai) / 65535) by (apply Z.div_pos; lia).
  rewrite (u32_id left) in H by lia. rewrite (u64_id (left + ai)) in H by lia.
  rewrite (u32_id (left + ai)) in H by lia. rewrite (u32_id (A - hdr)) in H by lia.
  replace (A <? hdr) with false in H by zb.
  replace (in_long left) with true in H by (unfold in_long; zb). cbn [bind guard] in H.
  rewrite (min_eq (left + ai) (A - hdr)) in H by lia.
  set (len := Z.min 65535 (left + ai)) in H.
  change (Z_FINISH =? Z_FINISH) with true in H. change (Z_FINISH =? Z_NO_FLUSH) with false in H.
  cbn [andb orb negb] in H. rewrite andb_false_r in H.
  set (last := if len =? left + ai then 1 else 0) in H.
  assert (Hlast : last = 1 <-> len = left + ai) by (subst last; destruct (Z.eqb_spec len (left + ai)); lia).
  assert (Hlast' : last = 0 \/ last = 1) by (subst last; destruct (len =? left + ai); lia).
  assert (Elen : len = Z.min 65535 (left + ai)) by reflexivity. clearbody len last.
  replace ((len <? mb) && (false || false || negb (len =? left + ai))) with false in H by zb.
  cbv iota in H.
  (* the empty stored block and its length bytes *)
  destruct (c_tr_stored_block (d_out s) [] 0 last) as [[o1 m1]|] eqn:E1; cbn [bind] in H; [|discriminate].
  match type of H with bind (c_pb_wr ?a ?b ?c) _ = _ => destruct (c_pb_wr a b c) as [s1|] eqn:E2 end;
    cbn [bind] in H; [|discriminate].
  match type of H with bind (c_pb_wr ?a ?b ?c) _ = _ => destruct (c_pb_wr a b c) as [s2|] eqn:E3 end;
    cbn [bind] in H; [|discriminate].
  match type of H with bind (c_pb_wr ?a ?b ?c) _ = _ => destruct (c_pb_wr a b c) as [s3|] eqn:E4 end;
    cbn [bind] in H; [|discriminate].
  match type of H with bind (c_pb_wr ?a ?b ?c) _ = _ => destruct (c_pb_wr a b c) as [s4|] eqn:E5 end;
    cbn [bind] in H; [|discriminate].
  destruct (c_flush_pending s4 z) as [[s5 z5]|] eqn:E6; cbn [bind] in H; [|discriminate].
  match type of H with bind ?c _ = _ => destruct c as [[[s6 z6] len6]|] eqn:E7 end;
    cbn [bind] in H; [|discriminate].
  match type of H with bind ?c _ = _ => destruct c as [z7|] eqn:E8 end;
    cbn [bind] in H; [|discriminate].
  (* facts on the stored block *)
  pose proof Hok as Hok0. destruct Hok0 as ((Hmlen & _) & _).
  cbn [d_pb mb_val mb_def] in Hmlen.
  unfold d_out in E1.
  destruct (sblk0_inv _ _ last _ _ Hmlen ltac:(unfold d_bi_valid in *; lia) ltac:(lia) E1) as (Wr & Bv1 & Bb1).
  fold (d_bi_valid s) in Wr. fold hdr in Wr.
  destruct (pb_wr_facts _ _ _ _ E2) as (I2 & K2 & P2 & V2 & O2 & L2 & U2).
  destruct (pb_wr_facts _ _ _ _ E3) as (I3 & K3 & P3 & V3 & O3 & L3 & U3).
  destruct (pb_wr_facts _ _ _ _ E4) as (I4 & K4 & P4 & V4 & O4 & L4 & U4).
  destruct (pb_wr_facts _ _ _ _ E5) as (I5 & K5 & P5 & V5 & O5 & L5 & U5).
  rewrite pj_out_pending in P2. pj.
  assert (Wr' := Wr). destruct Wr' as (R1 & R2 & R3 & R4 & R5).
  unfold d_pending in Hq1. rewrite Hq1 in R3.
  rewrite P2 in P3. rewrite P3 in P4. rewrite P4 in P5.
  rewrite P3, R3 in I4. rewrite P4, R3 in I5.
  rewrite L4, L3, L2, R1 in I5.
  rewrite (u64_id (0 + hdr - 1)) in I5 by lia.
  assert (Ok1 : outok (set_d_out s (o1, m1))).
  { unfold outok, d_pb. pj. cbn [mb_val mb_def]. split; [|split; [|split; [|split; [|split]]]].
    - apply (wr_region_mb_ok _ _ _ _ _ (proj1 Hok) Wr).
    - unfold bits_ok. rewrite Bv1, Bb1. cbn. lia.
    - lia.
    - rewrite R3. rewrite Hq2. unfold d_pending_buf_size in *. lia.
    - unfold mb_defined; cbn [mb_val mb_def]. rewrite Hq2, R3. split; [lia|split; [lia|]].
      intros j Hj. apply R5. lia.
    - intros _. exact Hq2. }
  assert (Ok4 : outok s4) by (apply U5; [apply U4; [apply U3; [apply U2; [exact Ok1|]|]|]|]; apply u8_range).
  (* flush_pending *)
  assert (Hps4 : d_pending_buf_size s4 = Zlength (o_buf (tr_out (d_tr s4))) /\ d_pending_buf_size s4 <= 131072).
  { assert (Kp : d_pending_buf_size s4 = d_pending_buf_size s).
    { change (d_pending_buf_size (fp_keep s4) = d_pending_buf_size (fp_keep s)).
      rewrite K5, K4, K3, K2, fp_keep_set_d_out. reflexivity. }
    rewrite Kp, L5, L4, L3, L2, R1. split; lia. }
  assert (Bv4 : d_bi_valid s4 = 0) by (rewrite V5, V4, V3, V2; exact Bv1).
  destruct (fpend_ok s4 z (proj1 Hps4) (proj2 Hps4) Ok4 Hz ltac:(left; lia))
    as (s5' & z5' & x & Ef & Zo & Bx & Lx & Pe & Bv & Ok5 & _ & K6 & Gr).
  rewrite E6 in Ef. inversion Ef; subst s5' z5'; clear Ef.
  rewrite Bv4, P5 in Lx. rewrite Bv4, P5 in Pe. rewrite Bv4 in Bv.
  change (0 / 8) with 0 in Lx, Pe. change (0 mod 8) with 0 in Bv.
  destruct Zo as (Zi1 & Zi2 & Zi3 & Zi4 & Zi5 & Zi6 & Zi7 & Zi8 & Zi9).
  rewrite Z.min_l in Lx by lia.
  assert (Kss : fp_keep s5 = fp_keep s) by (rewrite K6, K5, K4, K3, K2, fp_keep_set_d_out; reflexivity).
  assert (Ss5 : d_strstart s5 = d_strstart s) by exact (f_equal d_strstart Kss).
  assert (Sb5 : d_block_start s5 = d_block_start s) by exact (f_equal d_block_start Kss).
  assert (Sp5 : d_pending_buf_size s5 = d_pending_buf_size s) by exact (f_equal d_pending_buf_size Kss).
  destruct Gr as (Gr1 & _).
  rewrite L5, L4, L3, L2, R1 in Gr1.
  destruct Hz as (Hz1 & Hz2 & Hz3).
  assert (Hlen : 0 <= len <= 65535) by lia.
  (* the copies *)
  destruct (win_copy_inv s5 z5 len left s6 z6 len6 E7 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as (Es6 & Kle & Ao6 & To6 & Ai6 & Len6).
  set (k := Z.min left len) in *.
  assert (Hk : 0 <= k <= left /\ k <= len) by (subst k; lia).
  destruct (in_copy_inv s6 z6 len6 z7 E8 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as (Kle2 & Ao7 & To7 & Ai7).
  destruct Hlast' as [L0|L1]; rewrite ?L0, ?L1 in H; cbn in H; inversion H; subst r; clear H; [|lia].
  assert (Hne : len <> left + ai) by (intros E; apply Hlast in E; lia).
  assert (Hlen' : len = 65535) by lia.
  assert (Q1 : d_strstart s6 = d_strstart s) by (rewrite Es6; exact Ss5).
  assert (Q2 : d_block_start s6 = d_block_start s + k) by (rewrite Es6; cbn [d_block_start set_d_block_start]; rewrite Sb5; reflexivity).
  assert (Q3 : d_pending_buf_size s6 = d_pending_buf_size s) by (rewrite Es6; exact Sp5).
  assert (Q4 : Zlength (o_buf (tr_out (d_tr s6))) = Zlength (o_buf (tr_out (d_tr s)))) by (rewrite Es6; exact Gr1).
  assert (Q5 : outok s6) by (rewrite Es6; exact Ok5).
  assert (Q6 : d_pending s6 = 0) by (rewrite Es6; change (d_pending s5 = 0); lia).
  assert (Q7 : d_bi_valid s6 = 0) by (rewrite Es6; exact Bv).
  assert (Q8 : d_po s6 = 0) by (destruct Q5 as (_ & _ & _ & _ & _ & Hp0); apply Hp0; exact Q6).
  assert (Hdq : (left + ai) / 65535 = (left + ai - 65535) / 65535 + 1).
  { rewrite <- Z.div_add by lia. f_equal. lia. }
  unfold linv, lrest, quiet. rewrite stored_hdr_eq by lia. rewrite Q1, Q2, Q3, Q4, Q6, Q7, Q8.
  change ((0 + 42) / 8) with 5.
  assert (Enum : d_strstart s - (d_block_start s + k) + z_avail_in z7 = left + ai - 65535)
    by (rewrite Ai7, Ai6, Zi3; subst left ai; lia).
  rewrite Enum. unfold MAX_STORED, zout_ok.
  split; [lia|]. split; [lia|]. split; [exact Q5|]. split; [lia|].
  rewrite Ao7, To7, Ai7, Ao6, To6, Ai6, Zi8, Zi9, Zi3, Lx, R3. fold A ai. lia.
Qed.

(** ** The loop: every run from [linv] leaves with last <> 0 *)
Lemma ds_loop mb s z s1 z1 last :
  mb < MAX_STORED -> linv s z -> loop FUEL (ds_body Z_FINISH mb) (s, z) = Some (s1, z1, last) -> last <> 0.
Proof.
  intros Hmb Hi H. apply loop_runs in H.
  remember (s, z) as a eqn:Ea. remember (s1, z1, last) as b eqn:Eb.
  revert s z Hi Ea. induction H as [a r Hr|a a' r Hr Hrun IH]; intros s z Hi Ea; subst.
  - pose proof (ds_step _ _ _ _ Hmb Hi Hr) as G. exact G.
  - destruct a' as [s' z']. pose proof (ds_step _ _ _ _ Hmb Hi Hr) as G.
    exact (IH eq_refl s' z' G eq_refl).
Qed.
