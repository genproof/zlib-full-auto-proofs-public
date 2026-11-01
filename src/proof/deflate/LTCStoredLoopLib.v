(** * Helpers for LTCStoredLoop.v: the first-phase loop of deflate_stored.
    A generic termination lemma for [loop FUEL] (a measure that decreases on every continuing iteration), and
    forward lemmas for the pieces of [ds_body] (the byte stores into pending_buf, the copies to next_out).
    Some lemmas are adapted from LTCLiveKit.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTCStoredKit.
Require Export Zlib.proof.deflate.LTCFlushKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** A loop terminates when a measure decreases on every continuing iteration *)

Section Meas.
Context {A B : Type} (body : A -> option (A + B)) (P : A -> Prop) (Q : B -> Prop) (mu : A -> Z).
Hypothesis Hstep : forall a, P a ->
  exists r, body a = Some r /\
    match r with inl a' => P a' /\ 0 <= mu a' < mu a | inr b => Q b end.

Lemma loop2_meas : forall d a, P a -> 0 <= mu a ->
  (exists b, loop2 d body a = Some (inr b) /\ Q b) \/
  (exists a', loop2 d body a = Some (inl a') /\ P a' /\ 0 <= mu a' /\ mu a' + 2 ^ Z.of_nat d <= mu a).
Proof.
  induction d as [|d IH]; intros a Pa Ma; cbn [loop2].
  - destruct (Hstep a Pa) as ([a'|b] & E & H); rewrite E.
    + right. exists a'. destruct H as [H1 H2]. change (2 ^ Z.of_nat 0) with 1.
      split; [reflexivity|]. split; [exact H1|]. lia.
    + left. exists b. split; [reflexivity|exact H].
  - destruct (IH a Pa Ma) as [(b & E & Qb) | (a' & E & Pa' & M1 & M2)]; rewrite E.
    + left. exists b. split; [reflexivity|exact Qb].
    + destruct (IH a' Pa' M1) as [(b & E2 & Qb) | (a'' & E2 & Pa'' & M3 & M4)]; rewrite E2.
      * left. exists b. split; [reflexivity|exact Qb].
      * right. exists a''. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
        split; [reflexivity|]. split; [exact Pa''|]. lia.
Qed.

Lemma loop_meas : forall a, P a -> 0 <= mu a < 2 ^ 40 -> exists b, loop FUEL body a = Some b /\ Q b.
Proof.
  intros a Pa Ma. unfold loop.
  destruct (loop2_meas FUEL a Pa ltac:(lia)) as [(b & E & Qb) | (a' & E & _ & M1 & M2)]; rewrite E.
  - exists b. split; [reflexivity|exact Qb].
  - exfalso. change (Z.of_nat FUEL) with 40 in M2. lia.
Qed.
End Meas.

(** ** Arithmetic *)

Ltac zb := unfold Buf_size in *; repeat match goal with
  | |- context [Z.gtb ?a ?b] => rewrite (Z.gtb_ltb a b)
  | |- context [Z.geb ?a ?b] => rewrite (Z.geb_leb a b)
  | |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec a b)
  | |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b)
  | |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b)
  end; cbn [andb orb negb]; try reflexivity; try lia.

(** A wrapper that keeps a hypothesis away from lia (min / div / disequalities cause case splits). *)
Definition hide (P : Prop) : Prop := P.
Lemma hide_i (P : Prop) : P -> hide P. Proof. auto. Qed.
Lemma unhide (P : Prop) : hide P -> P. Proof. auto. Qed.
Global Opaque hide.

(** Boolean case analysis, then lia. *)
Ltac bsolve := repeat match goal with
  | |- context [Z.gtb ?a ?b] => rewrite (Z.gtb_ltb a b)
  | |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec a b)
  | |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b)
  | |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b)
  end; cbn [andb orb negb]; intros; try discriminate; try (unfold Z_FINISH, Z_NO_FLUSH in *; lia).

Lemma u32_id x : 0 <= x < 4294967296 -> u32 x = x.
Proof. intros H. unfold u32. apply Z.mod_small. exact H. Qed.

Lemma u8_range x : 0 <= u8 x < 256.
Proof. unfold u8. apply Z.mod_pos_bound. lia. Qed.

Lemma stored_hdr_eq s : 0 <= d_bi_valid s <= 7 -> stored_hdr s = (d_bi_valid s + 42) / 8.
Proof.
  intros H. unfold stored_hdr, d_bi_valid in *. rewrite (u32_id (o_bi_valid _)) by lia.
  rewrite u32_id by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma min3_eq L h :
  (if (if 65535 >? L then L else 65535) >? h then h else if 65535 >? L then L else 65535) =
  Z.min (Z.min 65535 L) h.
Proof.
  rewrite (Z.gtb_ltb 65535 L). destruct (Z.ltb_spec L 65535) as [E|E].
  - rewrite (Z.gtb_ltb L h). destruct (Z.ltb_spec h L); lia.
  - rewrite (Z.gtb_ltb 65535 h). destruct (Z.ltb_spec h 65535); lia.
Qed.

Lemma min_if a b : (if a >? b then b else a) = Z.min a b.
Proof. rewrite Z.gtb_ltb. destruct (Z.ltb_spec b a); lia. Qed.

Lemma min_if' a b : (if a >? b then b else a) = Z.min b a.
Proof. rewrite Z.gtb_ltb. destruct (Z.ltb_spec b a); lia. Qed.

(** ** Events *)

Lemma ev_chain_app g evs g1 e g2 :
  ev_chain g evs g1 -> ev_g e = g1 -> ev_after e = g2 -> ev_chain g (evs ++ [e]) g2.
Proof.
  revert g. induction evs as [|e0 r IH]; intros g H E1 E2; cbn [ev_chain app] in *.
  - split; [congruence|]. cbn [ev_chain]. congruence.
  - destruct H as [H1 H2]. split; [exact H1|]. eapply IH; eauto.
Qed.

Lemma sum_len_app evs e : sum_len (evs ++ [e]) = sum_len evs + ev_len e.
Proof. induction evs as [|e0 r IH]; cbn [sum_len fold_right app] in *; [lia|]. unfold sum_len in IH. lia. Qed.

(** ** pending_buf *)

Lemma pb_grow_refl o m : pb_grow o m o m.
Proof. unfold pb_grow. auto. Qed.

Lemma pb_grow_trans o m o1 m1 o2 m2 :
  pb_grow o m o1 m1 -> pb_grow o1 m1 o2 m2 -> pb_grow o m o2 m2.
Proof. unfold pb_grow. intros (A1 & A2 & A3 & A4) (B1 & B2 & B3 & B4). split; [congruence|]. split; [congruence|]. auto. Qed.

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

Lemma pb_wr_ok s i v :
  outok s -> 0 <= i < Zlength (o_buf (tr_out (d_tr s))) -> 0 <= v < 256 ->
  exists s', c_pb_wr s i v = Some s' /\
    fp_keep s' = fp_keep s /\ d_pending s' = d_pending s /\ d_bi_valid s' = d_bi_valid s /\
    d_po s' = d_po s /\ outok s' /\
    pb_grow (tr_out (d_tr s)) (d_pbm s) (tr_out (d_tr s')) (d_pbm s').
Proof.
  intros Ho Hi Hv.
  pose proof Ho as Ho'. destruct Ho' as ((Hm & _) & _). cbn [d_pb mb_val mb_def] in Hm.
  unfold c_pb_wr, mb_wr, d_pb. cbn [mb_val mb_def].
  replace (in_range i (Zlength (o_buf (tr_out (d_tr s))))) with true
    by (unfold in_range; symmetry; apply andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
  cbn [bind]. eexists. split; [reflexivity|].
  unfold set_d_pb. cbn [mb_val mb_def].
  split; [apply fp_keep_set_d_out|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [apply outok_wr; assumption|].
  pj. cbn [o_buf].
  unfold pb_grow. cbn [o_buf]. rewrite !upd_Znth_Zlength by lia.
  split; [reflexivity|]. split; [reflexivity|]. split.
  - intros j Hj. destruct (Z.eq_dec j i) as [->|N].
    + rewrite upd_Znth_same by lia. reflexivity.
    + destruct (Z_lt_le_dec j 0) as [L|L]; [rewrite Znth_outofbounds in Hj by lia; discriminate|].
      destruct (Z_lt_le_dec j (Zlength (d_pbm s))) as [L2|L2]; [|rewrite Znth_outofbounds in Hj by lia; discriminate].
      rewrite upd_Znth_diff by lia. exact Hj.
  - intros _. pose proof (outok_wr s i v Ho Hi Hv) as (Hmb & _). exact Hmb.
Qed.

Lemma outok_set_out s o m :
  mb_ok (mkMB (o_buf o) m) -> bits_ok o -> 0 <= d_po s -> d_po s + o_pending o <= d_pending_buf_size s ->
  mb_defined (mkMB (o_buf o) m) (d_po s) (d_po s + o_pending o) -> (o_pending o = 0 -> d_po s = 0) ->
  outok (set_d_out s (o, m)).
Proof. intros H1 H2 H3 H4 H5 H6. exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 H6))))). Qed.

Lemma outok_same s s' :
  d_tr s' = d_tr s -> d_pbm s' = d_pbm s -> d_po s' = d_po s -> d_pending_buf_size s' = d_pending_buf_size s ->
  outok s -> outok s'.
Proof. unfold outok, d_pb, d_pending. intros -> -> -> ->. auto. Qed.

Lemma gb_after t bv : 0 <= bv <= 7 -> 8 * ((8 * t + bv + 10) / 8) + 32 = 8 * (t + (bv + 42) / 8).
Proof. intros H. Z.div_mod_to_equations. lia. Qed.

(** ** The stream *)

Lemma zall_adler w z0 z k x :
  zall z0 -> adler_ok w (z_adler z0) -> zstep w z0 z k x -> adler_ok w (z_adler z).
Proof.
  intros ((Hb & _) & _) Ha (_ & _ & _ & _ & _ & E & _). rewrite E. apply adler_ok_upd; [|exact Ha].
  apply bytes_sublist. exact Hb.
Qed.

(** A write of [b] to next_out with avail_out / total_out updated as deflate_stored does. *)
Lemma out_step w z b n :
  zall z -> adler_ok w (z_adler z) -> Zlength b = n -> n <= z_avail_out z -> z_avail_out z < 4294967296 ->
  zstep w z (set_z_total_out (set_z_avail_out (set_z_out z (z_out z ++ b))
                                (u32 (z_avail_out (set_z_out z (z_out z ++ b)) - n)))
               (u64 (z_total_out (set_z_avail_out (set_z_out z (z_out z ++ b))
                                    (u32 (z_avail_out (set_z_out z (z_out z ++ b)) - n))) + n))) 0 b.
Proof.
  intros Hz Ha Hl Hn Hlt. pose proof Hz as ((_ & _ & _ & _ & _) & (Ho & Hto & Hs)).
  pose proof (Zlength_nonneg b).
  apply zout_only_zstep; [exact Hz|exact Ha| |];
    cbn [set_z_total_out set_z_avail_out set_z_out z_in z_next_in z_avail_in z_total_in z_adler z_msg z_out
         z_avail_out z_total_out];
    rewrite (u32_id (z_avail_out z - n)) by lia.
  - unfold zout_only; cbn [set_z_total_out set_z_avail_out set_z_out z_in z_next_in z_avail_in z_total_in z_adler
      z_msg z_out z_avail_out z_total_out].
    rewrite (u64_id (z_total_out z + n)) by lia.
    repeat split; lia.
  - lia.
Qed.

(** The copy from the window, verbatim from [ds_body]. *)
Lemma win_copy_ok w (s : dstate) (z : strm) (len left : Z) :
  0 <= left -> 0 <= len < 4294967296 -> 0 <= d_block_start s -> d_block_start s + left <= 4294967296 ->
  Z.min left len <= z_avail_out z -> z_avail_out z < 4294967296 ->
  zall z -> adler_ok w (z_adler z) -> mb_ok (d_window s) ->
  mb_defined (d_window s) (d_block_start s) (d_block_start s + Z.min left len) ->
  exists s6 z6 wb,
    (if left =? 0 then Some (s, z, len) else
     let left := if left >? len then len else left in
     let* bytes := mb_read (d_window s) (d_block_start s) left in
     let* z := out_put z bytes in
     let z := set_z_avail_out z (u32 (z_avail_out z - left)) in
     let z := set_z_total_out z (u64 (z_total_out z + left)) in
     let* _ := guard (in_long (d_block_start s + left)) in
     let s := set_d_block_start s (d_block_start s + left) in
     Some (s, z, u32 (len - left))) = Some (s6, z6, len - Z.min left len) /\
    zstep w z z6 0 wb /\ Zlength wb = Z.min left len /\ bytes wb /\
    d_block_start s6 = d_block_start s + Z.min left len /\ ob_keep s6 = ob_keep s /\
    d_tr s6 = d_tr s /\ d_pbm s6 = d_pbm s /\ d_po s6 = d_po s.
Proof.
  intros Hl Hn Hb Hbl Hao Haol Hz Ha Hmb Hdef.
  destruct (Z.eqb_spec left 0) as [->|N].
  - exists s, z, []. rewrite Z.min_l by lia. rewrite Z.sub_0_r, Z.add_0_r.
    split; [reflexivity|]. split; [apply zstep_refl; auto|]. split; [reflexivity|]. split; [constructor|].
    auto.
  - rewrite min_if. cbv zeta.
    set (kw := Z.min left len) in *.
    assert (Hkw : 0 <= kw <= left /\ kw <= len) by (unfold kw; lia). clearbody kw.
    rewrite (mb_read_some (d_window s) (d_block_start s) kw ltac:(lia) Hdef). cbn [bind].
    set (wb := sublist (d_block_start s) (d_block_start s + kw) (mb_val (d_window s))).
    assert (Lw : Zlength wb = kw).
    { unfold wb. destruct Hdef as (_ & D2 & _). rewrite Zlength_sublist by lia. lia. }
    unfold out_put. rewrite Lw. replace (kw <=? z_avail_out z) with true by zb. cbn [bind].
    replace (in_long (d_block_start s + kw)) with true by (unfold in_long; zb). cbn [bind guard].
    rewrite (u32_id (len - kw)) by lia.
    do 3 eexists. split; [reflexivity|].
    split; [apply out_step; auto|].
    split; [exact Lw|]. split; [unfold wb; apply mb_bytes; auto|].
    split; [reflexivity|]. split; [reflexivity|]. auto.
Qed.

(** The copy from next_in, verbatim from [ds_body]. *)
Lemma in_copy_ok (s : dstate) (z : strm) (len : Z) :
  0 <= len <= z_avail_in z -> len <= z_avail_out z -> z_avail_out z < 4294967296 ->
  zall z -> adler_ok (d_wrap s) (z_adler z) ->
  exists z7,
    (if len =? 0 then Some z else
     let* (z, data) := c_read_buf s z len in
     let* _ := guard (Zlength data =? len) in
     let* z := out_put z data in
     let z := set_z_avail_out z (u32 (z_avail_out z - len)) in
     Some (set_z_total_out z (u64 (z_total_out z + len)))) = Some z7 /\
    zstep (d_wrap s) z z7 len (sublist (z_next_in z) (z_next_in z + len) (z_in z)).
Proof.
  intros Hl Hao Haol Hz Ha.
  destruct (Z.eqb_spec len 0) as [->|N].
  - exists z. split; [reflexivity|]. rewrite Z.add_0_r, sublist_nil. apply zstep_refl; auto.
  - destruct (read_buf_ok s z len Hz Ha ltac:(lia)) as (z' & E & Zs & O1 & O2 & O3).
    rewrite E. cbn [bind]. rewrite Z.min_l by lia.
    set (data := sublist (z_next_in z) (z_next_in z + len) (z_in z)).
    pose proof Hz as ((Hb & Hni & Hai & Hil & _) & _).
    assert (Ld : Zlength data = len) by (unfold data; rewrite Zlength_sublist by lia; lia).
    rewrite Ld, Z.eqb_refl. cbn [bind guard].
    unfold out_put. rewrite Ld. replace (len <=? z_avail_out z') with true by zb. cbn [bind].
    eexists. split; [reflexivity|].
    assert (Zs' : zstep (d_wrap s) z z' len []) by (rewrite Z.min_l in Zs by lia; exact Zs).
    match goal with |- zstep _ _ ?z7 _ _ => assert (Z2 : zstep (d_wrap s) z' z7 0 data) end.
    { apply out_step; [| |exact Ld|lia|lia].
      + eapply zall_zstep; [exact Hz|exact Zs'|]. lia.
      + eapply zall_adler; [exact Hz|exact Ha|exact Zs']. }
    pose proof (zstep_trans _ _ _ _ _ _ _ _ (proj1 Hz) Ha Zs' Z2) as T. rewrite Z.add_0_r in T. exact T.
Qed.
