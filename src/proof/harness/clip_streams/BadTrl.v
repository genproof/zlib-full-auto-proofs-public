(* Law rj_bad_checksum: the trailer.  From a loop head in CHECK or LENGTH (BadKit.chead) the rest of the call
   reads the changed trailer: CHECK compares the Adler-32 (zlib, big-endian) or the CRC-32 (gzip) of the data
   with the bytes read, LENGTH (gzip) ISIZE with the total; since src differs from the stream in the trailer,
   one of them differs and the mode becomes BAD (the call returns Z_DATA_ERROR), or the input runs out first
   and the call returns Z_OK or Z_BUF_ERROR with part of the trailer read (BadKit.pc_state).  Never
   Z_STREAM_END. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.harness.clip_streams.BadKit.
Require Import Zlib.proof.inflate.Steps2.
Require Zlib.proof.crc32.Combine.
Require Zlib.proof.rfc1951.DecTrl.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* Bytes in the bit buffer                                                                        *)

Lemma bt_le_val_trl l : le_val l = Zlib.proof.rfc1951.DecTrl.trl_le l.
Proof. induction l as [|b l IH]; [reflexivity|]. unfold le_val in *. cbn [fold_right]. rewrite IH. reflexivity. Qed.

Lemma bt_le_val_app l x : le_val (l ++ [x]) = le_val l + x * 256 ^ Zlength l.
Proof.
  induction l as [|b l IH]; unfold le_val in *; cbn [app fold_right].
  - rewrite Zlength_nil. change (256 ^ 0) with 1. lia.
  - rewrite IH, Zlength_cons, Z.pow_succ_r by apply Zlength_nonneg. ring.
Qed.

Lemma bt_le_val_range l : Forall byte_ok l -> 0 <= le_val l < 256 ^ Zlength l.
Proof.
  induction l as [|b l IH]; intros F; [cbn; lia|].
  inversion F as [|? ? Hb Fl]; subst. specialize (IH Fl). unfold byte_ok in Hb.
  unfold le_val in *. cbn [fold_right]. rewrite Zlength_cons, Z.pow_succ_r by apply Zlength_nonneg. nia.
Qed.

Lemma bt_le_val_inj l1 : forall l2, Forall byte_ok l1 -> Forall byte_ok l2 -> Zlength l1 = Zlength l2 ->
  le_val l1 = le_val l2 -> l1 = l2.
Proof.
  induction l1 as [|b1 l1 IH]; intros [|b2 l2] F1 F2 L E; try reflexivity;
    try (rewrite ?Zlength_cons, ?Zlength_nil in L;
         match type of L with context [Zlength ?r] => pose proof (Zlength_nonneg r) end; lia).
  inversion F1 as [|? ? H1 G1]; inversion F2 as [|? ? H2 G2]; subst. unfold byte_ok in *.
  rewrite !Zlength_cons in L. unfold le_val in E. cbn [fold_right] in E. fold (le_val l1) (le_val l2) in E.
  pose proof (bt_le_val_range l1 G1). pose proof (bt_le_val_range l2 G2).
  assert (b1 = b2 /\ le_val l1 = le_val l2) as [-> E2] by lia. f_equal. apply IH; auto; lia.
Qed.

Lemma bt_len4 (l: list Z) : Zlength l = 4 -> exists b0 b1 b2 b3, l = [b0; b1; b2; b3].
Proof.
  intros L. destruct l as [|b0 [|b1 [|b2 [|b3 [|b4 r]]]]]; rewrite ?Zlength_cons, ?Zlength_nil in L;
    try (pose proof (Zlength_nonneg r)); try lia. eauto.
Qed.

Lemma bt_swap_inj l1 l2 : Forall byte_ok l1 -> Forall byte_ok l2 -> Zlength l1 = 4 -> Zlength l2 = 4 ->
  swap32 (le_val l1) = swap32 (le_val l2) -> l1 = l2.
Proof.
  intros F1 F2 L1 L2 E. destruct (bt_len4 l1 L1) as (a0 & a1 & a2 & a3 & ->).
  destruct (bt_len4 l2 L2) as (b0 & b1 & b2 & b3 & ->).
  repeat match goal with H: Forall _ (_ :: _) |- _ => inversion H; subst; clear H end. unfold byte_ok in *.
  unfold le_val in E. cbn [fold_right] in E.
  rewrite !Zlib.proof.rfc1951.DecTrl.trl_swap in E by lia.
  assert (a0 = b0 /\ a1 = b1 /\ a2 = b2 /\ a3 = b3) as (-> & -> & -> & ->) by lia. reflexivity.
Qed.

Lemma bt_le_bytes_ok v n : Forall byte_ok (le_bytes v n).
Proof. apply Zlib.proof.rfc1951.DecTrl.trl_le_bytes_ok. Qed.
Lemma bt_be_bytes_ok v n : Forall byte_ok (be_bytes v n).
Proof. apply Zlib.proof.rfc1951.DecTrl.trl_be_bytes_ok. Qed.

Lemma bt_bytes_ok l : bytes_ok l -> Forall byte_ok l.
Proof. intros F. eapply Forall_impl; [|exact F]. intros a H. unfold byte_ok. cbv beta in H. change compcert.lib.Integers.Byte.max_unsigned with 255 in H. lia. Qed.

Lemma bt_sub_bytes l a b : Forall byte_ok l -> Forall byte_ok (sublist a b l).
Proof.
  intros F. apply Forall_forall. intros x Hx. apply sublist_In in Hx. rewrite Forall_forall in F. auto.
Qed.

(* a 4-byte big-endian value read little-endian and swapped is the value *)
Lemma bt_swap_be l v : Forall byte_ok l -> Zlength l = 4 -> 0 <= v < 2 ^ 32 -> swap32 (le_val l) = v -> l = be_bytes v 4.
Proof.
  intros F L R E. apply bt_swap_inj; [exact F | apply bt_be_bytes_ok | exact L
    | apply Zlib.proof.rfc1951.DecTrl.trl_be_bytes_len; lia |].
  rewrite E, bt_le_val_trl, Zlib.proof.rfc1951.DecTrl.trl_be4_swap; auto.
Qed.

(* a 4-byte little-endian value *)
Lemma bt_le_eq l v : Forall byte_ok l -> Zlength l = 4 -> 0 <= v < 2 ^ 32 -> le_val l = v -> l = le_bytes v 4.
Proof.
  intros F L R E. apply bt_le_val_inj; [exact F | apply bt_le_bytes_ok
    | rewrite Zlib.proof.rfc1951.DecTrl.trl_le_bytes_len; lia |].
  rewrite E, bt_le_val_trl, Zlib.proof.rfc1951.DecTrl.trl_le4_val by lia. rewrite Z.mod_small; lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The stream's trailer                                                                           *)

Lemma bt_full G : bad_ctx G -> data (dc_hist G) (dc_bs G) = full G /\ dc_hist G = [].
Proof.
  intros (_ & Hh & _). split; [|exact Hh]. unfold data, full. rewrite Hh, Zlength_nil. apply sublist_same; lia.
Qed.

Lemma bt_produced G x : bad_ctx G -> produced G x = x.
Proof. intros C. unfold produced. rewrite (proj2 (bt_full G C)), Zlength_nil. apply sublist_same; lia. Qed.

Lemma bt_full_bytes G : bad_ctx G -> Forall byte_ok (full G).
Proof.
  intros ((Hs & _) & _). destruct Hs as (_ & _ & _ & _ & Hh & Hb). unfold full.
  eapply Zlib.proof.rfc1951.DecTrl.trl_blocks_bytes; eauto.
Qed.

Lemma bt_tail4 (X Y: list Z) : Zlength Y = 4 ->
  0 <= Zlength (X ++ Y) - 4 /\ sublist (Zlength (X ++ Y) - 4) (Zlength (X ++ Y)) (X ++ Y) = Y.
Proof.
  intros L. pose proof (Zlength_nonneg X). rewrite Zlength_app. split; [lia|].
  rewrite sublist_app2 by lia. replace (Zlength X + Zlength Y - 4 - Zlength X) with 0 by lia.
  replace (Zlength X + Zlength Y - Zlength X) with (Zlength Y) by lia. apply sublist_same; lia.
Qed.

Lemma bt_tail8 (X Y W: list Z) : Zlength Y = 4 -> Zlength W = 4 ->
  0 <= Zlength (X ++ Y ++ W) - 8 /\
  sublist (Zlength (X ++ Y ++ W) - 8) (Zlength (X ++ Y ++ W) - 8 + 4) (X ++ Y ++ W) = Y /\
  sublist (Zlength (X ++ Y ++ W) - 8 + 4) (Zlength (X ++ Y ++ W) - 8 + 8) (X ++ Y ++ W) = W.
Proof.
  intros L1 L2. pose proof (Zlength_nonneg X). rewrite !Zlength_app. split; [lia|].
  split.
  - rewrite sublist_app2 by lia. rewrite sublist_app1 by lia. replace (Zlength X + (Zlength Y + Zlength W) - 8 - Zlength X) with 0 by lia.
    replace (Zlength X + (Zlength Y + Zlength W) - 8 + 4 - Zlength X) with (Zlength Y) by lia.
    apply sublist_same; lia.
  - rewrite sublist_app2 by lia. rewrite sublist_app2 by lia.
    replace (Zlength X + (Zlength Y + Zlength W) - 8 + 4 - Zlength X - Zlength Y) with 0 by lia.
    replace (Zlength X + (Zlength Y + Zlength W) - 8 + 8 - Zlength X - Zlength Y) with (Zlength W) by lia.
    apply sublist_same; lia.
Qed.

(* zlib: the trailer is the Adler-32 of the data, big-endian *)
Lemma bt_trl_zlib G wb fl did : bad_ctx G -> dc_w G = WZlib wb fl did ->
  0 <= tpos G /\ tpos G + 4 = slen G /\
  sublist (tpos G) (slen G) (dc_src G) = be_bytes (ref_adler32 1 (full G)) 4.
Proof.
  intros C W. destruct (bt_full G C) as [D Hh]. pose proof C as (_ & _ & _ & Hd & Hs).
  specialize (Hd _ _ _ W). subst did. unfold tpos, slen, trl_len. rewrite Hs, W. clear Hs.
  unfold stream_bytes. cbv zeta. rewrite D. cbn [app].
  rewrite app_assoc.
  destruct (bt_tail4 (zlib_hdr wb fl false ++ deflate_bytes (dc_bs G)) (be_bytes (ref_adler32 1 (full G)) 4))
    as [A B]; [apply Zlib.proof.rfc1951.DecTrl.trl_be_bytes_len; lia|].
  split; [exact A|]. split; [lia|]. exact B.
Qed.

(* gzip: the trailer is the CRC-32 of the data and its length mod 2^32, little-endian *)
Lemma bt_trl_gzip G h : bad_ctx G -> dc_w G = WGzip h ->
  0 <= tpos G /\ tpos G + 8 = slen G /\
  sublist (tpos G) (tpos G + 4) (dc_src G) = le_bytes (ref_crc32 0 (full G)) 4 /\
  sublist (tpos G + 4) (tpos G + 8) (dc_src G) = le_bytes (Zlength (full G) mod 2 ^ 32) 4.
Proof.
  intros C W. destruct (bt_full G C) as [D Hh]. pose proof C as (_ & _ & _ & _ & Hs).
  unfold tpos, slen, trl_len. rewrite Hs, W. clear Hs.
  unfold stream_bytes. cbv zeta. rewrite D. rewrite app_assoc.
  destruct (bt_tail8 (gz_bytes h ++ deflate_bytes (dc_bs G)) (le_bytes (ref_crc32 0 (full G)) 4)
              (le_bytes (Zlength (full G) mod 2 ^ 32) 4)) as (A & B & B2);
    [apply Zlib.proof.rfc1951.DecTrl.trl_le_bytes_len; lia | apply Zlib.proof.rfc1951.DecTrl.trl_le_bytes_len; lia |].
  split; [exact A|]. split; [lia|].
  split; [exact B | exact B2].
Qed.

(* the wrappers covered: zlib or gzip *)
Lemma bt_wrapper G : bad_ctx G -> (exists wb fl did, dc_w G = WZlib wb fl did) \/ (exists h, dc_w G = WGzip h).
Proof.
  intros (_ & _ & Wr & _). unfold wrapped in Wr. destruct (dc_w G) as [|wb fl did|h]; [discriminate| |]; eauto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The fixed fields                                                                               *)

Lemma bt_wb_cases wb : 8 <= wb <= 15 ->
  wb = 8 \/ wb = 9 \/ wb = 10 \/ wb = 11 \/ wb = 12 \/ wb = 13 \/ wb = 14 \/ wb = 15.
Proof. lia. Qed.

(* the wrapper is checked: wrap is 5, 6 or 7 *)
Lemma bt_wrap G s : bad_ctx G -> glob_ok G s -> Z.land (i_wrap s) 4 <> 0.
Proof.
  intros (D & _ & Wr & _) ((wb0 & R & _) & _). destruct D as ((Hwb & Hw & Hz & _) & Ha & _).
  unfold accepts, wrapped in *. remember (i_wrap s) as w eqn:Ew. clear Ew.
  destruct (dc_w G) as [|wb fl did|h]; [discriminate| |];
    destruct (bt_wb_cases _ Hwb) as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E in *;
    repeat match goal with H: _ \/ _ |- _ => destruct H as [H|H] end; rewrite Ha in R;
    cbv in R; inversion R; subst; cbv; congruence.
Qed.

Lemma bt_is_bytes l : Forall byte_ok l -> Zlib.proof.adler32.Bytes.is_bytes l.
Proof.
  intros F. eapply Forall_impl; [|exact F]. intros a H. unfold byte_ok in H.
  change compcert.lib.Integers.Byte.max_unsigned with 255. lia.
Qed.

(* UPDATE_CHECK continues the check value of the data *)
Lemma bt_upd G s d ow : bad_ctx G -> glob_ok G s -> i_mode s <> HEAD -> i_mode s <> FLAGS ->
  Forall byte_ok d -> update_check (i_flags s) (chkv G d) ow = chkv G (d ++ ow).
Proof.
  intros (_ & _ & WR & _) (_ & _ & _ & FL) N1 N2 B. specialize (FL WR N1 N2).
  unfold chkv, update_check, wrapped in *. destruct (dc_w G) as [| wb fl did | h]; [discriminate| |].
  - rewrite FL, Z.eqb_refl.
    assert (V: Zlib.proof.adler32.Model.adler_valid 1).
    { unfold Zlib.proof.adler32.Model.adler_valid. vm_compute. repeat split; discriminate. }
    rewrite Zlib.proof.adler32.Model.adler32_z_val_ref
      by (apply Zlib.proof.adler32.Model.ref_adler32_valid; exact V).
    apply Zlib.proof.adler32.Model.ref_adler32_app. exact V.
  - rewrite FL. destruct (Z.eqb_spec (8 + 256 * gz_flg h) 0); [unfold gz_flg in *;
      destruct (gz_text h), (gz_hcrc h), (gz_extra h), (gz_name h), (gz_comment h); lia|].
    apply Zlib.proof.crc32.Combine.ref_crc32_app. apply bt_is_bytes. exact B.
Qed.

Lemma bt_glob G s s' : glob_ok G s -> i_wrap s' = i_wrap s -> i_head s' = i_head s -> i_mode s' = i_mode s ->
  i_wbits s' = i_wbits s -> i_flags s' = i_flags s -> glob_ok G s'.
Proof. intros Hg E1 E2 E3 E4 E5. unfold glob_ok in *. rewrite E1, E2, E3, E4, E5. exact Hg. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* NEEDBITS(32) over trailer bytes                                                                *)

(* the bit buffer holds bytes [b, b + k) of src (k <= 4); NEEDBITS(32) reads bytes up to b + 4 or to the end
   of the input (then leave = 1) *)
Lemma bt_nb n : forall m src pos b k,
  Forall byte_ok src -> 0 <= pos -> pos + Zlength (m_inp m) <= Zlength src ->
  m_inp m = sublist pos (pos + Zlength (m_inp m)) src ->
  0 <= m_nx m <= Zlength (m_inp m) -> 0 <= b -> 0 <= k <= 4 -> pos + m_nx m = b + k ->
  m_bits m = 8 * k -> m_hold m = le_val (sublist b (b + k) src) -> m_leave m = 0 ->
  4 <= k + Z.of_nat n ->
  exists k', k <= k' <= 4 /\ (k' < 4 -> b + k' - pos = Zlength (m_inp m)) /\ b + k' - pos <= Zlength (m_inp m) /\
    needbits_f n 32 m = Zlib.proof.rfc1951.DecTrl.trl_nb m (b + k' - pos) (le_val (sublist b (b + k') src)) (8 * k')
                          (if k' =? 4 then 0 else 1).
Proof.
  induction n as [|n IH]; intros m src pos b k Fs Hp Hl Hi Hn Hb Hk Hx Hbits Hh Hv Hf.
  - exists 4. assert (k = 4) by lia. subst k. split; [lia|]. split; [lia|]. split; [lia|].
    cbn [needbits_f]. destruct m; unfold Zlib.proof.rfc1951.DecTrl.trl_nb, set_m_leave, set_m_bits, set_m_hold, set_m_nx; cbn in *. subst. f_equal; lia.
  - cbn [needbits_f]. destruct (m_bits m <? 32) eqn:E1.
    2:{ apply Z.ltb_ge in E1. exists 4. assert (k = 4) by lia. subst k. split; [lia|]. split; [lia|]. split; [lia|].
        destruct m; unfold Zlib.proof.rfc1951.DecTrl.trl_nb, set_m_leave, set_m_bits, set_m_hold, set_m_nx; cbn in *. subst. f_equal; lia. }
    apply Z.ltb_lt in E1. unfold m_have. destruct (Zlength (m_inp m) - m_nx m =? 0) eqn:E2.
    + apply Z.eqb_eq in E2. exists k. split; [lia|]. split; [lia|]. split; [lia|].
      rewrite (proj2 (Z.eqb_neq k 4)) by lia.
      destruct m; unfold Zlib.proof.rfc1951.DecTrl.trl_nb, set_leave, set_m_leave, set_m_bits, set_m_hold, set_m_nx; cbn in *. subst. f_equal; lia.
    + apply Z.eqb_neq in E2.
      assert (Bz: Znth (m_nx m) (m_inp m) = Znth (b + k) src).
      { rewrite Hi at 1. rewrite Znth_sublist by lia. f_equal. lia. }
      assert (S1: sublist b (b + (k + 1)) src = sublist b (b + k) src ++ [Znth (b + k) src]).
      { rewrite Z.add_assoc. apply sublist_last_1; lia. }
      assert (Lk: Zlength (sublist b (b + k) src) = k) by (rewrite Zlength_sublist by lia; lia).
      assert (P1: m_inp (pull m) = m_inp m) by reflexivity.
      assert (P2: m_nx (pull m) = m_nx m + 1) by reflexivity.
      assert (P3: m_bits (pull m) = 8 * (k + 1))
        by (unfold pull; cbn [m_bits set_m_bits]; unfold u32; rewrite Hbits, Z.mod_small; lia).
      assert (P4: m_hold (pull m) = le_val (sublist b (b + (k + 1)) src)).
      { assert (V: le_val (sublist b (b + (k + 1)) src) = le_val (sublist b (b + k) src) + Znth (b + k) src * 256 ^ k)
          by (rewrite S1, bt_le_val_app, Lk; reflexivity).
        pose proof (bt_le_val_range (sublist b (b + (k + 1)) src) (bt_sub_bytes _ _ _ Fs)) as R.
        rewrite Zlength_sublist in R by lia.
        assert (256 ^ (b + (k + 1) - b) <= 256 ^ 4) by (apply Z.pow_le_mono_r; lia).
        unfold pull; cbn [m_hold set_m_bits set_m_hold set_m_nx]. rewrite Bz, Hh, Hbits.
        rewrite Z.pow_mul_r by lia. change (2 ^ 8) with 256. rewrite <- V. unfold u64. apply Z.mod_small. lia. }
      assert (P5: m_leave (pull m) = 0) by exact Hv.
      destruct (IH (pull m) src pos b (k + 1)) as (k' & R & L & L' & E); try rewrite P1; try rewrite P2; auto; try lia.
      exists k'. split; [lia|]. split; [exact L|]. split; [exact L'|]. rewrite E. unfold pull. destruct m; reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The end of the call                                                                            *)

Ltac bt_uw_tac := unfold updatewindow; cbv zeta;
  repeat (destruct (_ =? _) || destruct (_ <=? _) || destruct (_ <? _)); reflexivity.
Lemma bt_uw_mode s d : i_mode (updatewindow s d) = i_mode s.     Proof. bt_uw_tac. Qed.
Lemma bt_uw_wrap s d : i_wrap (updatewindow s d) = i_wrap s.     Proof. bt_uw_tac. Qed.
Lemma bt_uw_head s d : i_head (updatewindow s d) = i_head s.     Proof. bt_uw_tac. Qed.
Lemma bt_uw_wbits s d : i_wbits (updatewindow s d) = i_wbits s.  Proof. bt_uw_tac. Qed.
Lemma bt_uw_flags s d : i_flags (updatewindow s d) = i_flags s.  Proof. bt_uw_tac. Qed.
Lemma bt_uw_hold s d : i_hold (updatewindow s d) = i_hold s.     Proof. bt_uw_tac. Qed.
Lemma bt_uw_bits s d : i_bits (updatewindow s d) = i_bits s.     Proof. bt_uw_tac. Qed.
Lemma bt_uw_total s d : i_total (updatewindow s d) = i_total s.  Proof. bt_uw_tac. Qed.
Lemma bt_uw_check s d : i_check (updatewindow s d) = i_check s.  Proof. bt_uw_tac. Qed.

Ltac bt_lf_tac flush m :=
  unfold leave_fin, m_left; cbv zeta; destruct (leave_ok flush m); cbn -[updatewindow u32 u64 update_check];
  rewrite ?bt_uw_mode, ?bt_uw_wrap, ?bt_uw_head, ?bt_uw_wbits, ?bt_uw_flags, ?bt_uw_hold, ?bt_uw_bits,
    ?bt_uw_total, ?bt_uw_check; cbn -[updatewindow u32 u64 update_check];
  destruct (negb (Z.land _ 4 =? 0) && negb (_ =? 0));
  cbn -[updatewindow u32 u64 update_check];
  rewrite ?bt_uw_mode, ?bt_uw_wrap, ?bt_uw_head, ?bt_uw_wbits, ?bt_uw_flags, ?bt_uw_hold, ?bt_uw_bits,
    ?bt_uw_total, ?bt_uw_check; reflexivity.

Lemma bt_lf_snx flush m : m_snx (r_m (leave_fin flush m)) = m_nx m.
Proof. unfold leave_fin. cbv zeta. destruct (leave_ok flush m); destruct (negb (Z.land _ 4 =? 0) && negb (_ =? 0)); reflexivity. Qed.
Lemma bt_lf_sow flush m : m_sow (r_m (leave_fin flush m)) = Zlength (m_ow m).
Proof. unfold leave_fin. cbv zeta. destruct (leave_ok flush m); destruct (negb (Z.land _ 4 =? 0) && negb (_ =? 0)); reflexivity. Qed.
Lemma bt_lf_aout flush m : m_aout (r_m (leave_fin flush m)) = m_aout m.
Proof. unfold leave_fin. cbv zeta. destruct (leave_ok flush m); destruct (negb (Z.land _ 4 =? 0) && negb (_ =? 0)); reflexivity. Qed.
Lemma bt_lf_ow flush m : m_ow (r_m (leave_fin flush m)) = m_ow m.
Proof. unfold leave_fin. cbv zeta. destruct (leave_ok flush m); destruct (negb (Z.land _ 4 =? 0) && negb (_ =? 0)); reflexivity. Qed.
Lemma bt_lf_inp flush m : m_inp (r_m (leave_fin flush m)) = m_inp m.
Proof. unfold leave_fin. cbv zeta. destruct (leave_ok flush m); destruct (negb (Z.land _ 4 =? 0) && negb (_ =? 0)); reflexivity. Qed.
Lemma bt_lf_mode flush m : i_mode (m_s (r_m (leave_fin flush m))) = m_mode m.
Proof. unfold leave_fin. cbv zeta. destruct (leave_ok flush m); destruct (negb (Z.land _ 4 =? 0) && negb (_ =? 0));
  first [reflexivity | exact (bt_uw_mode _ _)]. Qed.
Lemma bt_lf_wrap flush m : i_wrap (m_s (r_m (leave_fin flush m))) = i_wrap (m_s m).
Proof. unfold leave_fin. cbv zeta. destruct (leave_ok flush m); destruct (negb (Z.land _ 4 =? 0) && negb (_ =? 0));
  first [reflexivity | exact (bt_uw_wrap _ _)]. Qed.
Lemma bt_lf_head flush m : i_head (m_s (r_m (leave_fin flush m))) = i_head (m_s m).
Proof. unfold leave_fin. cbv zeta. destruct (leave_ok flush m); destruct (negb (Z.land _ 4 =? 0) && negb (_ =? 0));
  first [reflexivity | exact (bt_uw_head _ _)]. Qed.
Lemma bt_lf_wbits flush m : i_wbits (m_s (r_m (leave_fin flush m))) = i_wbits (m_s m).
Proof. unfold leave_fin. cbv zeta. destruct (leave_ok flush m); destruct (negb (Z.land _ 4 =? 0) && negb (_ =? 0));
  first [reflexivity | exact (bt_uw_wbits _ _)]. Qed.
Lemma bt_lf_flags flush m : i_flags (m_s (r_m (leave_fin flush m))) = i_flags (m_s m).
Proof. unfold leave_fin. cbv zeta. destruct (leave_ok flush m); destruct (negb (Z.land _ 4 =? 0) && negb (_ =? 0));
  first [reflexivity | exact (bt_uw_flags _ _)]. Qed.
Lemma bt_lf_hold flush m : i_hold (m_s (r_m (leave_fin flush m))) = m_hold m.
Proof. unfold leave_fin. cbv zeta. destruct (leave_ok flush m); destruct (negb (Z.land _ 4 =? 0) && negb (_ =? 0));
  first [reflexivity | exact (bt_uw_hold _ _)]. Qed.
Lemma bt_lf_bits flush m : i_bits (m_s (r_m (leave_fin flush m))) = m_bits m.
Proof. unfold leave_fin. cbv zeta. destruct (leave_ok flush m); destruct (negb (Z.land _ 4 =? 0) && negb (_ =? 0));
  first [reflexivity | exact (bt_uw_bits _ _)]. Qed.
Lemma bt_lf_total flush m : i_total (m_s (r_m (leave_fin flush m))) = u64 (i_total (m_s m) + u32 (m_out m - m_left m)).
Proof. bt_lf_tac flush m. Qed.
Lemma bt_lf_check flush m : i_check (m_s (r_m (leave_fin flush m))) =
    (if negb (Z.land (i_wrap (m_s m)) 4 =? 0) && negb (u32 (m_out m - m_left m) =? 0)
     then update_check (i_flags (m_s m)) (i_check (m_s m))
            (sublist (Zlength (m_ow m) - u32 (m_out m - m_left m)) (Zlength (m_ow m)) (m_ow m))
     else i_check (m_s m)).
Proof. bt_lf_tac flush m. Qed.

(* inf_leave when the window update succeeds: what the trailer modes need *)
Lemma bt_lf flush m : let out := u32 (m_out m - m_left m) in
  m_snx (r_m (leave_fin flush m)) = m_nx m /\ m_sow (r_m (leave_fin flush m)) = Zlength (m_ow m) /\
  m_aout (r_m (leave_fin flush m)) = m_aout m /\
  m_ow (r_m (leave_fin flush m)) = m_ow m /\ m_inp (r_m (leave_fin flush m)) = m_inp m /\
  i_mode (m_s (r_m (leave_fin flush m))) = m_mode m /\ i_wrap (m_s (r_m (leave_fin flush m))) = i_wrap (m_s m) /\
  i_head (m_s (r_m (leave_fin flush m))) = i_head (m_s m) /\
  i_wbits (m_s (r_m (leave_fin flush m))) = i_wbits (m_s m) /\
  i_flags (m_s (r_m (leave_fin flush m))) = i_flags (m_s m) /\
  i_hold (m_s (r_m (leave_fin flush m))) = m_hold m /\ i_bits (m_s (r_m (leave_fin flush m))) = m_bits m /\
  i_total (m_s (r_m (leave_fin flush m))) = u64 (i_total (m_s m) + out) /\
  i_check (m_s (r_m (leave_fin flush m))) =
    (if negb (Z.land (i_wrap (m_s m)) 4 =? 0) && negb (out =? 0)
     then update_check (i_flags (m_s m)) (i_check (m_s m)) (sublist (Zlength (m_ow m) - out) (Zlength (m_ow m)) (m_ow m))
     else i_check (m_s m)).
Proof.
  cbv zeta. exact (conj (bt_lf_snx _ _) (conj (bt_lf_sow _ _) (conj (bt_lf_aout _ _) (conj (bt_lf_ow _ _) (conj (bt_lf_inp _ _) (conj (bt_lf_mode _ _) (conj (bt_lf_wrap _ _) (conj (bt_lf_head _ _) (conj (bt_lf_wbits _ _) (conj (bt_lf_flags _ _) (conj (bt_lf_hold _ _) (conj (bt_lf_bits _ _) (conj (bt_lf_total _ _) (bt_lf_check _ _)))))))))))))).
Qed.

Lemma bt_lf_ret flush m :
  (m_ret m <> Z_OK -> r_ret (leave_fin flush m) = m_ret m) /\
  (m_ret m = Z_OK -> r_ret (leave_fin flush m) = Z_OK \/ r_ret (leave_fin flush m) = Z_BUF_ERROR).
Proof.
  assert (E: exists c, r_ret (leave_fin flush m) = if c && (m_ret m =? Z_OK) then Z_BUF_ERROR else m_ret m).
  { unfold leave_fin. cbv zeta. destruct (leave_ok flush m); destruct (negb (Z.land _ 4 =? 0) && _);
      cbn -[updatewindow u32 u64 update_check]; eexists; reflexivity. }
  destruct E as (c & ->). split; intros H.
  - rewrite (proj2 (Z.eqb_neq _ _) H), andb_false_r. reflexivity.
  - destruct (c && (m_ret m =? Z_OK)); auto.
Qed.

(* the loop left at once *)
Lemma bt_fin_leave flush mC m' o res : stepf2 flush lenfix_list distfix_list mC = IBrk m' -> m_leave m' = 1 ->
  loop2 flush lenfix_list distfix_list mC o ->
  match o with IRet r m => res = Res r m None | IBrk m => inf_leave flush m res end ->
  r_ret res <> Z_MEM_ERROR -> res = leave_fin flush m'.
Proof.
  intros E Lv LP RS NM. inversion LP as [? ? ? E1 | ? ? E1 L1 | ? ? ? E1 L1 LP1]; subst; rewrite E in E1.
  - discriminate.
  - injection E1 as <-. inversion RS; subst; [cbn in NM; congruence | reflexivity].
  - injection E1 as <-. congruence.
Qed.

(* the mode became BAD: c_BAD returns Z_DATA_ERROR *)
Lemma bt_fin_bad flush mC m' o res : stepf2 flush lenfix_list distfix_list mC = IBrk m' -> m_leave m' = 0 ->
  m_mode m' = BAD -> loop2 flush lenfix_list distfix_list mC o ->
  match o with IRet r m => res = Res r m None | IBrk m => inf_leave flush m res end ->
  r_ret res <> Z_MEM_ERROR -> res = leave_fin flush (set_leave (set_m_ret m' Z_DATA_ERROR)).
Proof.
  intros E Lv Md LP RS NM. inversion LP as [? ? ? E1 | ? ? E1 L1 | ? ? ? E1 L1 LP1]; subst; rewrite E in E1.
  - discriminate.
  - injection E1 as <-. congruence.
  - injection E1 as <-. eapply bt_fin_leave; [| | exact LP1 | exact RS | exact NM].
    + rewrite stepf2_BAD by exact Md. reflexivity.
    + reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The trailer modes                                                                              *)

Ltac bt_md := unfold m_mode, CHECK, LENGTH, HEAD, FLAGS, BAD, TYPE in *; lia.

Lemma bt_glob2 G s s' : glob_ok G s -> i_mode s <> HEAD -> i_mode s <> FLAGS -> i_mode s' <> HEAD -> i_mode s' <> FLAGS ->
  i_wrap s' = i_wrap s -> i_head s' = i_head s -> i_wbits s' = i_wbits s -> i_flags s' = i_flags s -> glob_ok G s'.
Proof.
  intros ((wb0 & R & _) & H2 & H3 & H4) N1 N2 N1' N2' E1 E2 E4 E5. unfold glob_ok. rewrite E1, E2, E4, E5.
  split; [exists wb0; split; [exact R | intros; contradiction]|]. split; [exact H2|].
  split; [intros; apply H3; exact N1|]. intros W _ _. apply H4; auto.
Qed.

(* the check value after CHECK counted the call's output ow: the check of all the data *)
Lemma bt_chk G s ob ow : bad_ctx G -> glob_ok G s -> i_mode s <> HEAD -> i_mode s <> FLAGS ->
  ob ++ ow = full G -> i_check s = chkv G ob ->
  (if negb (Z.land (i_wrap s) 4 =? 0) && negb (Zlength ow =? 0)
   then update_check (i_flags s) (i_check s) (sublist (Zlength ow - Zlength ow) (Zlength ow) ow)
   else i_check s) = chkv G (full G).
Proof.
  intros CT Hg N1 N2 Eo Ck. rewrite <- Eo. destruct (Zlength ow =? 0) eqn:Ez.
  - apply Z.eqb_eq, Zlength_nil_inv in Ez. subst ow. rewrite andb_false_r, app_nil_r. exact Ck.
  - rewrite andb_true_r.
    replace (negb (Z.land (i_wrap s) 4 =? 0)) with true
      by (symmetry; apply negb_true_iff, Z.eqb_neq; exact (bt_wrap G s CT Hg)).
    rewrite Z.sub_diag, sublist_same by lia. rewrite Ck. apply bt_upd; auto.
    pose proof (bt_full_bytes G CT) as F. rewrite <- Eo in F. apply Forall_app in F. apply F.
Qed.

Lemma bt_total (ob ow: list Z) : u64 (Zlength ob mod 2 ^ 64 + Zlength ow) = Zlength (ob ++ ow) mod 2 ^ 64.
Proof. unfold u64. rewrite Zlength_app, Zplus_mod_idemp_l. reflexivity. Qed.

(* the outcome of the rest of the call, as bad_trl_call states it *)
Definition bt_concl (G: dctx) (src: list Z) (pos: Z) (inp ob: list Z) (aout: Z) (ow: list Z) (res: result) : Prop :=
  let m := r_m res in
  0 <= m_snx m <= Zlength inp /\ m_sow m = Zlength (m_ow m) /\ m_aout m = aout /\ m_ow m = ow /\
  m_inp m = inp /\
  (r_ret res = Z_DATA_ERROR \/
   ((r_ret res = Z_OK \/ r_ret res = Z_BUF_ERROR) /\ pc_state G src (pos + m_snx m) (ob ++ m_ow m) (m_s m))).

(* the mode became BAD: the call returns Z_DATA_ERROR *)
Lemma bt_concl_bad G src pos inp ob flush N e :
  m_inp N = inp -> 0 <= m_nx N <= Zlength inp ->
  bt_concl G src pos inp ob (m_aout N) (m_ow N)
    (leave_fin flush (set_leave (set_m_ret (set_bad N e) Z_DATA_ERROR))).
Proof.
  intros Hi Hn. unfold bt_concl. cbv zeta.
  rewrite bt_lf_snx, bt_lf_sow, bt_lf_aout, bt_lf_ow, bt_lf_inp.
  refine (conj Hn (conj eq_refl (conj eq_refl (conj eq_refl (conj Hi _))))).
  left. rewrite (proj1 (bt_lf_ret flush _)); [reflexivity | cbv; discriminate].
Qed.

Lemma bt_setbad_leave N e : m_leave (set_bad N e) = m_leave N.
Proof. reflexivity. Qed.
Lemma bt_setbad_mode N e : m_mode (set_bad N e) = BAD.
Proof. reflexivity. Qed.

Lemma bt_sub0 (l: list Z) a : le_val (sublist a (a + 0) l) = 0.
Proof. rewrite Z.add_0_r, sublist_nil. reflexivity. Qed.

Lemma bt_src_tail G src : bad_src G src -> dc_src G = stream_bytes (dc_w G) (dc_hist G) (dc_bs G) ->
  0 <= tpos G -> tpos G + 4 <= slen G ->
  sublist (tpos G) (tpos G + 4) src = sublist (tpos G) (tpos G + 4) (dc_src G) ->
  sublist (tpos G + 4) (slen G) src = sublist (tpos G + 4) (slen G) (dc_src G) -> False.
Proof.
  intros (Ls & _ & _ & Nd) Hs T0 T4 E1 E2. apply Nd.
  assert (Lo: Zlength (dc_src G) = slen G) by (rewrite Hs; reflexivity).
  rewrite (sublist_split (tpos G) (tpos G + 4) (slen G) src) by lia.
  rewrite (sublist_split (tpos G) (tpos G + 4) (slen G) (dc_src G)) by lia.
  rewrite E1, E2. reflexivity.
Qed.

(* LENGTH (gzip): ISIZE compared with the total *)
Lemma bt_length G src pos inp ob flush mC M o res k :
  bad_ctx G -> bad_src G src ->
  m_mode M = LENGTH -> glob_ok G (m_s M) -> (exists h, dc_w G = WGzip h) ->
  m_inp M = inp -> 0 <= pos -> pos + Zlength inp <= Zlength src -> inp = sublist pos (pos + Zlength inp) src ->
  0 <= m_nx M <= Zlength inp -> ob ++ m_ow M = full G -> m_out M = m_left M -> m_ret M = Z_OK -> m_leave M = 0 ->
  i_total (m_s M) = Zlength (full G) mod 2 ^ 64 ->
  sublist (tpos G) (tpos G + 4) src = sublist (tpos G) (tpos G + 4) (dc_src G) ->
  0 <= k < 4 -> pos + m_nx M = tpos G + 4 + k -> m_bits M = 8 * k ->
  m_hold M = le_val (sublist (tpos G + 4) (tpos G + 4 + k) src) ->
  stepf2 flush lenfix_list distfix_list mC = c_LENGTH M ->
  loop2 flush lenfix_list distfix_list mC o ->
  match o with IRet r m => res = Res r m None | IBrk m => inf_leave flush m res end ->
  r_ret res <> Z_MEM_ERROR ->
  bt_concl G src pos inp ob (m_aout M) (m_ow M) res.
Proof.
  intros CT BS Hm Hg (h & W) Hi Hp Hl Hs Hn Eo Hout Hr Hv Ht S4 Hk Hx Hb Hh E LP RS NM.
  pose proof BS as (Ls & Bs & _). apply bt_bytes_ok in Bs.
  destruct (bt_trl_gzip G h CT W) as (T0 & T8 & C4 & L4).
  pose proof (bt_wrap G _ CT Hg) as W4.
  assert (Hw0: i_wrap (m_s M) <> 0) by (intros Z0; rewrite Z0 in W4; apply W4; reflexivity).
  destruct (Zlib.proof.rfc1951.DecTrl.trl_flags G _ Hg) as [_ Hfl]; try bt_md.
  specialize (Hfl h W).
  unfold c_LENGTH in E. rewrite (proj2 (Z.eqb_neq _ _) Hw0), (proj2 (Z.eqb_neq _ _) Hfl) in E.
  cbn [negb andb] in E. cbv zeta in E. unfold needbits in E.
  destruct (bt_nb 4 M src pos (tpos G + 4) k Bs Hp) as (k' & R & Lk & Lk' & En);
    try rewrite Hi; try lia; auto.
  rewrite En in E. clear En.
  set (N := Zlib.proof.rfc1951.DecTrl.trl_nb M _ _ _ _) in E.
  assert (Ns: m_s N = m_s M) by reflexivity.
  destruct (Z.eq_dec k' 4) as [K4|K4].
  - subst k'. assert (NL: m_leave N = 0) by reflexivity. rewrite NL in E. cbn [Z.eqb] in E.
    rewrite Ns in E. replace (negb (Z.land (i_wrap (m_s M)) 4 =? 0)) with true in E
      by (symmetry; apply negb_true_iff, Z.eqb_neq; exact W4).
    cbn [andb] in E.
    destruct (m_hold N =? i_total (m_s M) mod 2 ^ 32) eqn:Eh.
    + exfalso. apply Z.eqb_eq in Eh. cbn [m_hold N Zlib.proof.rfc1951.DecTrl.trl_nb set_m_leave set_m_bits set_m_hold] in Eh.
      rewrite Ht in Eh. change (2 ^ 64) with (2 ^ 32 * 2 ^ 32) in Eh.
      rewrite Zaux.Zmod_mod_mult in Eh by lia.
      apply bt_le_eq in Eh.
      2: apply bt_sub_bytes, Bs.
      2: rewrite Zlength_sublist by lia; lia.
      2: apply Z.mod_pos_bound; lia.
      apply (bt_src_tail G src BS (proj2 (proj2 (proj2 (proj2 CT)))) T0 ltac:(lia) S4).
      replace (slen G) with (tpos G + 4 + 4) by lia. rewrite Eh. symmetry. rewrite <- L4. f_equal; lia.
    + cbn [negb] in E. eapply bt_fin_bad in E; [| exact NL | apply bt_setbad_mode | exact LP | exact RS | exact NM].
      subst res. change (m_aout M) with (m_aout N). change (m_ow M) with (m_ow N).
      apply bt_concl_bad; [exact Hi | cbn; rewrite Hi in Lk'; lia].
  - assert (NL: m_leave N = 1) by (cbn; rewrite (proj2 (Z.eqb_neq k' 4) K4); reflexivity).
    rewrite NL in E. cbn [Z.eqb Pos.eqb] in E.
    eapply bt_fin_leave in E; [| exact NL | exact LP | exact RS | exact NM]. subst res.
    unfold bt_concl. cbv zeta.
    rewrite bt_lf_snx, bt_lf_sow, bt_lf_aout, bt_lf_ow, bt_lf_inp.
    assert (Nx: m_nx N = tpos G + 4 + k' - pos) by reflexivity.
    refine (conj _ (conj eq_refl (conj eq_refl (conj eq_refl (conj Hi _))))); [rewrite Nx; rewrite Hi in Lk; lia|].
    right. split; [apply (proj2 (bt_lf_ret flush N)); exact Hr|].
    unfold pc_state. split; [exact Eo|]. split.
    + apply (bt_glob G (m_s M)); [exact Hg | rewrite bt_lf_wrap; reflexivity | rewrite bt_lf_head; reflexivity
        | rewrite bt_lf_mode; reflexivity | rewrite bt_lf_wbits; reflexivity | rewrite bt_lf_flags; reflexivity].
    + right. rewrite bt_lf_mode. split; [exact Hm|]. split; [exists h; exact W|]. split.
      * rewrite bt_lf_total, Ns, Ht, bt_produced by exact CT. change (ob ++ m_ow N) with (ob ++ m_ow M). rewrite Eo.
        assert (O0: m_out N - m_left N = 0) by (unfold m_left in *; cbn; lia). rewrite O0.
        unfold u64, u32. rewrite Zmod_0_l, Z.add_0_r, Zmod_mod. reflexivity.
      * split; [exact S4|]. exists k'. rewrite bt_lf_bits, bt_lf_hold, Nx.
        split; [lia|]. split; [lia|]. split; reflexivity.
Qed.

(* CHECK: the Adler-32 (zlib) or CRC-32 (gzip) of all the data compared with the trailer's first four bytes *)
Lemma bt_check G src pos inp ob flush mC o res k :
  bad_ctx G -> bad_src G src -> m_mode mC = CHECK -> glob_ok G (m_s mC) ->
  m_inp mC = inp -> 0 <= pos -> pos + Zlength inp <= Zlength src -> inp = sublist pos (pos + Zlength inp) src ->
  0 <= m_nx mC <= Zlength inp -> m_leave mC = 0 -> m_ret mC = Z_OK -> ob ++ m_ow mC = full G ->
  Zlength (m_ow mC) <= m_aout mC <= 2 ^ 32 - 1 -> m_out mC = m_aout mC ->
  i_check (m_s mC) = chkv G ob -> i_total (m_s mC) = Zlength ob mod 2 ^ 64 ->
  0 <= k < 4 -> pos + m_nx mC = tpos G + k -> m_bits mC = 8 * k ->
  m_hold mC = le_val (sublist (tpos G) (tpos G + k) src) ->
  loop2 flush lenfix_list distfix_list mC o ->
  match o with IRet r m => res = Res r m None | IBrk m => inf_leave flush m res end ->
  r_ret res <> Z_MEM_ERROR ->
  bt_concl G src pos inp ob (m_aout mC) (m_ow mC) res.
Proof.
  intros CT BS Hm Hg Hi Hp Hl Hs Hn Hv Hr Eo Hao Hout Ck Ht Hk Hx Hb Hh LP RS NM.
  pose proof BS as (Ls & Bs & _). apply bt_bytes_ok in Bs.
  assert (T0: 0 <= tpos G /\ tpos G + 4 <= slen G).
  { destruct (bt_wrapper G CT) as [(wb & fl & did & W) | (h & W)].
    - destruct (bt_trl_zlib G wb fl did CT W) as (A & B & _); lia.
    - destruct (bt_trl_gzip G h CT W) as (A & B & _); lia. }
  pose proof (bt_wrap G _ CT Hg) as W4.
  assert (Hw0: i_wrap (m_s mC) <> 0) by (intros Z0; rewrite Z0 in W4; apply W4; reflexivity).
  assert (NH: i_mode (m_s mC) <> HEAD) by bt_md. assert (NF: i_mode (m_s mC) <> FLAGS) by bt_md.
  pose proof (stepf2_CHECK flush lenfix_list distfix_list mC Hm) as E.
  rewrite Zlib.proof.rfc1951.DecTrl.trl_check_eq in E.
  rewrite (proj2 (Z.eqb_neq _ _) Hw0) in E. cbn [negb] in E. cbv zeta in E. unfold needbits in E.
  destruct (bt_nb 4 mC src pos (tpos G) k Bs Hp) as (k' & R & Lk & Lk' & En); try rewrite Hi; try lia; auto.
  rewrite En in E. clear En.
  set (N := Zlib.proof.rfc1951.DecTrl.trl_nb mC _ _ _ _) in E.
  assert (Ns: m_s N = m_s mC) by reflexivity.
  assert (Nx: m_nx N = tpos G + k' - pos) by reflexivity.
  assert (Out: u32 (m_out N - m_left N) = Zlength (m_ow N)).
  { unfold m_left. cbn. rewrite Hout. unfold u32. rewrite Z.mod_small; pose proof (Zlength_nonneg (m_ow mC)); lia. }
  destruct (Z.eq_dec k' 4) as [K4|K4].
  2:{ (* the input ran out *)
    assert (NL: m_leave N = 1) by (cbn; rewrite (proj2 (Z.eqb_neq k' 4) K4); reflexivity).
    rewrite NL in E. cbn [Z.eqb Pos.eqb] in E.
    eapply bt_fin_leave in E; [| exact NL | exact LP | exact RS | exact NM]. subst res.
    unfold bt_concl. cbv zeta.
    rewrite bt_lf_snx, bt_lf_sow, bt_lf_aout, bt_lf_ow, bt_lf_inp.
    refine (conj _ (conj eq_refl (conj eq_refl (conj eq_refl (conj Hi _))))); [rewrite Nx; rewrite Hi in Lk; lia|].
    right. split; [apply (proj2 (bt_lf_ret flush N)); exact Hr|].
    unfold pc_state. split; [exact Eo|]. split.
    + apply (bt_glob G (m_s mC)); [exact Hg | rewrite bt_lf_wrap; reflexivity | rewrite bt_lf_head; reflexivity
        | rewrite bt_lf_mode; reflexivity | rewrite bt_lf_wbits; reflexivity | rewrite bt_lf_flags; reflexivity].
    + left. rewrite bt_lf_mode. split; [exact Hm|].
      rewrite bt_produced by exact CT. change (ob ++ m_ow N) with (ob ++ m_ow mC). rewrite Eo.
      split; [|split].
      * rewrite bt_lf_check, Out, Ns. exact (bt_chk G (m_s mC) ob (m_ow N) CT Hg NH NF Eo Ck).
      * rewrite bt_lf_total, Out, Ns, Ht, bt_total. change (m_ow N) with (m_ow mC). rewrite Eo. reflexivity.
      * exists k'. rewrite bt_lf_bits, bt_lf_hold, Nx. split; [lia|]. split; [lia|]. split; reflexivity. }
  subst k'. assert (NL: m_leave N = 0) by reflexivity. rewrite NL in E. cbn [Z.eqb] in E.
  destruct (Zlib.proof.rfc1951.DecTrl.trl_m5_fields N)
    as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18).
  cbv zeta in F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12, F13, F14, F15, F16, F17, F18.
  rewrite Out in F17, F18. clear F10 F12.
  set (M := Zlib.proof.rfc1951.DecTrl.trl_m5 N) in *.
  assert (Mc: i_check (m_s M) = chkv G (full G)).
  { rewrite F18, Ns. exact (bt_chk G (m_s mC) ob (m_ow N) CT Hg NH NF Eo Ck). }
  assert (Mt: i_total (m_s M) = Zlength (full G) mod 2 ^ 64).
  { rewrite F17, Ns, Ht, bt_total. change (m_ow N) with (m_ow mC). rewrite Eo. reflexivity. }
  assert (Nh: m_hold N = le_val (sublist (tpos G) (tpos G + 4) src)) by reflexivity.
  assert (F6': m_aout M = m_aout mC) by exact F6. assert (F5': m_ow M = m_ow mC) by exact F5.
  assert (Mi: m_inp M = inp) by (rewrite F1; exact Hi).
  assert (Mn: 0 <= m_nx M <= Zlength inp) by (rewrite F2, Nx; rewrite Hi in Lk'; lia).
  assert (Ml: m_leave (set_bad M M_dcheck) = 0) by (rewrite bt_setbad_leave, F7; exact NL).
  set (l4 := sublist (tpos G) (tpos G + 4) src) in *.
  assert (B4: Forall byte_ok l4) by apply bt_sub_bytes, Bs.
  assert (L4: Zlength l4 = 4) by (unfold l4; rewrite Zlength_sublist by lia; lia).
  unfold Zlib.proof.rfc1951.DecTrl.trl_tail in E.
  rewrite F13, Ns in E. replace (negb (Z.land (i_wrap (m_s mC)) 4 =? 0)) with true in E
    by (symmetry; apply negb_true_iff, Z.eqb_neq; exact W4).
  cbn [andb] in E. rewrite F16, Ns, F3, Nh, Mc in E.
  destruct (Zlib.proof.rfc1951.DecTrl.trl_flags G _ Hg NH NF) as [Fz Fg].
  destruct (bt_wrapper G CT) as [(wb & fl & did & W) | (h & W)].
  - (* zlib: the Adler-32, big-endian *)
    rewrite (Fz wb fl did W) in E. cbn [Z.eqb] in E.
    destruct (swap32 (le_val l4) =? chkv G (full G)) eqn:Es.
    + exfalso. apply Z.eqb_eq in Es. unfold chkv in Es. rewrite W in Es.
      assert (V: Zlib.proof.adler32.Model.adler_valid 1).
      { unfold Zlib.proof.adler32.Model.adler_valid. vm_compute. repeat split; discriminate. }
      pose proof (proj1 (Zlib.proof.adler32.Model.ref_adler32_valid 1 (full G) V)) as Ra.
      apply bt_swap_be in Es; [| exact B4 | exact L4 | exact Ra].
      destruct (bt_trl_zlib G wb fl did CT W) as (A & B & C).
      destruct BS as (_ & _ & _ & Nd). apply Nd. rewrite C, <- B. exact Es.
    + cbn [negb] in E. eapply bt_fin_bad in E; [| exact Ml | apply bt_setbad_mode | exact LP | exact RS | exact NM].
      subst res. rewrite <- F6', <- F5'. apply bt_concl_bad; [exact Mi | exact Mn].
  - (* gzip: the CRC-32, little-endian; then LENGTH *)
    rewrite (proj2 (Z.eqb_neq _ 0) (Fg h W)) in E.
    destruct (le_val l4 =? chkv G (full G)) eqn:Es.
    + apply Z.eqb_eq in Es. unfold chkv in Es. rewrite W in Es.
      pose proof (Zlib.proof.crc32.Combine.ref_crc32_range 0 (full G) (bt_is_bytes _ (bt_full_bytes G CT))) as Rc.
      unfold Zlib.proof.crc32.GF2.is32 in Rc.
      apply bt_le_eq in Es; [| exact B4 | exact L4 | exact Rc].
      destruct (bt_trl_gzip G h CT W) as (A & B & C4 & _).
      cbn [negb] in E.
      rewrite <- F6', <- F5'.
      change (m_aout M) with (m_aout (set_mode (initbits M) LENGTH)).
      change (m_ow M) with (m_ow (set_mode (initbits M) LENGTH)).
      assert (Gm: glob_ok G (m_s M)).
      { apply (bt_glob G (m_s mC)); [exact Hg | rewrite F13, Ns; reflexivity | rewrite F14, Ns; reflexivity
          | rewrite F11, Ns; reflexivity | rewrite F15, Ns; reflexivity | rewrite F16, Ns; reflexivity]. }
      assert (Mm: i_mode (m_s M) = CHECK) by (rewrite F11, Ns; exact Hm).
      refine (bt_length G src pos inp ob flush mC (set_mode (initbits M) LENGTH) o res 0 CT BS eq_refl _
                (ex_intro _ h W) Mi Hp Hl Hs _ _ _ _ _ Mt _ _ _ _ _ E LP RS NM).
      * apply (bt_glob2 G (m_s M)); try reflexivity; [exact Gm | bt_md | bt_md | cbn; bt_md | cbn; bt_md].
      * cbn [m_nx set_mode upd_s set_m_s initbits set_m_bits set_m_hold]. exact Mn.
      * cbn [m_ow set_mode upd_s set_m_s initbits set_m_bits set_m_hold]. rewrite F5'. exact Eo.
      * unfold m_left in *. cbn [m_out m_aout m_ow set_mode upd_s set_m_s initbits set_m_bits set_m_hold]. exact F9.
      * cbn [m_ret set_mode upd_s set_m_s initbits set_m_bits set_m_hold]. rewrite F8. exact Hr.
      * cbn [m_leave set_mode upd_s set_m_s initbits set_m_bits set_m_hold]. rewrite F7. exact NL.
      * fold l4. rewrite Es, C4. reflexivity.
      * lia.
      * cbn [m_nx set_mode upd_s set_m_s initbits set_m_bits set_m_hold]. rewrite F2, Nx. lia.
      * reflexivity.
      * symmetry. apply bt_sub0.
    + cbn [negb] in E. eapply bt_fin_bad in E; [| exact Ml | apply bt_setbad_mode | exact LP | exact RS | exact NM].
      subst res. rewrite <- F6', <- F5'. apply bt_concl_bad; [exact Mi | exact Mn].
Qed.

(* a call that starts with part of the trailer read *)
Lemma bad_trl_start G src pos out z L inp :
  bad_ctx G -> bad_src G src -> pc_state G src pos out (l_s L) ->
  0 <= pos -> pos + Zlength inp <= Zlength src -> inp = sublist pos (pos + Zlength inp) src ->
  Zlength inp <= 2 ^ 32 - 1 -> 0 <= zf_ao z <= 2 ^ 32 - 1 ->
  chead G src pos inp out (m_init z L inp).
Proof.
  intros CT BS (Eo & Hg & Hmd) Hp Hl Hi Hli Hao.
  assert (NT: i_mode (l_s L) <> TYPE) by (destruct Hmd as [(E & _) | (E & _)]; rewrite E; bt_md).
  unfold m_init. cbv zeta. rewrite (proj2 (Z.eqb_neq _ _) NT).
  unfold chead, m_mode. cbn [m_s m_inp m_nx m_in m_leave m_ret m_ow m_aout m_out m_hold m_bits].
  refine (conj eq_refl (conj Hp (conj Hl (conj Hi (conj Hli (conj _ (conj eq_refl (conj eq_refl (conj eq_refl
    (conj Hg (conj _ (conj _ (conj eq_refl _))))))))))))).
  - pose proof (Zlength_nonneg inp). lia.
  - rewrite app_nil_r. exact Eo.
  - rewrite Zlength_nil. lia.
  - destruct Hmd as [(E & C & T & k & K & P & B & H) | (E & W & T & S & k & K & P & B & H)].
    + left. refine (conj E (conj C (conj T _))). exists k. rewrite Z.add_0_r. auto.
    + right. refine (conj E (conj W (conj eq_refl (conj T (conj S _))))). exists k. rewrite Z.add_0_r. auto.
Qed.

(* the rest of the call from a loop head in CHECK or LENGTH *)
Lemma bad_trl_call G src pos inp ob flush mC o res :
  bad_ctx G -> bad_src G src -> chead G src pos inp ob mC ->
  loop2 flush lenfix_list distfix_list mC o ->
  match o with IRet r m => res = Res r m None | IBrk m => inf_leave flush m res end ->
  r_ret res <> Z_MEM_ERROR ->
  let m := r_m res in
  0 <= m_snx m <= Zlength inp /\ m_sow m = Zlength (m_ow m) /\ m_aout m = m_aout mC /\ m_ow m = m_ow mC /\
  m_inp m = inp /\
  (r_ret res = Z_DATA_ERROR \/
   ((r_ret res = Z_OK \/ r_ret res = Z_BUF_ERROR) /\ pc_state G src (pos + m_snx m) (ob ++ m_ow m) (m_s m))).
Proof.
  intros CT BS CH LP RS NM. change (bt_concl G src pos inp ob (m_aout mC) (m_ow mC) res).
  destruct CH as (Ei & Hp & Hl & Hi & Hli & Hnx & Hin & Hlv & Hret & Hg & Eow & Haow & Hout & Hmd).
  destruct Hmd as [(Em & Ec & Et & k & K & P & B & H) | (Em & W & Ew & Et & S4 & k & K & P & B & H)].
  - rewrite bt_produced in Ec, Et by exact CT.
    exact (bt_check G src pos inp ob flush mC o res k CT BS Em Hg Ei Hp Hl Hi Hnx Hlv Hret Eow Haow Hout Ec Et
             K P B H LP RS NM).
  - rewrite bt_produced in Et by exact CT.
    assert (Eo': ob = full G) by (rewrite <- Eow, Ew, app_nil_r; reflexivity).
    apply (bt_length G src pos inp ob flush mC mC o res k CT BS Em Hg W Ei Hp Hl Hi Hnx Eow); auto.
    + unfold m_left. rewrite Ew, Zlength_nil. lia.
    + rewrite Et, Eo'. reflexivity.
    + apply stepf2_LENGTH. exact Em.
Qed.
