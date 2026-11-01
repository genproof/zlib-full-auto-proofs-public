(** * The header part of the deflate laws' theory: definitions and basic lemmas

    [hinv]: the invariant [HI] of RTDLTIface.hdr_facts (a stream in the middle of a gzip header).
    [hacc] / [hmid] / [hret]: a state during deflate()'s header stages, started at [(s0, z0)] with header [H]
    from byte [k0]: bytes [k0 .. kk) of [H] were put into pending_buf, those not handed to next_out are pending.
    [hmid]: still going (pending_out at 0); [hret]: about to return Z_OK with the output space full.
    [gent]: the entry of the gzip header stage [st] (EXTRA, NAME, COMMENT, HCRC).
    The basic lemmas: put_byte, the extra copy (mb_write), the read of pending_buf, HCRC_UPDATE, flush_pending,
    the flush-or-return step. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDLTIface.
Require Zlib.proof.crc32.Combine.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** Positions in the gzip header *)

(** strm->adler in the middle of a gzip header [H] at byte [k]: the CRC-32 of the bytes so far when the
    header has a header CRC, else 0. *)
Definition hadler (h : gzh) (H : list Z) (k : Z) : Z :=
  if gz_hcrc h =? 0 then 0 else Zlib.proof.crc32.Model.ref_crc32 0 (sublist 0 k H).

(** The header byte reached in status [st] with gzindex [g]. *)
Definition gpos (h : gzh) (st g : Z) : Z :=
  if st =? EXTRA_STATE then 10 + (match gz_extra h with Some _ => 2 + g | None => 0 end)
  else if st =? NAME_STATE then 10 + Zlength (gz_extra_bytes h) + g
  else if st =? COMMENT_STATE then 10 + Zlength (gz_extra_bytes h) + Zlength (cstr_bytes (gz_name h)) + g
  else Zlength (gz_body h 0).

(** The range of gzindex in status [st]. *)
Definition gidx_ok (h : gzh) (st g : Z) : Prop :=
  if st =? EXTRA_STATE then (match gz_extra h with Some _ => 0 <= g <= gz_extra_len h | None => g = 0 end)
  else if st =? NAME_STATE then (match gz_name h with Some l => 0 <= g < Zlength l | None => g = 0 end)
  else if st =? COMMENT_STATE then (match gz_comment h with Some l => 0 <= g < Zlength l | None => g = 0 end)
  else True.

(** The invariant [HI] of hdr_facts: deflate() returned Z_OK in the middle of the gzip header. *)
Definition hinv : hdr_inv := fun s a H k =>
  d_wrap s = 2 /\
  exists h xfl, d_gzhead s = Some h /\ hdr_ok h /\ H = gz_hdr_bytes (Some h) xfl /\
  ((d_status s = EXTRA_STATE /\ gz_extra h <> None /\ d_gzindex s < gz_extra_len h) \/
   (d_status s = NAME_STATE /\ gz_name h <> None) \/
   (d_status s = COMMENT_STATE /\ gz_comment h <> None) \/
   (d_status s = HCRC_STATE /\ gz_hcrc h <> 0)) /\
  gidx_ok h (d_status s) (d_gzindex s) /\ k = gpos h (d_status s) (d_gzindex s) /\ a = hadler h H k.

(** ** States during the header stages *)

Definition hacc (s0 : dstate) (z0 : strm) (H : list Z) (k0 : Z) (s : dstate) (z : strm) (kk : Z) : Prop :=
  core_eq s0 s /\ prm s /\ outok s /\ d_bi_valid s0 = 0 /\ d_bi_valid s = 0 /\ d_sym_next s = 0 /\
  d_wrap s = d_wrap s0 /\ d_gzhead s = d_gzhead s0 /\ d_pending_buf_size s = d_pending_buf_size s0 /\
  0 <= k0 /\ k0 <= kk <= Zlength H /\
  exists x, x ++ pend s = sublist k0 kk H /\ zout_step z0 z x (z_adler z).

Definition hmid (s0 : dstate) (z0 : strm) (H : list Z) (k0 : Z) (s : dstate) (z : strm) (kk : Z) : Prop :=
  hacc s0 z0 H k0 s z kk /\ d_po s = 0 /\ d_last_flush s = d_last_flush s0 /\ 0 <= z_avail_out z.

Definition hret (s0 : dstate) (z0 : strm) (H : list Z) (k0 : Z) (s : dstate) (z : strm) (kk : Z) : Prop :=
  hacc s0 z0 H k0 s z kk /\ d_last_flush s = -1 /\ z_avail_out z = 0 /\ d_pending s <> 0.

(** The return in the middle of the gzip header. *)
Definition hstop (s0 : dstate) (z0 : strm) (H : list Z) (k0 : Z) (s : dstate) (z : strm) : Prop :=
  exists kk, hret s0 z0 H k0 s z kk /\ hinv s (z_adler z) H kk.

(** The entry of the gzip header stage [st]. *)
Definition gent (s0 : dstate) (z0 : strm) (H : list Z) (k0 : Z) (st : Z) (s : dstate) (z : strm) : Prop :=
  d_status s = st /\ d_wrap s = 2 /\
  exists h xfl, d_gzhead s = Some h /\ hdr_ok h /\ H = gz_hdr_bytes (Some h) xfl /\
  gidx_ok h st (d_gzindex s) /\ hmid s0 z0 H k0 s z (gpos h st (d_gzindex s)) /\
  z_adler z = hadler h H (gpos h st (d_gzindex s)).

(** ** Basic lemmas *)

Lemma hmid_status : forall s0 z0 H k0 s z kk x,
  hmid s0 z0 H k0 s z kk -> hmid s0 z0 H k0 (set_d_status s x) z kk.
Proof. intros; assumption. Qed.

Lemma hmid_gzindex : forall s0 z0 H k0 s z kk x,
  hmid s0 z0 H k0 s z kk -> hmid s0 z0 H k0 (set_d_gzindex s x) z kk.
Proof. intros; assumption. Qed.

Lemma hmid_adler : forall s0 z0 H k0 s z kk a,
  hmid s0 z0 H k0 s z kk -> hmid s0 z0 H k0 s (set_z_adler z a) kk.
Proof.
  intros s0 z0 H k0 s z kk a [[Hc [Hp [Ho [Hb0 [Hb [Hs [Hw [Hg [Hpb [Hk0 [Hk [x [Hx Hz]]]]]]]]]]]]] Hr].
  split; [|exact Hr].
  repeat (split; [assumption|]).
  exists x. split; [exact Hx|].
  unfold zout_step in *; cbn [z_in z_next_in z_avail_in z_total_in z_out z_avail_out z_total_out z_adler z_msg set_z_adler].
  intuition.
Qed.

Lemma hret_status : forall s0 z0 H k0 s z kk x,
  hret s0 z0 H k0 s z kk -> hret s0 z0 H k0 (set_d_status s x) z kk.
Proof. intros; assumption. Qed.

Lemma hret_gzindex : forall s0 z0 H k0 s z kk x,
  hret s0 z0 H k0 s z kk -> hret s0 z0 H k0 (set_d_gzindex s x) z kk.
Proof. intros; assumption. Qed.

Lemma hret_adler : forall s0 z0 H k0 s z kk a,
  hret s0 z0 H k0 s z kk -> hret s0 z0 H k0 s (set_z_adler z a) kk.
Proof.
  intros s0 z0 H k0 s z kk a [[Hc [Hp [Ho [Hb0 [Hb [Hs [Hw [Hg [Hpb [Hk0 [Hk [x [Hx Hz]]]]]]]]]]]]] Hr].
  split; [|exact Hr].
  repeat (split; [assumption|]).
  exists x. split; [exact Hx|].
  unfold zout_step in *; cbn [z_in z_next_in z_avail_in z_total_in z_out z_avail_out z_total_out z_adler z_msg set_z_adler].
  intuition.
Qed.

(** ** Frame lemmas: what keeps [core_eq] and [prm] *)

Lemma strip_fields : forall s s', strip s' = strip s ->
  d_sym_next s' = d_sym_next s /\ d_L s' = d_L s /\ d_pending_buf_size s' = d_pending_buf_size s /\
  d_w_bits s' = d_w_bits s /\ d_w_size s' = d_w_size s /\ d_w_mask s' = d_w_mask s /\
  d_hash_bits s' = d_hash_bits s /\ d_hash_size s' = d_hash_size s /\ d_hash_mask s' = d_hash_mask s /\
  d_hash_shift s' = d_hash_shift s /\ tr_sym_end (d_tr s') = tr_sym_end (d_tr s) /\
  d_level s' = d_level s /\ d_strategy s' = d_strategy s /\ d_method s' = d_method s.
Proof.
  intros s s' E.
  repeat split;
    [ exact (f_equal (fun t => d_sym_next t) E) | exact (f_equal (fun t => d_L t) E)
    | exact (f_equal d_pending_buf_size E) | exact (f_equal d_w_bits E) | exact (f_equal d_w_size E)
    | exact (f_equal d_w_mask E) | exact (f_equal d_hash_bits E) | exact (f_equal d_hash_size E)
    | exact (f_equal d_hash_mask E) | exact (f_equal d_hash_shift E)
    | exact (f_equal (fun t => tr_sym_end (d_tr t)) E) | exact (f_equal (fun t => d_level t) E)
    | exact (f_equal (fun t => d_strategy t) E) | exact (f_equal d_method E) ].
Qed.

Lemma core_eq_step : forall s0 s s',
  core_eq s0 s -> strip s' = strip s -> d_sym_next s = 0 ->
  Zlength (o_buf (tr_out (d_tr s'))) = Zlength (o_buf (tr_out (d_tr s))) ->
  Zlength (d_pbm s') = Zlength (d_pbm s) -> core_eq s0 s'.
Proof.
  intros s0 s s' [E1 [E2 [E3 E4]]] E Hs L1 L2.
  destruct (strip_fields s s' E) as [Fs [FL _]].
  split; [congruence|]. split; [|split; congruence].
  rewrite <- E2. unfold sym_region. rewrite Fs, FL, Hs, Z.add_0_r, !sublist_nil. reflexivity.
Qed.

Lemma prm_step : forall s s',
  prm s -> strip s' = strip s ->
  Zlength (o_buf (tr_out (d_tr s'))) = Zlength (o_buf (tr_out (d_tr s))) ->
  Zlength (d_pbm s') = Zlength (d_pbm s) -> prm s'.
Proof.
  intros s s' P E L1 L2.
  destruct (strip_fields s s' E) as [F1 [F2 [F3 [F4 [F5 [F6 [F7 [F8 [F9 [F10 [F11 [F12 [F13 F14]]]]]]]]]]]]].
  unfold prm in *. rewrite F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12, F13, F14, L1, L2. exact P.
Qed.

Lemma pend_len : forall s, prm s -> outok s -> Zlength (pend s) = d_pending s.
Proof.
  intros s P O. destruct P as [_ [_ [_ [_ [_ [_ [_ [_ [P1 [P2 _]]]]]]]]]].
  destruct O as [_ [[_ [_ B]] [O1 [O2 _]]]].
  unfold pend, d_pending in *. rewrite Zlength_sublist; lia.
Qed.

(** The pending bytes are the last [pending] bytes put. *)
Lemma hacc_pending_le : forall s0 z0 H k0 s z kk,
  hacc s0 z0 H k0 s z kk -> 0 <= d_pending s <= kk - k0.
Proof.
  intros s0 z0 H k0 s z kk [Hc [Hp [Ho [Hb0 [Hb [Hs [Hw [Hg [Hpb [Hk0 [Hk [x [Hx Hz]]]]]]]]]]]]].
  pose proof (pend_len s Hp Ho) as L.
  assert (L2 : Zlength (x ++ pend s) = kk - k0) by (rewrite Hx, Zlength_sublist; lia).
  rewrite Zlength_app in L2. pose proof (Zlength_nonneg x). pose proof (Zlength_nonneg (pend s)). lia.
Qed.

Lemma hmid_pending_le : forall s0 z0 H k0 s z kk,
  hmid s0 z0 H k0 s z kk -> 0 <= d_pending s <= kk - k0.
Proof. intros s0 z0 H k0 s z kk [A _]. exact (hacc_pending_le _ _ _ _ _ _ _ A). Qed.

(** A store of the bytes [b] at pending_buf[pending ..], pending advanced: the general step. *)
Lemma hmid_store : forall s0 z0 H k0 s z kk s' b,
  hmid s0 z0 H k0 s z kk ->
  strip s' = strip s -> d_wrap s' = d_wrap s -> d_gzhead s' = d_gzhead s -> d_po s' = 0 ->
  d_last_flush s' = d_last_flush s ->
  o_buf (tr_out (d_tr s')) =
    sublist 0 (d_pending s) (o_buf (tr_out (d_tr s))) ++ b ++
    sublist (d_pending s + Zlength b) (Zlength (o_buf (tr_out (d_tr s)))) (o_buf (tr_out (d_tr s))) ->
  d_pbm s' =
    sublist 0 (d_pending s) (d_pbm s) ++ repeat true (Z.to_nat (Zlength b)) ++
    sublist (d_pending s + Zlength b) (Zlength (d_pbm s)) (d_pbm s) ->
  d_pending s' = d_pending s + Zlength b ->
  o_bi_valid (tr_out (d_tr s')) = o_bi_valid (tr_out (d_tr s)) ->
  o_bi_buf (tr_out (d_tr s')) = o_bi_buf (tr_out (d_tr s)) ->
  bytes b -> d_pending s + Zlength b <= d_pending_buf_size s ->
  kk + Zlength b <= Zlength H -> sublist kk (kk + Zlength b) H = b ->
  hmid s0 z0 H k0 s' z (kk + Zlength b).
Proof.
  intros s0 z0 H k0 s z kk s' b Hm E Ew Eg Epo Elf Ebuf Epbm Epend Ebv Ebb Hb Hroom Hkb Hsub.
  pose proof (hmid_pending_le _ _ _ _ _ _ _ Hm) as Hple.
  destruct Hm as [[Hc [Hp [Ho [Hb0 [Hbv [Hs [Hw [Hg [Hpb [Hk0 [Hk [x [Hx Hz]]]]]]]]]]]]] [Hpo [Hlf Hav]]].
  destruct (strip_fields s s' E) as [Fs [FL [Fpbs _]]].
  pose proof Hp as Hp'.
  destruct Hp' as [_ [_ [_ [_ [_ [_ [_ [_ [P1 [P2 [P3 _]]]]]]]]]]].
  destruct Ho as [[Ok1 Ok2] [[B1 [B2 B3]] [O1 [O2 [[D1 [D2 D3]] O4]]]]].
  unfold d_pending in *.
  set (buf := o_buf (tr_out (d_tr s))) in *. set (m := d_pbm s) in *.
  set (p := o_pending (tr_out (d_tr s))) in *.
  pose proof (Zlength_nonneg b) as Hb_nn.
  assert (Lb : Zlength (o_buf (tr_out (d_tr s'))) = Zlength buf).
  { rewrite Ebuf. rewrite !Zlength_app, !Zlength_sublist; lia. }
  assert (Lm : Zlength (d_pbm s') = Zlength m).
  { rewrite Epbm. rewrite !Zlength_app, !Zlength_sublist, Zlength_repeat; lia. }
  split; [split|].
  - eapply core_eq_step; eauto.
  - split; [eapply prm_step; eauto|].
    split.
    { (* outok *)
      unfold outok, d_pb, d_pending. cbv beta iota delta [mb_val mb_def].
      split; [split|].
      - change (Zlength (d_pbm s') = Zlength (o_buf (tr_out (d_tr s')))). rewrite Lm, Lb. exact Ok1.
      - intros i Hi Hd. change (0 <= i < Zlength (o_buf (tr_out (d_tr s')))) in Hi.
        change (Znth i (d_pbm s') = true) in Hd. change (0 <= Znth i (o_buf (tr_out (d_tr s'))) < 256).
        rewrite Lb in Hi. rewrite Ebuf. rewrite Epbm in Hd.
        assert (Zlength m = Zlength buf) as Lmb by exact Ok1.
        destruct (Z_lt_dec i p) as [H1|H1].
        + rewrite app_Znth1 in Hd |- * by (rewrite Zlength_sublist; lia).
          rewrite Znth_sublist in Hd by lia. rewrite Znth_sublist by lia. rewrite Z.add_0_r in *. apply Ok2; [lia|exact Hd].
        + destruct (Z_lt_dec i (p + Zlength b)) as [H2|H2].
          * rewrite app_Znth2 by (rewrite Zlength_sublist; lia). rewrite Zlength_sublist by lia.
            rewrite app_Znth1 by lia. eapply Forall_Znth; [lia|exact Hb].
          * assert (Hd' : Znth i m = true).
            { rewrite app_Znth2 in Hd by (rewrite Zlength_sublist; lia). rewrite Zlength_sublist in Hd by lia.
              rewrite app_Znth2 in Hd by (rewrite Zlength_repeat; lia). rewrite Zlength_repeat in Hd by lia.
              rewrite Znth_sublist in Hd by lia.
              replace (i - (p - 0) - Zlength b + (p + Zlength b)) with i in Hd by lia. exact Hd. }
            rewrite app_Znth2 by (rewrite Zlength_sublist; lia). rewrite Zlength_sublist by lia.
            rewrite app_Znth2 by lia. rewrite Znth_sublist by lia.
            replace (i - (p - 0) - Zlength b + (p + Zlength b)) with i by lia. apply Ok2; [change (0 <= i < Zlength buf); lia|exact Hd'].
      - cbn [mb_val mb_def]. split; [unfold bits_ok in *; rewrite Ebv, Ebb; rewrite Epend; lia|].
        rewrite Epo. split; [lia|]. split; [rewrite Epend, Fpbs; lia|].
        split; [|intros; reflexivity].
        split; [lia|]. cbn [mb_val mb_def]. split; [rewrite Epend, Lb; lia|].
        intros i Hi. rewrite Epend in Hi. change (Znth i (d_pbm s') = true). rewrite Epbm.
        destruct (Z_lt_dec i p) as [H1|H1].
        + rewrite app_Znth1 by (rewrite Zlength_sublist; lia). rewrite Znth_sublist by lia.
          rewrite Z.add_0_r. apply D3. rewrite Hpo in *. lia.
        + rewrite app_Znth2 by (rewrite Zlength_sublist; lia). rewrite Zlength_sublist by lia.
          rewrite app_Znth1 by (rewrite Zlength_repeat; lia).
          apply Znth_repeat_inrange. lia. }
    split; [exact Hb0|]. split; [rewrite <- Hbv; exact Ebv|]. split; [congruence|].
    split; [congruence|]. split; [congruence|]. split; [congruence|]. split; [exact Hk0|].
    split; [lia|].
    exists x. split; [|exact Hz].
    assert (Pend : pend s' = pend s ++ b).
    { unfold pend. rewrite Epo, Hpo. unfold d_pending. rewrite Epend. fold p.
      rewrite !Z.add_0_l. rewrite Ebuf. rewrite app_assoc.
      rewrite sublist0_app1 by (rewrite Zlength_app, Zlength_sublist; lia).
      rewrite sublist_same; [reflexivity|lia|rewrite Zlength_app, Zlength_sublist; lia]. }
    rewrite Pend, app_assoc, Hx. rewrite (sublist_split k0 kk (kk + Zlength b) H) by lia. rewrite Hsub. reflexivity.
  - rewrite Epo, Elf. split; [reflexivity|]. split; [exact Hlf|exact Hav].
Qed.

Lemma set_d_out_twice : forall s o1 o2, set_d_out (set_d_out s o1) o2 = set_d_out s o2.
Proof. intros. reflexivity. Qed.

Lemma set_d_out_id : forall s, set_d_out s (d_out s) = s.
Proof. intros [] ; unfold set_d_out, d_out; cbn. destruct d_tr; reflexivity. Qed.

Lemma hmid_buf_len : forall s0 z0 H k0 s z kk,
  hmid s0 z0 H k0 s z kk ->
  Zlength (o_buf (tr_out (d_tr s))) = d_pending_buf_size s /\ Zlength (d_pbm s) = d_pending_buf_size s /\
  0 <= d_pending s /\ d_pending s <= d_pending_buf_size s.
Proof.
  intros s0 z0 H k0 s z kk Hm. pose proof (hmid_pending_le _ _ _ _ _ _ _ Hm) as Hle.
  destruct Hm as [[_ [Hp [Ho _]]] [Hpo _]].
  destruct Hp as [_ [_ [_ [_ [_ [_ [_ [_ [P1 [P2 [P3 _]]]]]]]]]]].
  destruct Ho as [_ [_ [_ [O2 _]]]]. rewrite Hpo in O2. lia.
Qed.

Lemma dput_byte_mid : forall s0 z0 H k0 s z kk c,
  hmid s0 z0 H k0 s z kk -> d_pending s < d_pending_buf_size s ->
  kk < Zlength H -> Znth kk H = u8 c ->
  exists o, c_dput_byte s c = Some (set_d_out s o) /\ hmid s0 z0 H k0 (set_d_out s o) z (kk + 1) /\
    d_pending (set_d_out s o) = d_pending s + 1.
Proof.
  intros s0 z0 H k0 s z kk c Hm Hroom HkH Hc8.
  assert (Hk : 0 <= kk) by (destruct Hm as [[_ [_ [_ [_ [_ [_ [_ [_ [_ [Hk0 [Hk _]]]]]]]]]]] _]; lia).
  destruct (hmid_buf_len _ _ _ _ _ _ _ Hm) as [Lb [Lm [Hp0 _]]].
  unfold d_pending in *. set (o := tr_out (d_tr s)) in *.
  exists (mkOut (upd_Znth (o_pending o) (o_buf o) (u8 c)) (o_pending o + 1) (o_bi_buf o) (o_bi_valid o)
                (o_bi_used o), upd_Znth (o_pending o) (d_pbm s) true).
  assert (Hin : in_range (o_pending o) (Zlength (o_buf o)) = true).
  { unfold in_range. apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia. }
  split.
  { unfold c_dput_byte, c_put_byte, d_out, wr. fold o. cbv beta iota. rewrite Hin. reflexivity. }
  split; [|reflexivity].
  pose proof (hmid_store s0 z0 H k0 s z kk
     (set_d_out s (mkOut (upd_Znth (o_pending o) (o_buf o) (u8 c)) (o_pending o + 1) (o_bi_buf o) (o_bi_valid o)
                (o_bi_used o), upd_Znth (o_pending o) (d_pbm s) true)) [u8 c]) as HS.
  change (Zlength [u8 c]) with 1 in HS. apply HS; clear HS; try reflexivity; try assumption.
  - exact (proj1 (proj2 Hm)).
  - change (upd_Znth (o_pending o) (o_buf o) (u8 c) = sublist 0 (o_pending o) (o_buf o) ++ [u8 c] ++
      sublist (o_pending o + 1) (Zlength (o_buf o)) (o_buf o)). apply list_solver.upd_Znth_unfold. lia.
  - change (upd_Znth (o_pending o) (d_pbm s) true = sublist 0 (o_pending o) (d_pbm s) ++ [true] ++
      sublist (o_pending o + 1) (Zlength (d_pbm s)) (d_pbm s)). apply list_solver.upd_Znth_unfold. lia.
  - repeat constructor; unfold u8; apply Z.mod_pos_bound; lia.
  - change (o_pending o + 1 <= d_pending_buf_size s). lia.
  - lia.
  - rewrite sublist_len_1 by lia. rewrite Hc8. reflexivity.
Qed.

(** put_byte of each byte of [l]. *)
Lemma dput_bytes_mid : forall l s0 z0 H k0 s z kk,
  hmid s0 z0 H k0 s z kk -> d_pending s + Zlength l <= d_pending_buf_size s ->
  kk + Zlength l <= Zlength H -> sublist kk (kk + Zlength l) H = map u8 l ->
  exists o, c_dput_bytes s l = Some (set_d_out s o) /\ hmid s0 z0 H k0 (set_d_out s o) z (kk + Zlength l) /\
    d_pending (set_d_out s o) = d_pending s + Zlength l.
Proof.
  induction l as [|a l IH]; intros s0 z0 H k0 s z kk Hm Hroom HkH Hsub.
  - exists (d_out s). rewrite set_d_out_id. cbn. rewrite !Z.add_0_r. auto.
  - rewrite Zlength_cons in *.
    pose proof (Zlength_nonneg l) as Hl.
    assert (Hk : 0 <= kk) by (destruct Hm as [[_ [_ [_ [_ [_ [_ [_ [_ [_ [Hk0 [Hk _]]]]]]]]]]] _]; lia).
    assert (Ha : Znth kk H = u8 a).
    { assert (E := f_equal (Znth 0) Hsub). rewrite Znth_sublist in E by lia. rewrite Z.add_0_l in E.
      rewrite E. reflexivity. }
    destruct (dput_byte_mid s0 z0 H k0 s z kk a Hm ltac:(lia) ltac:(lia) Ha) as [o1 [E1 [Hm1 Hp1]]].
    destruct (IH s0 z0 H k0 (set_d_out s o1) z (kk + 1) Hm1) as [o2 [E2 [Hm2 Hp2]]].
    + rewrite Hp1. change (d_pending_buf_size (set_d_out s o1)) with (d_pending_buf_size s). lia.
    + lia.
    + assert (E := f_equal (sublist 1 (1 + Zlength l)) Hsub).
      rewrite sublist_sublist in E by lia. replace (1 + kk) with (kk + 1) in E by lia.
      replace (1 + Zlength l + kk) with (kk + 1 + Zlength l) in E by lia. rewrite E.
      cbn [map]. rewrite sublist_1_cons. rewrite sublist_same; [reflexivity|lia|].
      rewrite Zlength_map. lia.
    + exists o2. cbn [c_dput_bytes]. rewrite E1. cbn [bind]. rewrite E2, set_d_out_twice.
      rewrite set_d_out_twice in Hm2, Hp2. replace (kk + Z.succ (Zlength l)) with (kk + 1 + Zlength l) by lia.
      split; [reflexivity|]. split; [exact Hm2|]. rewrite Hp2, Hp1. lia.
Qed.

(** zmemcpy(s->pending_buf + s->pending, bytes, len); s->pending = ... (the extra field copy). *)
Lemma pb_write_mid : forall s0 z0 H k0 s z kk b,
  hmid s0 z0 H k0 s z kk -> d_pending s + Zlength b <= d_pending_buf_size s ->
  kk + Zlength b <= Zlength H -> sublist kk (kk + Zlength b) H = b -> bytes b ->
  exists pb, mb_write (d_pb s) (d_pending s) b = Some pb /\
    hmid s0 z0 H k0 (set_d_pending (set_d_pb s pb) (d_pending s + Zlength b)) z (kk + Zlength b).
Proof.
  intros s0 z0 H k0 s z kk b Hm Hroom HkH Hsub Hb.
  destruct (hmid_buf_len _ _ _ _ _ _ _ Hm) as [Lb [Lm [Hp0 _]]].
  pose proof (Zlength_nonneg b) as Hbn.
  set (pb := mkMB (sublist 0 (d_pending s) (o_buf (tr_out (d_tr s))) ++ b ++
                   sublist (d_pending s + Zlength b) (Zlength (o_buf (tr_out (d_tr s)))) (o_buf (tr_out (d_tr s))))
                  (sublist 0 (d_pending s) (d_pbm s) ++ repeat true (Z.to_nat (Zlength b)) ++
                   sublist (d_pending s + Zlength b) (Zlength (d_pbm s)) (d_pbm s))).
  exists pb. split.
  { unfold mb_write. change (mb_val (d_pb s)) with (o_buf (tr_out (d_tr s))).
    change (mb_def (d_pb s)) with (d_pbm s).
    replace ((0 <=? d_pending s) && (d_pending s + Zlength b <=? Zlength (o_buf (tr_out (d_tr s))))) with true
      by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.leb_le]; lia).
    reflexivity. }
  apply (hmid_store s0 z0 H k0 s z kk _ b Hm); try reflexivity; try assumption.
  - exact (proj1 (proj2 Hm)).
Qed.

Lemma mb_definedb_ok : forall b lo hi, mb_defined b lo hi -> mb_definedb b lo hi = true.
Proof.
  intros b lo hi [H1 [H2 H3]]. unfold mb_definedb.
  apply andb_true_intro. split; [apply andb_true_intro; split; apply Z.leb_le; lia|].
  apply forallb_forall. intros x Hin. apply in_map_iff in Hin. destruct Hin as [k [Ek Hk]]. subst x.
  apply in_seq in Hk. apply H3. lia.
Qed.

(** The read of pending_buf[beg .. pending) (HCRC_UPDATE). *)
Lemma mid_read : forall s0 z0 H k0 s z kk beg,
  hmid s0 z0 H k0 s z kk -> 0 <= beg <= d_pending s ->
  mb_read (d_pb s) beg (d_pending s - beg) = Some (sublist (kk - d_pending s + beg) kk H).
Proof.
  intros s0 z0 H k0 s z kk beg Hm Hbeg.
  destruct (hmid_buf_len _ _ _ _ _ _ _ Hm) as [Lb [Lm [Hp0 Hp1]]].
  destruct Hm as [[Hc [Hp [Ho [Hb0 [Hbv [Hs [Hw [Hg [Hpb [Hk0 [Hk [x [Hx Hz]]]]]]]]]]]]] [Hpo [Hlf Hav]]].
  pose proof (pend_len s Hp Ho) as Lp.
  destruct Ho as [_ [_ [_ [_ [Hdef _]]]]].
  unfold mb_read.
  replace ((0 <=? d_pending s - beg) && mb_definedb (d_pb s) beg (beg + (d_pending s - beg))) with true.
  2:{ symmetry. apply andb_true_intro. split; [apply Z.leb_le; lia|]. apply mb_definedb_ok.
      rewrite Hpo in Hdef. destruct Hdef as [D1 [D2 D3]]. split; [lia|]. split; [lia|].
      intros i Hi. apply D3. lia. }
  f_equal. replace (beg + (d_pending s - beg)) with (d_pending s) by lia.
  assert (Lx : Zlength x + d_pending s = kk - k0).
  { rewrite <- Lp, <- Zlength_app, Hx, Zlength_sublist; lia. }
  assert (E : sublist beg (d_pending s) (pend s) = sublist (Zlength x + beg) (Zlength x + d_pending s) (x ++ pend s)).
  { rewrite sublist_app2 by (pose proof (Zlength_nonneg x); lia). f_equal; lia. }
  pose proof (Zlength_nonneg x).
  rewrite Hx, sublist_sublist in E by lia.
  unfold pend in E. rewrite Hpo, Z.add_0_l, sublist_sublist in E by lia.
  rewrite !Z.add_0_r in E. change (mb_val (d_pb s)) with (o_buf (tr_out (d_tr s))). rewrite E.
  f_equal; lia.
Qed.

(** The CRC-32 of the header bytes so far, continued. *)
Lemma hadler_step : forall h H a b,
  bytes H -> 0 <= a <= b -> b <= Zlength H -> gz_hcrc h <> 0 ->
  Zlib.proof.crc32.Model.ref_crc32 (hadler h H a) (sublist a b H) = hadler h H b.
Proof.
  intros h H a b Hb Hab HbH Hc. unfold hadler.
  destruct (gz_hcrc h =? 0) eqn:E; [apply Z.eqb_eq in E; contradiction|].
  rewrite Zlib.proof.crc32.Combine.ref_crc32_app.
  - rewrite <- sublist_split by lia. reflexivity.
  - unfold Zlib.proof.adler32.Bytes.is_bytes. apply Forall_sublist.
    eapply Forall_impl; [|exact Hb]. intros y Hy. cbn beta in Hy. 
    change Integers.Byte.max_unsigned with 255. lia.
Qed.

(** HCRC_UPDATE(beg) brings strm->adler to the CRC-32 of all the bytes put. *)
Lemma hcrc_update_mid : forall s0 z0 H k0 s z kk h beg,
  hmid s0 z0 H k0 s z kk -> bytes H -> 0 <= beg <= d_pending s ->
  z_adler z = hadler h H (kk - d_pending s + beg) ->
  c_hcrc_update h s z beg = Some (set_z_adler z (hadler h H kk)).
Proof.
  intros s0 z0 H k0 s z kk h beg Hm Hb Hbeg Ha.
  pose proof (hmid_pending_le _ _ _ _ _ _ _ Hm) as Hle.
  assert (Hk : 0 <= k0 /\ kk <= Zlength H)
    by (destruct Hm as [[_ [_ [_ [_ [_ [_ [_ [_ [_ [Hk0 [Hk _]]]]]]]]]]] _]; lia).
  assert (Eta : forall a, z_adler z = a -> set_z_adler z a = z) by (intros a Ea; destruct z; cbn in *; subst; reflexivity).
  unfold c_hcrc_update.
  destruct (gz_hcrc h =? 0) eqn:E; cbn [negb andb].
  - rewrite Eta; [reflexivity|]. rewrite Ha. unfold hadler. rewrite E. reflexivity.
  - destruct (d_pending s >? beg) eqn:E2.
    + rewrite (mid_read s0 z0 H k0 s z kk beg Hm Hbeg). cbn [bind]. rewrite Ha.
      rewrite hadler_step; [reflexivity|exact Hb|lia|lia|]. apply Z.eqb_neq. exact E.
    + rewrite Z.gtb_ltb, Z.ltb_ge in E2.
      rewrite Eta; [reflexivity|]. rewrite Ha. f_equal. lia.
Qed.

(** The state after flush_pending handed [len] pending bytes to next_out. *)
Lemma hacc_flush_state : forall s0 z0 H k0 s z kk s' z' len,
  hmid s0 z0 H k0 s z kk -> 0 <= len <= d_pending s -> len <= z_avail_out z ->
  strip s' = strip s -> d_wrap s' = d_wrap s -> d_gzhead s' = d_gzhead s ->
  tr_out (d_tr s') = mkOut (o_buf (tr_out (d_tr s))) (d_pending s - len) (o_bi_buf (tr_out (d_tr s)))
                           (o_bi_valid (tr_out (d_tr s))) (o_bi_used (tr_out (d_tr s))) ->
  d_pbm s' = d_pbm s ->
  d_po s' = (if d_pending s - len =? 0 then 0 else len) ->
  z' = set_z_avail_out (set_z_total_out (set_z_out z (z_out z ++ sublist 0 len (o_buf (tr_out (d_tr s)))))
                                        (u64 (z_total_out z + len))) (z_avail_out z - len) ->
  hacc s0 z0 H k0 s' z' kk /\ 0 <= z_avail_out z'.
Proof.
  intros s0 z0 H k0 s z kk s' z' len Hm Hlen Hav' E Ew Eg Eout Epbm Epo Ez.
  destruct (hmid_buf_len _ _ _ _ _ _ _ Hm) as [Lb [Lm [Hp0 Hp1]]].
  destruct Hm as [[Hc [Hp [Ho [Hb0 [Hbv [Hs [Hw [Hg [Hpb [Hk0 [Hk [x [Hx Hz]]]]]]]]]]]]] [Hpo [Hlf Hav]]].
  pose proof (pend_len s Hp Ho) as Lp.
  destruct (strip_fields s s' E) as [Fs [FL [Fpbs _]]].
  assert (Lb' : Zlength (o_buf (tr_out (d_tr s'))) = Zlength (o_buf (tr_out (d_tr s)))) by (rewrite Eout; reflexivity).
  assert (Lm' : Zlength (d_pbm s') = Zlength (d_pbm s)) by (rewrite Epbm; reflexivity).
  assert (Epb : d_pb s' = d_pb s) by (unfold d_pb; rewrite Eout, Epbm; reflexivity).
  assert (Epend : d_pending s' = d_pending s - len) by (unfold d_pending at 1; rewrite Eout; reflexivity).
  assert (Ebv : d_bi_valid s' = d_bi_valid s) by (unfold d_bi_valid at 1; rewrite Eout; reflexivity).
  destruct Ho as [Ok [Bits [O1 [O2 [Hdef O4]]]]].
  rewrite Hpo in Hdef. destruct Hdef as [D1 [D2 D3]].
  assert (Pend : pend s' = sublist len (d_pending s) (o_buf (tr_out (d_tr s)))).
  { unfold pend. rewrite Epend, Epo. rewrite Eout. cbn [o_buf].
    destruct (d_pending s - len =? 0) eqn:E0.
    - apply Z.eqb_eq in E0. rewrite !sublist_nil'; [reflexivity|lia|lia].
    - f_equal. lia. }
  split; [|subst z'; cbn; lia].
  split; [eapply core_eq_step; eauto|].
  split; [eapply prm_step; eauto|].
  split.
  { split; [rewrite Epb; exact Ok|].
    split; [unfold bits_ok in *; rewrite Eout; cbn [o_bi_valid o_bi_buf o_pending]; unfold d_pending in *; lia|].
    rewrite Epo, Epend, Fpbs.
    destruct (d_pending s - len =? 0) eqn:E0; [apply Z.eqb_eq in E0|apply Z.eqb_neq in E0].
    - split; [lia|]. split; [lia|]. split; [|intros; reflexivity].
      rewrite Epb. split; [lia|]. split; [lia|]. intros; lia.
    - split; [lia|]. split; [lia|]. split; [|intros; lia].
      rewrite Epb. split; [lia|]. split; [lia|]. intros i Hi. apply D3. lia. }
  split; [exact Hb0|]. split; [rewrite Ebv; exact Hbv|]. split; [congruence|].
  split; [congruence|]. split; [congruence|]. split; [congruence|]. split; [exact Hk0|]. split; [exact Hk|].
  exists (x ++ sublist 0 len (o_buf (tr_out (d_tr s)))). split.
  - rewrite Pend, <- app_assoc, <- sublist_split by lia. rewrite <- Hx. f_equal.
    unfold pend. rewrite Hpo, Z.add_0_l. reflexivity.
  - subst z'. unfold zout_step in *. cbn [z_in z_next_in z_avail_in z_total_in z_out z_avail_out z_total_out
      z_adler z_msg set_z_avail_out set_z_total_out set_z_out].
    destruct Hz as [Z1 [Z2 [Z3 [Z4 [Z5 [Z6 [Z7 [Z8 Z9]]]]]]]].
    rewrite Zlength_app, Zlength_sublist by lia.
    repeat split; try assumption.
    + rewrite Z5, app_assoc. reflexivity.
    + rewrite Z6. lia.
    + rewrite Z7. unfold u64. rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

(** flush_pending(strm) *)
Lemma flush_mid : forall s0 z0 H k0 s z kk,
  hmid s0 z0 H k0 s z kk ->
  exists s' z', c_flush_pending s z = Some (s', z') /\
    d_status s' = d_status s /\ d_gzindex s' = d_gzindex s /\ d_last_flush s' = d_last_flush s /\
    z_adler z' = z_adler z /\
    ((d_pending s' = 0 /\ hmid s0 z0 H k0 s' z' kk) \/
     (d_pending s' <> 0 /\ z_avail_out z' = 0 /\ hacc s0 z0 H k0 s' z' kk)).
Proof.
  intros s0 z0 H k0 s z kk Hm.
  destruct (hmid_buf_len _ _ _ _ _ _ _ Hm) as [Lb [Lm [Hp0 Hp1]]].
  pose proof Hm as Hm'.
  destruct Hm' as [[Hc [Hp [Ho [Hb0 [Hbv [Hs [Hw [Hg [Hpb [Hk0 [Hk [x [Hx Hz]]]]]]]]]]]]] [Hpo [Hlf Hav]]].
  assert (Hsmall : d_pending s < 4294967296).
  { destruct Hp as [_ [_ [_ [[Hh1 Hh2] [_ [_ [_ [HL [P1 _]]]]]]]]].
    assert (2 ^ (d_hash_bits s - 1) <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia). lia. }
  assert (Hfb : c_tr_flush_bits (d_out s) = Some (d_out s)).
  { unfold c_tr_flush_bits, c_bi_flush, d_out. cbv beta iota. unfold d_bi_valid in Hbv. rewrite Hbv. reflexivity. }
  unfold c_flush_pending. rewrite Hfb. cbn [bind]. rewrite set_d_out_id.
  set (len := if d_pending s >? z_avail_out z then z_avail_out z else u32 (d_pending s)).
  assert (Hlen : len = Z.min (d_pending s) (z_avail_out z)).
  { subst len. unfold u32. rewrite Z.mod_small by lia.
    destruct (d_pending s >? z_avail_out z) eqn:E; [apply Z.gtb_lt in E|rewrite Z.gtb_ltb, Z.ltb_ge in E]; lia. }
  destruct (len =? 0) eqn:E0.
  - apply Z.eqb_eq in E0. exists s, z. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    destruct (Z.eq_dec (d_pending s) 0) as [P0|P0].
    + left. split; [exact P0|exact Hm].
    + right. split; [exact P0|]. split; [lia|exact (proj1 Hm)].
  - apply Z.eqb_neq in E0.
    assert (Hrd : mb_read (mkMB (o_buf (tr_out (d_tr s))) (d_pbm s)) (d_po s) len =
                  Some (sublist 0 len (o_buf (tr_out (d_tr s))))).
    { unfold mb_read. rewrite Hpo.
      replace ((0 <=? len) && mb_definedb {| mb_val := o_buf (tr_out (d_tr s)); mb_def := d_pbm s |} 0 (0 + len))
        with true.
      - reflexivity.
      - symmetry. apply andb_true_intro. split; [apply Z.leb_le; lia|]. apply mb_definedb_ok.
        destruct Ho as [_ [_ [_ [_ [[D1 [D2 D3]] _]]]]]. rewrite Hpo in *.
        split; [lia|]. split; [cbn; lia|]. intros i Hi. apply D3. lia. }
    rewrite Hrd. cbn [bind].
    unfold out_put. rewrite Zlength_sublist by lia.
    replace (len - 0 <=? z_avail_out z) with true by (symmetry; apply Z.leb_le; lia).
    cbn [bind].
    set (s2 := set_d_out (set_d_po s (d_po s + len))
                 (mkOut (o_buf (tr_out (d_tr (set_d_po s (d_po s + len)))))
                        (o_pending (tr_out (d_tr (set_d_po s (d_po s + len)))) - len)
                        (o_bi_buf (tr_out (d_tr (set_d_po s (d_po s + len)))))
                        (o_bi_valid (tr_out (d_tr (set_d_po s (d_po s + len)))))
                        (o_bi_used (tr_out (d_tr (set_d_po s (d_po s + len))))),
                  d_pbm (set_d_po s (d_po s + len)))).
    set (z2 := set_z_avail_out (set_z_total_out (set_z_out z (z_out z ++ sublist 0 len (o_buf (tr_out (d_tr s)))))
                 (u64 (z_total_out z + len))) (z_avail_out z - len)).
    assert (Ep2 : d_pending s2 = d_pending s - len) by reflexivity.
    exists (if d_pending s2 =? 0 then set_d_po s2 0 else s2), z2.
    split; [reflexivity|].
    rewrite Ep2.
    assert (Hst : forall s', strip s' = strip s -> d_wrap s' = d_wrap s -> d_gzhead s' = d_gzhead s ->
       tr_out (d_tr s') = tr_out (d_tr s2) -> d_pbm s' = d_pbm s ->
       d_po s' = (if d_pending s - len =? 0 then 0 else len) ->
       hacc s0 z0 H k0 s' z2 kk /\ 0 <= z_avail_out z2).
    { intros s' E1 E2 E3 E4 E5 E6.
      apply (hacc_flush_state s0 z0 H k0 s z kk s' z2 len Hm); try lia; try assumption; try reflexivity. }
    destruct (d_pending s - len =? 0) eqn:E1.
    + apply Z.eqb_eq in E1.
      destruct (Hst (set_d_po s2 0)) as [Ha Hz2]; try reflexivity.
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      left. split; [exact E1|]. split; [exact Ha|]. split; [reflexivity|]. split; [exact Hlf|exact Hz2].
    + apply Z.eqb_neq in E1.
      destruct (Hst s2) as [Ha Hz2]; try reflexivity.
      { cbn. rewrite Hpo. reflexivity. }
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      right. split; [exact E1|]. split; [|exact Ha]. cbn. lia.
Qed.

(** [flush_pending(strm); if (s->pending != 0) { s->last_flush = -1; return Z_OK; }] *)
Lemma flush_or_return_mid : forall s0 z0 H k0 s z kk,
  hmid s0 z0 H k0 s z kk ->
  exists s' z' r, c_flush_or_return s z = Some (s', z', r) /\
    d_status s' = d_status s /\ d_gzindex s' = d_gzindex s /\ z_adler z' = z_adler z /\
    match r with
    | None => hmid s0 z0 H k0 s' z' kk /\ d_pending s' = 0
    | Some c => c = Z_OK /\ hret s0 z0 H k0 s' z' kk
    end.
Proof.
  intros s0 z0 H k0 s z kk Hm.
  destruct (flush_mid s0 z0 H k0 s z kk Hm) as [s' [z' [Ef [E1 [E2 [E3 [E4 Hc]]]]]]].
  unfold c_flush_or_return. rewrite Ef. cbn [bind].
  destruct Hc as [[P0 Hm'] | [P0 [Av Ha]]].
  - rewrite P0. cbn [Z.eqb negb]. exists s', z', None.
    split; [reflexivity|]. split; [exact E1|]. split; [exact E2|]. split; [exact E4|]. split; [exact Hm'|exact P0].
  - destruct (d_pending s' =? 0) eqn:EP; [apply Z.eqb_eq in EP; contradiction|]. cbn [negb].
    exists (set_d_last_flush s' (-1)), z', (Some Z_OK).
    split; [reflexivity|]. split; [exact E1|]. split; [exact E2|]. split; [exact E4|].
    split; [reflexivity|]. split; [exact Ha|]. split; [reflexivity|]. split; [exact Av|exact P0].
Qed.

(** The gzip header's bytes are bytes. *)
Lemma gz_hdr_bytes_bytes : forall h xfl, hdr_ok h -> bytes (gz_hdr_bytes (Some h) xfl).
Proof.
  intros h xfl [_ [_ [_ [_ [_ [Hx [Hn Hc]]]]]]].
  assert (U : forall l, bytes (map u8 l)).
  { intros l. apply Forall_map. apply Forall_forall. intros y _. unfold u8. apply Z.mod_pos_bound. lia. }
  assert (L : forall y, 0 <= Z.land y 255 < 256).
  { intros y. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (C : forall o, cstr_ok o -> bytes (cstr_bytes o)).
  { intros [l|] Ho; [|constructor]. destruct (Ho l eq_refl) as [l0 [-> [_ F]]].
    unfold bytes. apply Forall_app. split; [|repeat constructor; lia].
    eapply Forall_impl; [|exact F]. cbn beta. intros; lia. }
  unfold gz_hdr_bytes, gz_body, bytes. rewrite !Forall_app. split; [split; [|split; [|split]]|].
  - apply U.
  - unfold gz_extra_bytes. destruct (gz_extra h) as [x|] eqn:Ex; [|constructor].
    apply Forall_app. split; [apply U|]. apply Forall_sublist. exact (proj2 (Hx x eq_refl)).
  - apply C. exact Hn.
  - apply C. exact Hc.
  - destruct (gz_hcrc h =? 0); [constructor|]. repeat constructor; apply L.
Qed.

(** ** Loops: a measure that decreases on every iteration and stays below 2^40 bounds the run within [FUEL]. *)
Lemma loop2_measure {A B : Type} (body : A -> option (A + B)) (P : A -> Prop) (Q : B -> Prop) (m : A -> Z) :
  (forall a, P a -> 0 <= m a /\ exists r, body a = Some r /\
     match r with inl a' => P a' /\ m a' < m a | inr b => Q b end) ->
  forall d a, P a ->
    (exists b, loop2 d body a = Some (inr b) /\ Q b) \/
    (exists a', loop2 d body a = Some (inl a') /\ P a' /\ m a' <= m a - 2 ^ Z.of_nat d).
Proof.
  intros Hb. induction d as [|d IH]; intros a Ha.
  - cbn [loop2]. destruct (Hb a Ha) as [_ [[a'|b] [E R]]]; rewrite E.
    + right. exists a'. change (2 ^ Z.of_nat 0) with 1. destruct R. split; [reflexivity|]. split; [auto|lia].
    + left. exists b. auto.
  - cbn [loop2]. destruct (IH a Ha) as [[b [E R]]|[a' [E [Ha' Hm]]]]; rewrite E.
    + left. exists b. auto.
    + destruct (IH a' Ha') as [[b [E' R]]|[a'' [E' [Ha'' Hm']]]]; rewrite E'.
      * left. exists b. auto.
      * right. exists a''. split; [reflexivity|]. split; [exact Ha''|].
        rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
Qed.

Lemma loop_measure {A B : Type} (body : A -> option (A + B)) (P : A -> Prop) (Q : B -> Prop) (m : A -> Z) :
  (forall a, P a -> 0 <= m a /\ exists r, body a = Some r /\
     match r with inl a' => P a' /\ m a' < m a | inr b => Q b end) ->
  forall a, P a -> m a < 2 ^ 40 -> exists b, loop FUEL body a = Some b /\ Q b.
Proof.
  intros Hb a Ha Hm. unfold loop.
  destruct (loop2_measure body P Q m Hb FUEL a Ha) as [[b [E R]]|[a' [E [Ha' Hm']]]]; rewrite E.
  - exists b. auto.
  - exfalso. destruct (Hb a' Ha') as [H0 _]. change (Z.of_nat FUEL) with 40 in Hm'. lia.
Qed.
