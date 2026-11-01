(** * flush_pending and FLUSH_BLOCK_ONLY: their part lemmas [fpend_ok] and [fbo_ok] *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDLTCLib.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** Masked reads *)

Lemma mb_definedb_true b lo hi : mb_defined b lo hi -> mb_definedb b lo hi = true.
Proof.
  intros (H0 & H1 & H2). unfold mb_definedb.
  apply andb_true_intro; split; [apply andb_true_intro; split; apply Z.leb_le; lia|].
  apply forallb_forall. intros x Hx. apply in_map_iff in Hx. destruct Hx as (k & <- & Hk).
  apply in_seq in Hk. apply H2. lia.
Qed.

Lemma mb_read_some b lo len :
  0 <= len -> mb_defined b lo (lo + len) -> mb_read b lo len = Some (sublist lo (lo + len) (mb_val b)).
Proof.
  intros Hl Hd. unfold mb_read. rewrite mb_definedb_true by exact Hd.
  replace (0 <=? len) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
Qed.

(** ** bi_flush *)

(** [o', m'] is [o, m] with [k] bytes written at pending. *)
Definition wr_region (o : outbuf) (m : list bool) (o' : outbuf) (m' : list bool) (k : Z) : Prop :=
  Zlength (o_buf o') = Zlength (o_buf o) /\ Zlength m' = Zlength m /\ o_pending o' = o_pending o + k /\
  (forall i, i < o_pending o \/ o_pending o + k <= i ->
     Znth i (o_buf o') = Znth i (o_buf o) /\ Znth i m' = Znth i m) /\
  (forall i, o_pending o <= i < o_pending o + k -> Znth i m' = true /\ 0 <= Znth i (o_buf o') < 256).

Lemma c_put_byte_ok o m c :
  Zlength m = Zlength (o_buf o) -> 0 <= o_pending o < Zlength (o_buf o) ->
  c_put_byte (o, m) c =
    Some (mkOut (upd_Znth (o_pending o) (o_buf o) (u8 c)) (o_pending o + 1) (o_bi_buf o) (o_bi_valid o)
                (o_bi_used o), upd_Znth (o_pending o) m true).
Proof.
  intros Hm Hp. unfold c_put_byte, wr, in_range.
  replace ((0 <=? o_pending o) && (o_pending o <? Zlength (o_buf o))) with true
    by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
  reflexivity.
Qed.

Lemma wr_region_put o m c :
  Zlength m = Zlength (o_buf o) -> 0 <= o_pending o < Zlength (o_buf o) ->
  wr_region o m (mkOut (upd_Znth (o_pending o) (o_buf o) (u8 c)) (o_pending o + 1) (o_bi_buf o) (o_bi_valid o)
                (o_bi_used o)) (upd_Znth (o_pending o) m true) 1.
Proof.
  intros Hm Hp. unfold wr_region; cbn [o_buf o_pending].
  rewrite !upd_Znth_Zlength by lia.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split.
  - intros i Hi. rewrite !upd_Znth_diff' by lia. auto.
  - intros i Hi. assert (i = o_pending o) as -> by lia. rewrite !upd_Znth_same by lia.
    split; [reflexivity|]. unfold u8. apply Z.mod_pos_bound. lia.
Qed.

Lemma wr_region_trans o m o1 m1 o2 m2 k1 k2 :
  0 <= k1 -> 0 <= k2 ->
  wr_region o m o1 m1 k1 -> wr_region o1 m1 o2 m2 k2 -> wr_region o m o2 m2 (k1 + k2).
Proof.
  intros K1 K2 (A1 & A2 & A3 & A4 & A5) (B1 & B2 & B3 & B4 & B5).
  unfold wr_region. rewrite B1, B2, B3, A3. split; [auto|]. split; [auto|]. split; [lia|]. split.
  - intros i Hi. destruct (B4 i ltac:(lia)) as [-> ->]. apply A4. lia.
  - intros i Hi. destruct (Z_lt_le_dec i (o_pending o + k1)).
    + destruct (B4 i ltac:(lia)) as [-> ->]. apply A5. lia.
    + apply B5. lia.
Qed.

Lemma wr_region_0 o m o' :
  o_buf o' = o_buf o -> o_pending o' = o_pending o -> wr_region o m o' m 0.
Proof.
  intros E1 E2. unfold wr_region. rewrite E1, E2. repeat split; auto; lia.
Qed.

Lemma wr_region_set_bits o m o' m' k bb bv :
  wr_region o m o' m' k -> wr_region o m (set_bits o' bb bv) m' k.
Proof. exact (fun H => H). Qed.

Lemma bi_flush_ok o m :
  bits_ok o -> Zlength m = Zlength (o_buf o) -> o_pending o + o_bi_valid o / 8 <= Zlength (o_buf o) ->
  exists o' m',
    c_bi_flush (o, m) = Some (o', m') /\ wr_region o m o' m' (o_bi_valid o / 8) /\
    o_bi_valid o' = o_bi_valid o mod 8 /\ bits_ok o' /\ o_bi_used o' = o_bi_used o.
Proof.
  intros (Hv & Hb & Hp) Hm Hr. unfold c_bi_flush.
  destruct (Z.eqb_spec (o_bi_valid o) 16) as [E16|N16].
  - rewrite E16 in *. cbn in Hr.
    unfold c_put_short. rewrite c_put_byte_ok by lia. cbn [bind].
    rewrite c_put_byte_ok by (cbn [o_buf o_pending]; rewrite ?upd_Znth_Zlength; lia). cbn [bind].
    eexists _, _. split; [reflexivity|]. cbn [o_buf o_pending o_bi_valid o_bi_buf o_bi_used set_bits].
    rewrite E16. split; [|split; [reflexivity|split; [|reflexivity]]].
    + change (16 / 8) with (1 + 1). apply wr_region_set_bits.
      eapply wr_region_trans; [lia|lia|apply (wr_region_put o m (Z.land (o_bi_buf o) 255)); lia|].
      rewrite E16.
      apply (wr_region_put (mkOut _ _ _ _ _) _ (Z.shiftr (u16 (o_bi_buf o)) 8));
        cbn [o_buf o_pending]; rewrite ?upd_Znth_Zlength; lia.
    + unfold bits_ok; cbn. lia.
  - destruct (Z.geb_spec (o_bi_valid o) 8) as [G8|L8].
    + assert (D1 : o_bi_valid o / 8 = 1) by (Z.div_mod_to_equations; lia).
      assert (M1 : o_bi_valid o mod 8 = o_bi_valid o - 8) by (Z.div_mod_to_equations; lia).
      rewrite c_put_byte_ok by lia.
      cbn [bind]. eexists _, _. split; [reflexivity|].
      rewrite D1, M1. cbn [set_bits o_bi_valid o_bi_used o_bi_buf].
      split; [apply wr_region_put; lia|]. split; [reflexivity|]. split; [|reflexivity].
      unfold bits_ok; cbn [set_bits o_bi_valid o_bi_buf o_pending]. split; [lia|]. split; [|lia].
      rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|].
      apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia.
      replace (2 ^ 8 + 0) with (2 ^ 8) by lia. replace (8 + (o_bi_valid o - 8)) with (o_bi_valid o) by lia.
      lia.
    + eexists _, _. split; [reflexivity|].
      assert (D0 : o_bi_valid o / 8 = 0) by (Z.div_mod_to_equations; lia).
      assert (M0 : o_bi_valid o mod 8 = o_bi_valid o) by (Z.div_mod_to_equations; lia).
      rewrite D0, M0. split; [apply wr_region_0; reflexivity|]. split; [reflexivity|].
      split; [unfold bits_ok; lia|reflexivity].
Qed.

Lemma wr_region_mb_ok o m o' m' k :
  mb_ok (mkMB (o_buf o) m) -> wr_region o m o' m' k -> mb_ok (mkMB (o_buf o') m').
Proof.
  intros (H1 & H2) (W1 & W2 & W3 & W4 & W5). cbn [mb_val mb_def] in *. unfold mb_ok; cbn [mb_val mb_def]. split; [lia|].
  intros i Hi Hd. destruct (Z_lt_le_dec i (o_pending o)) as [L1|G1].
  - destruct (W4 i (or_introl L1)) as [E1 E2]. rewrite E1. rewrite E2 in Hd. apply H2; auto. lia.
  - destruct (Z_lt_le_dec i (o_pending o + k)) as [L2|G2].
    + apply W5. lia.
    + destruct (W4 i (or_intror G2)) as [E1 E2]. rewrite E1. rewrite E2 in Hd. apply H2; auto. lia.
Qed.

Lemma wr_region_grow o m o' m' k :
  mb_ok (mkMB (o_buf o) m) -> wr_region o m o' m' k -> pb_grow o m o' m'.
Proof.
  intros Hm Hw. pose proof (wr_region_mb_ok _ _ _ _ _ Hm Hw) as Hm'.
  destruct Hw as (W1 & W2 & W3 & W4 & W5). unfold pb_grow.
  split; [exact W1|]. split; [exact W2|]. split; [|intros _; exact Hm'].
  intros i Hi. destruct (Z_lt_le_dec i (o_pending o)) as [L1|G1].
  - destruct (W4 i (or_introl L1)) as [_ ->]. exact Hi.
  - destruct (Z_lt_le_dec i (o_pending o + k)) as [L2|G2].
    + apply W5. lia.
    + destruct (W4 i (or_intror G2)) as [_ ->]. exact Hi.
Qed.

Lemma mb_bytes b lo hi : mb_ok b -> mb_defined b lo hi -> bytes (sublist lo hi (mb_val b)).
Proof.
  intros (H1 & H2) (D1 & D2 & D3). unfold bytes.
  destruct (Z_le_gt_dec lo hi) as [Le|Gt]; [|rewrite sublist_nil_gen by lia; constructor].
  apply Forall_forall. intros x Hx.
  apply In_Znth in Hx. destruct Hx as (j & Hj & <-).
  rewrite Zlength_sublist in Hj by lia.
  rewrite Znth_sublist by lia. apply H2; [lia|]. apply D3. lia.
Qed.

(** ** flush_pending *)

(** The precondition fix: the bytes bi_flush adds fit, and they are written
    at pending_buf[pending], which is the end of the pending bytes only when pending_out is at the start. *)
Definition fp_room (s : dstate) : Prop :=
  d_bi_valid s < 8 \/ (d_po s = 0 /\ bitpos (tr_out (d_tr s)) <= 8 * d_pending_buf_size s).

Definition fpend_concl (s : dstate) (z : strm) : Prop :=
  exists s' z' x,
    c_flush_pending s z = Some (s', z') /\ zout_only z z' x /\ bytes x /\
    Zlength x = Z.min (d_pending s + d_bi_valid s / 8) (z_avail_out z) /\
    d_pending s' = d_pending s + d_bi_valid s / 8 - Zlength x /\
    d_bi_valid s' = d_bi_valid s mod 8 /\
    outok s' /\ Gb s' (z_total_out z') = Gb s (z_total_out z) /\
    fp_keep s' = fp_keep s /\
    pb_grow (tr_out (d_tr s)) (d_pbm s) (tr_out (d_tr s')) (d_pbm s').

Lemma prm_pbsize s :
  prm s -> d_pending_buf_size s = Zlength (o_buf (tr_out (d_tr s))) /\ d_pending_buf_size s <= 131072.
Proof.
  intros (_ & _ & _ & Hhb & _ & _ & _ & HL & Hps & Hob & _).
  rewrite Hps, Hob. split; [reflexivity|]. rewrite HL.
  assert (2 ^ (d_hash_bits s - 1) <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Lemma fp_keep_set_d_out s o : fp_keep (set_d_out s o) = fp_keep s.
Proof. destruct s as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? t ?]. destruct t. reflexivity. Qed.

Lemma fp_keep_set_d_po s v : fp_keep (set_d_po s v) = fp_keep s.
Proof. reflexivity. Qed.

(** Projections of the setters (definitional). *)
Lemma pj_out_tr s o m : tr_out (d_tr (set_d_out s (o, m))) = o. Proof. reflexivity. Qed.
Lemma pj_out_pbm s o m : d_pbm (set_d_out s (o, m)) = m. Proof. reflexivity. Qed.
Lemma pj_out_po s om : d_po (set_d_out s om) = d_po s. Proof. reflexivity. Qed.
Lemma pj_out_pending s o m : d_pending (set_d_out s (o, m)) = o_pending o. Proof. reflexivity. Qed.
Lemma pj_out_bv s o m : d_bi_valid (set_d_out s (o, m)) = o_bi_valid o. Proof. reflexivity. Qed.
Lemma pj_out_pbs s om : d_pending_buf_size (set_d_out s om) = d_pending_buf_size s. Proof. reflexivity. Qed.
Lemma pj_po_tr s v : d_tr (set_d_po s v) = d_tr s. Proof. reflexivity. Qed.
Lemma pj_po_pbm s v : d_pbm (set_d_po s v) = d_pbm s. Proof. reflexivity. Qed.
Lemma pj_po_po s v : d_po (set_d_po s v) = v. Proof. reflexivity. Qed.
Lemma pj_po_pbs s v : d_pending_buf_size (set_d_po s v) = d_pending_buf_size s. Proof. reflexivity. Qed.
Lemma pj_po_pending s v : d_pending (set_d_po s v) = d_pending s. Proof. reflexivity. Qed.
Lemma pj_po_bv s v : d_bi_valid (set_d_po s v) = d_bi_valid s. Proof. reflexivity. Qed.

Ltac pj := repeat progress rewrite ?pj_out_tr, ?pj_out_pbm, ?pj_out_po, ?pj_out_pending, ?pj_out_bv, ?pj_out_pbs,
  ?pj_po_tr, ?pj_po_pbm, ?pj_po_po, ?pj_po_pbs, ?pj_po_pending, ?pj_po_bv in *.

Lemma fpend_ok s z :
  d_pending_buf_size s = Zlength (o_buf (tr_out (d_tr s))) -> d_pending_buf_size s <= 131072 ->
  outok s -> zout_ok z -> fp_room s -> fpend_concl s z.
Proof.
  intros Hps Hpb Hok Hz Hroom.
  destruct Hok as (Hmb & Hbits & Hpo & Hpe & Hdef & Hp0).
  unfold fp_room, d_pb, d_pending, d_bi_valid in *.
  set (o := tr_out (d_tr s)) in *. set (m := d_pbm s) in *.
  assert (Hm : Zlength m = Zlength (o_buf o)) by (destruct Hmb as [Hm _]; exact Hm).
  assert (Hr : o_pending o + o_bi_valid o / 8 <= Zlength (o_buf o)).
  { destruct Hbits as (Hv & _ & Hp). destruct Hroom as [Hlt|[_ Hle]].
    - assert (o_bi_valid o / 8 = 0) by (Z.div_mod_to_equations; lia). lia.
    - unfold bitpos in Hle. fold o in Hle. Z.div_mod_to_equations; lia. }
  assert (K : 0 <= o_bi_valid o / 8 <= 2) by (destruct Hbits as (? & _); Z.div_mod_to_equations; lia).
  destruct (bi_flush_ok o m Hbits Hm Hr) as (o' & m' & Hbf & Hwr & Hbv' & Hbits' & Hused).
  unfold fpend_concl, c_flush_pending, d_out, c_tr_flush_bits. fold o m. rewrite Hbf. cbn [bind].
  pj.
  destruct Hwr as (W1 & W2 & W3 & W4 & W5).
  assert (Hlen : (if o_pending o' >? z_avail_out z then z_avail_out z else u32 (o_pending o')) =
                 Z.min (o_pending o') (z_avail_out z)).
  { destruct (Z.gtb_spec (o_pending o') (z_avail_out z)); [lia|].
    unfold u32. rewrite Z.mod_small by (destruct Hbits as (_ & _ & ?); lia). lia. }
  assert (Hk : o_bi_valid o / 8 = 0 \/ d_po s = 0).
  { destruct Hroom as [Hlt|[? _]]; [left; Z.div_mod_to_equations; lia|right; auto]. }
  assert (Hd' : mb_defined (mkMB (o_buf o') m') (d_po s) (d_po s + o_pending o')).
  { destruct Hdef as (D1 & D2 & D3). unfold mb_defined. cbn [mb_val mb_def] in *.
    split; [lia|]. split; [destruct Hk as [Hk|Hk]; [rewrite W1; lia|rewrite W1, Hk; lia]|].
    intros i Hi. destruct (Z_lt_le_dec i (o_pending o + o_bi_valid o / 8)) as [Lt|Ge].
    - destruct (Z_lt_le_dec i (o_pending o)) as [Lt2|Ge2].
      + destruct (W4 i (or_introl Lt2)) as [_ ->]. apply D3. lia.
      + apply W5. lia.
    - destruct (W4 i (or_intror Ge)) as [_ ->]. apply D3. destruct Hk as [Hk|Hk]; lia. }
  assert (Hbv8 : o_bi_valid o / 8 = 0 \/ d_po s = 0 /\ o_pending o' <= d_pending_buf_size s).
  { destruct Hk as [Hk|Hk]; [left; exact Hk|right; split; [exact Hk|lia]]. }
  assert (Hwr : wr_region o m o' m' (o_bi_valid o / 8)) by exact (conj W1 (conj W2 (conj W3 (conj W4 W5)))).
  pose proof (wr_region_mb_ok o m o' m' _ Hmb Hwr) as Hmb'.
  pose proof (wr_region_grow o m o' m' _ Hmb Hwr) as Hgrow.
  assert (Hbvd : o_bi_valid o = 8 * (o_bi_valid o / 8) + o_bi_valid o mod 8) by (apply Z.div_mod; lia).
  change (d_pending s) with (o_pending o). change (d_bi_valid s) with (o_bi_valid o).
  replace (Gb s (z_total_out z)) with (8 * (z_total_out z + o_pending o) + o_bi_valid o) by reflexivity.
  clearbody o m.
  rewrite Hlen. set (len := Z.min (o_pending o') (z_avail_out z)).
  assert (Elen : len = Z.min (o_pending o') (z_avail_out z)) by reflexivity. clearbody len.
  assert (Hlen0 : 0 <= len <= o_pending o') by (destruct Hz; destruct Hbits' as (_ & _ & ?); lia).
  destruct (Z.eqb_spec len 0) as [L0|L0].
  - exists (set_d_out s (o', m')), z, []. split; [reflexivity|].
    split; [unfold zout_only; rewrite app_nil_r, Zlength_nil; repeat split; lia|].
    split; [constructor|]. rewrite Zlength_nil. split; [lia|]. pj.
    split; [lia|]. split; [exact Hbv'|].
    split; [|split; [unfold Gb; pj; lia|]].
    + unfold outok, d_pb. pj. split; [exact Hmb'|]. split; [exact Hbits'|]. split; [lia|].
      split; [destruct Hbv8 as [E|[E1 E2]]; [rewrite W3, E, Z.add_0_r, Hps; rewrite Hps in Hpe; lia|lia]|].
      split; [exact Hd'|]. intros E. destruct Hk as [Hk|Hk]; [apply Hp0; lia|exact Hk].
    + split; [apply fp_keep_set_d_out|]. pj. exact Hgrow.
  - rewrite mb_read_some
      by (lia || (destruct Hd' as (D1 & D2 & D3); split; [lia|split; [lia|intros i Hi; apply D3; lia]])).
    cbn [bind]. unfold out_put. rewrite Zlength_sublist by (destruct Hd' as (D1 & D2 & D3); cbn in *; lia).
    replace (d_po s + len - d_po s <=? z_avail_out z) with true
      by (symmetry; apply Z.leb_le; destruct Hz; lia).
    cbn [bind]. pj. cbn [o_pending o_buf o_bi_buf o_bi_valid o_bi_used mb_val].
    assert (Hx : bytes (sublist (d_po s) (d_po s + len) (o_buf o'))).
    { apply (mb_bytes (mkMB (o_buf o') m')); [exact Hmb'|].
      destruct Hd' as (D1 & D2 & D3). split; [lia|split; [lia|intros i Hi; apply D3; lia]]. }
    assert (Hxl : Zlength (sublist (d_po s) (d_po s + len) (o_buf o')) = len)
      by (destruct Hd' as (D1 & D2 & D3); cbn in D2; rewrite Zlength_sublist by lia; lia).
    assert (Htot : u64 (z_total_out z + len) = z_total_out z + len)
      by (apply u64_id; destruct Hz as (? & ? & ?); lia).
    destruct (Z.eqb_spec (o_pending o' - len) 0) as [P0|P0];
      eexists _, _, (sublist (d_po s) (d_po s + len) (o_buf o')); split; try reflexivity;
      (split; [unfold zout_only; cbn [z_in z_next_in z_avail_in z_total_in z_adler z_msg z_out z_avail_out
                 z_total_out set_z_avail_out set_z_total_out set_z_out]; rewrite Hxl, Htot;
               repeat split; reflexivity|]);
      (split; [exact Hx|]); rewrite Hxl; (split; [lia|]); pj; cbn [o_pending o_bi_valid];
      (split; [lia|]); (split; [exact Hbv'|]).
    + split; [|split; [unfold Gb; pj; cbn [o_pending o_bi_valid set_z_avail_out set_z_total_out set_z_out z_total_out];
                       rewrite Htot; lia|]].
      * unfold outok, d_pb. pj. cbn [o_pending o_buf]. split; [exact Hmb'|].
        split; [destruct Hbits' as (B1 & B2 & B3); unfold bits_ok; cbn; lia|]. split; [lia|].
        split; [lia|]. split; [|intros _; reflexivity].
        destruct Hd' as (D1 & D2 & D3). split; [lia|]. split; [cbn [mb_val mb_def] in *; lia|]. intros; lia.
      * rewrite fp_keep_set_d_po, fp_keep_set_d_out, fp_keep_set_d_po, fp_keep_set_d_out. split; [reflexivity|].
        pj. destruct Hgrow as (G1 & G2 & G3 & G4). split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
        intros _. exact Hmb'.
    + split; [|split; [unfold Gb; pj; cbn [o_pending o_bi_valid set_z_avail_out set_z_total_out set_z_out z_total_out];
                       rewrite Htot; lia|]].
      * unfold outok, d_pb. pj. cbn [o_pending o_buf]. split; [exact Hmb'|].
        split; [destruct Hbits' as (B1 & B2 & B3); unfold bits_ok; cbn; lia|]. split; [lia|].
        split; [destruct Hbv8 as [E|[E1 E2]]; [rewrite W3, E, Z.add_0_r, Hps; rewrite Hps in Hpe; lia|lia]|].
        split; [|intros E; lia].
        destruct Hd' as (D1 & D2 & D3). unfold mb_defined. cbn [mb_val mb_def] in *. split; [lia|]. split; [lia|]. intros i Hi; apply D3; lia.
      * rewrite fp_keep_set_d_out, fp_keep_set_d_po, fp_keep_set_d_out. split; [reflexivity|].
        pj. destruct Hgrow as (G1 & G2 & G3 & G4). split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
        intros _. exact Hmb'.
Qed.

(** ** FLUSH_BLOCK_ONLY *)

(** The addition to trflush_spec: the bits after _tr_flush_block fit in
    pending_buf (so that flush_pending's bi_flush has room). *)
Definition trflush_room : Prop :=
  forall t m syms buf sl last t' m' kind,
    flush_pre t syms -> tree_ok t m syms -> 0 < tr_level t -> 0 <= last <= 1 ->
    mb_ok (mkMB (o_buf (tr_out t)) m) -> sl = blk_len syms ->
    match buf with Some b => Zlength b = sl /\ bytes b /\ sl <= 65535 | None => True end ->
    c_tr_flush_block (t, m) buf sl last = Some ((t', m'), kind) ->
    bitpos (tr_out t') <= 8 * Zlength (o_buf (tr_out t')).

Lemma tree_ok_nil_set t m t2 m2 e :
  tree_ok t m [] -> set_out t2 e = set_out t e ->
  Zlength (o_buf (tr_out t2)) = Zlength (o_buf (tr_out t)) -> Zlength m2 = Zlength m -> tree_ok t2 m2 [].
Proof.
  intros H E L1 L2.
  destruct t as [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15],
           t2 as [b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15].
  unfold set_out in E. cbn [tr_ltree tr_dtree tr_bltree tr_lmax tr_dmax tr_blmax tr_wk tr_out tr_sym_next
    tr_sym_end tr_matches tr_lit_bufsize tr_level tr_strategy tr_data_type] in E.
  injection E; intros; subst. unfold tree_ok in *.
  cbn [tr_ltree tr_dtree tr_bltree tr_wk tr_out tr_sym_next tr_lit_bufsize] in *.
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
  rewrite Zlength_nil, Z.mul_0_r, Z.add_0_r, !sublist_nil in *.
  split; [lia|]. split; [lia|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|].
  auto.
Qed.

Lemma fbo_ok : trflush_spec -> trflush_room -> fbo_spec.
Proof.
  intros TF TR s z syms last Hpre.
  destruct Hpre as (Hprm & Hws & Hlev & Htok & HsL & Hblk & Hbs & Hbs24 & Hwin & Hok & Hq & Hlast & Hz).
  pose proof (prm_pbsize s Hprm) as [Hpbs Hpb].
  pose proof (flush_pre_of s syms Hprm Htok HsL Hok Hq) as Hfp.
  unfold c_flush_block_only.
  replace (in_long (d_strstart s - d_block_start s)) with true
    by (symmetry; unfold in_long; apply andb_true_intro; split; apply Z.leb_le; lia).
  cbn [guard bind]. rewrite u64_id by lia.
  set (sl := d_strstart s - d_block_start s) in *.
  assert (Hsl : 0 <= sl <= 16777216) by lia.
  assert (Esl : sl = d_strstart s - d_block_start s) by reflexivity.
  clearbody sl.
  (* the window bytes *)
  assert (Hbuf : exists buf,
    (if d_block_start s >=? 0
     then let* b := mb_read (d_window s) (d_block_start s) sl in Some (Some b) else Some None) = Some buf /\
    (0 <= d_block_start s -> exists b, buf = Some b /\ Zlength b = sl /\ bytes b) /\
    (d_block_start s < 0 -> buf = None) /\
    match buf with Some b => Zlength b = sl /\ bytes b /\ sl <= 65535 | None => True end).
  { destruct (Z.geb_spec (d_block_start s) 0) as [Bp|Bn].
    - destruct (Hwin ltac:(lia)) as (W1 & W2 & W3).
      destruct Hws as (_ & Hwok & _).
      assert (Hd : mb_defined (d_window s) (d_block_start s) (d_block_start s + sl)).
      { split; [lia|]. split; [lia|]. intros i Hi. apply W3. lia. }
      rewrite mb_read_some by (lia || exact Hd). cbn [bind].
      assert (Hb : bytes (sublist (d_block_start s) (d_block_start s + sl) (mb_val (d_window s))))
        by (apply mb_bytes; auto).
      assert (Hl : Zlength (sublist (d_block_start s) (d_block_start s + sl) (mb_val (d_window s))) = sl)
        by (rewrite Zlength_sublist by lia; lia).
      eexists. split; [reflexivity|]. split; [intros _; eexists; split; [reflexivity|]; auto|].
      split; [intros; lia|]. split; [exact Hl|]. split; [exact Hb|lia].
    - eexists. split; [reflexivity|]. split; [intros; lia|]. split; [reflexivity|exact I]. }
  destruct Hbuf as (buf & Ebuf & Hb1 & Hb2 & Hb3). rewrite Ebuf. cbn [bind].
  (* _tr_flush_block *)
  destruct Hok as (Hmb & Hbits & Hpo & Hpe & Hdef & Hp0).
  destruct (TF (d_tr s) (d_pbm s) syms buf sl last Hfp Htok Hlev Hlast Hmb ltac:(lia) Hb3)
    as (t' & m' & kind & Hcall & Heq & Htok' & Hcfg & Hmat & Hbits' & Hlast' & Hgrow & Hdef').
  pose proof (TR (d_tr s) (d_pbm s) syms buf sl last t' m' kind Hfp Htok Hlev Hlast Hmb ltac:(lia) Hb3 Hcall)
    as Hroom.
  unfold d_trm. rewrite Hcall. cbn [bind].
  change (d_strstart (set_d_trm s (t', m'))) with (d_strstart s).
  set (s1 := set_d_block_start (set_d_trm s (t', m')) (d_strstart s)).
  assert (E1 : d_tr s1 = t') by reflexivity. assert (E2 : d_pbm s1 = m') by reflexivity.
  assert (E3 : d_po s1 = d_po s) by reflexivity.
  assert (E4 : d_pending_buf_size s1 = d_pending_buf_size s) by reflexivity.
  destruct Hq as (Hq1 & Hq2 & Hq3).
  destruct Hgrow as (G1 & G2 & G3 & G4).
  destruct Hdef' as (D1 & D2 & D3). cbn [mb_val mb_def] in D2, D3.
  assert (Hs1 : outok s1).
  { unfold outok, d_pb, d_pending. rewrite E1, E2, E3, E4, Hq2.
    split; [apply G4, Hmb|]. split; [exact Hbits'|]. split; [lia|]. split; [lia|].
    split; [split; [lia|split; [cbn [mb_val]; lia|exact D3]]|]. intros; reflexivity. }
  assert (Hr1 : fp_room s1).
  { right. rewrite E3, E1, E4. split; [exact Hq2|lia]. }
  destruct (fpend_ok s1 z ltac:(rewrite E4, E1; lia) ltac:(rewrite E4; lia) Hs1 Hz Hr1)
    as (s' & z' & x & Hfp1 & Hzo & Hx & Hxl & Hpend & Hbv & Hok' & HGb & Hkeep & Hgrow').
  exists s', z', x, buf. split; [exact Hfp1|]. split; [exact Hb1|]. split; [exact Hb2|].
  split; [exact Hzo|]. split; [exact Hx|].
  split.
  { rewrite HGb. cbn [ev_after]. rewrite <- Heq. cbn [fst].
    unfold Gb, bitpos, d_pending, d_bi_valid. rewrite E1. lia. }
  split; [change (fbo_keep s') with (fbo_keep (fp_keep s')); rewrite Hkeep; reflexivity|].
  split; [change (d_block_start s') with (d_block_start (fp_keep s')); rewrite Hkeep; reflexivity|].
  destruct Hgrow' as (G1' & G2' & G3' & G4').
  split.
  { apply (tree_ok_nil_set t' m' (d_tr s') (d_pbm s') (mkOut [] 0 0 0 0) Htok').
    - change (set_out (d_tr s') (mkOut [] 0 0 0 0)) with (d_tr (fp_keep s')). rewrite Hkeep. reflexivity.
    - rewrite G1', E1. reflexivity.
    - rewrite G2', E2. reflexivity. }
  split; [change (tr_cfg (d_tr s')) with (tr_cfg (d_tr (fp_keep s'))); rewrite Hkeep; exact Hcfg|].
  split; [change (d_matches s') with (tr_matches (d_tr (fp_keep s'))); rewrite Hkeep; exact Hmat|].
  split; [exact Hok'|].
  assert (Hbv1 : d_bi_valid s1 = o_bi_valid (tr_out t')) by reflexivity.
  split; [rewrite Hbv, Hbv1; pose proof (Z.mod_pos_bound (o_bi_valid (tr_out t')) 8); lia|].
  split; [intros L1; rewrite Hbv, Hbv1, (Hlast' L1); reflexivity|].
  destruct Hzo as (_ & _ & _ & _ & _ & _ & _ & Za & _). lia.
Qed.

(** fpend_spec with the precondition fix ([prm s] and [fp_room s]). *)
Lemma fpend_fixed_ok s z : prm s -> outok s -> zout_ok z -> fp_room s -> fpend_concl s z.
Proof.
  intros Hp Ho Hz Hr. destruct (prm_pbsize s Hp) as [E B]. exact (fpend_ok s z E B Ho Hz Hr).
Qed.
