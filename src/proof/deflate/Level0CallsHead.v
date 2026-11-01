(** * Level 0 over several deflate() calls: the stages of deflate() around deflate_stored

    [Level0Head.l0_head] and [Level0Trail.l0_trail] follow the entry and header stages, and the trailer, of one
    deflate(Z_FINISH) call with 32-bit counters.  Here the same stages for the calls of the harnesses' loop:
    - [l0c_entry], [l0c_head]: the first call (on the state deflateInit2_ left) with Z_NO_FLUSH (some input
      offered) or Z_FINISH writes the wrapper header and flushes it;
    - [l0c_busy]: a later call (status BUSY, nothing pending, some input offered) passes the entry and header
      stages unchanged but for last_flush;
    - [l0c_trail]: the trailer of the last call, with total_out up to 2^64 - 1. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.Level0Stmts.
Require Import Zlib.proof.deflate.LTHdrStages.
Require Import Zlib.proof.deflate.LTApiEntry.
Require Import Zlib.proof.deflate.Level0Head.
Require Import Zlib.proof.deflate.Level0Trail.
Require Import Zlib.proof.deflate.Level0Stored.
Require Import Zlib.proof.deflate.LTCSpecs.
Import ListNotations.
Local Open Scope Z_scope.

(** deflate()'s entry stage on a state that is not FINISH, with nothing pending and room in the output: it
    records the flush in [last_flush], when input is offered or the flush is the first Z_FINISH after
    deflateInit2_. *)
Lemma l0c_entry s z flush :
  d_status s <> FINISH_STATE -> d_pending s = 0 -> 0 < z_avail_out z ->
  (z_avail_in z <> 0 \/ (flush = Z_FINISH /\ d_last_flush s = -2)) ->
  c_deflate_entry s z flush = Some (set_d_last_flush s flush, z, None).
Proof.
  intros Hst P0 Hav Hin. unfold c_deflate_entry.
  apply Z.eqb_neq in Hst. rewrite Hst. cbn [andb].
  replace (z_avail_out z =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  change (d_pending (set_d_last_flush s flush)) with (d_pending s). rewrite P0. cbn [Z.eqb negb].
  change (d_status (set_d_last_flush s flush)) with (d_status s).
  destruct (Z.eqb_spec (z_avail_in z) 0) as [E0|E0].
  - destruct Hin as [Hin|[-> Hlf]]; [contradiction|]. rewrite Hlf. cbn. rewrite Hst. reflexivity.
  - cbn. rewrite Hst. reflexivity.
Qed.

(** The first call: the entry stage and the header stages on the state deflateInit2_ leaves. *)
Lemma l0c_head s z flush :
  prm s -> outok s -> d_pending s = 0 -> d_po s = 0 -> d_bi_valid s = 0 -> d_sym_next s = 0 ->
  d_strstart s = 0 -> d_gzhead s = None -> d_last_flush s = -2 -> 0 <= d_wrap s <= 2 ->
  d_status s = (if d_wrap s =? 2 then GZIP_STATE else INIT_STATE) ->
  (z_avail_in z <> 0 \/ flush = Z_FINISH) ->
  hdr_len (d_wrap s) < z_avail_out z <= 4294967295 -> 0 <= z_total_out z <= 1099511627776 ->
  exists s2 z2 H,
    then_stage (c_deflate_entry s z flush) hdr_stages = Some (s2, z2, None) /\
    core_eq s s2 /\ outok s2 /\ d_pending s2 = 0 /\ d_po s2 = 0 /\ d_bi_valid s2 = 0 /\
    d_status s2 = BUSY_STATE /\ d_wrap s2 = d_wrap s /\ d_gzhead s2 = None /\
    Zlength H = hdr_len (d_wrap s) /\ bytes H /\ z_out z2 = z_out z ++ H /\
    z_in z2 = z_in z /\ z_next_in z2 = z_next_in z /\ z_avail_in z2 = z_avail_in z /\
    z_total_in z2 = z_total_in z /\ z_msg z2 = z_msg z /\
    z_avail_out z2 = z_avail_out z - hdr_len (d_wrap s) /\
    z_total_out z2 = z_total_out z + hdr_len (d_wrap s) /\
    z_adler z2 = (if d_wrap s =? 1 then 1 else if d_wrap s =? 2 then 0 else z_adler z).
Proof.
  intros Hp Ho P0 Po Hbv Hsn Hss Hgz Hlf Hw Hst Hin Hav Ht.
  assert (Hhl : 0 <= hdr_len (d_wrap s) <= 10)
    by (unfold hdr_len; destruct (d_wrap s =? 0); [lia|destruct (d_wrap s =? 1); lia]).
  assert (Hnf : d_status s <> FINISH_STATE)
    by (rewrite Hst; destruct (d_wrap s =? 2); discriminate).
  rewrite (l0c_entry s z flush Hnf P0 ltac:(lia) ltac:(destruct Hin; [left|right]; auto)).
  cbn [then_stage bind].
  set (s1 := set_d_last_flush s flush).
  assert (Hc1 : core_eq s s1) by apply ent_core_eq_lf.
  rewrite hdr_stages_eq.
  destruct (Z.eq_dec (d_wrap s) 2) as [W2|W2].
  - (* gzip, no user header: 10 bytes *)
    rewrite W2 in Hst. cbn [Z.eqb Pos.eqb] in Hst.
    rewrite zlib_id by (change (d_status s1) with (d_status s); rewrite Hst; discriminate).
    cbn [then_stage bind].
    destruct (gzip_stage s1 z Hp Ho P0 Hsn Hbv ltac:(lia) Ht Hst W2
                ltac:(intros h E; change (d_gzhead s1) with (d_gzhead s) in E; congruence))
      as [s' [z' [r [E [[_ Hge]|[Es Hpost]]]]]].
    + exfalso. destruct Hge as [_ [_ [h [xfl [Eh [_ [_ [_ [Hm _]]]]]]]]].
      destruct Hm as [[_ [_ [_ [_ [_ [_ [_ [Hg0 _]]]]]]]] _].
      change (d_gzhead s1) with (d_gzhead s) in Hg0. congruence.
    + change (d_gzhead s1) with (d_gzhead s) in Hpost. rewrite Hgz in Hpost.
      assert (LH : Zlength (gz_hdr_bytes None (xfl_byte s1)) = 10) by reflexivity.
      assert (Hhl2 : hdr_len (d_wrap s) = 10) by (rewrite W2; reflexivity).
      destruct (l0_post _ _ _ _ _ _ Hpost ltac:(lia))
        as [-> [Hc [Ho' [Hw' [Hbv' [Hs' [P0' [Po' Hz]]]]]]]].
      destruct Hpost as (_ & _ & _ & Hg' & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & Had & _)).
      rewrite E. cbn [then_stage bind].
      destruct (busy_rest s' z' Hs') as [_ B]. rewrite B.
      destruct (l0_zout _ _ _ _ Hz Ht ltac:(lia)) as [Eo [Ei [En [Ea [Eti [Em [Eao Eto]]]]]]].
      exists s', z', (gz_hdr_bytes None (xfl_byte s1)).
      split; [reflexivity|].
      split; [eapply ent_core_eq_trans; [exact Hc1|exact Hc]|].
      split; [exact Ho'|]. split; [exact P0'|]. split; [exact Po'|].
      split; [rewrite Hbv'; exact Hbv|]. split; [exact Hs'|]. split; [exact Hw'|].
      split; [rewrite Hg'; exact Hgz|].
      rewrite LH, Hhl2. split; [reflexivity|].
      split; [unfold gz_hdr_bytes, xfl_byte, OS_CODE, bytes;
              destruct (d_level s1 =? 9); [|destruct (_ || _)]; repeat constructor; lia|].
      repeat split; try assumption.
  - (* raw (no header) or zlib (2 bytes, no dictionary) *)
    assert (W2' : (d_wrap s =? 2) = false) by (apply Z.eqb_neq; exact W2).
    rewrite W2' in Hst.
    destruct (zlib_stage s1 z Hp Ho P0 Hsn Hbv ltac:(lia) Ht Hst ltac:(change (d_wrap s1) with (d_wrap s); lia))
      as [s' [z' [r [E [Es Hpost]]]]].
    set (H := hdr_bytes s1 (z_adler z)) in Hpost.
    assert (LH : Zlength H = hdr_len (d_wrap s)).
    { unfold H, hdr_bytes, zlib_hdr_bytes. change (d_wrap s1) with (d_wrap s).
      change (d_strstart s1) with (d_strstart s). rewrite Hss.
      destruct (Z.eq_dec (d_wrap s) 0) as [W0|W0].
      - rewrite W0. reflexivity.
      - replace (d_wrap s) with 1 by lia. reflexivity. }
    destruct (l0_post _ _ _ _ _ _ Hpost ltac:(lia))
      as [-> [Hc [Ho' [Hw' [Hbv' [Hs' [P0' [Po' Hz]]]]]]]].
    destruct Hpost as (_ & _ & _ & Hg' & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & Had & _)).
    rewrite E. cbn [then_stage bind].
    destruct (busy_rest s' z' Hs') as [B _]. rewrite B.
    destruct (l0_zout _ _ _ _ Hz Ht ltac:(lia)) as [Eo [Ei [En [Ea [Eti [Em [Eao Eto]]]]]]].
    exists s', z', H.
    split; [reflexivity|].
    split; [eapply ent_core_eq_trans; [exact Hc1|exact Hc]|].
    split; [exact Ho'|]. split; [exact P0'|]. split; [exact Po'|].
    split; [rewrite Hbv'; exact Hbv|]. split; [exact Hs'|]. split; [exact Hw'|].
    split; [rewrite Hg'; exact Hgz|].
    rewrite LH in *. split; [reflexivity|].
    split.
    { unfold H, hdr_bytes. change (d_wrap s1) with (d_wrap s). unfold bytes.
      destruct (Z.eqb_spec (d_wrap s) 1).
      - unfold zlib_hdr_bytes, msb2. change (d_strstart s1) with (d_strstart s). rewrite Hss. cbn [Z.eqb app].
        repeat (apply Forall_cons; [apply u8_range|]). apply Forall_nil.
      - destruct (Z.eqb_spec (d_wrap s) 2); [contradiction|]. apply Forall_nil. }
    repeat split; try assumption.
Qed.

(** A later call: status BUSY, nothing pending, some input offered. *)
Lemma l0c_busy s z flush :
  d_status s = BUSY_STATE -> d_pending s = 0 -> 0 < z_avail_out z -> z_avail_in z <> 0 ->
  then_stage (c_deflate_entry s z flush) hdr_stages = Some (set_d_last_flush s flush, z, None).
Proof.
  intros Hst P0 Hav Hin.
  rewrite (l0c_entry s z flush ltac:(rewrite Hst; discriminate) P0 Hav (or_introl Hin)).
  cbn [then_stage bind]. rewrite hdr_stages_eq.
  rewrite zlib_id by (change (d_status (set_d_last_flush s flush)) with (d_status s); rewrite Hst; discriminate).
  cbn [then_stage bind].
  destruct (busy_rest (set_d_last_flush s flush) z ltac:(exact Hst)) as [B _]. exact B.
Qed.

(** ** The trailer with total_out up to 2^64 - 1 (as [Level0Trail.l0_trail]) *)

(** The defined bytes of pending_buf are bytes. *)
Lemma bytes_sub_defined b m lo hi : mb_ok (mkMB b m) -> mb_defined (mkMB b m) lo hi -> bytes (sublist lo hi b).
Proof.
  intros [Hl Hok] (H0 & H1 & Hd). cbn [mb_val mb_def] in *. unfold bytes.
  apply Forall_forall. intros x Hx. apply In_Znth in Hx. destruct Hx as (i & Hi & <-).
  assert (lo <= hi \/ hi < lo) as [Le|Lt] by lia.
  - rewrite Zlength_sublist in Hi by lia. rewrite Znth_sublist by lia. apply Hok; [lia|]. apply Hd; lia.
  - rewrite sublist_nil_gen in Hi by lia. rewrite Zlength_nil in Hi. lia.
Qed.

(** put_byte stores [u8 c]: pending_buf's defined bytes stay bytes. *)
Lemma l0c_dput_bytes_ok l s s1 : c_dput_bytes s l = Some s1 -> mb_ok (d_pb s) -> mb_ok (d_pb s1).
Proof.
  revert s. induction l as [|c l IH]; intros s E Hok; cbn [c_dput_bytes] in E.
  - inversion E; subst; auto.
  - destruct (c_dput_byte s c) as [s2|] eqn:E1; cbn [bind] in E; [|discriminate].
    apply (IH s2 E). clear E IH.
    unfold c_dput_byte, c_put_byte, d_out in E1. cbn [fst snd] in E1.
    unfold wr, in_range in E1.
    destruct ((0 <=? o_pending (tr_out (d_tr s))) && (o_pending (tr_out (d_tr s)) <? Zlength (o_buf (tr_out (d_tr s)))))
      eqn:R; cbn [bind] in E1; [|discriminate].
    apply andb_true_iff in R. destruct R as [R1 R2]. apply Z.leb_le in R1. apply Z.ltb_lt in R2.
    inversion E1; subst s2. unfold d_pb in *.
    cbn [set_d_out fst snd set_d_pbm set_d_tr set_out d_tr d_pbm tr_out o_buf].
    apply mb_ok_upd; auto. apply u8_range.
Qed.


Lemma l0c_flush_all : forall s z,
  d_bi_valid s = 0 -> d_po s = 0 -> 0 <= d_pending s <= z_avail_out z ->
  mb_defined (d_pb s) 0 (d_pending s) -> 0 <= z_total_out z -> z_total_out z + z_avail_out z <= 18446744073709551615 ->
  z_avail_out z <= 4294967295 -> mb_ok (d_pb s) ->
  exists s' z' T, c_flush_pending s z = Some (s', z') /\ bytes T /\
    zout_only z z' T /\ Zlength T = d_pending s /\
    d_pending s' = 0 /\ d_wrap s' = d_wrap s.
Proof.
  intros s z Hbv Hpo Hp Hd Ht0 Ht Hao Hmb.
  unfold c_flush_pending, c_tr_flush_bits, c_bi_flush, d_out.
  unfold d_bi_valid, d_pending, d_pb in *.
  destruct (tr_out (d_tr s)) as [b pn bb bv bu] eqn:Eo. cbn [o_buf o_pending o_bi_buf o_bi_valid o_bi_used] in *.
  subst bv. cbn [Z.eqb Z.geb Z.compare negb]. cbn [bind].
  cbn [set_d_out fst snd tr_out d_tr d_pbm d_po d_wrap set_d_pbm set_d_tr set_out o_buf o_pending].
  rewrite Hpo.
  replace (if pn >? z_avail_out z then z_avail_out z else u32 pn) with pn.
  2: { destruct (Z.gtb_spec pn (z_avail_out z)); [lia|]. unfold u32. rewrite Z.mod_small by lia. reflexivity. }
  destruct (Z.eqb_spec pn 0) as [P0|P0].
  - exists (set_d_out s (mkOut b pn bb 0 bu, d_pbm s)), z, []. rewrite Zlength_nil, P0.
    split; [reflexivity|]. split; [constructor|].
    split; [unfold zout_only; rewrite app_nil_r, Zlength_nil, Z.sub_0_r, Z.add_0_r; repeat split; reflexivity|].
    repeat split; reflexivity.
  - unfold mb_read.
    replace ((0 <=? pn) && mb_definedb (mkMB b (d_pbm s)) 0 (0 + pn)) with true.
    2: { symmetry. apply andb_true_iff. split; [apply Z.leb_le; lia|]. rewrite Z.add_0_l.
         destruct Hd as (D0 & D1 & D2). unfold mb_definedb. cbn [mb_val mb_def] in *.
         apply andb_true_iff. split; [apply andb_true_iff; split; [apply Z.leb_le|apply Z.leb_le]; lia|].
         apply forallb_forall. intros i Hi. apply in_map_iff in Hi. destruct Hi as (k & <- & Hk).
         apply in_seq in Hk. apply D2. lia. }
    cbn [bind mb_val]. unfold out_put. rewrite Zlength_sublist by (destruct Hd as (_ & D1 & _); cbn in D1; lia).
    replace (0 + pn - 0 <=? z_avail_out z) with true by (symmetry; apply Z.leb_le; lia).
    cbn [bind set_d_out set_d_po fst snd tr_out d_tr d_pbm d_po d_wrap set_d_pbm set_d_tr set_out o_buf
         o_pending o_bi_buf o_bi_valid o_bi_used d_pending].
    rewrite Z.sub_diag. cbn [Z.eqb].
    do 3 eexists. split; [reflexivity|].
    split; [apply (bytes_sub_defined b (d_pbm s)); [exact Hmb|exact Hd]|].
    unfold zout_only.
    cbn [z_in z_next_in z_avail_in z_total_in z_adler z_msg z_out z_avail_out z_total_out set_z_out
         set_z_total_out set_z_avail_out d_pending d_wrap set_d_po set_d_out
         set_d_pbm set_d_tr set_out tr_out d_tr fst snd o_pending].
    unfold u64, u32. rewrite !Z.mod_small by lia.
    rewrite Zlength_sublist by (destruct Hd as (_ & D1 & _); cbn in D1; lia).
    repeat split; try reflexivity; lia.
Qed.

Theorem l0c_trail s z :
  outok s -> d_pending s = 0 -> d_po s = 0 -> d_bi_valid s = 0 ->
  8 <= Zlength (o_buf (tr_out (d_tr s))) -> 0 <= d_wrap s <= 2 ->
  tlr_len (d_wrap s) <= z_avail_out z <= 4294967295 -> 0 <= z_total_out z ->
  z_total_out z + z_avail_out z <= 18446744073709551615 ->
  exists s' z' T,
    c_deflate_trailer s z Z_FINISH = Some (s', z', Z_STREAM_END) /\
    zout_only z z' T /\ Zlength T = tlr_len (d_wrap s) /\ bytes T.
Proof.
  intros Hok Hpd Hpo Hbv Hbuf Hw Hroom Ht0 Ht.
  unfold c_deflate_trailer. cbn [Z.eqb negb].
  destruct (Z.leb_spec (d_wrap s) 0) as [W0|W0].
  { exists s, z, []. replace (d_wrap s) with 0 by lia.
    split; [cbn; reflexivity|].
    split; [unfold zout_only; rewrite app_nil_r, Zlength_nil, Z.sub_0_r, Z.add_0_r; repeat split; reflexivity|].
    split; [reflexivity|constructor]. }
  pose proof (proj1 Hok) as Hmbok.
  destruct Hok as ((Hm & _) & _ & _ & _ & _ & _). unfold d_pb in Hm. cbn [mb_val mb_def] in Hm.
  assert (Hd0 : mb_defined (d_pb s) 0 (d_pending s)).
  { rewrite Hpd. unfold mb_defined, d_pb. cbn [mb_val]. pose proof (Zlength_nonneg (o_buf (tr_out (d_tr s)))).
    split; [lia|]. split; [lia|]. intros; lia. }
  set (a := z_adler z). set (t := z_total_in z).
  assert (Hput : exists s1,
    (if d_wrap s =? 2 then
       c_dput_bytes s [Z.land a 255; Z.land (Z.shiftr a 8) 255; Z.land (Z.shiftr a 16) 255;
                       Z.land (Z.shiftr a 24) 255; Z.land t 255; Z.land (Z.shiftr t 8) 255;
                       Z.land (Z.shiftr t 16) 255; Z.land (Z.shiftr t 24) 255]
     else
       let* s := c_putShortMSB s (u32 (Z.shiftr a 16)) in
       c_putShortMSB s (u32 (Z.land a 65535))) = Some s1 /\
    d_pending s1 = tlr_len (d_wrap s) /\ mb_defined (d_pb s1) 0 (d_pending s1) /\
    d_po s1 = 0 /\ d_bi_valid s1 = 0 /\ d_wrap s1 = d_wrap s /\ mb_ok (d_pb s1)).
  { destruct (Z.eqb_spec (d_wrap s) 2) as [E2|E2].
    - match goal with |- exists s1, c_dput_bytes _ ?l = _ /\ _ =>
        destruct (l0t_dput_bytes l s) as (s1 & E & P & D & O & B & Wr); auto; try (rewrite Hpd; cbn; lia) end.
      exists s1. split; [exact E|].
      split; [rewrite P, Hpd, E2; reflexivity|]. split; [exact D|]. rewrite O, B, Wr, Hpo, Hbv.
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. exact (l0c_dput_bytes_ok _ _ _ E Hmbok).
    -
      (* the two putShortMSB are four put_byte *)
      replace (let* s := c_putShortMSB s (u32 (Z.shiftr a 16)) in c_putShortMSB s (u32 (Z.land a 65535)))
        with (c_dput_bytes s [Z.shiftr (u32 (Z.shiftr a 16)) 8; Z.land (u32 (Z.shiftr a 16)) 255;
                              Z.shiftr (u32 (Z.land a 65535)) 8; Z.land (u32 (Z.land a 65535)) 255]).
      2: { unfold c_putShortMSB. cbn [c_dput_bytes].
           destruct (c_dput_byte s _) as [s2|]; cbn [bind]; [|reflexivity].
           destruct (c_dput_byte s2 _) as [s3|]; cbn [bind]; [|reflexivity].
           destruct (c_dput_byte s3 _) as [s4|]; cbn [bind]; [|reflexivity].
           destruct (c_dput_byte s4 _); reflexivity. }
      match goal with |- exists s1, c_dput_bytes _ ?l = _ /\ _ =>
        destruct (l0t_dput_bytes l s) as (s1 & E & P & D & O & B & Wr); auto; try (rewrite Hpd; cbn; lia) end.
      exists s1. split; [exact E|].
      split; [rewrite P, Hpd; replace (d_wrap s) with 1 by lia; reflexivity|]. split; [exact D|].
      rewrite O, B, Wr, Hpo, Hbv.
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. exact (l0c_dput_bytes_ok _ _ _ E Hmbok). }
  destruct Hput as (s1 & E1 & P1 & D1 & O1 & B1 & Wr1 & M1).
  rewrite E1. cbn [bind].
  assert (Htl : 0 <= tlr_len (d_wrap s)) by (unfold tlr_len; destruct (d_wrap s =? 0), (d_wrap s =? 1); lia).
  destruct (l0c_flush_all s1 z) as (s' & z' & T & Ef & HbT & Hzo & HT & Pd & Wr'); auto; [lia..|].
  replace (negb (Z_FINISH =? Z_FINISH)) with false by reflexivity.
  rewrite Ef. cbn [bind].
  rewrite Wr', Wr1. replace (d_wrap s >? 0) with true by (symmetry; apply Z.gtb_lt; lia).
  exists (set_d_wrap s' (- d_wrap s)), z', T.
  change (d_pending (set_d_wrap s' (- d_wrap s))) with (d_pending s'). rewrite Pd. cbn [Z.eqb negb].
  split; [reflexivity|]. split; [exact Hzo|]. split; [congruence|]. exact HbT.
Qed.
