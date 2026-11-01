(** * Level 0 over several deflate() calls: a trailer that does not fit, and the calls after it

    With gzip and all the data in the first call (up to 65532 blocks), the Z_FINISH call may have to write
    10 + 65540 * 65532 + 8 > 2^32 - 1 bytes: the header and the stored blocks fit, the 8-byte trailer only partly.
    - [l0x_trail_part]: the trailer goes to pending_buf, as many bytes as fit are written, the rest (1 to 3 bytes)
      stays pending and deflate() returns Z_OK, status FINISH, wrap negated.
    - The next call (no input, Z_FINISH) flushes the pending bytes at its entry: when that fills its output space
      it returns Z_OK at once ([l0x_call_flush]), otherwise it passes the header and compression stages and
      returns Z_STREAM_END ([l0x_call_end]).
    - A call with no output space returns Z_BUF_ERROR ([l0x_call_buf]). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.Level0CallsComp.
Require Import Zlib.proof.deflate.LTCInit.
Require Import Zlib.proof.deflate.LTCMisc.
Require Import Zlib.proof.deflate.LTCStored2.
Require Import Zlib.proof.deflate.LTCStoredLoopLib.
Require Import Zlib.proof.deflate.Level0Stored.
Require Import Zlib.proof.deflate.Level0Trail.
Require Export Zlib.proof.wide.deflate.LTCFlushKit.
Require Import Zlib.proof.deflate.LTApiOut.
Require Import Zlib.proof.deflate.LTHdrStages.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** The fields deflate()'s flush_pending keeps. *)
Lemma fp_keep_fields s s' : fp_keep s' = fp_keep s ->
  d_status s' = d_status s /\ d_wrap s' = d_wrap s /\ d_pending_buf_size s' = d_pending_buf_size s.
Proof.
  intros H.
  pose proof (f_equal d_status H) as A. pose proof (f_equal d_wrap H) as B.
  pose proof (f_equal d_pending_buf_size H) as C. exact (conj A (conj B C)).
Qed.

Lemma fp_keep_fields2 s s' : fp_keep s' = fp_keep s ->
  d_lookahead s' = d_lookahead s /\ d_gzhead s' = d_gzhead s.
Proof.
  intros H. pose proof (f_equal d_lookahead H) as A. pose proof (f_equal d_gzhead H) as B. exact (conj A B).
Qed.

(** put_byte on a state with pending_out at the start: pending grows by one, the output part stays sane. *)
Lemma l0x_dput_byte s c s1 :
  c_dput_byte s c = Some s1 -> outok s -> d_po s = 0 ->
  d_pending_buf_size s = Zlength (o_buf (tr_out (d_tr s))) ->
  outok s1 /\ d_pending s1 = d_pending s + 1 /\ d_po s1 = 0 /\ d_bi_valid s1 = d_bi_valid s /\
  fp_keep s1 = fp_keep s /\ Zlength (o_buf (tr_out (d_tr s1))) = Zlength (o_buf (tr_out (d_tr s))).
Proof.
  intros E Hok Hpo Hpbs.
  destruct Hok as ((Hm & Hmv) & Hbits & Hpo0 & Hpe & Hdef & Hp0).
  unfold c_dput_byte, c_put_byte, d_out in E. cbn [fst snd] in E.
  unfold wr, in_range in E.
  destruct ((0 <=? o_pending (tr_out (d_tr s))) && (o_pending (tr_out (d_tr s)) <? Zlength (o_buf (tr_out (d_tr s)))))
    eqn:R; cbn [bind] in E; [|discriminate].
  apply andb_true_iff in R as [R1 R2]. apply Z.leb_le in R1. apply Z.ltb_lt in R2.
  inversion E; subst s1; clear E.
  unfold d_pb, d_pending, d_bi_valid in *. cbn [mb_val mb_def] in *.
  set (o := tr_out (d_tr s)) in *. set (p := o_pending o) in *.
  change (d_po (set_d_out s (mkOut (upd_Znth p (o_buf o) (u8 c)) (p + 1) (o_bi_buf o) (o_bi_valid o) (o_bi_used o),
                             upd_Znth p (d_pbm s) true))) with (d_po s).
  change (d_pending_buf_size (set_d_out s (mkOut (upd_Znth p (o_buf o) (u8 c)) (p + 1) (o_bi_buf o) (o_bi_valid o)
                                  (o_bi_used o), upd_Znth p (d_pbm s) true))) with (d_pending_buf_size s).
  cbn [set_d_out fst snd set_d_pbm set_d_tr set_out d_tr d_pbm tr_out o_buf o_pending o_bi_buf o_bi_valid o_bi_used].
  rewrite Hpo in *.
  split; [|split; [reflexivity|split; [reflexivity|split; [reflexivity|split; [reflexivity|]]]]].
  - unfold outok, d_pb, d_pending, d_pending_buf_size.
    cbn [set_d_out fst snd set_d_pbm set_d_tr set_out d_tr d_pbm tr_out o_buf o_pending o_bi_buf o_bi_valid o_bi_used].
    change (d_po (set_d_out s (mkOut (upd_Znth p (o_buf o) (u8 c)) (p + 1) (o_bi_buf o) (o_bi_valid o) (o_bi_used o),
                               upd_Znth p (d_pbm s) true))) with (d_po s). rewrite Hpo.
    fold (d_pending_buf_size s).
    split; [apply mb_ok_upd; [split; assumption|lia|apply u8_range]|].
    split; [destruct Hbits as (B1 & B2 & B3); unfold bits_ok; cbn [o_bi_valid o_bi_buf o_pending]; lia|].
    split; [lia|].
    split; [change (0 + (p + 1) <= d_pending_buf_size s); lia|].
    split; [|intros; lia].
    destruct Hdef as (D0 & D1 & D2). unfold mb_defined. cbn [mb_val mb_def].
    rewrite upd_Znth_Zlength by lia.
    split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.eq_dec i p) as [->|Ne].
    + rewrite upd_Znth_same by lia. reflexivity.
    + rewrite upd_Znth_diff by lia. apply D2. lia.
  - rewrite upd_Znth_Zlength by lia. reflexivity.
Qed.

Lemma l0x_dput_bytes l : forall s s1,
  c_dput_bytes s l = Some s1 -> outok s -> d_po s = 0 ->
  d_pending_buf_size s = Zlength (o_buf (tr_out (d_tr s))) ->
  outok s1 /\ d_pending s1 = d_pending s + Zlength l /\ d_po s1 = 0 /\ d_bi_valid s1 = d_bi_valid s /\
  fp_keep s1 = fp_keep s /\ Zlength (o_buf (tr_out (d_tr s1))) = Zlength (o_buf (tr_out (d_tr s))).
Proof.
  induction l as [|c l IH]; intros s s1 E Hok Hpo Hpbs; cbn [c_dput_bytes] in E.
  - inversion E; subst. rewrite Zlength_nil, Z.add_0_r. split; [exact Hok|]. repeat split; auto.
  - destruct (c_dput_byte s c) as [s2|] eqn:E1; cbn [bind] in E; [|discriminate].
    destruct (l0x_dput_byte s c s2 E1 Hok Hpo Hpbs) as (O2 & P2 & Po2 & B2 & K2 & L2).
    destruct (fp_keep_fields _ _ K2) as (_ & _ & Pb2).
    destruct (IH s2 s1 E O2 Po2 ltac:(rewrite Pb2, L2; exact Hpbs)) as (O1 & P1 & Po1 & B1 & K1 & L1).
    rewrite Zlength_cons. split; [exact O1|]. split; [lia|]. split; [exact Po1|].
    split; [congruence|]. split; [congruence|]. congruence.
Qed.

(** The gzip trailer with nothing pending: its 8 bytes go to pending_buf and as many as fit are written; with
    some left pending, deflate() returns Z_OK. *)
Lemma l0x_trail_part s z :
  outok s -> d_pending s = 0 -> d_po s = 0 -> d_bi_valid s = 0 -> d_wrap s = 2 ->
  8 <= Zlength (o_buf (tr_out (d_tr s))) ->
  d_pending_buf_size s = Zlength (o_buf (tr_out (d_tr s))) -> d_pending_buf_size s <= 131072 ->
  zout_ok_w z ->
  exists s' z' x r,
    c_deflate_trailer s z Z_FINISH = Some (s', z', r) /\ zout_only z z' x /\
    Zlength x = Z.min 8 (z_avail_out z) /\ d_pending s' = 8 - Zlength x /\ (d_pending s' <> 0 -> r = Z_OK) /\
    outok s' /\ d_bi_valid s' = 0 /\ d_status s' = d_status s /\
    d_pending_buf_size s' = Zlength (o_buf (tr_out (d_tr s'))) /\ d_pending_buf_size s' <= 131072 /\
    bytes x /\ d_wrap s' = -2 /\ d_lookahead s' = d_lookahead s /\ d_gzhead s' = d_gzhead s.
Proof.
  intros Hok Hp Hpo Hbv Hw H8 Hpbs Hpb Hz.
  unfold c_deflate_trailer. cbn [Z.eqb negb Pos.eqb]. rewrite Hw. cbn [Z.leb Z.compare Z.eqb Pos.eqb].
  pose proof Hok as ((Hm & _) & _).
  set (a := z_adler z). set (t := z_total_in z).
  match goal with |- context [c_dput_bytes s ?l] =>
    destruct (l0t_dput_bytes l s) as (s1 & E & _); [exact Hm|lia|rewrite Hp; cbn; lia|
      rewrite Hp; unfold mb_defined; split; [lia|split; [pose proof (Zlength_nonneg (o_buf (tr_out (d_tr s)))); cbn; lia|intros; lia]]|];
    destruct (l0x_dput_bytes l s s1 E Hok Hpo Hpbs) as (O1 & P1 & Po1 & B1 & K1 & L1) end.
  rewrite E. cbn [bind].
  destruct (fp_keep_fields _ _ K1) as (S1 & W1 & Pb1).
  destruct (fpend_ok_w s1 z ltac:(rewrite Pb1, L1; exact Hpbs) ltac:(rewrite Pb1; exact Hpb) O1 Hz
              ltac:(left; rewrite B1, Hbv; lia))
    as (s' & z' & x & Ef & Hzo & Hbx & Hlx & Hp' & Hbv' & Ho' & _ & K' & Hgr).
  rewrite Ef. cbn [bind].
  destruct (fp_keep_fields _ _ K') as (S' & W' & Pb').
  destruct (fp_keep_fields2 _ _ K') as (La' & G').
  destruct (fp_keep_fields2 _ _ K1) as (La1 & G1).
  rewrite W', W1, Hw. cbn [Z.gtb Z.compare].
  rewrite P1, Hp, B1, Hbv in Hlx. rewrite P1, Hp, B1, Hbv in Hp'. cbn [Zlength length Z.of_nat] in Hlx, Hp'.
  change (Zlength [Z.land a 255; Z.land (Z.shiftr a 8) 255; Z.land (Z.shiftr a 16) 255;
          Z.land (Z.shiftr a 24) 255; Z.land t 255; Z.land (Z.shiftr t 8) 255;
          Z.land (Z.shiftr t 16) 255; Z.land (Z.shiftr t 24) 255]) with 8 in Hlx, Hp'.
  change (0 + 8 + 0 / 8) with 8 in Hlx, Hp'.
  exists (set_d_wrap s' (- 2)), z', x, (if negb (d_pending s' =? 0) then Z_OK else Z_STREAM_END).
  change (d_pending (set_d_wrap s' (-2))) with (d_pending s').
  split; [reflexivity|]. split; [exact Hzo|]. split; [exact Hlx|]. split; [lia|].
  split; [intros N; apply Z.eqb_neq in N; rewrite N; reflexivity|].
  split; [exact Ho'|].
  split; [change (d_bi_valid s' = 0); rewrite Hbv', B1, Hbv; reflexivity|].
  split; [change (d_status s' = d_status s); congruence|].
  destruct Hgr as (Gr1 & _).
  change (d_pending_buf_size s' = Zlength (o_buf (tr_out (d_tr s'))) /\ d_pending_buf_size s' <= 131072 /\
          bytes x /\ -2 = -2 /\ d_lookahead s' = d_lookahead s /\ d_gzhead s' = d_gzhead s).
  split; [rewrite Gr1, Pb', Pb1, L1; lia|]. split; [rewrite Pb', Pb1; lia|].
  split; [exact Hbx|]. split; [reflexivity|]. split; congruence.
Qed.

(** A call that finds pending bytes and fills the output space with them returns Z_OK at once. *)
Lemma l0x_call_flush s z s' z' :
  bad_state s = false -> d_pending s <> 0 -> 0 < z_avail_out z ->
  c_flush_pending (set_d_last_flush s Z_FINISH) z = Some (s', z') -> z_avail_out z' = 0 ->
  c_deflate s z Z_FINISH = Some (set_d_last_flush s' (-1), z', Z_OK).
Proof.
  intros Hb Hp Ha Ef Ha'.
  rewrite c_deflate_stages, Hb. cbv beta iota.
  change ((Z_FINISH >? Z_BLOCK) || (Z_FINISH <? 0)) with false. cbn [orb].
  unfold c_deflate_entry.
  change (negb (Z_FINISH =? Z_FINISH)) with false. rewrite andb_false_r.
  replace (z_avail_out z =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  change (d_pending (set_d_last_flush s Z_FINISH)) with (d_pending s).
  replace (negb (d_pending s =? 0)) with true by (symmetry; apply negb_true_iff, Z.eqb_neq; exact Hp).
  rewrite Ef. cbn [bind]. rewrite Ha'. cbn [Z.eqb then_stage bind]. reflexivity.
Qed.


(** The header stages do nothing once the stream is finished. *)
Lemma hdr_stages_finish s z : d_status s = FINISH_STATE -> hdr_stages s z = Some (s, z, None).
Proof.
  intros H. unfold hdr_stages.
  rewrite zlib_id by (rewrite H; discriminate). cbn [then_stage bind].
  rewrite gzip_id by (rewrite H; discriminate). cbn [then_stage bind].
  rewrite extra_id by (rewrite H; discriminate). cbn [then_stage bind].
  rewrite name_id by (rewrite H; discriminate). cbn [then_stage bind].
  rewrite comment_id by (rewrite H; discriminate). cbn [then_stage bind].
  rewrite hcrc_id by (rewrite H; discriminate). reflexivity.
Qed.

(** A call that finds pending bytes, flushes them all with output space left, no input and nothing in the window,
    on a finished stream whose trailer is written (wrap negated): Z_STREAM_END. *)
Lemma l0x_call_end s z s' z' :
  bad_state s = false -> d_pending s <> 0 -> 0 < z_avail_out z ->
  c_flush_pending (set_d_last_flush s Z_FINISH) z = Some (s', z') -> z_avail_out z' <> 0 ->
  z_avail_in z' = 0 -> d_status s' = FINISH_STATE -> d_lookahead s' = 0 -> d_wrap s' <= 0 ->
  c_deflate s z Z_FINISH = Some (s', z', Z_STREAM_END).
Proof.
  intros Hb Hp Ha Ef Ha' Hai Hst Hla Hw.
  rewrite c_deflate_stages, Hb. cbv beta iota.
  change ((Z_FINISH >? Z_BLOCK) || (Z_FINISH <? 0)) with false. cbn [orb].
  unfold c_deflate_entry.
  change (negb (Z_FINISH =? Z_FINISH)) with false. rewrite andb_false_r.
  replace (z_avail_out z =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  change (d_pending (set_d_last_flush s Z_FINISH)) with (d_pending s).
  replace (negb (d_pending s =? 0)) with true by (symmetry; apply negb_true_iff, Z.eqb_neq; exact Hp).
  rewrite Ef. cbn [bind].
  replace (z_avail_out z' =? 0) with false by (symmetry; apply Z.eqb_neq; exact Ha').
  cbn [then_stage bind]. rewrite Hai. cbn [Z.eqb negb]. rewrite andb_false_r.
  cbn [then_stage bind]. rewrite (hdr_stages_finish s' z' Hst). cbn [then_stage bind].
  unfold c_deflate_compress. rewrite Hai, Hla, Hst. cbn.
  replace (d_wrap s' <=? 0) with true by (symmetry; apply Z.leb_le; exact Hw). reflexivity.
Qed.

(** A call with no output space: Z_BUF_ERROR (deflate.c: [if (strm->avail_out == 0) ERR_RETURN(strm, Z_BUF_ERROR)]). *)
Lemma l0x_call_buf s z :
  bad_state s = false -> z_avail_out z = 0 ->
  c_deflate s z Z_FINISH = Some (s, set_z_msg z (Some Z_BUF_ERROR), Z_BUF_ERROR).
Proof.
  intros Hb Ha.
  rewrite c_deflate_stages, Hb. cbv beta iota.
  change ((Z_FINISH >? Z_BLOCK) || (Z_FINISH <? 0)) with false. cbn [orb].
  unfold c_deflate_entry.
  change (negb (Z_FINISH =? Z_FINISH)) with false. rewrite andb_false_r. rewrite Ha. reflexivity.
Qed.

(** The call after a trailer that did not fit: no input, Z_FINISH, room for the pending bytes.  It writes them and
    returns Z_OK when that fills its output space, Z_STREAM_END otherwise. *)
Lemma l0x_pending_call s z :
  outok s -> d_bi_valid s = 0 -> d_status s = FINISH_STATE -> d_wrap s <= 0 -> d_lookahead s = 0 ->
  d_pending_buf_size s = Zlength (o_buf (tr_out (d_tr s))) -> d_pending_buf_size s <= 131072 ->
  0 < d_pending s <= z_avail_out z -> z_avail_in z = 0 -> zout_ok_w z ->
  exists s' z' x code,
    c_deflate s z Z_FINISH = Some (s', z', code) /\ zout_only z z' x /\ bytes x /\ Zlength x = d_pending s /\
    d_gzhead s' = d_gzhead s /\ d_status s' = FINISH_STATE /\
    ((z_avail_out z' = 0 /\ code = Z_OK) \/ (z_avail_out z' <> 0 /\ code = Z_STREAM_END)).
Proof.
  intros Ho Hbv Hst Hw Hla Hpbs Hpb Hp Hai Hz.
  assert (Hbad : bad_state s = false) by (unfold bad_state, c_deflateStateCheck; rewrite Hst; reflexivity).
  destruct (fpend_ok_w (set_d_last_flush s Z_FINISH) z Hpbs Hpb Ho Hz
              ltac:(left; change (d_bi_valid s < 8); lia))
    as (s1 & z1 & x & Ef & Hzo & Hbx & Hlx & _ & _ & _ & _ & K1 & _).
  change (d_pending (set_d_last_flush s Z_FINISH)) with (d_pending s) in Hlx.
  change (d_bi_valid (set_d_last_flush s Z_FINISH)) with (d_bi_valid s) in Hlx.
  rewrite Hbv in Hlx. change (0 / 8) with 0 in Hlx. rewrite Z.add_0_r, Z.min_l in Hlx by lia.
  destruct (fp_keep_fields _ _ K1) as (S1 & W1 & _).
  destruct (fp_keep_fields2 _ _ K1) as (La1 & G1).
  change (d_status (set_d_last_flush s Z_FINISH)) with (d_status s) in S1.
  change (d_wrap (set_d_last_flush s Z_FINISH)) with (d_wrap s) in W1.
  change (d_lookahead (set_d_last_flush s Z_FINISH)) with (d_lookahead s) in La1.
  change (d_gzhead (set_d_last_flush s Z_FINISH)) with (d_gzhead s) in G1.
  pose proof Hzo as (_ & _ & B3 & _).
  destruct (Z.eq_dec (z_avail_out z1) 0) as [E0|E0].
  - exists (set_d_last_flush s1 (-1)), z1, x, Z_OK.
    split; [apply l0x_call_flush; auto; lia|].
    split; [exact Hzo|]. split; [exact Hbx|]. split; [exact Hlx|].
    split; [exact G1|]. split; [change (d_status s1 = FINISH_STATE); congruence|]. left; auto.
  - exists s1, z1, x, Z_STREAM_END.
    split; [apply l0x_call_end; auto; try lia; congruence|].
    split; [exact Hzo|]. split; [exact Hbx|]. split; [exact Hlx|].
    split; [exact G1|]. split; [congruence|]. right; auto.
Qed.

(** ** The state between the call that cut the trailer and the next one *)

(** Finished, the trailer written (wrap negated), its last bytes pending. *)
Definition l0_pend (s : dstate) : Prop :=
  outok s /\ d_bi_valid s = 0 /\ d_status s = FINISH_STATE /\ d_wrap s <= 0 /\ d_lookahead s = 0 /\
  d_pending_buf_size s = Zlength (o_buf (tr_out (d_tr s))) /\ d_pending_buf_size s <= 131072 /\
  0 < d_pending s /\ d_gzhead s = None.

(** The gzip trailer after the stored blocks of the last call ([Level0CallsComp.l0c_comp_fin]'s state) with less
    than 8 bytes of output space: Z_OK, the bytes that fit written, the state [l0_pend]. *)
Lemma l0x_trail_cut s z :
  outok s -> d_pending s = 0 -> d_po s = 0 -> d_bi_valid s = 0 -> d_wrap s = 2 ->
  8 <= Zlength (o_buf (tr_out (d_tr s))) -> d_status s = FINISH_STATE -> d_gzhead s = None ->
  d_pending_buf_size s = Zlength (o_buf (tr_out (d_tr s))) -> d_pending_buf_size s <= 131072 ->
  d_lookahead s = 0 -> zout_ok_w z -> z_avail_out z < 8 ->
  exists s' z' x,
    c_deflate_trailer s z Z_FINISH = Some (s', z', Z_OK) /\ zout_only z z' x /\ bytes x /\
    Zlength x = z_avail_out z /\ Zlength x + d_pending s' = 8 /\ l0_pend s'.
Proof.
  intros Ho Hp Hpo Hbv Hw H8 Hst Hgz Hpbs Hpb Hla Hz Ha.
  destruct (l0x_trail_part s z Ho Hp Hpo Hbv Hw H8 Hpbs Hpb Hz)
    as (s' & z' & x & r & Et & Hzo & Hlx & Hp' & Hr & Ho' & Hbv' & Hst' & Hpbs' & Hpb' & Hbx & Hw' & Hla' & Hgz').
  pose proof Hz as (Ha0 & _).
  rewrite Z.min_r in Hlx by lia.
  assert (Er : r = Z_OK) by (apply Hr; lia). subst r.
  exists s', z', x. split; [exact Et|]. split; [exact Hzo|]. split; [exact Hbx|]. split; [exact Hlx|].
  split; [lia|].
  refine (conj Ho' (conj Hbv' (conj _ (conj _ (conj _ (conj Hpbs' (conj Hpb' (conj _ _)))))))); congruence || lia.
Qed.

(** The call after it: no input, Z_FINISH, [aout] bytes of output space, at least the pending ones.  Z_OK when they
    fill it (then nothing is pending and the stream stays finished), Z_STREAM_END otherwise. *)
Lemma l0x_pend_call s inb tin aout tout adler msg :
  l0_pend s -> inb = [] -> d_pending s <= aout <= 4294967295 -> 0 <= tout -> tout + aout <= 18446744073709551615 ->
  exists s' z' code,
    c_deflate s (zcall inb 0 (Zlength inb) tin aout tout adler msg) Z_FINISH = Some (s', z', code) /\
    z_in z' = inb /\ z_avail_in z' = 0 /\ z_next_in z' = 0 /\ z_total_in z' = tin /\
    z_avail_out z' = aout - d_pending s /\ Zlength (z_out z') = d_pending s /\
    z_total_out z' = tout + d_pending s /\ bytes (z_out z') /\ z_adler z' = adler /\
    d_gzhead s' = None /\ d_status s' = FINISH_STATE /\
    ((aout = d_pending s /\ code = Z_OK) \/ (aout <> d_pending s /\ code = Z_STREAM_END)).
Proof.
  intros (Ho & Hbv & Hst & Hw & Hla & Hpbs & Hpb & Hp & Hgz) -> Ha Ht0 Ht.
  destruct (l0x_pending_call s (zcall [] 0 (Zlength (@nil Z)) tin aout tout adler msg) Ho Hbv Hst Hw Hla Hpbs Hpb
              ltac:(cbn; lia) eq_refl ltac:(unfold zout_ok_w; cbn; lia))
    as (s' & z' & x & code & E & Hzo & Hbx & Hlx & Hg' & Hst' & Hc).
  destruct Hzo as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
  cbn [zcall z_in z_next_in z_avail_in z_total_in z_out z_avail_out z_total_out z_adler] in *.
  exists s', z', code. split; [exact E|].
  rewrite B7. cbn [app]. rewrite Hlx in B8, B9.
  split; [exact B1|]. split; [exact B3|]. split; [exact B2|]. split; [exact B4|].
  split; [exact B8|]. split; [exact Hlx|]. split; [exact B9|]. split; [exact Hbx|]. split; [exact B5|].
  split; [congruence|]. split; [exact Hst'|].
  destruct Hc as [[Hc1 Hc2]|[Hc1 Hc2]]; [left|right]; split; auto; lia.
Qed.

(** The call after that one when it got exactly the pending bytes: no output space, Z_BUF_ERROR, nothing moves. *)
Lemma l0x_full_call s inb tin tout adler msg :
  d_status s = FINISH_STATE -> inb = [] ->
  c_deflate s (zcall inb 0 (Zlength inb) tin 0 tout adler msg) Z_FINISH =
    Some (s, set_z_msg (zcall inb 0 (Zlength inb) tin 0 tout adler msg) (Some Z_BUF_ERROR), Z_BUF_ERROR).
Proof.
  intros Hst ->. apply l0x_call_buf; [|reflexivity].
  unfold bad_state, c_deflateStateCheck. rewrite Hst. reflexivity.
Qed.
