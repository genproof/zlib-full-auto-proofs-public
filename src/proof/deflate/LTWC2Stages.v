(** * deflate()'s stages: what compress2_z's loop needs beyond the deflateBound accounting

    The stage lemmas of LTWBEntry / LTWBHdr / LTWBComp / LTWBTrail keep the accounting [MidW] through one
    deflate() call.  compress2_z's loop needs three more things of a call (LawFactsC2W.c2f_split): when it
    returns Z_BUF_ERROR (no output space, or no input at Z_NO_FLUSH), that a Z_OK moves on (input consumed or
    output written), and that the bytes handed out, pending and still to put in the trailer do not grow once
    the last block is out (the margin LTWC2Defs.mg).  These are read off the stages' models (DModel4):

    - a stage that returns Z_OK after flush_pending with bytes still pending has filled the output space;
    - deflate()'s entry returns Z_BUF_ERROR only without output space, without input at a flush that is not
      Z_FINISH (and not stronger than the previous one), or with input after the end of the stream;
    - flush_pending moves bytes from pending_buf to the output, the trailer adds its bytes to pending_buf;
    - the compression stage returns what the compression function returned (Z_OK after need_more or
      finish_started), or does not call it (no input, no lookahead, and Z_NO_FLUSH or the stream finished). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTWC2Defs.
Require Zlib.proof.deflate.DeflateKit Zlib.proof.deflate.LTWBEntry Zlib.proof.deflate.LTBTrail
  Zlib.proof.deflate.LTWBTrail.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** flush_pending keeps the status and the input side of the stream. *)
Lemma fp_keep : forall s z s' z', c_flush_pending s z = Some (s', z') ->
  d_status s' = d_status s /\ z_avail_in z' = z_avail_in z.
Proof.
  intros s z s' z' E. pose proof (Zlib.proof.deflate.DeflateKit.c_flush_pending_same s z s' z' E) as (_ & _ & _ & Ha & _).
  split; [|exact Ha].
  unfold c_flush_pending in E. destruct (c_tr_flush_bits (d_out s)) as [o|]; cbn [bind] in E; [|discriminate E].
  destruct (_ =? 0); [injection E as <- _; destruct s; reflexivity|].
  destruct (mb_read _ _ _); cbn [bind] in E; [|discriminate E].
  destruct (out_put _ _); cbn [bind] in E; [|discriminate E].
  injection E as <- _. destruct (_ =? 0); destruct s; reflexivity.
Qed.

(** flush_pending leaves bytes pending only when it filled the output space. *)
Lemma fp_full : forall s z s' z', c_flush_pending s z = Some (s', z') ->
  0 <= z_avail_out z <= 4294967295 -> 0 <= d_pending s' -> d_pending s' <> 0 -> z_avail_out z' = 0.
Proof.
  intros s z s' z' E Ha Hp Hn.
  unfold c_flush_pending in E. destruct (c_tr_flush_bits (d_out s)) as [o|]; cbn [bind] in E; [|discriminate E].
  set (p := d_pending (set_d_out s o)) in *.
  assert (Hu : forall x, 0 <= u32 x < 4294967296) by (intros x; unfold u32; apply Z.mod_pos_bound; lia).
  destruct (Z.gtb_spec p (z_avail_out z)) as [G|G].
  - destruct (Z.eqb_spec (z_avail_out z) 0) as [E0|E0].
    + injection E as <- <-. exact E0.
    + destruct (mb_read _ _ _); cbn [bind] in E; [|discriminate E].
      destruct (out_put _ _) as [z1|] eqn:Eo; cbn [bind] in E; [|discriminate E].
      injection E as <- <-. unfold out_put in Eo. destruct (_ <=? _); [|discriminate Eo].
      injection Eo as <-. cbn. lia.
  - assert (Ep0 : p = o_pending (fst o)) by (unfold p; destruct s; reflexivity).
    assert (Q1 : forall s1 po, d_pending (set_d_po s1 po) = d_pending s1) by (intros [] po; reflexivity).
    assert (Q2 : forall s1 o1 m1, d_pending (set_d_out s1 (o1, m1)) = o_pending o1) by (intros [] o1 m1; reflexivity).
    destruct (Z.eqb_spec (u32 p) 0) as [E0|E0].
    + injection E as <- <-. exfalso.
      assert (Hp0 : 0 <= p < 4294967296) by (fold p in Hp; lia).
      unfold u32 in E0. rewrite Z.mod_small in E0 by lia. fold p in Hn. contradiction.
    + destruct (mb_read _ _ _); cbn [bind] in E; [|discriminate E].
      destruct (out_put _ _); cbn [bind] in E; [|discriminate E].
      injection E as <- _. exfalso.
      destruct (_ =? 0) eqn:Ez in Hp, Hn; rewrite ?Q1, ?Q2 in Hp, Hn; cbn [o_pending] in Hp, Hn.
      * apply Hn. rewrite Q2 in Ez. cbn [o_pending] in Ez. apply Z.eqb_eq in Ez. exact Ez.
      * rewrite <- Ep0 in Hp, Hn. pose proof (Hu p).
        assert (Hp0 : 0 <= p) by (destruct (Z_lt_le_dec p 0); [|lia]; pose proof (Hu p); lia).
        unfold u32 in Hn. rewrite Z.mod_small in Hn by lia. lia.
Qed.

(** deflate()'s entry returns Z_BUF_ERROR only without output space, without input at a flush other than
    Z_FINISH, or with input after the end of the stream. *)
Lemma entry_buf : forall s z flush s1 z1,
  c_deflate_entry s z flush = Some (s1, z1, Some Z_BUF_ERROR) ->
  z_avail_out z = 0 \/ (z_avail_in z = 0 /\ flush <> Z_FINISH) \/
  (d_status s = FINISH_STATE /\ z_avail_in z <> 0).
Proof.
  intros s z flush s1 z1 E. unfold c_deflate_entry in E.
  destruct ((d_status s =? FINISH_STATE) && negb (flush =? Z_FINISH)); [discriminate E|].
  destruct (Z.eqb_spec (z_avail_out z) 0) as [Ho|Ho]; [left; exact Ho|].
  right.
  destruct (negb (d_pending (set_d_last_flush s flush) =? 0)).
  - destruct (c_flush_pending _ z) as [[s2 z2]|] eqn:Ef; cbn [bind] in E; [|discriminate E].
    destruct (z_avail_out z2 =? 0); cbn in E; [discriminate E|].
    destruct ((d_status s2 =? FINISH_STATE) && negb (z_avail_in z2 =? 0)) eqn:G; [|discriminate E].
    right. destruct (fp_keep _ _ _ _ Ef) as [Es Ea].
    apply andb_true_iff in G. destruct G as [G1 G2]. apply Z.eqb_eq in G1. apply negb_true_iff, Z.eqb_neq in G2.
    rewrite Es in G1. rewrite Ea in G2. split; [destruct s; exact G1|exact G2].
  - destruct (Z.eqb_spec (z_avail_in z) 0) as [Hi|Hi].
    + cbn [bind] in E. destruct (guard _); cbn in E; [|discriminate E].
      destruct ((rank flush <=? rank (d_last_flush s)) && negb (flush =? Z_FINISH)) eqn:G.
      * left. split; [exact Hi|]. apply andb_true_iff in G. destruct G as [_ G].
        apply negb_true_iff, Z.eqb_neq in G. exact G.
      * cbn in E. destruct ((d_status _ =? FINISH_STATE) && negb (z_avail_in z =? 0)) eqn:G2; [|discriminate E].
        rewrite Hi in G2. rewrite andb_false_r in G2. discriminate G2.
    + cbn in E. destruct ((d_status _ =? FINISH_STATE) && negb (z_avail_in z =? 0)) eqn:G2; [|discriminate E].
      right. apply andb_true_iff in G2. destruct G2 as [G2 _]. apply Z.eqb_eq in G2.
      split; [destruct s; exact G2|exact Hi].
Qed.

(** deflate()'s entry returns Z_OK only after flush_pending filled the output space. *)
Lemma entry_ok : forall s z flush s1 z1,
  c_deflate_entry s z flush = Some (s1, z1, Some Z_OK) ->
  0 <= z_avail_out z <= 4294967295 -> 0 <= d_pending s1 -> z_avail_out z1 = 0.
Proof.
  intros s z flush s1 z1 E _ _. unfold c_deflate_entry in E.
  destruct ((d_status s =? FINISH_STATE) && negb (flush =? Z_FINISH)); [discriminate E|].
  destruct (z_avail_out z =? 0); [discriminate E|].
  destruct (negb (d_pending (set_d_last_flush s flush) =? 0)).
  - destruct (c_flush_pending _ z) as [[s2 z2]|] eqn:Ef; cbn [bind] in E; [|discriminate E].
    destruct (Z.eqb_spec (z_avail_out z2) 0) as [E0|E0]; cbn in E.
    + injection E as _ <-. exact E0.
    + destruct (_ && _); discriminate E.
  - destruct (z_avail_in z =? 0).
    + cbn [bind] in E. destruct (guard _); cbn in E; [|discriminate E].
      destruct (_ && _); cbn in E; [discriminate E|]. destruct (_ && _); discriminate E.
    + cbn in E. destruct (_ && _); discriminate E.
Qed.

(** deflate()'s entry moves pending bytes to the output: their sum with the bytes handed out is kept. *)
Lemma entry_cons : forall s z flush s1 z1 o,
  c_deflate_entry s z flush = Some (s1, z1, o) ->
  outok s -> d_bi_valid s <= 7 -> 0 <= z_avail_out z <= 4294967295 -> 0 <= z_total_out z ->
  z_total_out z + z_avail_out z <= 18446744073709551615 ->
  z_total_out z1 + d_pending s1 = z_total_out z + d_pending s.
Proof.
  intros s z flush s1 z1 o E Ho Hb Ha Ht Hta. unfold c_deflate_entry in E.
  assert (Q : forall s2 f, d_pending (set_d_last_flush s2 f) = d_pending s2) by (intros [] f; reflexivity).
  destruct ((d_status s =? FINISH_STATE) && negb (flush =? Z_FINISH)); [injection E as <- <- _; reflexivity|].
  destruct (z_avail_out z =? 0); [injection E as <- <- _; reflexivity|].
  destruct (negb (d_pending (set_d_last_flush s flush) =? 0)).
  - assert (Ho' : outok (set_d_last_flush s flush)) by (destruct s; exact Ho).
    assert (Hb' : d_bi_valid (set_d_last_flush s flush) <= 7) by (destruct s; exact Hb).
    destruct (Zlib.proof.deflate.LTWBEntry.en_flush_pending_ok_w _ z Ho' Hb' Ha Ht Hta)
      as (s2 & x & Ef & _ & Hx & _ & _ & _ & _ & _ & Hp2 & _).
    rewrite Ef in E. cbn [bind] in E.
    assert (Hx0 : 0 <= Zlength x) by apply Zlength_nonneg.
    destruct (_ =? 0); cbn in E.
    + injection E as <- <- _. rewrite Q, Hp2, Q. cbn. lia.
    + destruct (_ && _); injection E as <- <- _; cbn; rewrite Hp2, Q; lia.
  - destruct (z_avail_in z =? 0).
    + cbn [bind] in E. destruct (guard _); cbn in E; [|discriminate E].
      destruct (_ && _); cbn in E; [injection E as <- <- _; rewrite Q; reflexivity|].
      destruct (_ && _); injection E as <- <- _; rewrite Q; reflexivity.
    + cbn in E. destruct (_ && _); injection E as <- <- _; rewrite Q; reflexivity.
Qed.

(** The byte puts of the header stages keep the gzip header and the status. *)
Lemma dput_keep : forall s c s', c_dput_byte s c = Some s' -> d_gzhead s' = d_gzhead s /\ d_status s' = d_status s.
Proof.
  intros s c s' E. unfold c_dput_byte in E. destruct (c_put_byte _ _); cbn [bind] in E; [|discriminate E].
  injection E as <-. destruct s; split; reflexivity.
Qed.

Lemma dputs_keep : forall l s s', c_dput_bytes s l = Some s' -> d_gzhead s' = d_gzhead s /\ d_status s' = d_status s.
Proof.
  induction l as [|c l IH]; intros s s' E; cbn [c_dput_bytes] in E.
  - injection E as <-. split; reflexivity.
  - destruct (c_dput_byte s c) as [s1|] eqn:E1; cbn [bind] in E; [|discriminate E].
    destruct (dput_keep _ _ _ E1), (IH _ _ E). split; congruence.
Qed.

Lemma psm_keep : forall s b s', c_putShortMSB s b = Some s' -> d_gzhead s' = d_gzhead s /\ d_status s' = d_status s.
Proof.
  intros s b s' E. unfold c_putShortMSB in E.
  destruct (c_dput_byte s _) as [s1|] eqn:E1; cbn [bind] in E; [|discriminate E].
  destruct (dput_keep _ _ _ E1), (dput_keep _ _ _ E). split; congruence.
Qed.

(** [flush_pending(strm); if (s->pending != 0) { s->last_flush = -1; return Z_OK; }]: a return fills the
    output space; the status and the gzip header are kept. *)
Lemma for_some : forall s z s2 z2 c, c_flush_or_return s z = Some (s2, z2, Some c) ->
  0 <= z_avail_out z <= 4294967295 -> 0 <= d_pending s2 -> z_avail_out z2 = 0 /\ d_status s2 = d_status s.
Proof.
  intros s z s2 z2 c E Ha Hp. unfold c_flush_or_return in E.
  destruct (c_flush_pending s z) as [[s1 z1]|] eqn:Ef; cbn [bind] in E; [|discriminate E].
  destruct (Z.eqb_spec (d_pending s1) 0) as [E0|E0]; cbn in E; [discriminate E|].
  injection E as <- <- _.
  assert (Q : d_pending (set_d_last_flush s1 (-1)) = d_pending s1) by (destruct s1; reflexivity).
  rewrite Q in Hp. split; [exact (fp_full s z s1 z1 Ef Ha Hp E0)|].
  destruct (fp_keep _ _ _ _ Ef) as [Es _]. destruct s1; exact Es.
Qed.

Lemma for_none : forall s z s2 z2, c_flush_or_return s z = Some (s2, z2, None) ->
  d_status s2 = d_status s /\ d_gzhead s2 = d_gzhead s.
Proof.
  intros s z s2 z2 E. unfold c_flush_or_return in E.
  destruct (c_flush_pending s z) as [[s1 z1]|] eqn:Ef; cbn [bind] in E; [|discriminate E].
  destruct (negb _); [discriminate E|]. injection E as <- <-.
  destruct (fp_keep _ _ _ _ Ef) as [Es _]. split; [exact Es|].
  unfold c_flush_pending in Ef. destruct (c_tr_flush_bits (d_out s)); cbn [bind] in Ef; [|discriminate Ef].
  destruct (_ =? 0); [injection Ef as <- _; destruct s; reflexivity|].
  destruct (mb_read _ _ _); cbn [bind] in Ef; [|discriminate Ef].
  destruct (out_put _ _); cbn [bind] in Ef; [|discriminate Ef].
  injection Ef as <- _. destruct (_ =? 0); destruct s; reflexivity.
Qed.

Lemma zh_some : forall s z s1 z1 c, c_deflate_zlib_header s z = Some (s1, z1, Some c) ->
  0 <= z_avail_out z <= 4294967295 -> 0 <= d_pending s1 -> z_avail_out z1 = 0 /\ d_status s1 = BUSY_STATE.
Proof.
  intros s z s1 z1 c E Ha Hp. unfold c_deflate_zlib_header in E.
  match type of E with context [if d_status ?S =? INIT_STATE then _ else _] =>
    destruct (d_status S =? INIT_STATE) end; [|discriminate E].
  match type of E with context [let* s := c_putShortMSB ?S ?B in _] =>
    destruct (c_putShortMSB S B) as [sa|]; cbn [bind] in E; [|discriminate E] end.
  match type of E with context [let* s := ?X in _] => destruct X as [sb|]; cbn [bind] in E; [|discriminate E] end.
  destruct (for_some _ _ _ _ _ E ltac:(cbn; lia) Hp) as [H1 H2].
  split; [exact H1|]. rewrite H2. destruct sb; reflexivity.
Qed.

Lemma zh_none : forall s z s1 z1, c_deflate_zlib_header s z = Some (s1, z1, None) ->
  (d_status s1 = BUSY_STATE \/ (s1 = s /\ z1 = z)) /\ d_gzhead s1 = d_gzhead s.
Proof.
  intros s z s1 z1 E. unfold c_deflate_zlib_header in E.
  destruct ((d_status s =? INIT_STATE) && (d_wrap s =? 0)) eqn:G.
  - assert (Q : d_status (set_d_status s BUSY_STATE) = BUSY_STATE) by (destruct s; reflexivity).
    rewrite Q in E. cbn in E. injection E as <- <-. split; [left; exact Q|]. destruct s; reflexivity.
  - destruct (d_status s =? INIT_STATE); [|injection E as <- <-; split; [right; auto|reflexivity]].
    destruct (c_putShortMSB s _) as [sa|] eqn:Ea; cbn [bind] in E; [|discriminate E].
    destruct (psm_keep _ _ _ Ea) as [Ga _].
    match type of E with context [let* s := ?X in _] => destruct X as [sb|] eqn:Eb; cbn [bind] in E; [|discriminate E] end.
    assert (Gb : d_gzhead sb = d_gzhead sa).
    { destruct (d_strstart sa =? 0); [injection Eb as <-; reflexivity|].
      destruct (c_putShortMSB sa _) as [sc|] eqn:Ec; cbn [bind] in Eb; [|discriminate Eb].
      destruct (psm_keep _ _ _ Ec), (psm_keep _ _ _ Eb). congruence. }
    destruct (for_none _ _ _ _ E) as [H1 H2]. split.
    + left. rewrite H1. destruct sb; reflexivity.
    + rewrite H2. transitivity (d_gzhead sb); [destruct sb; reflexivity|congruence].
Qed.

Lemma gz_some : forall s z s2 z2 c, c_deflate_gzip_header s z = Some (s2, z2, Some c) -> d_gzhead s = None ->
  0 <= z_avail_out z <= 4294967295 -> 0 <= d_pending s2 -> z_avail_out z2 = 0 /\ d_status s2 = BUSY_STATE.
Proof.
  intros s z s2 z2 c E Hg Ha Hp. unfold c_deflate_gzip_header in E.
  destruct (d_status s =? GZIP_STATE); [|discriminate E].
  destruct (c_dput_bytes s [31; 139; 8]) as [sa|] eqn:Ea; cbn [bind] in E; [|discriminate E].
  destruct (dputs_keep _ _ _ Ea) as [Ga _]. rewrite Ga, Hg in E.
  destruct (c_dput_bytes sa _) as [sb|] eqn:Eb; cbn [bind] in E; [|discriminate E].
  destruct (for_some _ _ _ _ _ E ltac:(cbn; lia) Hp) as [H1 H2].
  split; [exact H1|]. rewrite H2. destruct sb; reflexivity.
Qed.

Lemma gz_none : forall s z s2 z2, c_deflate_gzip_header s z = Some (s2, z2, None) -> d_gzhead s = None ->
  d_gzhead s2 = None.
Proof.
  intros s z s2 z2 E Hg. unfold c_deflate_gzip_header in E.
  destruct (d_status s =? GZIP_STATE); [|injection E as <- <-; exact Hg].
  destruct (c_dput_bytes s [31; 139; 8]) as [sa|] eqn:Ea; cbn [bind] in E; [|discriminate E].
  destruct (dputs_keep _ _ _ Ea) as [Ga _]. rewrite Ga, Hg in E.
  destruct (c_dput_bytes sa _) as [sb|] eqn:Eb; cbn [bind] in E; [|discriminate E].
  destruct (dputs_keep _ _ _ Eb) as [Gb _].
  destruct (for_none _ _ _ _ E) as [_ H2]. rewrite H2. transitivity (d_gzhead sb); [destruct sb; reflexivity|congruence].
Qed.

(** Without a gzip header, the stages of the gzip header's fields fail or do nothing. *)
Lemma tail_none : forall s z s2 z2 c, d_gzhead s = None ->
  then_stage (c_deflate_extra s z) (fun s z =>
  then_stage (c_deflate_name s z) (fun s z =>
  then_stage (c_deflate_comment s z) (fun s z => c_deflate_hcrc s z))) = Some (s2, z2, Some c) -> False.
Proof.
  intros s z s2 z2 c Hg E.
  unfold c_deflate_extra, c_deflate_name, c_deflate_comment, c_deflate_hcrc, c_gzhead, then_stage in E.
  rewrite Hg in E.
  destruct (d_status s =? EXTRA_STATE); cbn in E; rewrite ?Hg in E; cbn in E; [discriminate E|].
  destruct (d_status s =? NAME_STATE); cbn in E; rewrite ?Hg in E; cbn in E; [discriminate E|].
  destruct (d_status s =? COMMENT_STATE); cbn in E; rewrite ?Hg in E; cbn in E; [discriminate E|].
  destruct (d_status s =? HCRC_STATE); cbn in E; rewrite ?Hg in E; cbn in E; discriminate E.
Qed.

(** Without a gzip header given to deflateSetHeader, the header stages return Z_OK only after the zlib or the
    gzip header was put and flush_pending filled the output space; the stream is then compressing. *)
Lemma hdr_stages_ok : forall s z s2 z2 c,
  hdr_stages s z = Some (s2, z2, Some c) -> d_gzhead s = None ->
  0 <= z_avail_out z <= 4294967295 -> 0 <= d_pending s2 ->
  z_avail_out z2 = 0 /\ d_status s2 = BUSY_STATE.
Proof.
  intros s z s2 z2 c E Hg Ha Hp.
  unfold hdr_stages, then_stage in E.
  destruct (c_deflate_zlib_header s z) as [[[s1 z1] [c1|]]|] eqn:E1; cbn [bind] in E; [| |discriminate E].
  { injection E as -> -> _. exact (zh_some s z s2 z2 c1 E1 Ha Hp). }
  - destruct (zh_none s z s1 z1 E1) as [Hs1 Hg1]. clear E1.
    destruct (c_deflate_gzip_header s1 z1) as [[[s3 z3] [c3|]]|] eqn:E3; cbn [bind] in E; [| |discriminate E].
    + injection E as -> -> _.
      destruct Hs1 as [Hb|(-> & ->)].
      * unfold c_deflate_gzip_header in E3. rewrite Hb in E3. cbn in E3. discriminate E3.
      * exact (gz_some s z s2 z2 c3 E3 Hg Ha Hp).
    + assert (Hg3 : d_gzhead s3 = None).
      { apply (gz_none s1 z1 s3 z3 E3). congruence. }
      exfalso. exact (tail_none s3 z3 s2 z2 c Hg3 E).
Qed.

(** The compression stage returns a code only from the compression function's result: Z_OK after need_more or
    finish_started (with its stream), or after block_done. *)
Lemma comp_some : forall s z flush s3 z3 c,
  c_deflate_compress s z flush = Some (s3, z3, Some c) ->
  exists s' z' bs, c_compress_func s z flush = Some (s', z', bs) /\
    (bs = need_more \/ bs = finish_started \/ bs = block_done) /\
    ((bs = need_more \/ bs = finish_started) ->
     z3 = z' /\ d_pending s3 = d_pending s' /\ d_wrap s3 = d_wrap s' /\
     d_status s3 = (match bs with finish_started => FINISH_STATE | _ => d_status s' end)).
Proof.
  intros s z flush s3 z3 c E. unfold c_deflate_compress in E.
  destruct (_ || _ || _); [|discriminate E].
  destruct (c_compress_func s z flush) as [[[s' z'] bs]|] eqn:Ec; cbn [bind] in E; [|discriminate E].
  exists s', z', bs. split; [reflexivity|].
  destruct bs; cbn in E.
  - injection E as <- <- _. split; [left; reflexivity|]. intros _. split; [reflexivity|].
    destruct (z_avail_out z' =? 0); cbn; auto.
  - split; [right; right; reflexivity|]. intros [H|H]; discriminate H.
  - injection E as <- <- _. split; [right; left; reflexivity|]. intros _. split; [reflexivity|].
    destruct (z_avail_out z' =? 0); cbn; auto.
  - discriminate E.
Qed.

(** The compression stage goes on to the trailer when the compression function is not called (no input, no
    lookahead, and Z_NO_FLUSH or the stream finished), or after block_done / finish_done. *)
Lemma comp_none : forall s z flush s3 z3,
  c_deflate_compress s z flush = Some (s3, z3, None) ->
  (z_avail_in z = 0 /\ d_lookahead s = 0 /\ (flush = Z_NO_FLUSH \/ d_status s = FINISH_STATE) /\
   s3 = s /\ z3 = z) \/
  (exists s' z' bs, c_compress_func s z flush = Some (s', z', bs) /\ (bs = block_done \/ bs = finish_done) /\
     (bs = finish_done -> s3 = set_d_status s' FINISH_STATE /\ z3 = z')).
Proof.
  intros s z flush s3 z3 E. unfold c_deflate_compress in E.
  destruct (negb (z_avail_in z =? 0) || negb (d_lookahead s =? 0) ||
            (negb (flush =? Z_NO_FLUSH) && negb (d_status s =? FINISH_STATE))) eqn:G.
  - right. destruct (c_compress_func s z flush) as [[[s' z'] bs]|] eqn:Ec; cbn [bind] in E; [|discriminate E].
    exists s', z', bs. split; [reflexivity|].
    destruct bs; cbn in E.
    + discriminate E.
    + split; [left; reflexivity|]. intros H; discriminate H.
    + discriminate E.
    + injection E as <- <-. split; [right; reflexivity|]. auto.
  - left. injection E as <- <-.
    apply orb_false_iff in G. destruct G as [G1 G2]. apply orb_false_iff in G1. destruct G1 as [G0 G1].
    apply negb_false_iff, Z.eqb_eq in G0. apply negb_false_iff, Z.eqb_eq in G1.
    apply andb_false_iff in G2. destruct G2 as [G2|G2]; apply negb_false_iff, Z.eqb_eq in G2; auto.
Qed.

(** The trailer stage at Z_FINISH returns Z_OK only after flush_pending filled the output space. *)
Lemma trailer_ok : forall s z s4 z4,
  c_deflate_trailer s z Z_FINISH = Some (s4, z4, Z_OK) ->
  0 <= z_avail_out z <= 4294967295 -> 0 <= d_pending s4 -> z_avail_out z4 = 0.
Proof.
  intros s z s4 z4 E Ha Hp. unfold c_deflate_trailer in E. cbn [negb Z.eqb Z_FINISH Pos.eqb] in E.
  destruct (d_wrap s <=? 0); [discriminate E|].
  match type of E with context [let* s := ?X in _] => destruct X as [s1|] end; cbn [bind] in E; [|discriminate E].
  destruct (c_flush_pending s1 z) as [[s2 z2]|] eqn:Ef; cbn [bind] in E; [|discriminate E].
  assert (Q : forall s3 w, d_pending (set_d_wrap s3 w) = d_pending s3) by (intros [] w; reflexivity).
  assert (Q2 : d_pending (if d_wrap s2 >? 0 then set_d_wrap s2 (- d_wrap s2) else s2) = d_pending s2)
    by (destruct (_ >? 0); [apply Q|reflexivity]).
  rewrite Q2 in E.
  destruct (Z.eqb_spec (d_pending s2) 0) as [E0|E0]; cbn in E; [discriminate E|].
  injection E as Es4 <-.
  assert (Hp2 : d_pending s4 = d_pending s2) by (rewrite <- Es4; destruct (_ >? 0); [apply Q|reflexivity]).
  apply (fp_full s1 z s2 z2 Ef Ha); lia.
Qed.

(** The trailer stage puts the trailer still to put into pending_buf and moves pending bytes to the output:
    the bytes handed out, pending and still to put in the trailer add up as before. *)
Lemma trailer_cons : forall s z flush s4 z4 c,
  c_deflate_trailer s z flush = Some (s4, z4, c) ->
  prm s -> outok s -> d_pending s = 0 -> d_po s = 0 -> d_sym_next s = 0 -> d_bi_valid s <= 7 -> d_wrap s <= 2 ->
  0 <= z_avail_out z <= 4294967295 -> 0 <= z_total_out z <= 13835058055282163712 ->
  d_status s4 = d_status s /\ z_total_out z4 + d_pending s4 + tleft s4 = z_total_out z + d_pending s + tleft s.
Proof.
  intros s z flush s4 z4 c E Hp Ho Hpd Hpo Hsy Hbv Hw Ha Ht. unfold c_deflate_trailer in E.
  destruct (negb (flush =? Z_FINISH)); [injection E as <- <- _; auto|].
  destruct (Z.leb_spec (d_wrap s) 0) as [Hw0|Hw0]; [injection E as <- <- _; auto|].
  destruct (Zlib.proof.deflate.LTBTrail.tb_put_trailer s (z_adler z) (z_total_in z) Hp Ho Hpd Hpo Hsy
              ltac:(lia)) as (s1 & E1 & Ho1 & _ & (A1 & A2 & _) & Hb1 & Hp1).
  rewrite E1 in E. cbn [bind] in E.
  destruct (Zlib.proof.deflate.LTWBTrail.tw_flush_pending_ok s1 z Ho1 ltac:(lia) Ha Ht)
    as (s2 & x & Ef & _ & Hx & _ & _ & _ & (B1 & B2 & _) & _ & Hp2 & _).
  rewrite Ef in E. cbn [bind] in E.
  assert (Hw2 : d_wrap s2 = d_wrap s) by congruence.
  rewrite Hw2 in E. destruct (Z.gtb_spec (d_wrap s) 0) as [_|G]; [|lia].
  injection E as <- <- _.
  assert (Q1 : d_pending (set_d_wrap s2 (- d_wrap s)) = d_pending s2) by (destruct s2; reflexivity).
  assert (Q2 : d_wrap (set_d_wrap s2 (- d_wrap s)) = - d_wrap s) by (destruct s2; reflexivity).
  assert (Q3 : d_status (set_d_wrap s2 (- d_wrap s)) = d_status s2) by (destruct s2; reflexivity).
  unfold tleft. rewrite Q1, Q2, Q3.
  destruct (Z.ltb_spec 0 (- d_wrap s)) as [G|_]; [lia|].
  destruct (Z.ltb_spec 0 (d_wrap s)) as [_|G]; [|lia].
  split; [congruence|]. rewrite Hpd. cbn [z_total_out]. lia.
Qed.

