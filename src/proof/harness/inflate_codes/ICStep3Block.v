(* The block cases TYPE, TYPEDO, STORED, COPY_, COPY and the trailer cases CHECK, LENGTH, DONE, BAD
   preserve mwf3x (ICStep3Stmts.v).  The fixed tables: FixedValid2.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.harness.inflate_codes.ICStep3Stmts.
Import ListNotations.
Local Open Scope Z_scope.

Require Import Zlib.proof.inflate.FixedValid2.
Require Import Zlib.proof.crc32.Combine.

(* ---------------------------------------------------------------------------------------------- *)
(* modes that need nothing of the state (no table, no code lengths)                              *)

Definition plain_md (md: Z) : Prop := md <> LENLENS /\ md <> CODELENS /\ ~ decode_mode md.

Ltac plain_tac :=
  unfold plain_md, decode_mode, HEAD, SYNC, Model.TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, CHECK, LENGTH, DONE,
    BAD, LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT; lia.

Lemma modewf_plain: forall s, plain_md (i_mode s) -> modewf s.
Proof.
  intros s P. unfold plain_md, decode_mode in P.
  constructor; try (intros E; exfalso; unfold decode_mode, LENEXT, DIST, DISTEXT, MATCH in *; lia).
  repeat split; intros E; exfalso; unfold LENEXT, DIST, DISTEXT, MATCH in *; lia.
Qed.

Lemma xwf3_plain: forall m, plain_md (m_mode m) -> (m_mode m = HEAD -> i_wbits (m_s m) = 0 -> i_wrap (m_s m) <> 0 -> i_wsize (m_s m) = 0 /\ i_win (m_s m) = false) -> xwf3 m.
Proof.
  intros m P H. unfold plain_md, decode_mode in P.
  constructor; auto; try (intros E; exfalso; unfold decode_mode, LENEXT, DIST, DISTEXT, MATCH in *; lia).
Qed.

(* a new state of a plain mode, the mode unchanged *)
Lemma mwf3x_set_s_plain: forall m s', mwf3x m -> swf s' -> i_mode s' = m_mode m -> plain_md (i_mode s') ->
  (i_mode s' = HEAD -> i_wbits s' = 0 -> i_wrap s' <> 0 -> i_wsize s' = 0 /\ i_win s' = false) -> mwf3x (set_m_s m s').
Proof.
  intros m s' [W X] S E P B. constructor.
  - destruct W. constructor; simpl; auto.
    + apply modewf_plain; auto.
    + unfold m_mode in *; simpl; rewrite E; auto.
  - apply xwf3_plain; auto.
Qed.

(* the machine fields *)
Ltac mfield W m := destruct W as [W X]; constructor;
  [destruct W; constructor; simpl; auto | apply xwf3_ext with m; auto].

Lemma mwf3x_set_ret: forall m r, mwf3x m -> -5 <= r <= 2 -> mwf3x (set_m_ret m r).
Proof. intros m r W H. mfield W m. Qed.

Lemma mwf3x_set_msg: forall m e, mwf3x m -> mwf3x (set_m_msg m e).
Proof. intros m e W. mfield W m. Qed.

Lemma mwf3x_set_tout: forall m x, mwf3x m -> lrange x -> mwf3x (set_m_tout m x).
Proof. intros m x W H. mfield W m. Qed.

Lemma mwf3x_set_adler: forall m x, mwf3x m -> lrange x -> mwf3x (set_m_adler m x).
Proof. intros m x W H. mfield W m. Qed.

Lemma mwf3x_set_out_late: forall m x, mwf3x m -> urange x ->
  (m_mode m = LENGTH \/ m_mode m = DONE \/ m_mode m = BAD) -> mwf3x (set_m_out m x).
Proof. intros m x W H M. mfield W m. all: try (right; exact M). Qed.

Lemma mwf3x_bad: forall m e, mwf3x m -> (m_out m = m_aout m \/ True) -> mwf3x (set_bad m e).
Proof.
  intros m e W _. unfold set_bad. apply mwf3x_set_mode_plain; [apply mwf3x_set_msg; auto | plain_tac | plain_tac |
    plain_tac | plain_tac | right; right; right; reflexivity].
Qed.

Lemma lrange_u64: forall x, lrange (u64 x).
Proof. intros x. unfold lrange, u64. pose proof (Z.mod_pos_bound x (2 ^ 64)). rep_lia. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* DONE, BAD, LENGTH                                                                              *)

Lemma c_DONE_any: forall m, mwf3x m -> iout_ok mwf3x (c_DONE m).
Proof.
  intros m W. unfold c_DONE, iout_ok. apply mwf3x_set_leave, mwf3x_set_ret; auto. unfold Z_STREAM_END; lia.
Qed.

Lemma c_BAD_any: forall m, mwf3x m -> iout_ok mwf3x (c_BAD m).
Proof.
  intros m W. unfold c_BAD, iout_ok. apply mwf3x_set_leave, mwf3x_set_ret; auto. unfold Z_DATA_ERROR; lia.
Qed.


Lemma TYPEDO_ok : ok_TYPEDO.
Proof.
  intros flush m W L Md. unfold c_TYPEDO. cbv beta zeta.
  assert (PM: forall x, m_mode x = m_mode m -> plain_md (m_mode x)).
  { intros x E; rewrite E. destruct Md as [Md | Md]; rewrite Md; plain_tac. }
  assert (OE: forall x, mwf3x x -> m_mode x = m_mode m -> m_out x = m_aout x).
  { intros x Wx E. apply (mwf_out_eq _ (m3_w _ Wx)); rewrite E; destruct Md as [Md | Md]; rewrite Md; plain_tac. }
  destruct (negb (i_last (m_s m) =? 0)).
  { apply mwf3x_set_mode_plain; try plain_tac; [apply mwf3x_bytebits; auto|].
    left. change (m_out m = m_aout m). apply OE; auto. }
  set (m1 := needbits 3 m).
  assert (W1: mwf3x m1) by (apply mwf3x_needbits; auto; lia).
  destruct (Z.eqb_spec (m_leave m1) 1) as [E | E]; [exact W1|].
  destruct (needbits_ok 3 m (m3_w _ W) L ltac:(lia) E) as [NB L1]. fold m1 in NB, L1.
  assert (Md1: m_mode m1 = m_mode m) by (unfold m1, m_mode; rewrite needbits_s; reflexivity).
  set (m2 := dropbits 1 (upd_s m1 (fun s => set_i_last s (bitsn m1 1)))).
  assert (W2: mwf3x m2).
  { apply mwf3x_dropbits; [| simpl; lia]. unfold upd_s. apply mwf3x_set_s_plain; auto.
    - destruct (mw_s _ (m3_w _ W1)). constructor; simpl; auto.
      pose proof (bitsn_range m1 1 ltac:(lia)). simpl in H. lia.
    - simpl. change (plain_md (m_mode m1)). apply PM; auto.
    - simpl. apply (x3_head _ (m3_x _ W1)). }
  assert (Md2: m_mode m2 = m_mode m) by exact Md1.
  assert (B2: 2 <= m_bits m2).
  { unfold m2, dropbits. simpl. unfold u32. rewrite Z.mod_small; destruct (m3_w _ W1); lia. }
  assert (OE2: m_out m2 = m_aout m2) by (apply OE; auto).
  clearbody m2.
  destruct (bitsn m2 2 =? 0).
  { unfold iout_ok. apply mwf3x_dropbits; [| simpl; lia].
    apply mwf3x_set_mode_plain; try plain_tac; auto. }
  destruct (bitsn m2 2 =? 1).
  { set (m3 := set_mode (upd_s m2 (fun s => set_i_distbits (set_i_distcode (set_i_lenbits
                 (set_i_lencode s TLenfix) 9) TDistfix) 5)) LEN_).
    assert (W3: mwf3x m3).
    { apply mwf3x_set_mode; try plain_tac;
        try (intros EE; exfalso; unfold LEN_, LENLENS, CODELENS, LENEXT, DISTEXT, MATCH, DIST in EE; lia).
      - unfold upd_s. apply mwf3x_set_s_plain; auto.
        + destruct (mw_s _ (m3_w _ W2)). constructor; simpl; auto; lia.
        + simpl. change (plain_md (m_mode m2)). apply PM; auto.
        + simpl. apply (x3_head _ (m3_x _ W2)).
      - intros _. simpl. split; [apply lvalid_fixed | apply (proj2 (tvalid_fixed2 _))].
      - left. exact OE2. }
    assert (B3: 0 <= 2 <= m_bits m3) by (simpl; lia).
    destruct (flush =? Z_TREES); unfold iout_ok;
      [apply mwf3x_set_leave|]; apply mwf3x_dropbits; auto. }
  destruct (bitsn m2 2 =? 2).
  { unfold iout_ok. apply mwf3x_dropbits; [| simpl; lia].
    apply mwf3x_set_mode_plain; try plain_tac; auto. }
  unfold iout_ok. apply mwf3x_dropbits; [| simpl; lia]. apply mwf3x_bad; auto.
Qed.

Lemma TYPE_ok : ok_TYPE.
Proof.
  intros flush m W L Md. unfold c_TYPE.
  destruct (orb _ _); [apply mwf3x_set_leave; exact W|].
  apply TYPEDO_ok; auto.
Qed.

Lemma COPY_ok : ok_COPY.
Proof.
  intros m W L Md. unfold c_COPY. cbv beta zeta.
  pose proof (mwf_left _ (m3_w _ W)) as HL. pose proof (mwf_have _ (m3_w _ W)) as HH.
  pose proof (sw_length _ (mw_s _ (m3_w _ W))) as HLen.
  destruct (negb (i_length (m_s m) =? 0)).
  - set (copy := Z.min (Z.min (i_length (m_s m)) (m_have m)) (m_left m)).
    destruct (Z.eqb_spec copy 0) as [E0 | E0]; [apply mwf3x_set_leave; auto|].
    assert (C1: copy <= Z.min (i_length (m_s m)) (m_have m)) by apply Z.le_min_l.
    assert (C2: copy <= m_left m) by apply Z.le_min_r.
    pose proof (Z.le_min_l (i_length (m_s m)) (m_have m)). pose proof (Z.le_min_r (i_length (m_s m)) (m_have m)).
    assert (C0: 0 <= copy) by (unfold copy; repeat apply Z.min_glb; unfold urange in HLen; lia).
    unfold m_have, m_left in *.
    assert (W1: mwf3x (set_m_nx (set_m_ow m (m_ow m ++ inbytes m copy)) (m_nx m + copy))).
    { assert (ZI: Zlength (inbytes m copy) = copy).
      { unfold inbytes. rewrite Zlength_sublist; try lia; pose proof (mw_nx _ (m3_w _ W)); lia. }
      mfield W m; rewrite ?Zlength_app, ?ZI; try lia.
      split; [lia|]. unfold bytes_ok. apply Forall_app. split; [apply mw_ow|].
      unfold inbytes. apply Forall_sublist. apply mw_inp. }
    unfold iout_ok, upd_s. apply mwf3x_set_s_plain; auto.
    + destruct (mw_s _ (m3_w _ W)). constructor; simpl; auto. unfold urange in *; lia.
    + simpl. change (plain_md (m_mode m)). rewrite Md. plain_tac.
    + simpl. apply (x3_head _ (m3_x _ W)).
  - unfold iout_ok. apply mwf3x_set_mode_plain; auto; try plain_tac.
    left. apply (mwf_out_eq _ (m3_w _ W)); rewrite Md; plain_tac.
Qed.

Lemma COPY__ok : ok_COPY_.
Proof.
  intros m W L Md. unfold c_COPY_. apply COPY_ok; [| exact L | reflexivity].
  apply mwf3x_set_mode_plain; auto; try plain_tac.
  left. apply (mwf_out_eq _ (m3_w _ W)); rewrite Md; plain_tac.
Qed.

Lemma STORED_ok : ok_STORED.
Proof.
  intros flush m W L Md. unfold c_STORED. cbv beta zeta.
  set (m1 := needbits 32 (bytebits m)).
  assert (W1: mwf3x m1) by (apply mwf3x_needbits; [apply mwf3x_bytebits; auto | lia]).
  destruct (Z.eqb_spec (m_leave m1) 1) as [E | E]; [exact W1|].
  destruct (needbits_ok 32 (bytebits m) (m3_w _ (mwf3x_bytebits _ W)) L ltac:(lia) E) as [NB L1].
  fold m1 in NB, L1.
  assert (Md1: m_mode m1 = STORED) by (unfold m1, m_mode; rewrite needbits_s; exact Md).
  destruct (negb _); [apply mwf3x_bad; auto|].
  set (m2 := set_mode (initbits (upd_s m1 (fun s => set_i_length s (m_hold m1 mod 65536)))) COPY_).
  assert (W2: mwf3x m2).
  { apply mwf3x_set_mode_plain; try plain_tac.
    - apply mwf3x_initbits. unfold upd_s. apply mwf3x_set_s_plain; auto.
      + destruct (mw_s _ (m3_w _ W1)). constructor; simpl; auto.
        unfold urange. pose proof (Z.mod_pos_bound (m_hold m1) 65536). rep_lia.
      + simpl. change (plain_md (m_mode m1)). rewrite Md1. plain_tac.
      + simpl. apply (x3_head _ (m3_x _ W1)).
    - left. change (m_out m1 = m_aout m1). apply (mwf_out_eq _ (m3_w _ W1)); rewrite Md1; plain_tac. }
  destruct (flush =? Z_TREES); [apply mwf3x_set_leave; exact W2|].
  apply COPY__ok; [exact W2 | exact L1 | reflexivity].
Qed.

Lemma DONE_ok : ok_DONE.
Proof. intros m W _ _. apply c_DONE_any; auto. Qed.

Lemma BAD_ok : ok_BAD.
Proof. intros m W _ _. apply c_BAD_any; auto. Qed.

Lemma LENGTH_ok : ok_LENGTH.
Proof.
  intros m W L Md. unfold c_LENGTH. cbv beta zeta.
  destruct (andb (negb (i_wrap (m_s m) =? 0)) (negb (i_flags (m_s m) =? 0))).
  - assert (W1: mwf3x (needbits 32 m)) by (apply mwf3x_needbits; auto; lia).
    destruct (Z.eqb_spec (m_leave (needbits 32 m)) 1) as [E | E]; [exact W1|].
    destruct (andb _ _).
    + apply mwf3x_bad; auto.
    + apply c_DONE_any. apply mwf3x_set_mode_plain; [apply mwf3x_initbits; auto | plain_tac | plain_tac |
        plain_tac | plain_tac | right; right; left; reflexivity].
  - apply c_DONE_any. apply mwf3x_set_mode_plain; [auto | plain_tac | plain_tac |
        plain_tac | plain_tac | right; right; left; reflexivity].
Qed.

(* the end of CHECK: out = left, then the check comparison *)
Lemma check_fin: forall mc (b: bool), mwf3x mc -> m_mode mc = CHECK -> m_leave mc = 0 ->
  iout_ok mwf3x (if b then IBrk (set_bad (set_m_out mc (m_left mc)) M_dcheck)
                else c_LENGTH (set_mode (initbits (set_m_out mc (m_left mc))) LENGTH)).
Proof.
  intros mc b W Md L. pose proof (mwf_left _ (m3_w _ W)) as HL.
  destruct b.
  - unfold iout_ok.
    change (set_bad (set_m_out mc (m_left mc)) M_dcheck) with (set_m_out (set_bad mc M_dcheck) (m_left mc)).
    apply mwf3x_set_out_late; [apply mwf3x_bad; auto | unfold urange; rep_lia | right; right; reflexivity].
  - change (set_mode (initbits (set_m_out mc (m_left mc))) LENGTH)
      with (set_m_out (set_mode (initbits mc) LENGTH) (m_left mc)).
    apply LENGTH_ok; [| exact L | reflexivity].
    apply mwf3x_set_out_late; [| unfold urange; rep_lia | left; reflexivity].
    apply mwf3x_set_mode_plain; try plain_tac. apply mwf3x_initbits; auto.
Qed.

Lemma CHECK_ok : ok_CHECK.
Proof.
  intros m W L Md. unfold c_CHECK. cbv beta zeta.
  destruct (negb (i_wrap (m_s m) =? 0)).
  2:{ apply LENGTH_ok; [| exact L | reflexivity].
      apply mwf3x_set_mode_plain; try plain_tac; auto. }
  set (m1 := needbits 32 m).
  assert (W1: mwf3x m1) by (apply mwf3x_needbits; auto; lia).
  destruct (Z.eqb_spec (m_leave m1) 1) as [E | E]; [exact W1|].
  destruct (needbits_ok 32 m (m3_w _ W) L ltac:(lia) E) as [NB L1]. fold m1 in NB, L1.
  assert (Md1: m_mode m1 = CHECK) by (unfold m1, m_mode; rewrite needbits_s; exact Md).
  assert (OE1: m_out m1 = m_aout m1) by (apply (mwf_out_eq _ (m3_w _ W1)); rewrite Md1; plain_tac).
  clearbody m1.
  set (o := u32 (m_out m1 - m_left m1)).
  assert (Ho: o = Zlength (m_ow m1)).
  { unfold o, u32, m_left. rewrite OE1. pose proof (mw_ow _ (m3_w _ W1)). pose proof (mw_aout _ (m3_w _ W1)). pose proof (Zlength_nonneg (m_ow m1)).
    rewrite Z.mod_small; rep_lia. }
  clearbody o.
  set (mb := upd_s (set_m_tout m1 (u64 (m_tout m1 + o))) (fun s => set_i_total s (u64 (i_total s + o)))).
  assert (Wb: mwf3x mb).
  { unfold mb, upd_s. apply mwf3x_set_s_plain.
    - apply mwf3x_set_tout; auto. apply lrange_u64.
    - destruct (mw_s _ (m3_w _ W1)). constructor; simpl; auto. apply lrange_u64.
    - reflexivity.
    - simpl. change (plain_md (m_mode m1)). rewrite Md1. plain_tac.
    - simpl. apply (x3_head _ (m3_x _ W1)). }
  assert (Mdb: m_mode mb = CHECK) by exact Md1.
  assert (Lb: m_leave mb = 0) by exact L1.
  assert (Owb: m_ow mb = m_ow m1) by reflexivity.
  clearbody mb.
  destruct (andb _ (negb (o =? 0))); [| apply check_fin; auto].
  set (c := update_check (i_flags (m_s mb)) (i_check (m_s mb))
              (sublist (Zlength (m_ow mb) - o) (Zlength (m_ow mb)) (m_ow mb))).
  assert (Hc: lrange c).
  { assert (IB: is_bytes (sublist (Zlength (m_ow mb) - o) (Zlength (m_ow mb)) (m_ow mb))).
    { unfold is_bytes. apply Forall_sublist. apply (mw_ow _ (m3_w _ Wb)). }
    unfold c, update_check, lrange. destruct (i_flags (m_s mb) =? 0).
    - pose proof (adler32_z_val_range (i_check (m_s mb)) _ IB). rep_lia.
    - pose proof (ref_crc32_range (i_check (m_s mb)) _ IB). unfold is32 in H. rep_lia. }
  clearbody c.
  apply check_fin; auto.
  apply mwf3x_set_adler; auto. unfold upd_s. apply mwf3x_set_s_plain; auto.
  - destruct (mw_s _ (m3_w _ Wb)). constructor; simpl; auto.
  - simpl. change (plain_md (m_mode mb)). rewrite Mdb. plain_tac.
  - simpl. apply (x3_head _ (m3_x _ Wb)).
Qed.

(* all the cases of this file in one statement *)
Lemma block_all : ok_TYPEDO /\ ok_TYPE /\ ok_STORED /\ ok_COPY /\ ok_COPY_ /\ ok_DONE /\ ok_BAD /\
  ok_LENGTH /\ ok_CHECK.
Proof.
  split; [exact TYPEDO_ok|]. split; [exact TYPE_ok|]. split; [exact STORED_ok|]. split; [exact COPY_ok|].
  split; [exact COPY__ok|]. split; [exact DONE_ok|]. split; [exact BAD_ok|]. split; [exact LENGTH_ok|].
  exact CHECK_ok.
Qed.
