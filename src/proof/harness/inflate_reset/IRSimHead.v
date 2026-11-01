(* Law inflate_reset, theory part: one pass of HEAD from related machines (the only part that unfolds c_HEAD2). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_reset.IRDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* NEEDBITS(16) in HEAD (as inflate_codes' TheoryHead.v)                                          *)

Lemma irh_byte src pos inp k :
  ir_ctx src pos inp -> 0 <= k < Zlength inp ->
  Znth k inp = Znth (pos + k) src /\ 0 <= Znth (pos + k) src <= 255.
Proof.
  intros (Hp & Hl & Hb & He) Hk. split; [apply He; auto|].
  unfold bytes_ok in Hb. rewrite Forall_forall in Hb.
  assert (0 <= pos + k < Zlength src) by lia.
  pose proof (Hb (Znth (pos + k) src)) as X. replace Byte.max_unsigned with 255 in X by reflexivity.
  apply X. apply Znth_In; lia.
Qed.

Lemma irh_srcbyte src k : bytes_ok src -> 0 <= k < Zlength src -> 0 <= Znth k src <= 255.
Proof.
  intros Hb Hk. unfold bytes_ok in Hb. rewrite Forall_forall in Hb.
  pose proof (Hb (Znth k src)) as X. replace Byte.max_unsigned with 255 in X by reflexivity.
  apply X, Znth_In; lia.
Qed.

Lemma irh_pull m src pos :
  ir_ctx src pos (m_inp m) -> 0 <= m_nx m < Zlength (m_inp m) ->
  0 <= pos + m_nx m <= 1 -> m_bits m = 8 * (pos + m_nx m) ->
  m_hold m = ir_le (sublist 0 (pos + m_nx m) src) ->
  pull m = set_m_bits (set_m_hold (set_m_nx m (m_nx m + 1)) (ir_le (sublist 0 (pos + (m_nx m + 1)) src)))
                      (8 * (pos + (m_nx m + 1))).
Proof.
  intros Hc Hn Hp Hb Hh.
  destruct (irh_byte src pos (m_inp m) (m_nx m) Hc Hn) as [Eb Rb].
  pose proof Hc as (H0 & Hl & _).
  unfold pull. rewrite Eb, Hb, Hh. f_equal; [f_equal|].
  - assert (pos + m_nx m = 0 \/ pos + m_nx m = 1) as [E|E] by lia.
    + rewrite E in *. replace (pos + (m_nx m + 1)) with 1 by lia.
      rewrite (sublist_one 0 1 src) by lia. rewrite sublist_nil. cbn [ir_le].
      change (2 ^ (8 * 0)) with 1. unfold u64. rewrite Z.mod_small; lia.
    + rewrite E in *. replace (pos + (m_nx m + 1)) with 2 by lia.
      rewrite (sublist_one 0 1 src) by lia.
      rewrite (sublist_split 0 1 2 src), (sublist_one 0 1 src), (sublist_one 1 2 src) by lia.
      cbn [ir_le app].
      assert (0 <= Znth 0 src <= 255).
      { destruct Hc as (_ & _ & Hbo & _). apply irh_srcbyte; auto; lia. }
      change (2 ^ (8 * 1)) with 256. unfold u64. rewrite Z.mod_small; lia.
  - unfold u32. rewrite Z.mod_small; lia.
Qed.

Lemma irh_same m : set_m_bits (set_m_hold (set_m_nx m (m_nx m)) (m_hold m)) (m_bits m) = m.
Proof. destruct m; reflexivity. Qed.

Lemma irh_nbS k n m :
  needbits_f (S k) n m = if m_bits m <? n then if m_have m =? 0 then set_leave m else needbits_f k n (pull m) else m.
Proof. reflexivity. Qed.

Lemma irh_nb m src pos :
  ir_ctx src pos (m_inp m) -> 0 <= m_nx m <= Zlength (m_inp m) ->
  ir_hd src (pos + m_nx m) (m_hold m) (m_bits m) ->
  exists nx', m_nx m <= nx' <= Zlength (m_inp m) /\
   ((needbits 16 m = set_leave (set_m_bits (set_m_hold (set_m_nx m nx') (ir_le (sublist 0 (pos + nx') src)))
                                          (8 * (pos + nx'))) /\ pos + nx' <= 1) \/
    (needbits 16 m = set_m_bits (set_m_hold (set_m_nx m nx') (ir_le (sublist 0 2 src))) 16 /\ pos + nx' = 2)).
Proof.
  intros Hc Hn (Hp & Hb & Hh). unfold needbits. rewrite irh_nbS.
  rewrite Hb. replace (8 * (pos + m_nx m) <? 16) with true by (symmetry; apply Z.ltb_lt; lia).
  destruct (m_have m =? 0) eqn:E0.
  { exists (m_nx m). split; [lia|]. left. split; [|lia]. rewrite <- Hh, <- Hb, irh_same. reflexivity. }
  unfold m_have in E0. apply Z.eqb_neq in E0.
  rewrite (irh_pull m src pos) by (auto; lia).
  set (m1 := set_m_bits _ _).
  assert (Hc1 : ir_ctx src pos (m_inp m1)) by exact Hc.
  assert (Hnx1 : m_nx m1 = m_nx m + 1) by reflexivity.
  assert (Hb1 : m_bits m1 = 8 * (pos + (m_nx m + 1))) by reflexivity.
  assert (Hh1 : m_hold m1 = ir_le (sublist 0 (pos + (m_nx m + 1)) src)) by reflexivity.
  assert (Hi1 : m_inp m1 = m_inp m) by reflexivity.
  assert (pos + m_nx m = 0 \/ pos + m_nx m = 1) as [P|P] by lia.
  - rewrite irh_nbS, Hb1. replace (8 * (pos + (m_nx m + 1)) <? 16) with true by (symmetry; apply Z.ltb_lt; lia).
    destruct (m_have m1 =? 0) eqn:E1.
    { exists (m_nx m + 1). split; [lia|]. left. split; [|lia].
      reflexivity. }
    unfold m_have in E1. apply Z.eqb_neq in E1. rewrite Hi1, Hnx1 in E1.
    rewrite (irh_pull m1 src pos) by (rewrite ?Hi1, ?Hnx1; auto; lia).
    rewrite irh_nbS. cbn [m_bits set_m_bits]. rewrite Hnx1.
    replace (8 * (pos + (m_nx m + 1 + 1)) <? 16) with false by (symmetry; apply Z.ltb_ge; lia).
    exists (m_nx m + 1 + 1). split; [lia|]. right. split; [|lia].
    replace (pos + (m_nx m + 1 + 1)) with 2 by lia. unfold m1.
    destruct m; reflexivity.
  - rewrite irh_nbS, Hb1. replace (8 * (pos + (m_nx m + 1)) <? 16) with false by (symmetry; apply Z.ltb_ge; lia).
    exists (m_nx m + 1). split; [lia|]. right. split; [|lia].
    unfold m1. replace (pos + (m_nx m + 1)) with 2 by lia. reflexivity.
Qed.

(* NEEDBITS does not touch the state nor the header *)
Lemma irh_nb_sh k n m s h :
  needbits_f k n (set_m_h (set_m_s m s) h) = set_m_h (set_m_s (needbits_f k n m) s) h.
Proof.
  revert m. induction k as [|k IH]; intros m; [reflexivity|].
  rewrite !irh_nbS. cbn [m_bits set_m_h set_m_s].
  destruct (m_bits m <? n); [|reflexivity].
  unfold m_have. cbn [m_inp m_nx set_m_h set_m_s].
  destruct (Zlength (m_inp m) - m_nx m =? 0); [reflexivity|].
  replace (pull (set_m_h (set_m_s m s) h)) with (set_m_h (set_m_s (pull m) s) h) by (destruct m; reflexivity).
  apply IH.
Qed.

Lemma irh_nb_sh16 m s h :
  needbits 16 (set_m_h (set_m_s m s) h) = set_m_h (set_m_s (needbits 16 m) s) h.
Proof. apply irh_nb_sh. Qed.

Lemma irh_mrel_eq ma mb : mrel ma mb -> ma = set_m_h (set_m_s mb (m_s ma)) (m_h ma).
Proof.
  intros R. destruct R. destruct ma, mb; cbn in *; subst; reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The header bytes                                                                               *)

Lemma irh_le2 src : 2 <= Zlength src ->
  ir_le (sublist 0 2 src) = Znth 0 src + 256 * Znth 1 src.
Proof.
  intros L. rewrite (sublist_split 0 1 2 src), (sublist_one 0 1 src), (sublist_one 1 2 src) by lia.
  cbn [ir_le app]. lia.
Qed.

Lemma irh_hdr_facts b0 b1 : 0 <= b0 <= 255 -> 0 <= b1 <= 255 ->
  (b0 + 256 * b1) mod 256 = b0 /\ Z.shiftr (b0 + 256 * b1) 8 = b1 /\
  (b0 + 256 * b1) mod 16 = Z.land b0 15 /\ Z.shiftr (b0 + 256 * b1) 4 mod 16 = Z.shiftr b0 4 /\
  ((b0 + 256 * b1 =? 35615) = ((b0 =? 31) && (b1 =? 139)))%bool.
Proof.
  intros H0 H1. split; [|split; [|split; [|split]]].
  - replace (b0 + 256 * b1) with (b0 + b1 * 256) by lia. rewrite Z_mod_plus_full. apply Z.mod_small; lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace (b0 + 256 * b1) with (b0 + b1 * 256) by lia. rewrite Z.div_add by lia.
    rewrite Z.div_small by lia. lia.
  - change 15 with (Z.ones 4). rewrite Z.land_ones by lia. change (2 ^ 4) with 16.
    replace (b0 + 256 * b1) with (b0 + (16 * b1) * 16) by lia. apply Z_mod_plus_full.
  - rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
    replace (b0 + 256 * b1) with (b0 + (16 * b1) * 16) by lia. rewrite Z.div_add by lia.
    replace (b0 / 16 + 16 * b1) with (b0 / 16 + b1 * 16) by lia. rewrite Z_mod_plus_full.
    apply Z.mod_small. split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia.
  - destruct (Z.eqb_spec (b0 + 256 * b1) 35615), (Z.eqb_spec b0 31), (Z.eqb_spec b1 139); cbn; auto; lia.
Qed.

(* the gzip branch of HEAD is taken: hdr_wb is 15 *)
Lemma irh_hdr_gz wrap src : 2 <= Zlength src -> bytes_ok src ->
  (negb (Z.land wrap 2 =? 0) && (ir_le (sublist 0 2 src) =? 35615))%bool = true ->
  hdr_wb wrap src = Some 15.
Proof.
  intros L Hb G. rewrite irh_le2 in G by lia.
  pose proof (irh_srcbyte src 0 Hb ltac:(lia)). pose proof (irh_srcbyte src 1 Hb ltac:(lia)).
  destruct (irh_hdr_facts (Znth 0 src) (Znth 1 src)) as (_ & _ & _ & _ & E); auto.
  rewrite E in G. unfold hdr_wb.
  replace (Zlength src <? 2) with false by (symmetry; apply Z.ltb_ge; lia). cbv zeta.
  rewrite andb_assoc in G. rewrite G. reflexivity.
Qed.

(* the zlib branch of HEAD (check and method accepted): hdr_wb is the window size if it is <= 15 *)
Lemma irh_hdr_zl wrap src : 2 <= Zlength src -> bytes_ok src ->
  let H2 := ir_le (sublist 0 2 src) in
  (negb (Z.land wrap 2 =? 0) && (H2 =? 35615))%bool = false ->
  Z.land wrap 1 <> 0 ->
  (((H2 mod 256) * 256 + Z.shiftr H2 8) mod 31 =? 0) = true ->
  (H2 mod 16 =? 8) = true ->
  hdr_wb wrap src = if 15 <? Z.shiftr H2 4 mod 16 + 8 then None else Some (Z.shiftr H2 4 mod 16 + 8).
Proof.
  intros L Hb H2 G W1 C M. subst H2. rewrite irh_le2 in * by lia.
  pose proof (irh_srcbyte src 0 Hb ltac:(lia)). pose proof (irh_srcbyte src 1 Hb ltac:(lia)).
  destruct (irh_hdr_facts (Znth 0 src) (Znth 1 src)) as (E1 & E2 & E3 & E4 & E5); auto.
  rewrite E5 in G. rewrite E1, E2 in C. rewrite E3 in M. rewrite E4.
  unfold hdr_wb.
  replace (Zlength src <? 2) with false by (symmetry; apply Z.ltb_ge; lia). cbv zeta.
  rewrite andb_assoc in G. rewrite G.
  replace (negb (Z.land wrap 1 =? 0)) with true by (symmetry; apply negb_true_iff, Z.eqb_neq; auto).
  rewrite C, M. cbn [andb].
  destruct (Z.ltb_spec 15 (Z.shiftr (Znth 0 src) 4 + 8)), (Z.leb_spec (Z.shiftr (Znth 0 src) 4 + 8) 15);
    auto; lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* wbits                                                                                          *)

(* the wbits HEAD stores, when the header gives v: the same on both streams *)
Lemma irh_wnew W0 wrap src w v :
  wcl W0 wrap src w -> hdr_wb wrap src = Some v ->
  (if w =? 0 then v else w) = (if W0 =? 0 then v else W0).
Proof.
  intros [E|(E & Wz & F)] Hv; subst; auto.
  rewrite (F v Hv). destruct (v =? 0); reflexivity.
Qed.

Lemma irh_hdr_wrap wrap src v : hdr_wb wrap src = Some v -> wrap <> 0.
Proof.
  intros Hv Wz. subst wrap. unfold hdr_wb in Hv.
  destruct (Zlength src <? 2); [discriminate|]. cbn in Hv. discriminate.
Qed.

Lemma irh_wcl_new W0 wrap src v :
  hdr_wb wrap src = Some v -> wcl W0 wrap src (if W0 =? 0 then v else W0).
Proof.
  intros Hv. pose proof (irh_hdr_wrap _ _ _ Hv) as Wn. destruct (Z.eqb_spec W0 0) as [E|E].
  - right. split; auto. split; auto. intros v' Hv'. congruence.
  - left. reflexivity.
Qed.

Lemma irh_wcl_none W0 wrap src w len :
  wrap <> 0 -> hdr_wb wrap src = None -> wcl W0 wrap src w -> wcl W0 wrap src (if w =? 0 then len else w).
Proof.
  intros Wn0 Hn [E|(E & Wn & F)].
  - subst. destruct (Z.eqb_spec W0 0) as [E|E].
    + right. split; auto. split; auto. intros v Hv. congruence.
    + left. reflexivity.
  - destruct (w =? 0); right; (split; [auto|]); (split; [auto|]); intros v Hv; congruence.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Building the result                                                                            *)

Ltac irh_red :=
  unfold m_mode; cbn [m_nx m_bits m_hold m_msg m_s m_h m_inp m_aout m_out m_ret m_leave m_adler m_ow m_in
       m_tin m_tout m_snx m_sow
       set_mode upd_s set_m_s set_m_h upd_h set_m_nx set_m_hold set_m_bits set_m_msg set_m_adler
       set_leave set_m_leave set_bad initbits dropbits
       i_mode i_last i_wrap i_havedict i_flags i_dmax i_check i_total i_head i_wbits i_wsize i_whave i_wnext
       i_wdata i_hold i_bits i_lencode i_distcode i_next i_sane i_back i_length i_offset i_extra i_lenbits
       i_distbits i_ncode i_nlen i_ndist i_have i_lens
       set_i_mode set_i_check set_i_wbits set_i_flags set_i_dmax].

Ltac irh_mode_contra :=
  intros; exfalso;
  repeat match goal with H: _ \/ _ |- _ => destruct H end;
  repeat match goal with H: _ /\ _ |- _ => destruct H end;
  repeat match goal with H: lenlive _ |- _ => unfold lenlive in H | H: decode_mode _ |- _ => unfold decode_mode in H end;
  irh_red;
  repeat match goal with H: _ \/ _ |- _ => destruct H end;
  repeat match goal with H: _ /\ _ |- _ => destruct H end;
  unfold HEAD, FLAGS, DICTID, TYPEDO, BAD, Zlib.proof.inflate.Model.TYPE, COPY_, COPY, LENEXT, DIST, DISTEXT,
    MATCH, LIT, EXTRA, CODELENS, LENLENS, LEN_, LEN in *; lia.

(* the states after a pass that leaves mode md, not a mode with live conditional fields *)
Lemma irh_srel N N' sa sb sa' sb' :
  srel N sa sb ->
  i_mode sa' = i_mode sb' ->
  i_last sa' = i_last sa -> i_last sb' = i_last sb ->
  i_wrap sa' = i_wrap sa -> i_wrap sb' = i_wrap sb ->
  i_havedict sa' = i_havedict sa -> i_havedict sb' = i_havedict sb ->
  (i_flags sa' = i_flags sb' \/ (i_flags sa' = i_flags sa /\ i_flags sb' = i_flags sb)) ->
  (i_dmax sa' = i_dmax sb' \/ (i_dmax sa' = i_dmax sa /\ i_dmax sb' = i_dmax sb)) ->
  i_total sa' = i_total sa -> i_total sb' = i_total sb ->
  i_head sa' = i_head sa -> i_head sb' = i_head sb ->
  i_wsize sa' = i_wsize sa -> i_wsize sb' = i_wsize sb ->
  i_whave sa' = i_whave sa -> i_whave sb' = i_whave sb ->
  i_wnext sa' = i_wnext sa -> i_wnext sb' = i_wnext sb ->
  i_wdata sa' = i_wdata sa -> i_wdata sb' = i_wdata sb ->
  i_hold sa' = i_hold sa -> i_hold sb' = i_hold sb ->
  i_bits sa' = i_bits sa -> i_bits sb' = i_bits sb ->
  i_lencode sa' = i_lencode sa -> i_lencode sb' = i_lencode sb ->
  i_distcode sa' = i_distcode sa -> i_distcode sb' = i_distcode sb ->
  i_next sa' = i_next sa -> i_next sb' = i_next sb ->
  i_sane sa' = i_sane sa -> i_sane sb' = i_sane sb ->
  i_back sa' = i_back sa -> i_back sb' = i_back sb ->
  (i_wbits sa' = i_wbits sb' \/ i_mode sb' = HEAD \/ i_mode sb' = BAD) ->
  (i_check sa' = i_check sb' \/ i_wrap sb' = 0 \/ ((i_mode sb' = HEAD \/ i_mode sb' = BAD) /\ N')) ->
  i_mode sb' = HEAD \/ i_mode sb' = BAD \/ i_mode sb' = FLAGS \/ i_mode sb' = TYPEDO \/
    i_mode sb' = Zlib.proof.inflate.Model.TYPE \/ i_mode sb' = DICTID ->
  srel N' sa' sb'.
Proof.
  intros R. destruct R.
  intros Emd El1 El2 Ew1 Ew2 Ehd1 Ehd2 Efl Edm Et1 Et2 Eh1 Eh2 Ews1 Ews2 Ewh1 Ewh2 Ewn1 Ewn2 Ewd1 Ewd2
    Eho1 Eho2 Ebi1 Ebi2 Elc1 Elc2 Edc1 Edc2 Ene1 Ene2 Esa1 Esa2 Eba1 Eba2 Ewb Eck Hmd.
  assert (HM : forall P: Prop, i_mode sb' <> HEAD -> i_mode sb' <> BAD -> i_mode sb' <> FLAGS ->
    i_mode sb' <> TYPEDO -> i_mode sb' <> Zlib.proof.inflate.Model.TYPE -> i_mode sb' <> DICTID -> P).
  { intros P A1 A2 A3 A4 A5 A6. exfalso. destruct Hmd as [X|[X|[X|[X|[X|X]]]]]; congruence. }
  constructor; try congruence;
  try (destruct Efl as [Efl|[Efl1 Efl2]]; congruence);
  try (destruct Edm as [Edm|[Edm1 Edm2]]; congruence);
  try exact Ewb; try exact Eck;
  intros X; apply HM; try (unfold lenlive in X); try (unfold decode_mode in X);
  intros Y; rewrite Y in X;
  unfold HEAD, FLAGS, DICTID, TYPEDO, BAD, Zlib.proof.inflate.Model.TYPE, COPY_, COPY, LENEXT, DIST, DISTEXT,
    MATCH, LIT, EXTRA, CODELENS, LENLENS, LEN_, LEN in X; lia.
Qed.

Lemma irh_Kr W0 wrap src pos inp aout ma' mb' :
  set_m_h (set_m_s mb' (m_s ma')) (m_h ma') = ma' ->
  srel (m_ow mb' = []) (m_s ma') (m_s mb') ->
  m_inp mb' = inp -> m_aout mb' = aout -> i_wrap (m_s mb') = wrap -> i_head (m_s mb') = false ->
  wcl W0 wrap src (i_wbits (m_s ma')) -> wcl W0 wrap src (i_wbits (m_s mb')) ->
  (wrap <> 0 -> m_mode mb' = HEAD -> ir_hd src (pos + m_nx mb') (m_hold mb') (m_bits mb') /\ m_ow mb' = []) ->
  Kr W0 wrap src pos inp aout ma' mb'.
Proof.
  intros E S Hi Ha Hw Hh Hwa Hwb Hhd. constructor; auto.
  rewrite <- E. constructor; cbn [m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler
    m_msg m_tin m_tout m_snx m_sow set_m_s set_m_h]; auto.
Qed.

(* the a-side machine kept in the form set_m_h (set_m_s <b-side> sa) ha (no kernel conversion between
   the two sides' setter chains) *)
Lemma irh_Kr' W0 wrap src pos inp aout mb' sa' ha' :
  srel (m_ow mb' = []) sa' (m_s mb') ->
  m_inp mb' = inp -> m_aout mb' = aout -> i_wrap (m_s mb') = wrap -> i_head (m_s mb') = false ->
  wcl W0 wrap src (i_wbits sa') -> wcl W0 wrap src (i_wbits (m_s mb')) ->
  (wrap <> 0 -> m_mode mb' = HEAD -> ir_hd src (pos + m_nx mb') (m_hold mb') (m_bits mb') /\ m_ow mb' = []) ->
  Kr W0 wrap src pos inp aout (set_m_h (set_m_s mb' sa') ha') mb'.
Proof. intros. apply irh_Kr; auto. Qed.

Lemma c_upd_s M s h f : upd_s (set_m_h (set_m_s M s) h) f = set_m_h (set_m_s (upd_s M f) (f s)) h.
Proof. destruct M; reflexivity. Qed.
Lemma c_set_mode M s h md :
  set_mode (set_m_h (set_m_s M s) h) md = set_m_h (set_m_s (set_mode M md) (set_i_mode s md)) h.
Proof. destruct M; reflexivity. Qed.
Lemma c_initbits M s h : initbits (set_m_h (set_m_s M s) h) = set_m_h (set_m_s (initbits M) s) h.
Proof. destruct M; reflexivity. Qed.
Lemma c_dropbits M s h n : dropbits n (set_m_h (set_m_s M s) h) = set_m_h (set_m_s (dropbits n M) s) h.
Proof. destruct M; reflexivity. Qed.
Lemma c_adler M s h v : set_m_adler (set_m_h (set_m_s M s) h) v = set_m_h (set_m_s (set_m_adler M v) s) h.
Proof. destruct M; reflexivity. Qed.
Lemma c_bad M s h e :
  set_bad (set_m_h (set_m_s M s) h) e = set_m_h (set_m_s (set_bad M e) (set_i_mode s BAD)) h.
Proof. destruct M; reflexivity. Qed.

Ltac irh_norm := repeat rewrite ?c_upd_s, ?c_set_mode, ?c_initbits, ?c_dropbits, ?c_adler, ?c_bad.

Lemma irh_step_head flush m : m_mode m = HEAD -> stepf2 flush lenfix_list distfix_list m = c_HEAD2 m.
Proof. intros H. unfold stepf2, step2. rewrite H. reflexivity. Qed.

Lemma irh_lv1 x : (m_leave (set_leave x) =? 1) = true.
Proof. reflexivity. Qed.

Ltac irh_side :=
  first [ reflexivity | assumption
        | match goal with H: srel _ ?sa _ |- srel _ _ _ =>
            eapply irh_srel; [exact H|..]; irh_red; auto 10; fail end
        | (apply irh_wcl_new; assumption)
        | (apply irh_wcl_none; assumption)
        | (intros _ X; unfold m_mode in X; irh_red;
           unfold HEAD, FLAGS, BAD, Zlib.proof.inflate.Model.TYPE, DICTID in X; lia) ].

Lemma head_core W0 wrap src pos inp aout flush ma mb :
  ir_ctx src pos inp -> Kr W0 wrap src pos inp aout ma mb -> mwf3 mb -> m_leave mb = 0 -> m_mode mb = HEAD ->
  (wrap = 0 -> i_wbits (m_s ma) = i_wbits (m_s mb)) ->
  sim_post W0 wrap src pos inp aout (stepf2 flush lenfix_list distfix_list ma)
    (stepf2 flush lenfix_list distfix_list mb).
Proof.
  intros Hc K Hwf Hl Hmd Hw0.
  destruct K as [R Hinp Haout Hwrap Hhead Hwa Hwb Hhd].
  pose proof (irh_mrel_eq _ _ R) as Ema.
  pose proof (mr_s _ _ R) as S.
  assert (Hmda : m_mode ma = HEAD) by (unfold m_mode; rewrite (sr_mode _ _ _ S); exact Hmd).
  rewrite (irh_step_head flush ma Hmda), (irh_step_head flush mb Hmd).
  rewrite Ema. set (sa := m_s ma) in *. set (ha := m_h ma) in *. clearbody sa ha. clear Ema R Hmda.
  pose proof (Inv.mw_nx _ (proj1 Hwf)) as Hnx.
  subst inp aout.
  unfold c_HEAD2. cbv beta zeta. rewrite !irh_nb_sh16.
  change (i_wrap (m_s (set_m_h (set_m_s mb sa) ha))) with (i_wrap sa).
  rewrite (sr_wrap _ _ _ S), Hwrap.
  destruct (Z.eqb_spec wrap 0) as [Wz|Wz].
  { cbn [sim_post]. irh_norm; apply irh_Kr'; irh_red; auto.
    eapply irh_srel; [exact S|..]; irh_red; auto; try (subst wrap; auto; fail). }
  destruct (Hhd Wz Hmd) as [Hhd1 Hhd2].
  pose proof Hc as (Hpos & Hsrc & Hbytes & _).
  destruct (irh_nb mb src pos Hc Hnx Hhd1) as (nx' & Hn' & [[E Hp]|[E Hp]]); rewrite E.
  { rewrite !irh_lv1. cbn [sim_post]. irh_norm; apply irh_Kr'; irh_red; auto.
    intros _ _. split; [|exact Hhd2]. unfold ir_hd. split; [lia|]. split; reflexivity. }
  set (H2 := ir_le (sublist 0 2 src)) in *.
  irh_red. rewrite Hl. change (0 =? 1) with false. cbv iota.
  rewrite (sr_head _ _ _ S), (sr_wrap _ _ _ S), Hhead, Hwrap. cbv iota. irh_red.
  assert (L2 : 2 <= Zlength src) by lia.
  destruct (negb (Z.land wrap 2 =? 0) && (H2 =? 35615))%bool eqn:G.
  { pose proof (irh_hdr_gz wrap src L2 Hbytes G) as Hgz.
    cbn [sim_post]. irh_norm; apply irh_Kr'; irh_red;
    rewrite ?(irh_wnew _ _ _ _ _ Hwa Hgz), ?(irh_wnew _ _ _ _ _ Hwb Hgz); irh_side. }
  destruct ((Z.land wrap 1 =? 0) || negb ((H2 mod 256 * 256 + Z.shiftr H2 8) mod 31 =? 0))%bool eqn:G1.
  { cbn [sim_post]. irh_norm; apply irh_Kr'; irh_red; irh_side. }
  destruct (negb (H2 mod 16 =? 8)) eqn:G2.
  { cbn [sim_post]. irh_norm; apply irh_Kr'; irh_red; irh_side. }
  apply orb_false_iff in G1. destruct G1 as [G1a G1b]. apply Z.eqb_neq in G1a. apply negb_false_iff in G1b.
  apply negb_false_iff in G2.
  pose proof (irh_hdr_zl wrap src L2 Hbytes G G1a G1b G2) as Hzl. fold H2 in Hzl.
  destruct (15 <? Z.shiftr H2 4 mod 16 + 8) eqn:G4.
  { cbn [orb sim_post]. irh_norm; apply irh_Kr'; irh_red; irh_side. }
  (* patch F7 (Model2.c_HEAD2): the window size is checked against the stored one before it is stored *)
  assert (Wc : forall w v, wcl W0 wrap src w -> hdr_wb wrap src = Some v ->
    (negb (w =? 0) && (w <? v))%bool = (negb (W0 =? 0) && (W0 <? v))%bool).
  { clear. intros w v [Ew|(Ew & _ & F)] Hv; subst; auto. rewrite (F v Hv), Z.ltb_irrefl, andb_false_r. reflexivity. }
  rewrite (Wc _ _ Hwa Hzl), (Wc _ _ Hwb Hzl).
  destruct (negb (W0 =? 0) && (W0 <? Z.shiftr H2 4 mod 16 + 8))%bool eqn:G5.
  { cbn [orb sim_post]. irh_norm; apply irh_Kr'; irh_red;
    rewrite ?(irh_wnew _ _ _ _ _ Hwa Hzl), ?(irh_wnew _ _ _ _ _ Hwb Hzl); irh_side. }
  destruct (Z.land (Z.shiftr H2 4) 512 =? 0).
  { cbn [orb sim_post]. irh_norm; apply irh_Kr'; irh_red;
    rewrite ?(irh_wnew _ _ _ _ _ Hwa Hzl), ?(irh_wnew _ _ _ _ _ Hwb Hzl); irh_side. }
  { cbn [orb sim_post]. irh_norm; apply irh_Kr'; irh_red;
    rewrite ?(irh_wnew _ _ _ _ _ Hwa Hzl), ?(irh_wnew _ _ _ _ _ Hwb Hzl); irh_side. }
Qed.

(* uses the conjunct `wrap <> 0` of IRDefs.wcl's second disjunct *)
Lemma head_sim : head_sim_stmt.
Proof.
  intros W0 wrap src pos inp aout flush ma mb Hc K Ha Hb Hl Hmd. unfold md_head in Hmd.
  apply head_core; auto.
  intros Wz. pose proof (kr_wa _ _ _ _ _ _ _ _ K) as Wa. pose proof (kr_wb _ _ _ _ _ _ _ _ K) as Wb.
  destruct Wa as [Ea|(_ & Wn & _)]; [|congruence]. destruct Wb as [Eb|(_ & Wn & _)]; [|congruence].
  congruence.
Qed.
