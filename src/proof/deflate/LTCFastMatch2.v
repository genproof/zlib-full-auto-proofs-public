(** * deflate_fast, part match, against the CORRECTED tally specification [tally_spec2] (LTCSpecs2.v:
    tally_spec is false without a bound on lit_bufsize; tally_spec2 adds [tr_lit_bufsize t <= 32768], which follows
    from prm: L = 2^(hash_bits - 1) <= 2^15).  With LTCSpecs2.tally_spec_2, [match_stmt]
    also follows from the original [tally_spec]. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTCFastKit.
Require Export Zlib.proof.deflate.LTCSpecs2.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Lemma mt_u32_id x : 0 <= x < 4294967296 -> u32 x = x.
Proof. intros. unfold u32. apply Z.mod_small. lia. Qed.

Lemma mt_lim_mono s s' : d_w_size s' = d_w_size s -> d_strstart s <= d_strstart s' -> lim s <= lim s'.
Proof.
  intros E H. unfold lim, MAX_DIST. rewrite E.
  destruct (Z.gtb_spec (d_strstart s) (d_w_size s - MIN_LOOKAHEAD));
  destruct (Z.gtb_spec (d_strstart s') (d_w_size s - MIN_LOOKAHEAD)); lia.
Qed.

Lemma mt_chain_mono s n n' l l' G : chain_with s n l G -> n <= n' -> l <= l' -> chain_with s n' l' G.
Proof.
  intros (A & B & C) Hn Hl. split; [intros v Hv; destruct (A v Hv); [left|right]; lia|].
  split; [exact B|]. intros q Hq Hq0 Hql. apply C; auto; lia.
Qed.

(** The fields the match branch changes outside the trees state blanked. *)
Definition mt_keep (x : dstate) : dstate := set_d_lookahead (set_d_match_start (il_keep x) 0) 0.

Lemma mt_keep_sr x t m a :
  mt_keep (set_d_lookahead (set_d_pbm (set_d_tr x t) m) a) = mt_keep (set_d_pbm (set_d_tr (sr_keep x) t) m).
Proof. reflexivity. Qed.

Lemma mt_keep_ml x a : mt_keep (set_d_match_length x a) = mt_keep x.
Proof. reflexivity. Qed.

Lemma mt_keep_ss x a : mt_keep (set_d_strstart x a) = mt_keep x.
Proof. reflexivity. Qed.

Lemma mt_keep_ih x a : mt_keep (set_d_ins_h x a) = mt_keep x.
Proof. reflexivity. Qed.

Lemma mt_keep_il x y : il_keep x = il_keep y -> mt_keep x = mt_keep y.
Proof. intros E. unfold mt_keep. rewrite E. reflexivity. Qed.

Lemma mt_sym_ok s s' x :
  d_w_size s' = d_w_size s -> d_level s' = d_level s -> d_strategy s' = d_strategy s ->
  sym_ok s x -> sym_ok s' x.
Proof. unfold sym_ok, MAX_DIST. intros E1 E2 E3. rewrite E1, E2, E3. auto. Qed.

Ltac sr_field Hk f E := assert (E := f_equal f Hk); unfold sr_keep, hc_keep in E; autorewrite with fproj in E.

Ltac mt_fld Hk f E := assert (E := f_equal f Hk); unfold mt_keep, il_keep, hc_keep in E; autorewrite with fproj in E.

(** The state after the match branch: TS and fr. *)
Lemma mt_core s s3 syms t' m' ml dist G :
  W s -> outok s -> quiet s -> fn_of s = 1 -> wtrees s syms ->
  tree_ok t' m' (syms ++ [(dist, ml - 3)]) -> tally_frame (d_tr s) (d_pbm s) t' m' ->
  mt_keep s3 = mt_keep (set_d_pbm (set_d_tr s t') m') -> wstruct s3 ->
  d_strstart s3 = d_strstart s + ml -> d_lookahead s3 = d_lookahead s - ml -> d_match_length s3 = 0 ->
  chain_with s3 (d_strstart s3) (lim s) G ->
  3 <= ml <= d_lookahead s -> 1 <= dist <= MAX_DIST s -> d_strstart s + ml < d_window_size s ->
  TS s3 (syms ++ [(dist, ml - 3)]) (3 * Zlength syms + 3 =? tr_sym_end (d_tr s)) /\ fr s s3 /\
  d_lookahead s3 < d_lookahead s.
Proof.
  intros HW Ho Hq Hfn Hwt Htr Hfr Hk Hws3 Hss3 Hla3 Hml3 Hch Hml Hd Hwin3.
  destruct HW as (Hp & Hws & Hpos & Hwin & Hh & Hm & _ & _).
  assert (Hlev := fn_of_fast s Hp Hfn).
  assert (Ha : d_match_available s = 0).
  { destruct Hm as (_ & _ & [A|A] & _ & B); [exact A|]. destruct (B A) as (C & _). lia. }
  assert (Hpl : d_prev_length s < MIN_MATCH) by (destruct Hm as (_ & _ & _ & B & _); destruct (B Ha); lia).
  destruct Hfr as (Hcfg & Hmat & Hpnd & Hbb & Hbv & Hbu & Hgrow).
  unfold tr_cfg in Hcfg. injection Hcfg as Ec1 Ec2 Ec3 Ec4.
  mt_fld Hk d_tr Etr. mt_fld Hk d_pbm Epbm. mt_fld Hk d_status Estatus. mt_fld Hk d_po Epo.
  mt_fld Hk d_wrap Ewrap. mt_fld Hk d_gzhead Egzh. mt_fld Hk d_gzindex Egzi. mt_fld Hk d_method Emeth.
  mt_fld Hk d_last_flush Elf. mt_fld Hk d_w_size Ewsize. mt_fld Hk d_w_bits Ewbits. mt_fld Hk d_w_mask Ewmask.
  mt_fld Hk d_window Ewin. mt_fld Hk d_window_size Ewsz. mt_fld Hk d_hash_size Ehsize.
  mt_fld Hk d_hash_bits Ehbits. mt_fld Hk d_hash_mask Ehmask. mt_fld Hk d_hash_shift Ehshift.
  mt_fld Hk d_block_start Ebs. mt_fld Hk d_match_available Ema. mt_fld Hk d_prev_length Eplen.
  mt_fld Hk d_insert Eins. mt_fld Hk d_high_water Ehw. mt_fld Hk d_pending_buf_size Epbs.
  assert (Elev : d_level s3 = d_level s) by (unfold d_level; rewrite Etr; exact Ec3).
  assert (Estr : d_strategy s3 = d_strategy s) by (unfold d_strategy; rewrite Etr; exact Ec4).
  assert (EL : d_L s3 = d_L s) by (unfold d_L; rewrite Etr; exact Ec1).
  assert (Efn : fn_of s3 = 1) by (unfold fn_of; rewrite Elev, Estr; exact Hfn).
  assert (Epend : d_pending s3 = d_pending s) by (unfold d_pending; rewrite Etr; exact Hpnd).
  assert (Ebiv : d_bi_valid s3 = d_bi_valid s) by (unfold d_bi_valid; rewrite Etr; exact Hbv).
  destruct Hp as (Hwb & Hwsz & Hwm & Hhb & Hhs & Hhm & Hhsh & HL & Hpbs & Hob & Hpbm & Hse & Hlv & Hstrat & Hmeth).
  destruct Hpos as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
  destruct Hwt as (Ht1 & HL2 & Hf & _ & Hb).
  assert (Hb' : blk_len syms = d_strstart s - d_block_start s) by (rewrite Hb by lia; lia).
  assert (Htr' := Htr). destruct Htr' as (T1 & T2 & T3 & T4 & _).
  set (syms' := syms ++ [(dist, ml - 3)]) in *.
  assert (Hlen' : Zlength syms' = Zlength syms + 1) by (unfold syms'; rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  assert (Hbl' : blk_len syms' = d_strstart s - d_block_start s + ml).
  { unfold syms'. rewrite blk_len_app, Hb'. unfold sym_len. cbn [fst snd].
    destruct (Z.eqb_spec dist 0); lia. }
  assert (Hbb' := blk_len_bound syms' T4).
  assert (HL15 : d_L s <= 32768).
  { rewrite HL. change 32768 with (2 ^ 15). apply Z.pow_le_mono_r; lia. }
  assert (HTS0 : TS0 s3 syms').
  { unfold TS0. split.
    { unfold prm. rewrite Ewbits, Ewsize, Ewmask, Ehbits, Ehsize, Ehmask, Ehshift, EL, Epbs, Elev, Estr, Emeth.
      rewrite Etr, Epbm, T1, T2, Ec2, Ec1. fold (d_L s).
      exact (conj Hwb (conj Hwsz (conj Hwm (conj Hhb (conj Hhs (conj Hhm (conj Hhsh (conj HL (conj Hpbs
        (conj eq_refl (conj eq_refl (conj Hse (conj Hlv (conj Hstrat Hmeth)))))))))))))). }
    split; [exact Hws3|].
    split.
    { unfold wpos. unfold MAX_DIST in *. rewrite Hla3, Hss3, Ewsz, Ebs, Eins, Ehw, Ewsize. lia. }
    split.
    { unfold wwin. rewrite Ewin, Hla3, Hss3, Ehw. intros i Hi. apply Hwin. lia. }
    split.
    { unfold whash. rewrite Elev. destruct (Z.eqb_spec (d_level s) 0); [lia|].
      unfold whash in Hh. destruct (Z.eqb_spec (d_level s) 0); [lia|]. destruct Hh as [Hm0 _].
      split; [unfold d_matches in *; rewrite Etr, Hmat; exact Hm0|].
      exists G. eapply mt_chain_mono; [exact Hch|lia|]. apply mt_lim_mono; [exact Ewsize|lia]. }
    split.
    { unfold wmatch. rewrite Hml3, Eplen, Ema, Ha. destruct Hm as (_ & Hm2 & _).
      split; [unfold MAX_MATCH; lia|]. split; [exact Hm2|]. split; [left; reflexivity|].
      split; [intros _; unfold MIN_MATCH in *; lia|]. intros; lia. }
    split; [rewrite Etr, Epbm; exact Htr|].
    split; [rewrite EL; lia|].
    split.
    { unfold syms'. apply Forall_app. split.
      - eapply Forall_impl; [|exact Hf]. intros x. apply mt_sym_ok; assumption.
      - constructor; [|constructor]. unfold sym_ok. cbn [fst snd]. unfold MAX_DIST in *. rewrite Ewsize, Elev.
        split; [exact (T4 (dist, ml - 3) ltac:(unfold syms'; apply in_or_app; right; left; reflexivity))|].
        split; [intros _; exact (proj2 Hd)|]. intros; lia. }
    split; [rewrite Hss3, Ebs; lia|].
    split.
    { apply (outok_grow s s3 Ho); [rewrite Etr, Epbm; exact Hgrow|exact Epo|exact Epend|exact Epbs|].
      destruct Ho as (_ & Hbo & _). unfold bits_ok in *. rewrite Etr, Hbv, Hbb, Hpnd. exact Hbo. }
    split.
    { unfold quiet in *. rewrite Epend, Epo, Ebiv. exact Hq. }
    split; [exact Efn|].
    rewrite Hss3, Ewsz. exact Hwin3. }
  split; [split; [exact HTS0|]|].
  { rewrite Hse, EL, Hlen'. destruct (Z.eqb_spec (3 * Zlength syms + 3) (3 * (d_L s - 1)));
    destruct (Z.eqb_spec (Zlength syms + 1) (d_L s - 1)); lia. }
  split; [|lia].
  unfold fr. split.
  { unfold same_prm. rewrite Ewbits, Ewsize, Ehbits, EL, Epbs, Elev, Estr. repeat split; reflexivity. }
  split.
  { unfold api_eq. rewrite Estatus, Ewrap, Egzh, Egzi, Elf, Emeth. repeat split; reflexivity. }
  split.
  { unfold ub. rewrite Hss3, Hla3, Ebs. lia. }
  intros tout. unfold Gb. rewrite Epend, Ebiv. reflexivity.
Qed.

Lemma mt_prm s x t' m' syms' :
  prm s -> tally_frame (d_tr s) (d_pbm s) t' m' -> tree_ok t' m' syms' ->
  mt_keep x = mt_keep (set_d_pbm (set_d_tr s t') m') -> prm x.
Proof.
  intros Hp Hfr Htr Hk.
  destruct Hfr as (Hcfg & _). unfold tr_cfg in Hcfg. injection Hcfg as Ec1 Ec2 Ec3 Ec4.
  destruct Htr as (T1 & T2 & _).
  mt_fld Hk d_tr Etr. mt_fld Hk d_pbm Epbm. mt_fld Hk d_method Emeth.
  mt_fld Hk d_w_size Ewsize. mt_fld Hk d_w_bits Ewbits. mt_fld Hk d_w_mask Ewmask.
  mt_fld Hk d_hash_size Ehsize. mt_fld Hk d_hash_bits Ehbits. mt_fld Hk d_hash_mask Ehmask.
  mt_fld Hk d_hash_shift Ehshift. mt_fld Hk d_pending_buf_size Epbs.
  destruct Hp as (Hwb & Hwsz & Hwm & Hhb & Hhs & Hhm & Hhsh & HL & Hpbs & Hob & Hpbm & Hse & Hlv & Hstrat & Hmeth).
  unfold prm, d_L, d_level, d_strategy in *.
  rewrite Ewbits, Ewsize, Ewmask, Ehbits, Ehsize, Ehmask, Ehshift, Epbs, Emeth, Etr, Epbm, T1, T2, Ec1, Ec2, Ec3, Ec4.
  exact (conj Hwb (conj Hwsz (conj Hwm (conj Hhb (conj Hhs (conj Hhm (conj Hhsh (conj HL (conj Hpbs
    (conj eq_refl (conj eq_refl (conj Hse (conj Hlv (conj Hstrat Hmeth)))))))))))))).
Qed.

Lemma mt_chain_eq s s' n l G :
  d_head s' = d_head s -> d_prev s' = d_prev s -> d_hash_size s' = d_hash_size s -> d_w_mask s' = d_w_mask s ->
  chain_with s n l G -> chain_with s' n l G.
Proof. intros E1 E2 E3 E4. unfold chain_with. rewrite E1, E2, E3, E4. auto. Qed.

Lemma mt_rd s i : wstruct s -> wwin s -> d_high_water s <= d_window_size s ->
  d_strstart s + d_lookahead s <= d_window_size s ->
  0 <= i < Z.max (d_strstart s + d_lookahead s) (d_high_water s) ->
  mb_rd (d_window s) i = Some (Znth i (mb_val (d_window s))).
Proof.
  intros (Hl & _ & Hws & _) Hw Hh Hs Hi. unfold mb_rd. rewrite (Hw i Hi). unfold in_range.
  replace ((0 <=? i) && (i <? Zlength (mb_val (d_window s)))) with true by lia. reflexivity.
Qed.

Theorem match_ok2 : tally_spec2 -> insloop_stmt -> match_stmt.
Proof.
  intros [_ Htd] Hins s s2 HW Ho Hq Hfn Hrd Hla HSR Hml.
  destruct HSR as (Hk2 & Hws2 & [G HG] & Hml2 & Hmm).
  destruct (Hmm Hml) as (Hmla & Hlim & Hms).
  assert (HW0 := HW).
  destruct HW as (Hp & Hws & Hpos & Hwin & Hh & Hm & _ & syms & Hwt).
  assert (Hwt0 := Hwt).
  sr_field Hk2 d_window Ewin. sr_field Hk2 d_window_size Ewsz. sr_field Hk2 d_strstart Ess.
  sr_field Hk2 d_lookahead Ela. sr_field Hk2 d_tr Etr. sr_field Hk2 d_pbm Epbm.
  sr_field Hk2 d_w_size Ewsize. sr_field Hk2 d_max_lazy_match Elazy. sr_field Hk2 d_hash_shift Ehshift.
  sr_field Hk2 d_high_water Ehw.
  assert (Hlev := fn_of_fast s Hp Hfn).
  assert (Hp0 := Hp).
  destruct Hp as (Hwb & Hwsz & Hwm & Hhb & Hhs & Hhm & Hhsh & HL & Hpbs & Hob & Hpbm & Hse & Hlv & Hstrat & Hmeth).
  destruct Hpos as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
  destruct Hwt as (Ht1 & HL2 & Hf & _ & Hb).
  assert (HL15 : d_L s <= 32768).
  { rewrite HL. change 32768 with (2 ^ 15). apply Z.pow_le_mono_r; lia. }
  assert (Hw15 : d_w_size s <= 32768).
  { rewrite Hwsz. change 32768 with (2 ^ 15). apply Z.pow_le_mono_r; lia. }
  assert (Hw9 : 512 <= d_w_size s).
  { rewrite Hwsz. change 512 with (2 ^ 9). apply Z.pow_le_mono_r; lia. }
  assert (Hws0 := Hws). destruct Hws as (Hwl & Hwok & Hwss & Hpl & Hhl).
  set (ml := d_match_length s2) in *.
  set (dist := d_strstart s - d_match_start s2).
  assert (Hd : 1 <= dist <= MAX_DIST s).
  { unfold dist. unfold lim in Hlim.
    destruct (Z.gtb_spec (d_strstart s) (MAX_DIST s)); unfold MAX_DIST, MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *; lia. }
  assert (Hd' : 1 <= dist <= 32768) by (unfold MAX_DIST, MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in Hd; lia).
  assert (Hlen : 0 <= ml - 3 <= 255) by (unfold MAX_MATCH, MIN_MATCH in *; lia).
  destruct (Htd (d_tr s) (d_pbm s) syms dist (ml - 3) Ht1 HL2 HL15 Hd' Hlen) as (t' & m' & Etl & Ht' & Hfr).
  unfold fmatch. fold ml. rewrite Ess.
  rewrite (mt_u32_id (d_strstart s - d_match_start s2)) by lia. fold dist.
  rewrite (mt_u32_id (ml - MIN_MATCH)) by (unfold MIN_MATCH, MAX_MATCH in *; lia).
  unfold c_dtally_dist, d_trm. rewrite Etr, Epbm. change MIN_MATCH with 3. rewrite Etl.
  cbn [bind]. unfold set_d_trm. cbn [fst snd]. autorewrite with fproj. fold ml.
  rewrite ?Ela, ?Ess, ?Ewin, ?Ehshift, ?Elazy.
  rewrite (mt_u32_id (d_lookahead s - ml)) by lia.
  set (sin := set_d_lookahead (set_d_pbm (set_d_tr s2 t') m') (d_lookahead s - ml)).
  assert (Hkin : mt_keep sin = mt_keep (set_d_pbm (set_d_tr s t') m')).
  { unfold sin. rewrite mt_keep_sr, Hk2. reflexivity. }
  assert (Hsin : d_strstart sin = d_strstart s /\ d_window sin = d_window s /\ d_w_size sin = d_w_size s /\
                 d_head sin = d_head s2 /\ d_prev sin = d_prev s2 /\ d_hash_size sin = d_hash_size s2 /\
                 d_w_mask sin = d_w_mask s2 /\ d_hash_shift sin = d_hash_shift s /\ wstruct sin /\
                 d_lookahead sin = d_lookahead s - ml).
  { unfold sin, wstruct. autorewrite with fproj. rewrite Ess, Ewin, Ewsize, Ehshift.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [rewrite <- Ewin, <- Ewsize; exact Hws2|reflexivity]. }
  destruct Hsin as (Si1 & Si2 & Si3 & Si4 & Si5 & Si6 & Si7 & Si8 & Si9 & Si10).
  clearbody sin.
  unfold MIN_MATCH, MAX_MATCH in Hml, Hml2.
  destruct ((ml <=? d_max_lazy_match s) && (d_lookahead s - ml >=? 3)) eqn:Ec.
  - apply andb_true_iff in Ec. destruct Ec as [Ec1 Ec2]. apply Z.leb_le in Ec1. apply Z.geb_le in Ec2.
    rewrite (mt_u32_id (ml - 1)) by lia.
    destruct (Hins (set_d_match_length sin (ml - 1)) (lim s) G) as (s' & G' & Eloop & Hil & Hws' & Hss' & Hml' & Hch').
    + apply (mt_prm s _ t' m' (syms ++ [(dist, ml - 3)]) Hp0 Hfr Ht'). rewrite mt_keep_ml. exact Hkin.
    + unfold wstruct. autorewrite with fproj. exact Si9.
    + apply (mt_chain_eq s2); autorewrite with fproj; try assumption. rewrite Si1. exact HG.
    + autorewrite with fproj. lia.
    + autorewrite with fproj. lia.
    + autorewrite with fproj. rewrite ?Si1, ?Si3. lia.
    + autorewrite with fproj. rewrite ?Si1, ?Si2, ?Hwl. lia.
    + autorewrite with fproj. rewrite Si1, Si2. intros i Hi. apply Hwin. lia.
    + autorewrite with fproj. rewrite ?Si1, ?Si3. unfold lim, MAX_DIST, MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH.
      destruct (Z.gtb_spec (d_strstart s) (d_w_size s - (258 + 3 + 1))); lia.
    + autorewrite with fproj in Hss'. rewrite Si1 in Hss'.
      rewrite Eloop. cbn [bind].
      rewrite (mt_u32_id (d_strstart s' + 1)) by lia.
      assert (Ela' := f_equal d_lookahead Hil). unfold il_keep, hc_keep in Ela'. autorewrite with fproj in Ela'.
      eexists _, _, _. split; [reflexivity|].
      apply (mt_core s (set_d_strstart s' (d_strstart s' + 1)) syms t' m' ml dist G' HW0 Ho Hq Hfn Hwt0 Ht' Hfr).
      * rewrite mt_keep_ss, (mt_keep_il _ _ Hil), mt_keep_ml. exact Hkin.
      * unfold wstruct. autorewrite with fproj. exact Hws'.
      * autorewrite with fproj. lia.
      * autorewrite with fproj. rewrite Ela', Si10. reflexivity.
      * autorewrite with fproj. exact Hml'.
      * autorewrite with fproj. apply (mt_chain_eq s'); autorewrite with fproj; try reflexivity.
        replace (d_strstart s' + 1) with (d_strstart s' + 1) by lia. exact Hch'.
      * lia.
      * exact Hd.
      * lia.
  - assert (Hrd2 : d_strstart s + ml + 1 < Z.max (d_strstart s + d_lookahead s) (d_high_water s) /\
                   d_strstart s + ml < d_window_size s).
    { unfold ready in Hrd. unfold MAX_DIST, MIN_LOOKAHEAD, WIN_INIT in *. unfold MAX_MATCH, MIN_MATCH in *.
      destruct Hrd as [R|R]; lia. }
    rewrite (mt_u32_id (d_strstart s + ml)) by lia.
    rewrite (mt_rd s (d_strstart s + ml) Hws0 Hwin) by lia. cbn [bind].
    autorewrite with fproj. rewrite Si8.
    assert (Hsh : d_hash_shift s < 32) by (rewrite Hhsh; apply Z.div_lt_upper_bound; lia).
    rewrite (proj2 (Z.ltb_lt _ _) Hsh). cbn [guard bind]. rewrite Si2.
    rewrite (mt_u32_id (d_strstart s + ml + 1)) by lia.
    rewrite (mt_rd s (d_strstart s + ml + 1) Hws0 Hwin) by lia. cbn [bind].
    eexists _, _, _. split; [reflexivity|].
    apply (mt_core s _ syms t' m' ml dist G HW0 Ho Hq Hfn Hwt0 Ht' Hfr).
    * rewrite mt_keep_ih, mt_keep_ih, mt_keep_ml, mt_keep_ss. exact Hkin.
    * unfold wstruct. autorewrite with fproj. exact Si9.
    * autorewrite with fproj. reflexivity.
    * autorewrite with fproj. exact Si10.
    * autorewrite with fproj. reflexivity.
    * autorewrite with fproj. apply (mt_chain_eq s2); try assumption.
      apply (mt_chain_mono s2 _ _ _ _ G HG); lia.
    * lia.
    * exact Hd.
    * lia.
Qed.
