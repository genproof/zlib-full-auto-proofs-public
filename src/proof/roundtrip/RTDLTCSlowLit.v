(** * deflate_slow, part Lit: [lit_ok].  Invariant, split and statements: RTDLTCSlowInv.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDLTCSlowInv.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** Helpers *)

(** The state with every field the literal branch (with dsl_pre before it) may change blanked. *)
Definition lk (s : dstate) : dstate := set_d_lookahead (set_d_strstart (pre_keep (fbo_keep s)) 0) 0.

Lemma lk_pre s s1 : pre_keep s1 = pre_keep s -> lk s1 = lk s.
Proof.
  intros E.
  assert (F : forall x, lk x = set_d_lookahead (set_d_strstart (fbo_keep (pre_keep x)) 0) 0)
    by (intros []; reflexivity).
  rewrite (F s1), (F s), E. reflexivity.
Qed.

Lemma lk_fbo s s' : fbo_keep s' = fbo_keep s -> lk s' = lk s.
Proof. intros E. unfold lk. rewrite E. reflexivity. Qed.

Lemma lk_trm s x : lk (set_d_trm s x) = lk s.
Proof. destruct s; reflexivity. Qed.

Lemma lk_pos s a b : lk (set_d_lookahead (set_d_strstart s a) b) = lk s.
Proof. destruct s; reflexivity. Qed.

Ltac lkf H f :=
  let E := fresh "E" in pose proof (f_equal f H) as E;
  cbn [lk pre_keep fbo_keep hc_keep set_d_lookahead set_d_strstart set_d_match_start set_d_match_length
       set_d_prev_match set_d_prev_length set_d_ins_h set_d_prev set_d_head set_d_block_start set_d_po
       set_d_pbm set_d_tr f] in E.

Lemma prm_frame s s' :
  prm s -> lk s' = lk s -> tr_cfg (d_tr s') = tr_cfg (d_tr s) ->
  Zlength (o_buf (tr_out (d_tr s'))) = Zlength (o_buf (tr_out (d_tr s))) ->
  Zlength (d_pbm s') = Zlength (d_pbm s) -> prm s'.
Proof.
  intros Hp H Hc Hb Hm.
  lkf H d_w_bits. lkf H d_w_size. lkf H d_w_mask. lkf H d_hash_bits. lkf H d_hash_size. lkf H d_hash_mask.
  lkf H d_hash_shift. lkf H d_pending_buf_size. lkf H d_method.
  unfold tr_cfg in Hc. injection Hc as C1 C2 C3 C4.
  unfold prm, d_L, d_level, d_strategy in *.
  rewrite E, E0, E1, E2, E3, E4, E5, E6, E7, C1, C2, C3, C4, Hb, Hm. exact Hp.
Qed.

Lemma same_prm_frame s s' :
  lk s' = lk s -> tr_cfg (d_tr s') = tr_cfg (d_tr s) -> same_prm s s'.
Proof.
  intros H Hc. lkf H d_w_bits. lkf H d_w_size. lkf H d_hash_bits. lkf H d_pending_buf_size.
  unfold tr_cfg in Hc. injection Hc as C1 C2 C3 C4.
  unfold same_prm, d_L, d_level, d_strategy. repeat split; assumption.
Qed.

Lemma api_eq_frame s s' : lk s' = lk s -> api_eq s s'.
Proof.
  intros H. lkf H d_status. lkf H d_wrap. lkf H d_gzhead. lkf H d_gzindex. lkf H d_last_flush. lkf H d_method.
  unfold api_eq. repeat split; assumption.
Qed.

Lemma same_prm_trans a b c : same_prm a b -> same_prm b c -> same_prm a c.
Proof. unfold same_prm. intros (? & ? & ? & ? & ? & ? & ?) (? & ? & ? & ? & ? & ? & ?). repeat split; congruence. Qed.

Lemma api_eq_trans a b c : api_eq a b -> api_eq b c -> api_eq a c.
Proof. unfold api_eq. intros (? & ? & ? & ? & ? & ?) (? & ? & ? & ? & ? & ?). repeat split; congruence. Qed.

Lemma sym_ok_frame s s' x :
  d_w_size s' = d_w_size s -> d_level s' = d_level s -> d_strategy s' = d_strategy s -> sym_ok s x -> sym_ok s' x.
Proof. intros E1 E2 E3. unfold sym_ok, MAX_DIST. rewrite E1, E2, E3. exact (fun h => h). Qed.

Lemma EI_frame s0 z0 flush s z evs s' :
  EI s0 z0 flush s z evs -> outok s' -> same_prm s s' -> api_eq s s' -> ub s' = ub s ->
  d_pending s' = d_pending s -> d_bi_valid s' = d_bi_valid s -> EI s0 z0 flush s' z evs.
Proof.
  intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10) Ho Hs Ha Hu Hp Hb.
  split; [exact H1|]. split; [exact H2|]. split; [exact Ho|].
  split; [exact (same_prm_trans _ _ _ H4 Hs)|]. split; [exact (api_eq_trans _ _ _ H5 Ha)|].
  split; [exact H6|]. split; [exact H7|].
  split; [rewrite Hu; exact H8|].
  split; [|exact H10].
  replace (Gb s' (z_total_out z)) with (Gb s (z_total_out z)) by (unfold Gb; rewrite Hp, Hb; reflexivity).
  exact H9.
Qed.

Lemma blk_len_app l x : blk_len (l ++ [x]) = blk_len l + sym_len x.
Proof.
  unfold blk_len. rewrite map_app. cbn [map]. induction (map sym_len l) as [|a r IH]; cbn; lia.
Qed.

Lemma blk_len_bound l :
  (forall x, In x l -> valid_sym (fst x) (snd x)) -> 0 <= blk_len l <= 258 * Zlength l.
Proof.
  induction l as [|a r IH]; intros H.
  - cbn. lia.
  - rewrite Zlength_cons. unfold blk_len in *. cbn [map].
    cbn [Zlib.proof.huffman.HuffAbs.sumZ].
    assert (Ha : valid_sym (fst a) (snd a)) by (apply H; left; reflexivity).
    assert (IH' := IH (fun x Hx => H x (or_intror Hx))).
    unfold sym_len, valid_sym in *. destruct (fst a =? 0); lia.
Qed.

Lemma chain_with_frame s s' n l G :
  d_hash_size s' = d_hash_size s -> d_head s' = d_head s -> d_w_mask s' = d_w_mask s -> d_prev s' = d_prev s ->
  chain_with s n l G -> chain_with s' n l G.
Proof. intros E1 E2 E3 E4. unfold chain_with. rewrite E1, E2, E3, E4. exact (fun h => h). Qed.

Lemma u32_small x : 0 <= x < 4294967296 -> u32 x = x.
Proof. intros H. unfold u32. apply Z.mod_small. exact H. Qed.

Lemma wsize_range s : prm s -> 512 <= d_w_size s <= 32768.
Proof.
  intros (Hb & Hs & _). rewrite Hs. split.
  - change 512 with (2 ^ 9). apply Z.pow_le_mono_r; lia.
  - change 32768 with (2 ^ 15). apply Z.pow_le_mono_r; lia.
Qed.

Lemma L_range s : prm s -> 128 <= d_L s <= 32768.
Proof.
  intros (_ & _ & _ & Hh & _ & _ & _ & HL & _). rewrite HL. split.
  - change 128 with (2 ^ 7). apply Z.pow_le_mono_r; lia.
  - change 32768 with (2 ^ 15). apply Z.pow_le_mono_r; lia.
Qed.

(** After the tally (and the flush): strstart++, lookahead--, then need_more or go on. *)
Lemma lit_post s0 z0 flush s z evs s1 s3 z3 evs3 syms3 :
  SI s0 z0 flush s z evs -> rdy s -> MID s s1 ->
  ~ (MIN_MATCH <= d_prev_length s1 /\ d_match_length s1 <= d_prev_length s1) -> d_match_available s1 <> 0 ->
  lk s3 = lk s ->
  d_prev s3 = d_prev s1 -> d_head s3 = d_head s1 -> d_match_length s3 = d_match_length s1 ->
  d_prev_length s3 = d_prev_length s1 -> d_match_start s3 = d_match_start s1 ->
  d_strstart s3 = d_strstart s -> d_lookahead s3 = d_lookahead s ->
  tree_ok (d_tr s3) (d_pbm s3) syms3 -> Zlength syms3 <= d_L s - 2 -> Forall (sym_ok s) syms3 ->
  blk_len syms3 = d_strstart s - d_block_start s3 ->
  tr_cfg (d_tr s3) = tr_cfg (d_tr s) -> d_matches s3 = 0 ->
  d_block_start s3 <= d_strstart s -> d_strstart s + 1 - d_block_start s3 <= 16777216 ->
  (d_block_start s3 < 0 -> MAX_DIST s < d_strstart s - d_block_start s3) ->
  EI s0 z0 flush s3 z3 evs3 -> Forall (fun e => ev_last e = 0) evs3 -> z_avail_in z3 = z_avail_in z ->
  (z_avail_out z3 <> 0 -> quiet s3) -> d_bi_valid s3 <= 7 ->
  step_ok s0 z0 flush s z
    (let s' := set_d_strstart s3 (u32 (d_strstart s3 + 1)) in
     let s' := set_d_lookahead s' (u32 (d_lookahead s' - 1)) in
     if z_avail_out z3 =? 0 then inr (s', z3, Some need_more) else inl (s', z3)).
Proof.
  intros HSI Hrdy HMID Hnot Hav Hlk Ep Eh Eml Epl Ems Ess Ela HT HLen HFs Hblk Hcfg Hmat Hbs1 Hbs2 Hbs3
    HEI3 HL3 Hai Hq3 Hbv3.
  destruct HSI as (HW2 & Hq & HLs & HEI). destruct HW2 as [HW Hse].
  destruct HW as (Hp & Hws & Hwp & Hww & Hwh & Hwm & Hl0 & syms & Hwt).
  destruct HMID as (Hpk & Hws1 & [G HG] & Hpl1 & Hpm1 & Hml1 & Hmid).
  pose proof (lk_pre s s1 Hpk) as H1.
  lkf H1 d_match_available. lkf Hlk d_match_available. rename E into Eav1, E0 into Eav3.
  destruct Hwm as (Wm1 & Wm2 & Wm3 & Wm4 & Wm5).
  assert (Hav0 : d_match_available s = 1) by (clear - Eav1 Wm3 Hav; lia).
  destruct (Wm5 Hav0) as (Hfn & HS1 & _).
  assert (Hlev : d_level s <> 0).
  { intros E. unfold fn_of in Hfn. rewrite E in Hfn. discriminate. }
  pose proof (wsize_range s Hp) as Hwsz. pose proof (L_range s Hp) as HLr.
  destruct Hrdy as (Hla & Hroom & Hdef).
  destruct Hwp as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
  destruct Hws as (S1 & S2 & S3 & S4 & S5).
  assert (HPm : MIN_MATCH <= d_match_length s1 \/ MIN_MATCH <= d_prev_length s1 ->
                d_prev_length s1 < d_match_length s1) by (clear - Hnot; lia).
  cbv zeta.
  set (s4 := set_d_lookahead (set_d_strstart s3 (u32 (d_strstart s3 + 1)))
               (u32 (d_lookahead (set_d_strstart s3 (u32 (d_strstart s3 + 1))) - 1))).
  assert (Gss : d_strstart s4 = d_strstart s + 1).
  { change (u32 (d_strstart s3 + 1) = d_strstart s + 1). rewrite Ess. apply u32_small. clear - P1 P2 P3 S3 Hwsz; lia. }
  assert (Gla : d_lookahead s4 = d_lookahead s - 1).
  { change (u32 (d_lookahead s3 - 1) = d_lookahead s - 1). rewrite Ela. apply u32_small. clear - P1 P2 P3 S3 Hwsz Hla; lia. }
  assert (H4 : lk s4 = lk s) by (unfold s4; rewrite lk_pos; exact Hlk).
  assert (H41 : lk s4 = lk s1) by congruence.
  lkf H4 d_w_size. rename E into Gws.
  lkf H4 d_window. rename E into Gwin.
  lkf H4 d_window_size. rename E into Gwsz.
  lkf H4 d_insert. rename E into Gins.
  lkf H4 d_high_water. rename E into Ghw.
  lkf H4 d_match_available. rename E into Gav.
  lkf H41 d_hash_size. rename E into Ghs1.
  lkf H41 d_w_mask. rename E into Gwm1.
  lkf H41 d_w_size. rename E into Gws1.
  lkf H41 d_window. rename E into Gwin1.
  lkf H41 d_window_size. rename E into Gwsz1.
  assert (Gcfg : tr_cfg (d_tr s4) = tr_cfg (d_tr s)) by exact Hcfg.
  pose proof Gcfg as Gc. unfold tr_cfg in Gc. injection Gc as C1 C2 C3 C4.
  assert (GL : d_L s4 = d_L s) by exact C1.
  assert (Glev : d_level s4 = d_level s) by exact C3.
  assert (Gstr : d_strategy s4 = d_strategy s) by exact C4.
  assert (Gfn : fn_of s4 = fn_of s) by (unfold fn_of; rewrite Glev, Gstr; reflexivity).
  assert (Gmd : MAX_DIST s4 = MAX_DIST s) by (unfold MAX_DIST; rewrite Gws; reflexivity).
  assert (Gbs : d_block_start s4 = d_block_start s3) by reflexivity.
  assert (Gml : d_match_length s4 = d_match_length s1) by exact Eml.
  assert (Gpl : d_prev_length s4 = d_prev_length s1) by exact Epl.
  assert (Gms : d_match_start s4 = d_match_start s1) by exact Ems.
  assert (Ho3 : outok s3) by (destruct HEI3 as (_ & _ & Ho3 & _); exact Ho3).
  assert (HEI4 : EI s0 z0 flush s4 z3 evs3).
  { apply (EI_frame s0 z0 flush s3 z3 evs3 s4 HEI3).
    - exact Ho3.
    - apply same_prm_frame; [unfold s4; apply lk_pos|reflexivity].
    - apply api_eq_frame. unfold s4; apply lk_pos.
    - unfold ub. rewrite Gss, Gla, Gbs, Ess, Ela. clear; lia.
    - reflexivity.
    - reflexivity. }
  assert (HW4 : W2 s4).
  { split.
    - split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
      + apply (prm_frame s s4 Hp H4 Gcfg).
        * destruct HT as (T1 & _). destruct Hp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hb & _).
          change (Zlength (o_buf (tr_out (d_tr s3))) = Zlength (o_buf (tr_out (d_tr s)))).
          rewrite T1, Hb. unfold d_L. rewrite C1. reflexivity.
        * destruct HT as (_ & T2 & _). destruct Hp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hm & _).
          change (Zlength (d_pbm s3) = Zlength (d_pbm s)).
          rewrite T2, Hm. unfold d_L. rewrite C1. reflexivity.
      + destruct Hws1 as (U1 & U2 & U3 & U4 & U5). unfold wstruct.
        change (d_prev s4) with (d_prev s3). change (d_head s4) with (d_head s3).
        lkf H41 d_hash_size. rewrite Gwin1, Gws1, Gwsz1, Ep, Eh, E. auto.
      + unfold wpos. rewrite Gss, Gla, Gbs, Gins, Ghw, Gwsz, Gmd, Gws. clear - P1 P2 P3 P4 P5 P6 P7 P8 P9 Hla Hbs1 Hbs2 Hbs3; lia.
      + unfold wwin. rewrite Gss, Gla, Ghw, Gwin. intros i Hi. apply Hww. clear - Hi; lia.
      + unfold whash. rewrite Glev. destruct (Z.eqb_spec (d_level s) 0) as [E|_]; [contradiction|].
        split; [exact Hmat|]. exists G.
        apply chain_with_mono with (n := d_strstart s + 1) (l := lim s).
        * apply (chain_with_frame s1 s4); [exact Ghs1|exact Eh|exact Gwm1|exact Ep|exact HG].
        * rewrite Gss. clear; lia.
        * apply lim_mono; [rewrite Gws; reflexivity|rewrite Gss; clear; lia].
      + unfold wmatch. rewrite Gml, Gpl, Gav, Gss, Gla, Gfn, Gms, Gmd, Gstr, Hav0.
        replace (d_strstart s + 1 - 1) with (d_strstart s) by (clear; lia).
        rewrite Hpl1. split; [clear - Hml1; lia|]. split; [clear - Wm1; lia|]. split; [right; reflexivity|].
        split; [intros; discriminate|].
        intros _. split; [exact Hfn|]. split; [clear - HS1; lia|].
        intros Hm3. destruct (Hmid Hm3) as (Hm4 & Hm5).
        destruct (Hm5 (HPm (or_introl Hm3))) as (Hd1 & Hd2).
        split; [clear - Hm4; lia|]. split; [exact Hd1|exact Hd2].
      + rewrite Glev. intros E; contradiction.
      + exists syms3. unfold wtrees. split; [exact HT|]. split; [rewrite GL; exact HLen|].
        split.
        * eapply Forall_impl; [|exact HFs]. intros x. apply sym_ok_frame; assumption.
        * rewrite Glev, Gav, Gss, Gbs. split; [intros E; contradiction|]. intros _. clear - Hblk Hav0; lia.
    - unfold slow_extra. rewrite Gav, Gpl, Gml. intros _ Hm. apply HPm. right. exact Hm. }
  destruct (Z.eqb_spec (z_avail_out z3) 0) as [A0|A0].
  - unfold step_ok. exists evs3. apply EI_need_more; [exact HW4|exact HL3|exact HEI4|exact Hbv3|right; exact A0].
  - unfold step_ok. exists evs3. split.
    + split; [exact HW4|]. split; [exact (Hq3 A0)|]. split; [exact HL3|exact HEI4].
    + unfold msr. rewrite Gla, Hai. clear; lia.
Qed.

Theorem lit_ok : tally_spec2 -> fboev_part -> lit_part.
Proof.
  intros [Htl _] Hfbo s0 z0 flush s z evs s1 HSI Hrdy HMID Hnot Hav.
  pose proof HSI as (HW2 & Hq & HLs & HEI).
  pose proof HW2 as [HW Hse].
  pose proof HW as (Hp & Hws & Hwp & Hww & Hwh & Hwm & Hl0 & syms & Hwt).
  pose proof HMID as (Hpk & Hws1 & _).
  pose proof (lk_pre s s1 Hpk) as H1.
  lkf Hpk d_strstart. rename E into Fss.
  lkf Hpk d_lookahead. rename E into Fla.
  lkf Hpk d_window. rename E into Fwin.
  lkf Hpk d_tr. rename E into Ftr.
  lkf Hpk d_pbm. rename E into Fpbm.
  lkf Hpk d_po. rename E into Fpo.
  lkf Hpk d_block_start. rename E into Fbs.
  lkf Hpk d_match_available. rename E into Fav.
  lkf Hpk d_w_size. rename E into Fws.
  lkf Hpk d_pending_buf_size. rename E into Fpbs.
  destruct Hwm as (Wm1 & Wm2 & Wm3 & Wm4 & Wm5).
  assert (Hav0 : d_match_available s = 1) by (clear - Fav Wm3 Hav; lia).
  destruct (Wm5 Hav0) as (Hfn & HS1 & _).
  assert (Hlev : d_level s <> 0) by (intros E; unfold fn_of in Hfn; rewrite E in Hfn; discriminate).
  assert (Hmat0 : d_matches s = 0).
  { unfold whash in Hwh. destruct (Z.eqb_spec (d_level s) 0) as [E|_]; [contradiction|exact (proj1 Hwh)]. }
  pose proof (wsize_range s Hp) as Hwsz. pose proof (L_range s Hp) as HLr.
  assert (Hsend : tr_sym_end (d_tr s) = 3 * (d_L s - 1))
    by (destruct Hp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _); exact X).
  assert (Hlv : 0 <= d_level s <= 9)
    by (destruct Hp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _); exact X).
  pose proof Hrdy as (Hla & Hroom & Hdef).
  pose proof Hwp as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
  pose proof Hws as (S1 & S2 & S3 & S4 & S5).
  (* the pending byte *)
  set (c := Znth (d_strstart s - 1) (mb_val (d_window s))).
  assert (Hdc : Znth (d_strstart s - 1) (mb_def (d_window s)) = true)
    by (apply Hdef; clear - HS1; unfold MAX_MATCH; lia).
  assert (Hc : 0 <= c < 256).
  { destruct S2 as [_ Hb]. apply Hb; [clear - S1 S3 P3 HS1 Hla; lia|exact Hdc]. }
  assert (Hrd : mb_rd (d_window s1) (u32 (d_strstart s1 - 1)) = Some c).
  { rewrite Fwin, Fss, u32_small by (clear - HS1 Hwsz P1 P3 S3; lia).
    assert (Ir : in_range (d_strstart s - 1) (Zlength (mb_val (d_window s))) = true).
    { unfold in_range. apply andb_true_iff. split; [apply Z.leb_le|apply Z.ltb_lt];
        clear - S1 S3 P3 HS1 Hla; lia. }
    unfold mb_rd. rewrite Ir, Hdc. reflexivity. }
  (* the tally *)
  destruct Hwt as (T & Lsy & Fs & _ & Bl).
  specialize (Bl Hlev).
  assert (L32 : tr_lit_bufsize (d_tr s) <= 32768) by exact (proj2 HLr).
  destruct (Htl (d_tr s) (d_pbm s) syms c T Lsy L32 Hc) as (t' & m' & HT & Htok & Hfr).
  assert (HT1 : c_tr_tally_lit (d_trm s1) c =
                Some ((t', m'), 3 * Zlength syms + 3 =? tr_sym_end (d_tr s))).
  { unfold d_trm. rewrite Ftr, Fpbm. exact HT. }
  unfold dsl_lit. rewrite Hrd. cbn [bind]. unfold c_dtally_lit. rewrite HT1. cbn [bind fst snd].
  destruct Hfr as (Fc & Fm & Fp & Fbb & Fbv & Fbu & Fg).
  set (s2 := set_d_trm s1 (t', m')).
  assert (H2 : lk s2 = lk s) by (unfold s2; rewrite lk_trm; exact H1).
  assert (Ho : outok s) by (destruct HEI as (_ & _ & Ho & _); exact Ho).
  assert (Ho2 : outok s2).
  { apply (outok_grow s s2 Ho).
    - change (pb_grow (tr_out (d_tr s)) (d_pbm s) (tr_out t') m'). exact Fg.
    - change (d_po s1 = d_po s). exact Fpo.
    - exact Fp.
    - change (d_pending_buf_size s1 = d_pending_buf_size s). exact Fpbs.
    - destruct Ho as (_ & Hb & _). change (bits_ok (tr_out t')). unfold bits_ok in *.
      rewrite Fbb, Fbv, Fp. exact Hb. }
  assert (Hcfg2 : tr_cfg (d_tr s2) = tr_cfg (d_tr s)) by exact Fc.
  pose proof Hcfg2 as Gc. unfold tr_cfg in Gc. injection Gc as C1 C2 C3 C4.
  assert (GL2 : d_L s2 = d_L s) by exact C1.
  assert (Glev2 : d_level s2 = d_level s) by exact C3.
  assert (Gstr2 : d_strategy s2 = d_strategy s) by exact C4.
  assert (Gws2 : d_w_size s2 = d_w_size s) by exact Fws.
  assert (HEI2 : EI s0 z0 flush s2 z evs).
  { apply (EI_frame s0 z0 flush s z evs s2 HEI Ho2).
    - apply same_prm_frame; [exact H2|exact Hcfg2].
    - apply api_eq_frame. exact H2.
    - unfold ub. change (d_strstart s1 - d_block_start s1 + d_lookahead s1 = ub s).
      rewrite Fss, Fbs, Fla. reflexivity.
    - exact Fp.
    - exact Fbv. }
  assert (Hq2 : quiet s2).
  { destruct Hq as (Q1 & Q2 & Q3). split; [|split].
    - change (o_pending (tr_out t') = 0). rewrite Fp. exact Q1.
    - change (d_po s1 = 0). rewrite Fpo. exact Q2.
    - change (o_bi_valid (tr_out t') <= 7). rewrite Fbv. exact Q3. }
  assert (Hsym' : Forall (sym_ok s) (syms ++ [(0, c)])).
  { apply Forall_app. split; [exact Fs|]. constructor; [|constructor].
    split; [unfold valid_sym; cbn [fst snd]; clear - Hc; lia|].
    cbn [fst]. split; intros; congruence. }
  assert (Hbl' : blk_len (syms ++ [(0, c)]) = d_strstart s - d_block_start s).
  { rewrite blk_len_app. change (sym_len (0, c)) with 1. clear - Bl Hav0; lia. }
  destruct (Z.eqb_spec (3 * Zlength syms + 3) (tr_sym_end (d_tr s))) as [Ef|Ef].
  - (* FLUSH_BLOCK_ONLY(s, 0) *)
    assert (HLen' : Zlength (syms ++ [(0, c)]) = d_L s - 1).
    { rewrite Zlength_app, Zlength_cons, Zlength_nil. clear - Ef Hsend; lia. }
    assert (Hpre : fbo_pre s2 z (syms ++ [(0, c)]) 0).
    { split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split;
        [|split; [|split; [|split]]]]]]]]]]].
      - apply (prm_frame s s2 Hp H2 Hcfg2); [exact (proj1 Fg)|exact (proj1 (proj2 Fg))].
      - exact Hws1.
      - rewrite Glev2. clear - Hlev Hlv; lia.
      - exact Htok.
      - rewrite GL2, HLen'. clear; lia.
      - change (blk_len (syms ++ [(0, c)]) = d_strstart s1 - d_block_start s1). rewrite Fss, Fbs. exact Hbl'.
      - change (d_block_start s1 <= d_strstart s1). rewrite Fss, Fbs. exact P4.
      - change (d_strstart s1 - d_block_start s1 <= 16777216). rewrite Fss, Fbs. exact P5.
      - change (0 <= d_block_start s1 ->
                d_strstart s1 - d_block_start s1 <= 65535 /\ d_strstart s1 <= Zlength (mb_val (d_window s1)) /\
                forall i, d_block_start s1 <= i < d_strstart s1 -> Znth i (mb_def (d_window s1)) = true).
        rewrite Fss, Fbs, Fwin. intros Hb0. split; [|split].
        + unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in Hroom. clear - Hb0 Hroom S3 Hwsz; lia.
        + clear - S1 S3 P3 P1; lia.
        + intros i Hi. apply Hww. clear - Hi Hla Hb0; lia.
      - exact Ho2.
      - exact Hq2.
      - clear; lia.
      - destruct HEI as (_ & _ & _ & _ & _ & [_ Hzo] & _). exact Hzo. }
    assert (Hsym2 : Forall (sym_ok s2) (syms ++ [(0, c)])).
    { eapply Forall_impl; [|exact Hsym']. intros x. apply sym_ok_frame; assumption. }
    assert (HLen2 : Zlength (syms ++ [(0, c)]) = d_L s2 - 1) by (rewrite GL2; exact HLen').
    assert (Hneg2 : d_block_start s2 < 0 -> MAX_DIST s2 < d_strstart s2 - d_block_start s2).
    { change (d_block_start s1 < 0 -> MAX_DIST s2 < d_strstart s1 - d_block_start s1).
      unfold MAX_DIST. rewrite Gws2, Fss, Fbs. exact P6. }
    destruct (Hfbo s0 z0 flush s2 z evs (syms ++ [(0, c)]) 0 HEI2 Hpre Hsym2
                (fun H => ltac:(discriminate)) (fun _ => or_introl HLen2) Hneg2)
      as (s3 & z3 & e & Hc3 & He & HEI3 & Hfk & Hbs3 & Htr3 & Hcfg3 & Hmat3 & Hbv3 & _ & Hpend3 & Hai3).
    rewrite Hc3. cbn [bind].
    assert (Hbs3' : d_block_start s3 = d_strstart s) by (rewrite Hbs3; exact Fss).
    refine (ex_intro _ _ (conj _ (lit_post s0 z0 flush s z evs s1 s3 z3 (evs ++ [e]) [] HSI Hrdy HMID Hnot Hav _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)));
      [cbv zeta; destruct (z_avail_out z3 =? 0); reflexivity|..].
    + rewrite (lk_fbo s2 s3 Hfk). exact H2.
    + lkf Hfk d_prev. exact E.
    + lkf Hfk d_head. exact E.
    + lkf Hfk d_match_length. exact E.
    + lkf Hfk d_prev_length. exact E.
    + lkf Hfk d_match_start. exact E.
    + lkf Hfk d_strstart. transitivity (d_strstart s1); [exact E|exact Fss].
    + lkf Hfk d_lookahead. transitivity (d_lookahead s1); [exact E|exact Fla].
    + exact Htr3.
    + rewrite Zlength_nil. clear - HLr; lia.
    + constructor.
    + change (blk_len []) with 0. rewrite Hbs3'. clear; lia.
    + rewrite Hcfg3. exact Hcfg2.
    + exact Hmat3.
    + rewrite Hbs3'. clear; lia.
    + rewrite Hbs3'. clear; lia.
    + rewrite Hbs3'. clear - P2; lia.
    + exact HEI3.
    + apply Forall_app. split; [exact HLs|]. constructor; [exact He|constructor].
    + exact Hai3.
    + intros A. destruct Hpend3 as [Q0|A0]; [|contradiction].
      destruct HEI3 as (_ & _ & Ho3 & _). destruct Ho3 as (_ & _ & _ & _ & _ & Hz).
      split; [exact Q0|]. split; [exact (Hz Q0)|exact Hbv3].
    + exact Hbv3.
  - (* no flush *)
    cbn [bind].
    assert (Hv : forall x, In x (syms ++ [(0, c)]) -> valid_sym (fst x) (snd x))
      by (destruct Htok as (_ & _ & _ & X & _); exact X).
    pose proof (blk_len_bound _ Hv) as Hbb.
    assert (HLen' : Zlength (syms ++ [(0, c)]) <= d_L s - 2).
    { rewrite Zlength_app, Zlength_cons, Zlength_nil. clear - Ef Hsend Lsy; lia. }
    refine (ex_intro _ _ (conj _ (lit_post s0 z0 flush s z evs s1 s2 z evs (syms ++ [(0, c)]) HSI Hrdy HMID Hnot Hav _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)));
      [cbv zeta; destruct (z_avail_out z =? 0); reflexivity|..].
    + exact H2.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + exact Fss.
    + exact Fla.
    + exact Htok.
    + exact HLen'.
    + exact Hsym'.
    + change (blk_len (syms ++ [(0, c)]) = d_strstart s - d_block_start s1). rewrite Fbs. exact Hbl'.
    + exact Hcfg2.
    + change (tr_matches t' = 0). rewrite Fm. exact Hmat0.
    + change (d_block_start s1 <= d_strstart s). rewrite Fbs. exact P4.
    + change (d_strstart s + 1 - d_block_start s1 <= 16777216). rewrite Fbs.
      clear - Hbb Hbl' HLen' HLr; nia.
    + change (d_block_start s1 < 0 -> MAX_DIST s < d_strstart s - d_block_start s1). rewrite Fbs. exact P6.
    + exact HEI2.
    + exact HLs.
    + reflexivity.
    + intros _. exact Hq2.
    + exact (proj2 (proj2 Hq2)).
Qed.
