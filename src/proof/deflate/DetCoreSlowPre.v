(** * deflate_slow for wide streams, part Pre: INSERT_STRING, longest_match and the filter

    Port of LTCSlowPre.v to the invariant [SIw] / [EIw] of DetCoreSlowInv.v; the helpers that do not mention
    the invariant are LTCSlowPre's. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.DetCoreSlowInv.
Require Import Zlib.proof.deflate.LTCSlowPre.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Theorem pre_okw : ins_spec -> lm_spec -> pre_partw.
Proof.
  intros Hins Hlm s0 z0 flush s z evs HSI Hrdy.
  destruct HSI as ((HW & _) & _ & _ & HEI).
  destruct HEI as (_ & Hfn0 & _ & Hsp & _).
  assert (Hlev : d_level s <> 0).
  { destruct Hsp as (_ & _ & _ & _ & _ & El & _). rewrite El. intros E. unfold fn_of in Hfn0.
    rewrite E in Hfn0. cbn in Hfn0. discriminate. }
  destruct HW as (Hp & Hws & Hpos & Hwin & Hhash & Hmatch & _ & _).
  assert (Hwsz := sp_wsize s Hp).
  unfold whash in Hhash.
  destruct (Z.eqb_spec (d_level s) 0) as [E0|_]; [lia|].
  destruct Hhash as (_ & G & HG).
  destruct Hmatch as (Hml & Hpl & _).
  pose proof Hws as Hws'. destruct Hws' as (Hwl & Hmb & Hwsize & Hprevl & Hheadl).
  destruct Hpos as (Hla0 & Hss0 & Hsl & _).
  destruct Hrdy as (Hla1 & Hroom & Hdef).
  assert (HMD : MAX_DIST s = d_w_size s - 262) by reflexivity.
  unfold dsl_pre, c_insert_head.
  destruct (Z.geb_spec (d_lookahead s) MIN_MATCH) as [Hge|Hlt].
  2:{ cbn [bind]. cbn [d_prev_length d_strstart set_d_match_length set_d_prev_match set_d_prev_length].
      eexists. split; [reflexivity|].
      split; [rewrite sp_keep_ml, sp_keep_pm, sp_keep_pl; reflexivity|].
      split; [exact Hws|].
      split; [exists G; apply (chain_with_mono s (d_strstart s) (lim s)); [exact HG|lia|lia]|].
      cbn. split; [reflexivity|]. split; [reflexivity|]. split; [unfold MIN_MATCH, MAX_MATCH; lia|].
      intros F. unfold MIN_MATCH in *; lia. }
  destruct (Hins s (d_strstart s) (d_strstart s) (lim s) G) as (s1 & h & Ec & Ek & Hws1 & Gh & Hch1 & Hcl1);
    [exact Hp | exact Hws | exact HG
    | unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *; lia
    | unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *; lia
    | apply Hdef; unfold MAX_MATCH in *; lia
    | lia
    | unfold lim; destruct (Z.gtb_spec (d_strstart s) (MAX_DIST s)); lia |].
  rewrite Ec. cbn [bind].
  assert (Ess := f_equal d_strstart Ek). assert (Ews := f_equal d_w_size Ek).
  assert (Ela := f_equal d_lookahead Ek). assert (Ewin := f_equal d_window Ek).
  assert (Ewsz := f_equal d_window_size Ek). assert (Epl := f_equal d_prev_length Ek).
  assert (Eml := f_equal d_match_length Ek). assert (Ems := f_equal d_match_start Ek).
  assert (Est := f_equal d_strategy Ek).
  cbn in Ess, Ews, Ela, Ewin, Ewsz, Epl, Eml, Ems, Est.
  assert (Elim : lim s1 = lim s) by (unfold lim, MAX_DIST; rewrite Ess, Ews; reflexivity).
  assert (Emd : max_dist s1 = MAX_DIST s).
  { unfold max_dist, MAX_DIST. rewrite Ews. unfold u32. apply Z.mod_small. unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH. lia. }
  rewrite Z.max_r in Hch1 by lia.
  change (d_match_start (set_d_prev_length s1 (d_match_length s1))) with (d_match_start s1).
  set (s2 := set_d_match_length (set_d_prev_match (set_d_prev_length s1 (d_match_length s1)) (d_match_start s1))
               (MIN_MATCH - 1)).
  assert (Hp1 : prm s1) by exact (sp_prm_hc s s1 Ek Hp).
  assert (E2s : d_strstart s2 = d_strstart s1) by reflexivity.
  assert (E2l : d_lookahead s2 = d_lookahead s1) by reflexivity.
  assert (E2pl : d_prev_length s2 = d_match_length s) by (subst s2; cbn; exact Eml).
  assert (E2pm : d_prev_match s2 = d_match_start s) by (subst s2; cbn; exact Ems).
  assert (E2ml : d_match_length s2 = MIN_MATCH - 1) by reflexivity.
  assert (Hkeep2 : pre_keep s2 = pre_keep s).
  { subst s2. rewrite sp_keep_ml, sp_keep_pm, sp_keep_pl. apply sp_keep_hc; exact Ek. }
  assert (Hmd2 : max_dist s2 = max_dist s1) by reflexivity.
  rewrite Hmd2, Emd, E2s, Ess.
  destruct (negb (h =? NIL) && (d_prev_length s2 <? d_max_lazy_match s2) &&
            (u32 (d_strstart s - h) <=? MAX_DIST s)) eqn:Eb.
  2:{ exists s2. split; [reflexivity|].
      split; [exact Hkeep2|]. split; [exact Hws1|].
      split; [eexists; exact Hch1|].
      split; [exact E2pl|]. split; [exact E2pm|].
      rewrite E2ml. split; [unfold MIN_MATCH, MAX_MATCH; lia|]. intros F. unfold MIN_MATCH in *; lia. }
  apply andb_true_iff in Eb. destruct Eb as (Eb & Ed). apply andb_true_iff in Eb. destruct Eb as (Eh & _).
  apply negb_true_iff, Z.eqb_neq in Eh. apply Z.leb_le in Ed.
  destruct (proj1 HG h Gh) as [F|Hh]; [unfold NIL in Eh; lia|].
  unfold u32 in Ed. rewrite (Z.mod_small (d_strstart s - h)) in Ed by (unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *; lia).
  assert (Hlimh : lim s <= h) by (unfold lim; destruct (Z.gtb_spec (d_strstart s) (MAX_DIST s)); lia).
  pose proof Hws1 as Hws1'. destruct Hws1' as (Hwl1 & Hmb1 & Hwsize1 & Hprevl1 & Hheadl1).
  assert (Elim2 : lim s2 = lim s) by exact Elim.
  destruct (Hlm s2 h (d_strstart s) (lim s) G) as (ms & ml & El & Hml' & Hmll & _ & Hgt);
    [ exact Hp1 | exact Hws1 | exact Hcl1
    | rewrite E2s; lia | lia
    | exact Gh | lia | rewrite Elim2; lia | rewrite E2pl; lia | rewrite E2l, Ela; exact Hge
    | rewrite E2s, E2l, Ess, Ela; change (d_window_size s2) with (d_window_size s1); lia
    | change (d_window s2) with (d_window s1); rewrite Hwl1, E2s, Ess, Ews;
      unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *; lia
    | intros i Hi; change (d_window s2) with (d_window s1); rewrite Ewin; apply Hdef; rewrite E2s, Ess in Hi; lia | ].
  rewrite El. cbn [bind].
  rewrite Elim2, E2s, Ess, E2pl in Hgt. rewrite E2l, Ela in Hmll.
  set (s3 := set_d_match_length (set_d_match_start s2 ms) ml).
  assert (Hkeep3 : pre_keep s3 = pre_keep s) by (subst s3; rewrite sp_keep_ml, sp_keep_ms; exact Hkeep2).
  assert (E3ml : d_match_length s3 = ml) by reflexivity.
  assert (E3ms : d_match_start s3 = ms) by reflexivity.
  assert (E3st : d_strategy s3 = d_strategy s) by (subst s3; cbn; exact Est).
  assert (E3s : d_strstart s3 = d_strstart s) by (subst s3; cbn; exact Ess).
  assert (E3pl : d_prev_length s3 = d_match_length s) by exact E2pl.
  assert (E3pm : d_prev_match s3 = d_match_start s) by exact E2pm.
  rewrite E3ml, E3ms, E3st, E3s.
  destruct ((ml <=? 5) && ((d_strategy s =? Z_FILTERED) ||
            ((ml =? MIN_MATCH) && (u32 (d_strstart s - ms) >? TOO_FAR)))) eqn:Ef.
  - eexists. split; [reflexivity|].
    split; [rewrite sp_keep_ml; exact Hkeep3|]. split; [exact Hws1|].
    split; [eexists; exact Hch1|].
    split; [exact E3pl|]. split; [exact E3pm|].
    change (d_match_length (set_d_match_length s3 (MIN_MATCH - 1))) with (MIN_MATCH - 1).
    split; [unfold MIN_MATCH, MAX_MATCH; lia|]. intros F. unfold MIN_MATCH in *; lia.
  - exists s3. split; [reflexivity|].
    split; [exact Hkeep3|]. split; [exact Hws1|].
    split; [eexists; exact Hch1|].
    split; [exact E3pl|]. split; [exact E3pm|].
    rewrite E3ml, E3ms, E3pl. split; [exact Hml'|]. intros Hm3. split; [exact Hmll|].
    intros Hlt'. destruct (Hgt Hlt') as (Hl1 & Hl2 & Hl3).
    assert (Eu : u32 (d_strstart s - ms) = d_strstart s - ms)
      by (unfold u32; apply Z.mod_small; unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *; lia).
    rewrite Eu. split.
    + split; [lia|]. unfold lim in Hl1. destruct (Z.gtb_spec (d_strstart s) (MAX_DIST s)); lia.
    + intros E3 Hnf. rewrite Eu, E3 in Ef.
      apply andb_false_iff in Ef. destruct Ef as [Ef|Ef]; [apply Z.leb_gt in Ef; unfold MIN_MATCH in *; lia|].
      apply orb_false_iff in Ef. destruct Ef as (_ & Ef).
      rewrite Z.eqb_refl in Ef. cbn [andb] in Ef. rewrite Z.gtb_ltb in Ef. apply Z.ltb_ge in Ef. exact Ef.
Qed.
