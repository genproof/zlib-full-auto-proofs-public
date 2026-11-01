(** * deflate_api theory: deflateParams

    [api_params] (the field af_params of [api_facts (Iapi W HI) Iend]): the argument checks, the deflate(strm,
    Z_BLOCK) call when the function or the strategy changes and deflate was called before ([api_deflate]), the
    checks after it (the in_long guards by [cf_pos]), then [params_tail] by [cf_params]. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTApiDeflate.
Require Import Zlib.proof.deflate.LTApiInit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Lemma bind_set_strategy : forall (o : option dstate) st (z : strm) s2,
  (let* s := o in Some (set_d_strategy s st)) = Some s2 ->
  (let* s := o in Some (set_d_strategy s st, z, Z_OK)) = Some (s2, z, Z_OK).
Proof. intros [s|] st z s2 H; cbn in *; congruence. Qed.

(** A call without progress keeps the invariant. *)
Lemma params_noprog : forall W HI dict wrap D O s tin tout adler inb aout msg,
  Iapi W HI dict wrap D O None s tin tout adler -> 0 <= aout ->
  call_ok inb aout tin tout (zcall inb 0 (Zlength inb) tin aout tout adler msg) /\
  Iapi W HI dict wrap (D ++ sublist 0 (Zlength inb - z_avail_in (zcall inb 0 (Zlength inb) tin aout tout adler msg)) inb)
    (O ++ z_out (zcall inb 0 (Zlength inb) tin aout tout adler msg)) None s
    (z_total_in (zcall inb 0 (Zlength inb) tin aout tout adler msg))
    (z_total_out (zcall inb 0 (Zlength inb) tin aout tout adler msg))
    (z_adler (zcall inb 0 (Zlength inb) tin aout tout adler msg)).
Proof.
  intros. unfold zcall; cbn [z_in z_next_in z_avail_in z_total_in z_out z_avail_out z_total_out z_adler].
  replace (Zlength inb - Zlength inb) with 0 by lia.
  replace (sublist 0 0 inb) with (@nil Z) by (unfold sublist; reflexivity). rewrite !app_nil_r.
  split; [|assumption].
  unfold call_ok; cbn. pose proof (Zlength_nonneg inb).
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [cbn; lia|]. split; [cbn; lia|]. constructor.
Qed.

Lemma params_finish : forall W HI dict wrap D O s tin tout adler lv st,
  core_facts W -> hdr_facts HI -> Iapi W HI dict wrap D O None s tin tout adler ->
  0 <= lv <= 9 -> 0 <= st <= 4 ->
  (cfg_f lv = cfg_f (d_level s) /\ st = d_strategy s) \/ (d_lookahead s = 0 /\ d_strstart s = d_block_start s) ->
  exists s2, params_tail s lv st = Some s2 /\ d_gzhead s2 = d_gzhead s /\
    Iapi W HI dict wrap D O None s2 tin tout adler.
Proof.
  intros W HI dict wrap D O s tin tout adler lv st CF HF HI' Hlv Hst Hc.
  pose proof HI' as HI0. destruct HI0 as (HW & _).
  destruct (cf_params W CF s lv st HW Hlv Hst Hc)
    as (s2 & Hpt & HW2 & Hapi & Hout & _ & _ & Hwb & Hhb & Hss & Hla & Hbs & Hsn).
  exists s2. split; [exact Hpt|]. split; [apply Hapi|].
  apply (Iapi_frame W HI dict wrap D O None s s2 tin tout adler HF HI' HW2 Hapi Hout); auto.
  pose proof (cf_prm W CF s HW) as P1. pose proof (cf_prm W CF s2 HW2) as P2.
  destruct Hout as (Ho1 & _).
  destruct P1 as (_ & _ & _ & _ & _ & _ & _ & _ & A1 & A2 & _).
  destruct P2 as (_ & _ & _ & _ & _ & _ & _ & _ & B1 & B2 & _).
  rewrite Ho1 in B2. lia.
Qed.

Lemma api_params : forall W HI dict wrap D O s tin tout adler inb aout level strategy msg,
    core_facts W -> hdr_facts HI ->
    Iapi W HI dict wrap D O None s tin tout adler -> s32 level -> s32 strategy ->
    bytes inb -> Zlength D + Zlength inb <= 1048576 -> 0 <= aout <= 1048576 -> Zlength O + aout <= 4194304 ->
    exists s' z' code,
      c_deflateParams s (zcall inb 0 (Zlength inb) tin aout tout adler msg) level strategy = Some (s', z', code) /\
      d_gzhead s' = d_gzhead s /\ call_ok inb aout tin tout z' /\
      (code = Z_OK \/ code = Z_BUF_ERROR \/ code = Z_STREAM_ERROR) /\
      (code = Z_STREAM_ERROR <-> ~ (-1 <= level <= 9 /\ 0 <= strategy <= 4)) /\
      Iapi W HI dict wrap (D ++ sublist 0 (Zlength inb - z_avail_in z') inb) (O ++ z_out z') None
        s' (z_total_in z') (z_total_out z') (z_adler z').
Proof.
  intros W HI dict wrap D O s tin tout adler inb aout level strategy msg CF HF HI' Hl Hs Hb Hd Ha Ho.
  assert (Hbad := Iapi_bad_state W HI dict wrap D O None s tin tout adler HF HI').
  pose proof HI' as HI0. destruct HI0 as (HW & _).
  pose proof (cf_prm W CF s HW) as Hprm.
  destruct (params_noprog W HI dict wrap D O s tin tout adler inb aout msg HI' (proj1 Ha)) as [NP1 NP2].
  unfold c_deflateParams. rewrite Hbad. cbv zeta.
  set (lv := if level =? Z_DEFAULT_COMPRESSION then 6 else level).
  set (z0 := zcall inb 0 (Zlength inb) tin aout tout adler msg) in *.
  assert (Hlv : -1 <= level <= 9 <-> 0 <= lv <= 9).
  { subst lv. unfold Z_DEFAULT_COMPRESSION. destruct (Z.eqb_spec level (-1)); lia. }
  destruct ((lv <? 0) || (lv >? 9) || (strategy <? 0) || (strategy >? Z_FIXED)) eqn:Er.
  { exists s, z0, Z_STREAM_ERROR. split; [reflexivity|]. split; [reflexivity|]. split; [exact NP1|].
    split; [right; right; reflexivity|]. split; [|exact NP2].
    split; [|intros; reflexivity]. intros _ [H1 H2]. apply Hlv in H1. unfold Z_FIXED in Er.
    rewrite !orb_true_iff, Z.ltb_lt, Z.gtb_ltb, Z.ltb_lt, Z.ltb_lt, Z.gtb_ltb, Z.ltb_lt in Er. lia. }
  assert (Hrange : 0 <= lv <= 9 /\ 0 <= strategy <= 4).
  { unfold Z_FIXED in Er. rewrite !orb_false_iff, Z.ltb_ge, Z.gtb_ltb, Z.ltb_ge, Z.ltb_ge, Z.gtb_ltb, Z.ltb_ge in Er.
    lia. }
  assert (Hlvl : 0 <= d_level s <= 9) by (destruct Hprm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L & _); exact L).
  assert (Hcf : cfg_func (d_level s) = Some (cfg_f (d_level s))).
  { unfold cfg_func, cfg_f. replace ((0 <=? d_level s) && (d_level s <=? 9)) with true
      by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
    destruct (Znth (d_level s) config_table) as [[[[? ?] ?] ?] ?]. reflexivity. }
  rewrite Hcf. cbn [bind].
  destruct ((negb (strategy =? d_strategy s) || negb (cfg_f (d_level s) =? cfg_f lv)) && negb (d_last_flush s =? -2))
    eqn:Ec.
  - assert (Hfl : 0 <= Z_BLOCK <= 5) by (unfold Z_BLOCK; lia).
    assert (Hfin : forall R, (None : option (list Z)) = Some R -> Z_BLOCK = Z_FINISH /\ inb = R)
      by (intros R HR; discriminate).
    destruct (api_deflate W HI dict wrap D O None s tin tout adler inb aout Z_BLOCK msg CF HF HI' Hfl Hb Hd Ha Ho Hfin)
      as (s1 & z1 & code & E & G & C & Hc & Hend & Hbuf & Post).
    fold z0 in E. rewrite E. cbn [bind].
    assert (Hc2 : code = Z_OK \/ code = Z_BUF_ERROR).
    { destruct Hc as [Hc|[Hc|Hc]]; auto. destruct (Hend Hc) as [Hf _]. discriminate. }
    assert (Hpost : Iapi W HI dict wrap (D ++ sublist 0 (Zlength inb - z_avail_in z1) inb) (O ++ z_out z1) None s1
                      (z_total_in z1) (z_total_out z1) (z_adler z1)).
    { cbv zeta in Post. destruct Hc2 as [-> | ->]; exact Post. }
    replace (code =? Z_STREAM_ERROR) with false by (destruct Hc2 as [-> | ->]; reflexivity).
    assert (Hnot : (Z_BUF_ERROR = Z_STREAM_ERROR <-> ~ (-1 <= level <= 9 /\ 0 <= strategy <= 4))).
    { split; [discriminate|]. intros H. exfalso. apply H. split; [apply Hlv|]; lia. }
    destruct (negb (z_avail_in z1 =? 0)) eqn:Ea.
    + exists s1, z1, Z_BUF_ERROR. split; [reflexivity|]. split; [exact G|]. split; [exact C|].
      split; [right; left; reflexivity|]. split; [exact Hnot|exact Hpost].
    + pose proof Hpost as HP0. destruct HP0 as (HW1 & _).
      destruct (cf_pos W CF s1 HW1) as (P1 & P2 & P3 & P4).
      pose proof (cf_prm W CF s1 HW1) as Hprm1.
      assert (Hws : d_w_size s1 <= 32768).
      { destruct Hprm1 as (Hb1 & Hb2 & _). rewrite Hb2.
        assert (2 ^ d_w_bits s1 <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia). lia. }
      replace (in_long (d_strstart s1 - d_block_start s1)) with true
        by (symmetry; unfold in_long; apply andb_true_iff; split; apply Z.leb_le; lia).
      replace (in_long (d_strstart s1 - d_block_start s1 + d_lookahead s1)) with true
        by (symmetry; unfold in_long; apply andb_true_iff; split; apply Z.leb_le; lia).
      cbn [bind guard].
      destruct (negb (d_strstart s1 - d_block_start s1 + d_lookahead s1 =? 0)) eqn:Eu.
      * exists s1, z1, Z_BUF_ERROR. split; [reflexivity|]. split; [exact G|]. split; [exact C|].
        split; [right; left; reflexivity|]. split; [exact Hnot|exact Hpost].
      * apply negb_false_iff, Z.eqb_eq in Eu.
        destruct (params_finish W HI dict wrap _ _ s1 _ _ _ lv strategy CF HF Hpost (proj1 Hrange) (proj2 Hrange))
          as (s2 & Hpt & G2 & HI2); [right; lia|].
        exists s2, z1, Z_OK. split; [apply bind_set_strategy; exact Hpt|].
        split; [congruence|]. split; [exact C|]. split; [left; reflexivity|].
        split; [|exact HI2]. split; [discriminate|]. intros H. exfalso. apply H. split; [apply Hlv|]; lia.
  - destruct (params_finish W HI dict wrap _ _ s _ _ _ lv strategy CF HF NP2 (proj1 Hrange) (proj2 Hrange))
      as (s2 & Hpt & G2 & HI2).
    { apply andb_false_iff in Ec. destruct Ec as [Ec|Ec].
      - left. apply orb_false_iff in Ec. destruct Ec as [E1 E2].
        apply negb_false_iff, Z.eqb_eq in E1. apply negb_false_iff, Z.eqb_eq in E2. auto.
      - right. apply negb_false_iff, Z.eqb_eq in Ec.
        destruct NP2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [P0 | (Hlf & _)]).
        + destruct P0 as (_ & _ & _ & _ & _ & _ & _ & Hla & Hss & _). auto.
        + contradiction. }
    exists s2, z0, Z_OK. split; [apply bind_set_strategy; exact Hpt|].
    split; [exact G2|]. split; [exact NP1|]. split; [left; reflexivity|].
    split; [|exact HI2]. split; [discriminate|]. intros H. exfalso. apply H. split; [apply Hlv|]; lia.
Qed.
