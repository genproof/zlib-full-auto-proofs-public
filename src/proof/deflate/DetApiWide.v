(** * deflate() and deflateParams() on the deflate_api invariant without its size limits ([api_wide_stmt], DetWide.v) *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.DetWide.
Require Import Zlib.proof.deflate.DetApiEntry Zlib.proof.deflate.DetApiHdrSt Zlib.proof.deflate.DetApiComp
  Zlib.proof.deflate.DetApiTrail.
Require Import Zlib.proof.deflate.LTApiInit Zlib.proof.deflate.LTApiParams.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** The proof follows LTApiDeflate.api_deflate and LTApiParams.api_params: deflate() is its four stages
    (entry, headers, compression, trailer: DetApiEntry, DetApiHdrSt, DetApiComp, DetApiTrail), run under [MidW]
    (DetApiMid.v), the invariant inside a call that starts at next_in [nin]. *)

(** [MidW] at the start of a call. *)
Lemma midw_start : forall W HI dict wrap D O fin s tin tout adler inb nin aout flush msg,
  Iapi W HI dict wrap D O fin s tin tout adler -> 0 <= nin <= Zlength inb ->
  Zlength D + (Zlength inb - nin) <= 1048576 -> 0 <= aout <= 4294967295 -> Zlength O + aout <= 8589934592 ->
  (forall R, fin = Some R -> flush = Z_FINISH /\ R = sublist nin (Zlength inb) inb) ->
  MidW W HI dict wrap D O inb nin aout tin tout flush s (zcall inb nin (Zlength inb - nin) tin aout tout adler msg).
Proof.
  intros W HI dict wrap D O fin s tin tout adler inb nin aout flush msg HI' Hn Hd Ha Ho Hfin.
  unfold MidW, zrunw, zcall; cbn [z_in z_next_in z_avail_in z_total_in z_avail_out z_out z_total_out z_adler].
  split.
  { split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [rewrite Zlength_nil; lia|]. split; [rewrite Zlength_nil; lia|]. constructor. }
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  rewrite sublist_nil, !app_nil_r.
  destruct HI' as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14).
  unfold Iapi. do 12 (split; [assumption|]). split; [|exact A14].
  intros Hst. destruct (Hfin _ (A13 Hst)) as [Ef Er]. unfold fin_of; cbn [z_next_in].
  rewrite Ef, Z.eqb_refl, <- Er. reflexivity.
Qed.

(** The running stream at the end of a call is the stream [call_okw] describes. *)
Lemma zrunw_okw : forall inb nin aout tin tout z,
  zrunw inb nin aout tin tout z -> 0 <= tout -> tout + aout <= 8589934592 -> call_okw inb nin aout tin tout z.
Proof.
  intros inb nin aout tin tout z (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8) Ht Hb.
  pose proof (Zlength_nonneg (z_out z)).
  unfold call_okw. split; [exact Z1|]. split; [exact Z2|]. split; [exact Z3|]. split; [exact Z4|].
  split; [lia|]. split; [exact Z6|]. split; [|exact Z8].
  rewrite Z7, Z6. unfold u64. rewrite Z.mod_small by lia. reflexivity.
Qed.

(** deflate() under [MidW]: Z_STREAM_END only for Z_FINISH, otherwise [MidW] at the end of the call. *)
Lemma deflate_w : forall W HI dict wrap D O fin s tin tout adler inb nin aout flush msg,
  core_facts W -> cf_compress_wide W -> cf_still_wide W -> hdr_facts HI -> hf_run_wide HI ->
  Iapi W HI dict wrap D O fin s tin tout adler ->
  0 <= flush <= 5 -> bytes inb -> 0 <= nin <= Zlength inb -> Zlength D + (Zlength inb - nin) <= 1048576 ->
  0 <= aout <= 4294967295 -> Zlength O + aout <= 8589934592 ->
  (forall R, fin = Some R -> flush = Z_FINISH /\ R = sublist nin (Zlength inb) inb) ->
  exists s' z' code,
    c_deflate s (zcall inb nin (Zlength inb - nin) tin aout tout adler msg) flush = Some (s', z', code) /\
    d_gzhead s' = d_gzhead s /\ zrunw inb nin aout tin tout z' /\
    (0 <= adler < 4294967296 -> 0 <= z_adler z' < 4294967296) /\
    (code = Z_OK \/ code = Z_BUF_ERROR \/ code = Z_STREAM_END) /\ (code = Z_STREAM_END -> flush = Z_FINISH) /\
    (code <> Z_STREAM_END -> MidW W HI dict wrap D O inb nin aout tin tout flush s' z').
Proof.
  intros W HI dict wrap D O fin s tin tout adler inb nin aout flush msg CF CW CS HF HR HI' Hfl Hb Hn Hd Ha Ho Hfin.
  pose proof (midw_start W HI dict wrap D O fin s tin tout adler inb nin aout flush msg HI' Hn Hd Ha Ho Hfin) as M0.
  set (z0 := zcall inb nin (Zlength inb - nin) tin aout tout adler msg) in *.
  assert (Ad0 : z_adler z0 = adler) by reflexivity.
  rewrite c_deflate_stages.
  rewrite (Iapi_bad_state W HI dict wrap D O fin s tin tout adler HF HI').
  replace (flush >? Z_BLOCK) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; unfold Z_BLOCK; lia).
  replace (flush <? 0) with false by (symmetry; apply Z.ltb_ge; lia). cbn [orb].
  destruct (entryw_ok W HI dict wrap D O inb nin aout tin tout flush s z0 CF HF M0 eq_refl eq_refl eq_refl Hfl)
    as (s1 & z1 & o1 & E1 & G1 & M1 & A1 & P1).
  rewrite E1. destruct o1 as [c|].
  { cbn [then_stage bind]. exists s1, z1, c. split; [reflexivity|]. split; [exact G1|].
    split; [exact (proj1 M1)|]. split; [rewrite A1, Ad0; auto|].
    split; [destruct P1 as [->|(->&_)]; auto|]. split; [|intros _; exact M1].
    intros E. exfalso. destruct P1 as [->|(->&_)]; discriminate. }
  cbn [then_stage bind]. destruct P1 as (Q1 & Q2 & Q3 & Q4 & Q5).
  destruct (hdrw_stage_ok W HI dict wrap D O inb nin aout tin tout flush s1 z1 CF HF HR M1 Q1 Q2 Hfl Q3 Q5)
    as (s2 & z2 & r2 & E2 & G2 & M2 & N2 & A2 & P2).
  rewrite E2. destruct r2 as [c|].
  { cbn [then_stage bind]. exists s2, z2, c. split; [reflexivity|]. split; [congruence|].
    split; [exact (proj1 M2)|]. split; [intros Hr; apply A2; rewrite A1, Ad0; exact Hr|].
    split; [left; exact P2|]. split; [|intros _; exact M2]. intros E. subst c. discriminate. }
  cbn [then_stage bind]. destruct P2 as (R1 & R2).
  destruct (compw_stage_ok W HI dict wrap D O inb nin aout tin tout flush s2 z2 CF CW CS HF Hb M2 R1 Hfl R2)
    as (s3 & z3 & o3 & E3 & G3 & M3 & A3 & P3).
  rewrite E3. destruct o3 as [c|].
  { cbn [bind]. exists s3, z3, c. split; [reflexivity|]. split; [congruence|].
    split; [exact (proj1 M3)|]. split; [intros Hr; apply A3, A2; rewrite A1, Ad0; exact Hr|].
    split; [left; exact P3|]. split; [|intros _; exact M3]. intros E. subst c. discriminate. }
  cbn [bind]. destruct P3 as (T1 & T2 & T3).
  destruct (trailerw_ok W HI dict wrap D O inb nin aout tin tout flush s3 z3 CF HF M3 T1 Hfl T2 T3)
    as (s4 & z4 & c & E4 & G4 & A4 & P4).
  exists s4, z4, c. split; [exact E4|]. split; [congruence|].
  assert (Hadl : 0 <= adler < 4294967296 -> 0 <= z_adler z4 < 4294967296)
    by (intros Hr; rewrite A4; apply A3, A2; rewrite A1, Ad0; exact Hr).
  destruct P4 as [(-> & M4) | (-> & Hf & _ & Zr)].
  - split; [exact (proj1 M4)|]. split; [exact Hadl|]. split; [left; reflexivity|]. split; [|intros _; exact M4].
    intros E. discriminate.
  - split; [exact Zr|]. split; [exact Hadl|]. split; [right; right; reflexivity|]. split; [intros _; exact Hf|]. intros E. contradiction.
Qed.

Lemma api_deflate_w : forall W HI, core_facts W -> cf_compress_wide W -> cf_still_wide W -> hdr_facts HI ->
  hf_run_wide HI -> api_deflate_wide W HI.
Proof.
  intros W HI CF CW CS HF HR dict wrap D O fin s tin tout adler inb nin aout flush msg HI' Hfl Hb Hn Hd Ha Ho Hfin.
  assert (Ht : tout = Zlength O) by apply HI'.
  destruct (deflate_w W HI dict wrap D O fin s tin tout adler inb nin aout flush msg CF CW CS HF HR HI' Hfl Hb Hn
              Hd Ha Ho Hfin) as (s' & z' & code & E & G & Zr & Ad & _ & _ & Hm).
  exists s', z', code. split; [exact E|]. split; [exact G|].
  split; [apply zrunw_okw; [exact Zr| |]; pose proof (Zlength_nonneg O); lia|].
  split; [exact Ad|]. intros Hc. exact (proj2 (proj2 (proj2 (proj2 (proj2 (Hm Hc)))))).
Qed.

(** What [MidW] says at the end of a call: the stream of [call_okw], and [Iapi] (no Z_FINISH: fin = None). *)
Lemma midw_okw : forall W HI dict wrap D O inb nin aout tin tout flush s z,
  MidW W HI dict wrap D O inb nin aout tin tout flush s z -> call_okw inb nin aout tin tout z.
Proof.
  intros W HI dict wrap D O inb nin aout tin tout flush s z (Zr & _ & _ & _ & Ho & IA).
  assert (Ht : z_total_out z = Zlength (O ++ z_out z)) by apply IA.
  pose proof (Zlength_nonneg O).
  apply zrunw_okw; [exact Zr| |]; destruct Zr as (_ & _ & _ & _ & _ & _ & Z7 & _); rewrite Zlength_app in Ht; lia.
Qed.

Lemma midw_iapi : forall W HI dict wrap D O inb nin aout tin tout flush s z,
  MidW W HI dict wrap D O inb nin aout tin tout flush s z -> flush <> Z_FINISH ->
  Iapi W HI dict wrap (D ++ sublist nin (z_next_in z) inb) (O ++ z_out z) None s
    (z_total_in z) (z_total_out z) (z_adler z).
Proof.
  intros W HI dict wrap D O inb nin aout tin tout flush s z (_ & _ & _ & _ & _ & IA) Hf.
  unfold fin_of in IA. replace (flush =? Z_FINISH) with false in IA by (symmetry; apply Z.eqb_neq; exact Hf).
  exact IA.
Qed.

(** deflateParams() (LTApiParams.api_params): the argument checks, the deflate(strm, Z_BLOCK) call when the
    function or the strategy changes and deflate was called before ([deflate_w]), the checks after it, then
    [params_tail] ([LTApiParams.params_finish]). *)
Lemma api_params_w : forall W HI, core_facts W -> cf_compress_wide W -> cf_still_wide W -> hdr_facts HI ->
  hf_run_wide HI -> api_params_wide W HI.
Proof.
  intros W HI CF CW CS HF HR dict wrap D O s tin tout adler inb nin aout level strategy msg HI' Hl Hs Hb Hn Hd Ha Ho.
  assert (Hbad := Iapi_bad_state W HI dict wrap D O None s tin tout adler HF HI').
  pose proof HI' as HI0. destruct HI0 as (HW & _).
  pose proof (cf_prm W CF s HW) as Hprm.
  assert (Hfin : forall R, (None : option (list Z)) = Some R -> Z_BLOCK = Z_FINISH /\ R = sublist nin (Zlength inb) inb)
    by (intros R HR'; discriminate).
  pose proof (midw_start W HI dict wrap D O None s tin tout adler inb nin aout Z_BLOCK msg HI' Hn Hd Ha Ho Hfin) as M0.
  set (z0 := zcall inb nin (Zlength inb - nin) tin aout tout adler msg) in *.
  assert (NP1 := midw_okw _ _ _ _ _ _ _ _ _ _ _ _ _ _ M0).
  assert (NP2 := midw_iapi _ _ _ _ _ _ _ _ _ _ _ _ _ _ M0 ltac:(discriminate)).
  assert (NA : 0 <= adler < 4294967296 -> 0 <= z_adler z0 < 4294967296) by (intros Hr; exact Hr).
  unfold c_deflateParams. rewrite Hbad. cbv zeta.
  set (lv := if level =? Z_DEFAULT_COMPRESSION then 6 else level).
  destruct ((lv <? 0) || (lv >? 9) || (strategy <? 0) || (strategy >? Z_FIXED)) eqn:Er.
  { exists s, z0, Z_STREAM_ERROR. split; [reflexivity|]. split; [reflexivity|]. split; [exact NP1|].
    split; [exact NA|exact NP2]. }
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
    destruct (deflate_w W HI dict wrap D O None s tin tout adler inb nin aout Z_BLOCK msg CF CW CS HF HR HI' Hfl Hb
                Hn Hd Ha Ho Hfin) as (s1 & z1 & code & E & G & _ & Ad & Hc & Hend & Hm).
    fold z0 in E. rewrite E. cbn [bind].
    assert (Hne : code <> Z_STREAM_END) by (intros Hc'; specialize (Hend Hc'); discriminate).
    assert (Hc2 : code = Z_OK \/ code = Z_BUF_ERROR) by (destruct Hc as [Hc|[Hc|Hc]]; auto; contradiction).
    specialize (Hm Hne).
    assert (C := midw_okw _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm).
    assert (Hpost := midw_iapi _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm ltac:(discriminate)).
    replace (code =? Z_STREAM_ERROR) with false by (destruct Hc2 as [-> | ->]; reflexivity).
    destruct (negb (z_avail_in z1 =? 0)) eqn:Ea.
    + exists s1, z1, Z_BUF_ERROR. split; [reflexivity|]. split; [exact G|]. split; [exact C|].
      split; [exact Ad|exact Hpost].
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
        split; [exact Ad|exact Hpost].
      * apply negb_false_iff, Z.eqb_eq in Eu.
        destruct (params_finish W HI dict wrap _ _ s1 _ _ _ lv strategy CF HF Hpost (proj1 Hrange) (proj2 Hrange))
          as (s2 & Hpt & G2 & HI2); [right; lia|].
        exists s2, z1, Z_OK. split; [apply bind_set_strategy; exact Hpt|].
        split; [congruence|]. split; [exact C|]. split; [exact Ad|exact HI2].
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
    split; [exact G2|]. split; [exact NP1|]. split; [exact NA|exact HI2].
Qed.

Theorem api_wide : api_wide_stmt.
Proof.
  intros W HI CF CW CS HF HR. split.
  - exact (api_deflate_w W HI CF CW CS HF HR).
  - exact (api_params_w W HI CF CW CS HF HR).
Qed.
