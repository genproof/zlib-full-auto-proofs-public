(** * Law api_deterministic on data of any length: deflateInit2 and deflateParams on RTK7Defs.Iapi7

    [Iapi7_init]: deflateInit2 with accepted parameters and successful allocations starts [Iapi7 W3 hinv7]
    (RTDLTApiInit.api_init for [Iapi7], from RTDLTCore.W3_init).
    [api7_params]: deflateParams before Z_FINISH keeps [Iapi7], for the streams of the C types (DetApiWide's
    api_params_w for [Iapi7]): its argument checks, its deflate(strm, Z_BLOCK) call (a call of
    RTK7Api.api7_deflate_stmt) when the compression function or the strategy changes and deflate was called
    before, the checks after it, then the level change (DetTheory2Inv.params_finish7). *)
From Coq Require Import ZArith.
From Coq Require Import List.
From Coq Require Import Lia.
From Coq Require Import Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.DetTheory2Inv.
Require Import Zlib.proof.roundtrip.RTK7Hdr.
Require Import Zlib.proof.roundtrip.RTK7DMid.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** deflateInit2 *)

Lemma Iapi7_init : forall level method wbits mem strategy z,
  params_ok level method wbits mem strategy = true ->
  exists s z',
    c_deflateInit2_ true true false level method wbits mem strategy true true true true true z =
      Some (Some s, z', Z_OK) /\ d_gzhead s = None /\
    z' = mkST (z_in z) (z_next_in z) (z_avail_in z) 0 (z_out z) (z_avail_out z) 0
              (if wrap_of wbits =? 2 then 0 else 1) None /\
    Iapi7 W3 hinv7 [] (wrap_of wbits) [] [] None s 0 0 (if wrap_of wbits =? 2 then 0 else 1).
Proof.
  intros level method wbits mem strategy z P.
  destruct (W3_init level method wbits mem strategy z P)
    as (s & z' & E & HW & HO & Hst & Hwr & Hgz & Hgi & Hlf & Hpo & Hpe & Hbv & Hss & Hla & Hbs & Hsn & _ & _ & _ & _
        & Hz').
  exists s, z'. split; [exact E|]. split; [exact Hgz|]. split; [exact Hz'|].
  assert (Hw : 0 <= wrap_of wbits <= 2) by (unfold wrap_of; destruct (wbits <? 0), (wbits >? 15); lia).
  unfold Iapi7. split; [exact HW|]. split; [exact HO|]. split; [exact Hw|].
  split; [auto|]. split; [constructor|]. split; [cbn; lia|]. split; [rewrite Hlf; lia|].
  split; [rewrite Hgz; discriminate|]. split; [reflexivity|]. split; [constructor|]. split; [constructor|].
  split; [cbn; lia|].
  split; [exists 0; split; [cbn; lia|reflexivity]|].
  split; [rewrite Hst; destruct (wrap_of wbits =? 2); unfold INIT_STATE, GZIP_STATE, FINISH_STATE; discriminate|].
  split; [intros _; split; [exact Hla|lia]|].
  left. unfold ph0. split.
  { rewrite Hst. destruct (wrap_of wbits =? 2) eqn:E2; [right|left]; split; auto; lia. }
  split; [exact Hwr|]. do 2 (split; [reflexivity|]).
  do 4 (split; [assumption|]). split; [lia|]. split; [tauto|].
  intros H1. rewrite H1. reflexivity.
Qed.

(** ** deflateParams before Z_FINISH *)

(** The call's stream when deflateParams returns before doing anything. *)
Lemma params_noprog7 : forall dict wrap D O s tin tout adler inb nin aout msg,
  Iapi7 W3 hinv7 dict wrap D O None s tin tout adler -> 0 <= nin <= Zlength inb -> 0 <= aout ->
  call_ok7 inb nin aout tin tout (rzcall inb nin (Zlength inb - nin) tin aout tout adler msg) /\
  Iapi7 W3 hinv7 dict wrap (D ++ sublist nin (z_next_in (rzcall inb nin (Zlength inb - nin) tin aout tout adler msg)) inb)
    (O ++ z_out (rzcall inb nin (Zlength inb - nin) tin aout tout adler msg)) None s
    (z_total_in (rzcall inb nin (Zlength inb - nin) tin aout tout adler msg))
    (z_total_out (rzcall inb nin (Zlength inb - nin) tin aout tout adler msg))
    (z_adler (rzcall inb nin (Zlength inb - nin) tin aout tout adler msg)).
Proof.
  intros dict wrap D O s tin tout adler inb nin aout msg HI' Hn Ha.
  unfold rzcall; cbn [z_in z_next_in z_avail_in z_total_in z_out z_avail_out z_total_out z_adler].
  rewrite sublist_nil, !app_nil_r. split; [|exact HI'].
  pose proof HI' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (k & _ & Htin) & _).
  unfold call_ok7; cbn [z_in z_next_in z_avail_in z_total_in z_out z_avail_out z_total_out].
  split; [reflexivity|]. split; [lia|]. split; [lia|].
  split; [rewrite Z.sub_diag, Z.add_0_r, Htin; unfold u64; rewrite Z.mod_mod by lia; reflexivity|].
  split; [lia|]. split; [cbn; lia|]. split; [lia|]. constructor.
Qed.

Lemma api7_params : api7_deflate_stmt ->
  forall dict wrap D O s tin tout adler inb nin aout level strategy msg,
    Iapi7 W3 hinv7 dict wrap D O None s tin tout adler -> rbytes inb -> 0 <= nin <= Zlength inb ->
    Zlength inb - nin <= 4294967295 -> Zlength D + (Zlength inb - nin) <= 18446744073709551615 ->
    0 <= aout <= 4294967295 -> Zlength O + aout <= 18446744073709551615 ->
    exists s' z' code,
      c_deflateParams s (rzcall inb nin (Zlength inb - nin) tin aout tout adler msg) level strategy =
        Some (s', z', code) /\
      d_gzhead s' = d_gzhead s /\ call_ok7 inb nin aout tin tout z' /\
      (0 <= adler < 4294967296 -> 0 <= z_adler z' < 4294967296) /\
      Iapi7 W3 hinv7 dict wrap (D ++ sublist nin (z_next_in z') inb) (O ++ z_out z') None
        s' (z_total_in z') (z_total_out z') (z_adler z').
Proof.
  intros AD dict wrap D O s tin tout adler inb nin aout level strategy msg HI' Hb Hn Hin Hd Ha Ho.
  assert (Hbad := Iapi7_bad_state W3 hinv7 dict wrap D O None s tin tout adler rtk7_hdr_ok HI').
  pose proof HI' as HI0. destruct HI0 as (HW & _).
  pose proof (W3_prm s HW) as Hprm.
  assert (Hfin : forall R, (None : option (list Z)) = Some R -> Z_BLOCK = Z_FINISH /\ R = sublist nin (Zlength inb) inb)
    by (intros R HR'; discriminate).
  destruct (params_noprog7 dict wrap D O s tin tout adler inb nin aout msg HI' Hn (proj1 Ha)) as [NP1 NP2].
  set (z0 := rzcall inb nin (Zlength inb - nin) tin aout tout adler msg) in *.
  assert (NA : 0 <= adler < 4294967296 -> 0 <= z_adler z0 < 4294967296) by (intros Hr; exact Hr).
  unfold c_deflateParams. rewrite Hbad. cbv zeta.
  set (lv := if level =? Z_DEFAULT_COMPRESSION then 6 else level).
  destruct ((lv <? 0) || (lv >? 9) || (strategy <? 0) || (strategy >? Z_FIXED)) eqn:Er.
  { exists s, z0, Z_STREAM_ERROR. split; [reflexivity|]. split; [reflexivity|]. split; [exact NP1|].
    split; [exact NA|exact NP2]. }
  assert (Hrange : 0 <= lv <= 9 /\ 0 <= strategy <= 4).
  { unfold Z_FIXED in Er. rewrite !orb_false_iff, Z.ltb_ge, Z.gtb_ltb, Z.ltb_ge, Z.ltb_ge, Z.gtb_ltb, Z.ltb_ge in Er.
    lia. }
  assert (Hlvl : 0 <= d_level s <= 9)
    by (destruct Hprm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L & _); exact L).
  rewrite (cfg_func_ok (d_level s) Hlvl). cbn [bind].
  destruct ((negb (strategy =? d_strategy s) || negb (cfg_f (d_level s) =? cfg_f lv)) && negb (d_last_flush s =? -2))
    eqn:Ec.
  - assert (Hfl : 0 <= Z_BLOCK <= 5) by (unfold Z_BLOCK; lia).
    destruct (AD dict wrap D O None s tin tout adler inb nin aout Z_BLOCK msg HI' Hfl Hb Hn Hin Hd Ha Ho Hfin)
      as (s1 & z1 & code & E & G & _ & C & Ad & Hc & Hend & _ & Hpost).
    fold z0 in E. rewrite E. cbn [bind].
    assert (Hne : code <> Z_STREAM_END) by (intros Hc'; destruct (Hend Hc') as [Hf _]; discriminate).
    specialize (Hpost Hne). replace (Z_BLOCK =? Z_FINISH) with false in Hpost by reflexivity.
    replace (code =? Z_STREAM_ERROR) with false
      by (destruct Hc as [-> | [-> | ->]]; [reflexivity|contradiction|reflexivity]).
    destruct (negb (z_avail_in z1 =? 0)) eqn:Ea.
    + exists s1, z1, Z_BUF_ERROR. split; [reflexivity|]. split; [exact G|]. split; [exact C|].
      split; [exact Ad|exact Hpost].
    + pose proof Hpost as HP0. destruct HP0 as (HW1 & _).
      destruct (W3_pos s1 HW1) as (P1 & P2 & P3 & P4).
      pose proof (W3_prm s1 HW1) as Hprm1.
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
        destruct (params_finish7 dict wrap _ _ None s1 _ _ _ lv strategy Hpost (proj1 Hrange) (proj2 Hrange))
          as (s2 & Hpt & G2 & HI2); [right; lia|].
        exists s2, z1, Z_OK. split; [apply set_strategy_bind7; exact Hpt|].
        split; [congruence|]. split; [exact C|]. split; [exact Ad|exact HI2].
  - destruct (params_finish7 dict wrap _ _ None s _ _ _ lv strategy NP2 (proj1 Hrange) (proj2 Hrange))
      as (s2 & Hpt & G2 & HI2).
    { apply andb_false_iff in Ec. destruct Ec as [Ec|Ec].
      - left. apply orb_false_iff in Ec. destruct Ec as [E1 E2].
        apply negb_false_iff, Z.eqb_eq in E1. apply negb_false_iff, Z.eqb_eq in E2. auto.
      - right. apply negb_false_iff, Z.eqb_eq in Ec.
        destruct NP2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [P0 | (Hlf & _)]).
        + destruct P0 as (_ & _ & _ & _ & _ & _ & _ & Hla & Hss & _). auto.
        + contradiction. }
    exists s2, z0, Z_OK. split; [apply set_strategy_bind7; exact Hpt|].
    split; [exact G2|]. split; [exact NP1|]. split; [exact NA|exact HI2].
Qed.
