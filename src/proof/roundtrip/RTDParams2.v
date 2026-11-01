(* RT-D part PARAMS: deflateParams keeps K, for interface v2 (Krt2) and v1 (Krt).
   [params_gen]: for any functional invariant KFx kept by params_tail (RTDParamsFrame: kf2_params, kf_params),
   kf_deflate_stmt (Iapi W3 hinv /\ KFx) gives kf_params_stmt (Iapi W3 hinv /\ KFx).  The deflate(strm, Z_BLOCK)
   call's side conditions come from deflateParams' own (rcall_ok, d_gzhead) and from RTDParamsKit.deflate_block_codes
   (for any avail_out: the LT theory's api_deflate is limited to 2^20, kf_params_stmt allows 2^21). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDV2.
Require Import Zlib.proof.roundtrip.RTDParamsKit Zlib.proof.roundtrip.RTDParamsFrame.
Require Import Zlib.proof.roundtrip.RTDLTCore Zlib.proof.roundtrip.RTDLTHdrKit.
Require Import Zlib.proof.roundtrip.RTDLTApiInit Zlib.proof.roundtrip.RTDLTApiParams.
Import ListNotations.
Local Open Scope Z_scope.

Lemma bind_strategy_inv : forall (o : option dstate) st (z : strm) s' z' c,
  (let* s := o in Some (set_d_strategy s st, z, Z_OK)) = Some (s', z', c) ->
  (let* s := o in Some (set_d_strategy s st)) = Some s' /\ z' = z /\ c = Z_OK.
Proof. intros [s|] st z s' z' c H; cbn in *; [injection H; intros; subst; auto|discriminate]. Qed.

(** params_finish of the LT theory, for W3 / hinv, with the given run of params_tail *)
Lemma params_finish3 : forall dict wrap D O s tin tout adler lv st s2,
  Iapi W3 hinv dict wrap D O None s tin tout adler -> 0 <= lv <= 9 -> 0 <= st <= 4 -> pcase s lv st ->
  params_tail s lv st = Some s2 ->
  Iapi W3 hinv dict wrap D O None s2 tin tout adler.
Proof.
  intros dict wrap D O s tin tout adler lv st s2 HI' Hlv Hst Hc E.
  pose proof HI' as HI0. destruct HI0 as (HW & _).
  destruct (W3_params s lv st HW Hlv Hst Hc)
    as (s3 & Hpt & HW2 & Hapi & Hout & _ & _ & Hwb & Hhb & Hss & Hla & Hbs & Hsn).
  rewrite E in Hpt. injection Hpt as <-.
  apply (Iapi_frame W3 hinv dict wrap D O None s s2 tin tout adler hinv_facts HI' HW2 Hapi Hout); auto.
  pose proof (W3_prm s HW) as P1. pose proof (W3_prm s2 HW2) as P2.
  destruct Hout as (Ho1 & _).
  destruct P1 as (_ & _ & _ & _ & _ & _ & _ & _ & A1 & A2 & _).
  destruct P2 as (_ & _ & _ & _ & _ & _ & _ & _ & B1 & B2 & _).
  rewrite Ho1 in B2. lia.
Qed.

Lemma noprog_z : forall inb tin aout tout adler msg,
  let z0 := rzcall inb 0 (Zlength inb) tin aout tout adler msg in
  sublist 0 (Zlength inb - z_avail_in z0) inb = [] /\ z_out z0 = [] /\
  z_total_in z0 = tin /\ z_total_out z0 = tout /\ z_adler z0 = adler.
Proof.
  intros. subst z0. unfold rzcall; cbn. replace (Zlength inb - Zlength inb) with 0 by lia.
  split; [unfold sublist; reflexivity|]. auto.
Qed.

Section Gen.
Variable KFx : rinv.
Hypothesis Hpt : forall dict wrap D O fin s tin tout adler lv st s2,
  W s -> KFx dict wrap D O fin s tin tout adler -> 0 <= lv <= 9 -> pcase s lv st ->
  params_tail s lv st = Some s2 -> KFx dict wrap D O fin s2 tin tout adler.

Definition Kx : rinv := fun dict wrap D O fin s tin tout adler =>
  Iapi W3 hinv dict wrap D O fin s tin tout adler /\ KFx dict wrap D O fin s tin tout adler.

Lemma params_gen : kf_deflate_stmt Kx -> kf_params_stmt Kx.
Proof.
  intros Hdef dict wrap D O s tin tout adler inb aout level strategy msg s' z' code
    [HI' KF] Hl Hs Hb Hd Ha Ho E Hgz Hcall Hcode Hiff.
  assert (Hbad := Iapi_bad_state W3 hinv dict wrap D O None s tin tout adler hinv_facts HI').
  pose proof HI' as HI0. destruct HI0 as (HW3 & _).
  assert (HW : W s) by exact (proj1 (proj1 HW3)).
  destruct (params_noprog W3 hinv dict wrap D O s tin tout adler inb aout msg HI' (proj1 Ha)) as [NP1 NP2].
  set (z0 := rzcall inb 0 (Zlength inb) tin aout tout adler msg) in *.
  change (zcall inb 0 (Zlength inb) tin aout tout adler msg) with z0 in NP1, NP2.
  destruct (noprog_z inb tin aout tout adler msg) as (Z1 & Z2 & Z3 & Z4 & Z5). fold z0 in Z1, Z2, Z3, Z4, Z5.
  unfold c_deflateParams in E. rewrite Hbad in E. cbv zeta in E.
  set (lv := if level =? Z_DEFAULT_COMPRESSION then 6 else level) in *.
  assert (Hlv : -1 <= level <= 9 <-> 0 <= lv <= 9).
  { subst lv. unfold Z_DEFAULT_COMPRESSION. destruct (Z.eqb_spec level (-1)); lia. }
  destruct ((lv <? 0) || (lv >? 9) || (strategy <? 0) || (strategy >? Z_FIXED)) eqn:Er.
  { injection E as <- <- <-. split; [reflexivity|].
    rewrite Z1, Z2, Z3, Z4, Z5, !app_nil_r. split; [|exact KF].
    rewrite Z1, Z2, Z3, Z4, Z5, !app_nil_r in NP2. exact NP2. }
  assert (Hrange : 0 <= lv <= 9 /\ 0 <= strategy <= 4).
  { unfold Z_FIXED in Er. rewrite !orb_false_iff, Z.ltb_ge, Z.gtb_ltb, Z.ltb_ge, Z.ltb_ge, Z.gtb_ltb, Z.ltb_ge in Er.
    lia. }
  assert (Hnse : code <> Z_STREAM_ERROR).
  { intros Ec. apply Hiff in Ec. apply Ec. split; [apply Hlv|]; lia. }
  pose proof (prm_level s HW) as Hlvl.
  assert (Hcf : cfg_func (d_level s) = Some (cfg_f (d_level s))).
  { unfold cfg_func, cfg_f. replace ((0 <=? d_level s) && (d_level s <=? 9)) with true
      by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
    destruct (Znth (d_level s) config_table) as [[[[? ?] ?] ?] ?]. reflexivity. }
  rewrite Hcf in E. cbn [bind] in E.
  destruct ((negb (strategy =? d_strategy s) || negb (cfg_f (d_level s) =? cfg_f lv)) && negb (d_last_flush s =? -2))
    eqn:Ec.
  - (* deflate(strm, Z_BLOCK) *)
    destruct (c_deflate s z0 Z_BLOCK) as [[[s1 z1] c1]|] eqn:Ed; cbn [bind] in E; [|discriminate].
    pose proof (deflate_block_codes s z0 s1 z1 c1 Ed) as Hc1.
    destruct (c1 =? Z_STREAM_ERROR) eqn:Ese.
    { injection E as _ _ <-. apply Z.eqb_eq in Ese. contradiction. }
    assert (Hc1' : c1 = Z_OK \/ (c1 = Z_BUF_ERROR /\ z_avail_in z1 = Zlength inb /\ z_avail_out z1 = aout)).
    { destruct Hc1 as [H|[H|H]]; [left; exact H| |right; exact H]. rewrite H in Ese. discriminate. }
    (* the outcome: s' is s1 or params_tail of s1; z' = z1 *)
    assert (Hout : z' = z1 /\
      ((s' = s1 /\ code = Z_BUF_ERROR) \/
       (d_strstart s1 - d_block_start s1 + d_lookahead s1 = 0 /\ params_tail s1 lv strategy = Some s' /\
        code = Z_OK))).
    { destruct (negb (z_avail_in z1 =? 0)).
      - injection E as <- <- <-. auto.
      - pose proof (deflate_block_codes s z0 s1 z1 c1 Ed) as _.
        destruct (guard (in_long (d_strstart s1 - d_block_start s1))); cbn [bind] in E; [|discriminate].
        destruct (guard (in_long (d_strstart s1 - d_block_start s1 + d_lookahead s1))); cbn [bind] in E;
          [|discriminate].
        destruct (negb (d_strstart s1 - d_block_start s1 + d_lookahead s1 =? 0)) eqn:Eu.
        + injection E as <- <- <-. auto.
        + apply negb_false_iff, Z.eqb_eq in Eu. cbn [bind] in E.
          apply bind_strategy_inv in E. destruct E as (E & -> & ->).
          split; [reflexivity|]. right. auto. }
    destruct Hout as (-> & Hout).
    assert (Hgz1 : d_gzhead s1 = d_gzhead s).
    { rewrite <- Hgz. destruct Hout as [(-> & _) | (_ & Hpt1 & _)]; [reflexivity|].
      destruct (params_tail_shape _ _ _ _ Hpt1) as (P & _). pf_destruct P. congruence. }
    assert (Hfl : 0 <= Z_BLOCK <= 5) by (unfold Z_BLOCK; lia).
    assert (Hfin : forall R, (None : option (list Z)) = Some R -> Z_BLOCK = Z_FINISH /\ inb = R)
      by (intros R HR; discriminate).
    assert (Hc1a : c1 = Z_OK \/ c1 = Z_STREAM_END \/ c1 = Z_BUF_ERROR)
      by (destruct Hc1' as [->|(->&_)]; auto).
    assert (Hc1b : c1 = Z_STREAM_END -> Z_BLOCK = Z_FINISH /\ z_avail_in z1 = 0)
      by (intros H; destruct Hc1' as [->|(->&_)]; discriminate).
    assert (Hc1c : c1 = Z_BUF_ERROR -> z_avail_in z1 = Zlength inb /\ z_avail_out z1 = aout)
      by (intros H; destruct Hc1' as [->|(_&?&?)]; [discriminate|auto]).
    destruct (Hdef dict wrap D O None s tin tout adler inb aout Z_BLOCK msg s1 z1 c1 (conj HI' KF) Hfl Hb Hd Ha Ho
                Hfin Ed Hgz1 Hcall Hc1a Hc1b Hc1c) as (Hwb1 & Post).
    replace (c1 =? Z_STREAM_END) with false in Post by (destruct Hc1' as [->|(->&_)]; reflexivity).
    cbv zeta in Post. change (Z_BLOCK =? Z_FINISH) with false in Post. cbv iota in Post.
    destruct Post as (HI1 & KF1).
    destruct Hout as [(-> & _) | (Eu & Hpt1 & ->)].
    + split; [exact Hwb1|]. split; assumption.
    + pose proof HI1 as HI10. destruct HI10 as (HW31 & _).
      pose proof (W3_pos s1 HW31) as (Q1 & Q2 & Q3 & Q4).
      assert (Hc : pcase s1 lv strategy) by (right; clear - Eu Q1 Q3; lia).
      destruct (params_tail_shape _ _ _ _ Hpt1) as (P & _).
      split; [pose proof P as P'; pf_destruct P'; congruence|].
      split.
      * exact (params_finish3 _ _ _ _ s1 _ _ _ lv strategy s' HI1 (proj1 Hrange) (proj2 Hrange) Hc Hpt1).
      * exact (Hpt _ _ _ _ None s1 _ _ _ lv strategy s' (proj1 (proj1 HW31)) KF1 (proj1 Hrange) Hc Hpt1).
  - (* no deflate call *)
    cbn [bind] in E. apply bind_strategy_inv in E. destruct E as (E & -> & ->).
    change (params_tail s lv strategy = Some s') in E.
    assert (Hc : pcase s lv strategy).
    { apply andb_false_iff in Ec. destruct Ec as [Ec|Ec].
      - left. apply orb_false_iff in Ec. destruct Ec as [E1 E2].
        apply negb_false_iff, Z.eqb_eq in E1. apply negb_false_iff, Z.eqb_eq in E2. auto.
      - right. apply negb_false_iff, Z.eqb_eq in Ec.
        destruct HI' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [P0 | (Hlf & _)]).
        + destruct P0 as (_ & _ & _ & _ & _ & _ & _ & Hla & Hss & _). auto.
        + contradiction. }
    destruct (params_tail_shape s lv strategy s' E) as (P & _).
    split; [pose proof P as P'; pf_destruct P'; exact Pwb|].
    rewrite Z1, Z2, Z3, Z4, Z5, !app_nil_r. split.
    + rewrite Z1, Z2, Z3, Z4, Z5, !app_nil_r in NP2.
      exact (params_finish3 dict wrap D O s tin tout adler lv strategy s' NP2 (proj1 Hrange) (proj2 Hrange) Hc E).
    + exact (Hpt dict wrap D O None s tin tout adler lv strategy s' HW KF (proj1 Hrange) Hc E).
Qed.
End Gen.

(** ** Interface v2 *)
Theorem rtd_params_ok2 : Zlib.proof.huffman.Overlay.overlay_statement -> kf_deflate_stmt Krt2 -> kf_params_stmt Krt2.
Proof. intros _. exact (params_gen KF2 (fun dict wrap D O fin s tin tout adler lv st s2 => kf2_params dict wrap D O fin s tin tout adler lv st s2)). Qed.

(** ** Interface v1 *)
Theorem rtd_params_ok1 : kf_deflate_stmt Krt -> kf_params_stmt Krt.
Proof. exact (params_gen KF (fun dict wrap D O fin s tin tout adler lv st s2 => kf_params dict wrap D O fin s tin tout adler lv st s2)). Qed.
