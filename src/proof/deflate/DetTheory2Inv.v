(** * Law api_deterministic on data of any length: the wide deflate_api invariant RTK7Defs.Iapi7 kept short

    The invariant of DetTheory2.v is [Iapi7 W3 hinv7] with no dictionary and no gzip header given.  Here, as
    DetTheory.v does for LTApiDefs.Iapi: the output kept in the invariant can be cut down to the header and the
    part of the trailer already handed out ([Iapi7_shrink]); [Iapi7] only sees the state invariant, the API
    part, the output part and the positions ([Iapi7_frame]); deflateParams' level change ([params_finish7]). *)
From Coq Require Import ZArith.
From Coq Require Import List.
From Coq Require Import Lia.
From Coq Require Import Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTK7Api.
Require Import Zlib.proof.roundtrip.RTK7Hdr.
Require Import Zlib.proof.roundtrip.RTK7DMid.
Require Zlib.proof.deflate.DetTheory.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** Keeping the output short *)

(** A header without a dictionary has a prefix of at most 10 bytes that is one too (DetTheory.hdr_good_short
    for the round trips' copy of [hdr_good]). *)
Lemma hdr_good_short7 : forall wrap H, 0 <= wrap <= 2 -> hdr_good [] wrap H ->
  exists H' R, H = H' ++ R /\ hdr_good [] wrap H' /\ Zlength H' <= 10 /\ (wrap <> 0 -> H' <> []).
Proof.
  intros wrap H Hw G.
  assert (Hc : wrap = 0 \/ wrap = 1 \/ wrap = 2) by lia.
  destruct Hc as [-> | [-> | ->]].
  - exists H, []. rewrite app_nil_r. pose proof G as (_ & G0 & _). pose proof (G0 eq_refl) as E.
    split; [reflexivity|]. split; [exact G|]. split; [rewrite E; cbn; lia|]. tauto.
  - exists H, []. rewrite app_nil_r. split; [reflexivity|]. split; [exact G|].
    destruct G as (_ & _ & G1 & _). destruct (G1 eq_refl) as (L & _). cbn in L.
    split; [lia|]. intros _ C. subst H. cbn in L. discriminate.
  - destruct G as (GB & _ & _ & G2). destruct (G2 eq_refl) as (L & G3).
    exists (sublist 0 10 H), (sublist 10 (Zlength H) H).
    split; [rewrite <- sublist_split by lia; rewrite sublist_same by lia; reflexivity|].
    assert (L10 : Zlength (sublist 0 10 H) = 10) by (rewrite Zlength_sublist by lia; lia).
    split.
    + split; [apply Forall_sublist; exact GB|].
      split; [lia|]. split; [lia|]. intros _. split; [lia|].
      rewrite sublist_sublist by lia. exact G3.
    + split; [lia|]. intros _ C. rewrite C in L10. cbn in L10. discriminate.
Qed.

(** [Iapi7] without a dictionary and without a gzip header given only needs the start of the output: the
    header (at most 10 bytes) and, after the trailer was put, the part of the trailer already handed out (at
    most 8).  The rest of the output never matters again. *)
Lemma Iapi7_shrink : forall wrap D O fin s tin tout adler,
  Iapi7 W3 hinv7 [] wrap D O fin s tin tout adler -> d_gzhead s = None ->
  exists O', Iapi7 W3 hinv7 [] wrap D O' fin s tin (Zlength O') adler /\ Zlength O' <= 18.
Proof.
  intros wrap D O fin s tin tout adler HI' Hgn.
  pose proof HI' as (HW & HO & Hw & Hd & Hbd & Hld & Hlf & Hgz & Ht & HbO & HbD & HDl & HtD & Hfin & HD0 & Hph).
  assert (Hph' : exists O', bytes O' /\ Zlength O' <= 18 /\
            (ph0 [] wrap D O' s tin adler \/
             (d_last_flush s <> -2 /\
              (ph1 hinv7 [] wrap D O' s tin adler \/ ph2 [] wrap D O' s tin adler \/
               ph3 [] wrap D O' s tin adler)))).
  { destruct Hph as [P0 | (Hl2 & [P1 | [P2 | P3]])].
    - exists O. pose proof P0 as (_ & _ & _ & EO & _). subst O.
      split; [exact HbO|]. split; [cbn; lia|]. left; exact P0.
    - destruct P1 as (_ & _ & _ & _ & _ & H & k & Hh & _).
      destruct Hh as (_ & h & _ & Eh & _). congruence.
    - destruct P2 as (St & Dw & Bv & Hne & Chk & H & body & G & E).
      destruct (hdr_good_short7 wrap H Hw G) as (H' & R & EH & G' & L' & NH').
      rewrite EH, <- app_assoc, <- (app_nil_r (R ++ body)) in E.
      destruct (DetTheory.shrink_list O (pend s) H' (R ++ body) [] E HbO (proj1 G') (Forall_nil _))
        as (O' & B' & E' & BO' & LO' & NO').
      exists O'. split; [exact BO'|]. split; [cbn in LO'; lia|].
      right. split; [exact Hl2|]. right; left.
      split; [exact St|]. split; [exact Dw|]. split; [exact Bv|].
      split; [intros W0; apply NO'; [apply Hne|apply NH']; exact W0|]. split; [exact Chk|].
      exists H', B'. split; [exact G'|]. rewrite app_nil_r in E'. exact E'.
    - destruct P3 as (St & La & Sn & Bv & Hne & Chk & H & body & G & HE).
      destruct (hdr_good_short7 wrap H Hw G) as (H' & R & EH & G' & L' & NH').
      assert (Hne' : forall O' : list Z, (O <> [] -> H' <> [] -> O' <> []) -> wrap <> 0 -> O' <> [])
        by (intros O' N W0; apply N; [apply Hne|apply NH']; exact W0).
      destruct HE as [(Dw & E) | (Wp & Dw & E)].
      + rewrite EH, <- app_assoc, <- (app_nil_r (R ++ body)) in E.
        destruct (DetTheory.shrink_list O (pend s) H' (R ++ body) [] E HbO (proj1 G') (Forall_nil _))
          as (O' & B' & E' & BO' & LO' & NO').
        exists O'. split; [exact BO'|]. split; [cbn in LO'; lia|].
        right. split; [exact Hl2|]. right; right.
        do 4 (split; [assumption|]). split; [apply Hne'; exact NO'|]. split; [exact Chk|].
        exists H', B'. split; [exact G'|]. left. split; [exact Dw|]. rewrite app_nil_r in E'. exact E'.
      + rewrite EH, <- app_assoc, app_assoc with (l := R) in E.
        assert (BT : bytes (trailer wrap adler tin)).
        { unfold trailer. destruct (wrap =? 1); [|destruct (wrap =? 2)].
          - unfold msb2. repeat constructor; unfold u8, u32; apply Z.mod_pos_bound; lia.
          - unfold bytes; cbn. repeat constructor; unfold u8; apply Z.mod_pos_bound; lia.
          - constructor. }
        destruct (DetTheory.shrink_list O (pend s) H' (R ++ body) (trailer wrap adler tin) E HbO (proj1 G') BT)
          as (O' & B' & E' & BO' & LO' & NO').
        assert (LT : Zlength (trailer wrap adler tin) <= 8).
        { unfold trailer. destruct (wrap =? 1); [|destruct (wrap =? 2)]; cbn; [unfold msb2; cbn|..]; lia. }
        exists O'. split; [exact BO'|]. split; [lia|].
        right. split; [exact Hl2|]. right; right.
        do 4 (split; [assumption|]). split; [apply Hne'; exact NO'|]. split; [exact Chk|].
        exists H', B'. split; [exact G'|]. right. split; [exact Wp|]. split; [exact Dw|]. exact E'. }
  destruct Hph' as (O' & BO' & LO' & Ph').
  exists O'. split; [|exact LO'].
  unfold Iapi7. repeat (split; [assumption|]). split; [reflexivity|]. repeat (split; [assumption|]). exact Ph'.
Qed.

(** [Iapi7] mentions [fin] only in FINISH_STATE. *)
Lemma Iapi7_fin : forall dict wrap D O fin fin' s tin tout adler,
  Iapi7 W3 hinv7 dict wrap D O fin s tin tout adler -> (d_status s = FINISH_STATE -> fin' = Some []) ->
  Iapi7 W3 hinv7 dict wrap D O fin' s tin tout adler.
Proof.
  intros dict wrap D O fin fin' s tin tout adler HI' Hf.
  destruct HI' as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16).
  unfold Iapi7. tauto.
Qed.

(** ** The frame of the invariant *)

(** [Iapi7] only sees the state invariant, the API part, the output part and the positions
    (RTDLTApiInit.Iapi_frame for [Iapi7]). *)
Lemma Iapi7_frame : forall dict wrap D O fin s s' tin tout adler,
    Iapi7 W3 hinv7 dict wrap D O fin s tin tout adler -> W3 s' -> api_eq s s' -> out_eq s s' ->
    d_pending_buf_size s' = d_pending_buf_size s -> d_sym_next s' = d_sym_next s ->
    d_lookahead s' = d_lookahead s -> d_strstart s' = d_strstart s -> d_block_start s' = d_block_start s ->
    Iapi7 W3 hinv7 dict wrap D O fin s' tin tout adler.
Proof.
  intros dict wrap D O fin s s' tin tout adler HI' HW (A1 & A2 & A3 & A4 & A5 & A6) (B1 & B2 & B3)
    E1 E2 E3 E4 E5.
  assert (Hpend : pend s' = pend s) by (unfold pend, d_pending; rewrite B1, B3; reflexivity).
  assert (Hpen : d_pending s' = d_pending s) by (unfold d_pending; rewrite B1; reflexivity).
  assert (Hbv : d_bi_valid s' = d_bi_valid s) by (unfold d_bi_valid; rewrite B1; reflexivity).
  assert (Hout : outok s' <-> outok s).
  { unfold outok, d_pb, d_pending. rewrite B1, B2, B3, E1. tauto. }
  destruct HI' as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & Hph).
  unfold Iapi7. rewrite A1, A3, A5. split; [exact HW|]. split; [apply Hout; exact H2|].
  do 12 (split; [assumption|]).
  split; [rewrite E3, E4, E5; exact H15|].
  destruct Hph as [P0 | (Hlf & Ph)]; [left | right; split; [exact Hlf|]].
  - unfold ph0 in *. rewrite A1, A2, Hpen, Hbv, E2, E3, E4, E5. exact P0.
  - destruct Ph as [P1 | [P2 | P3]]; [left | right; left | right; right].
    + unfold ph1 in *. rewrite Hbv, E2, Hpend.
      destruct P1 as (Q1 & Q2 & Q3 & Q4 & Q5 & H & k & Hh & Q6).
      do 5 (split; [assumption|]). exists H, k. split; [|exact Q6].
      apply (hf7_frame hinv7 rtk7_hdr_ok s s' adler H k Hh); auto.
    + unfold ph2 in *. rewrite A1, A2, Hbv, Hpend. exact P2.
    + unfold ph3 in *. rewrite A1, A2, Hbv, Hpend, E2, E3. exact P3.
Qed.

(** ** deflateParams' level change *)

(** params_tail (the level and strategy set by deflateParams, after its checks) keeps [Iapi7]
    (RTDLTApiParams.params_finish for [Iapi7], from RTDLTCore.W3_params). *)
Lemma params_finish7 : forall dict wrap D O fin s tin tout adler lv st,
  Iapi7 W3 hinv7 dict wrap D O fin s tin tout adler ->
  0 <= lv <= 9 -> 0 <= st <= 4 ->
  (cfg_f lv = cfg_f (d_level s) /\ st = d_strategy s) \/ (d_lookahead s = 0 /\ d_strstart s = d_block_start s) ->
  exists s2, params_tail s lv st = Some s2 /\ d_gzhead s2 = d_gzhead s /\
    Iapi7 W3 hinv7 dict wrap D O fin s2 tin tout adler.
Proof.
  intros dict wrap D O fin s tin tout adler lv st HI' Hlv Hst Hc.
  pose proof HI' as HI0. destruct HI0 as (HW & _).
  destruct (W3_params s lv st HW Hlv Hst Hc)
    as (s2 & Hpt & HW2 & Hapi & Hout & _ & _ & Hwb & Hhb & Hss & Hla & Hbs & Hsn).
  exists s2. split; [exact Hpt|]. split; [apply Hapi|].
  apply (Iapi7_frame dict wrap D O fin s s2 tin tout adler HI' HW2 Hapi Hout); auto.
  pose proof (W3_prm s HW) as P1. pose proof (W3_prm s2 HW2) as P2.
  destruct Hout as (Ho1 & _).
  destruct P1 as (_ & _ & _ & _ & _ & _ & _ & _ & A1 & A2 & _).
  destruct P2 as (_ & _ & _ & _ & _ & _ & _ & _ & B1 & B2 & _).
  rewrite Ho1 in B2. lia.
Qed.

(** The compression function of a valid level. *)
Lemma cfg_func_ok : forall l, 0 <= l <= 9 -> cfg_func l = Some (cfg_f l).
Proof.
  intros l Hl. unfold cfg_func, cfg_f. replace ((0 <=? l) && (l <=? 9)) with true
    by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
  destruct (Znth l config_table) as [[[[? ?] ?] ?] ?]. reflexivity.
Qed.

Lemma set_strategy_bind7 : forall (o : option dstate) st (z : strm) s2,
  (let* s := o in Some (set_d_strategy s st)) = Some s2 ->
  (let* s := o in Some (set_d_strategy s st, z, Z_OK)) = Some (s2, z, Z_OK).
Proof. intros [s|] st z s2 H; cbn in *; congruence. Qed.

(** deflate(strm, Z_BLOCK) in FINISH_STATE: Z_STREAM_ERROR at entry, only msg set. *)
Lemma deflate_block_finish7 : forall s z,
  bad_state s = false -> d_status s = FINISH_STATE ->
  c_deflate s z Z_BLOCK = Some (s, set_z_msg z (Some Z_STREAM_ERROR), Z_STREAM_ERROR).
Proof.
  intros s z Hb Hs. rewrite c_deflate_stages, Hb. cbn [orb].
  unfold c_deflate_entry. rewrite Hs. cbn. reflexivity.
Qed.

(** deflateParams in FINISH_STATE (last_flush is not -2 there): either its deflate(strm, Z_BLOCK) fails at
    entry, or the compression function and the strategy are unchanged and only the level changes
    (DetTheory.params_in_finish for [Iapi7]). *)
Lemma params_in_finish7 : forall dict wrap D O fin s tin tout adler z level strategy,
  Iapi7 W3 hinv7 dict wrap D O fin s tin tout adler -> d_status s = FINISH_STATE ->
  exists s' z' code, c_deflateParams s z level strategy = Some (s', z', code) /\
    (z' = z \/ z' = set_z_msg z (Some Z_STREAM_ERROR)) /\ d_gzhead s' = d_gzhead s /\
    Iapi7 W3 hinv7 dict wrap D O fin s' tin tout adler.
Proof.
  intros dict wrap D O fin s tin tout adler z level strategy HI' Hst.
  assert (Hbad := Iapi7_bad_state W3 hinv7 dict wrap D O fin s tin tout adler rtk7_hdr_ok HI').
  pose proof HI' as HI0.
  destruct HI0 as (HW & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hph).
  assert (Hlf : d_last_flush s <> -2).
  { destruct Hph as [P0 | (L & _)]; [|exact L].
    destruct P0 as [[[E _] | [E _]] _]; rewrite Hst in E; unfold FINISH_STATE, INIT_STATE, GZIP_STATE in E;
      discriminate. }
  pose proof (W3_prm s HW) as Hprm.
  unfold c_deflateParams. rewrite Hbad. cbv zeta.
  set (lv := if level =? Z_DEFAULT_COMPRESSION then 6 else level).
  destruct ((lv <? 0) || (lv >? 9) || (strategy <? 0) || (strategy >? Z_FIXED)) eqn:Er.
  { exists s, z, Z_STREAM_ERROR. split; [reflexivity|]. split; [left; reflexivity|]. split; [reflexivity|].
    exact HI'. }
  assert (Hrange : 0 <= lv <= 9 /\ 0 <= strategy <= 4).
  { unfold Z_FIXED in Er. rewrite !orb_false_iff, Z.ltb_ge, Z.gtb_ltb, Z.ltb_ge, Z.ltb_ge, Z.gtb_ltb, Z.ltb_ge in Er.
    lia. }
  assert (Hlvl : 0 <= d_level s <= 9)
    by (destruct Hprm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L & _); exact L).
  rewrite (cfg_func_ok (d_level s) Hlvl). cbn [bind].
  destruct ((negb (strategy =? d_strategy s) || negb (cfg_f (d_level s) =? cfg_f lv)) && negb (d_last_flush s =? -2))
    eqn:Ec.
  - rewrite (deflate_block_finish7 s z Hbad Hst). cbn [bind]. rewrite Z.eqb_refl.
    exists s, (set_z_msg z (Some Z_STREAM_ERROR)), Z_STREAM_ERROR.
    split; [reflexivity|]. split; [right; reflexivity|]. split; [reflexivity|]. exact HI'.
  - assert (Hc : cfg_f lv = cfg_f (d_level s) /\ strategy = d_strategy s).
    { apply andb_false_iff in Ec. destruct Ec as [Ec|Ec].
      - apply orb_false_iff in Ec. destruct Ec as [E1 E2].
        apply negb_false_iff, Z.eqb_eq in E1. apply negb_false_iff, Z.eqb_eq in E2. auto.
      - apply negb_false_iff, Z.eqb_eq in Ec. contradiction. }
    destruct (params_finish7 dict wrap D O fin s tin tout adler lv strategy HI' (proj1 Hrange) (proj2 Hrange)
                (or_introl Hc)) as (s2 & Hpt & G2 & HI2).
    exists s2, z, Z_OK. split; [apply set_strategy_bind7; exact Hpt|].
    split; [left; reflexivity|]. split; [exact G2|exact HI2].
Qed.
