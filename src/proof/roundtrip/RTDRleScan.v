(* RT-D part RLE: the run scan repeats the byte at strstart - 1 (statement: RTDRleKit.v; model on
   RTDLTCRleScan.rscan_ok). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDRleKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** The comparison loop from scan = strstart + 2 (the bytes strstart .. strstart + 2 equal to prev): every byte
    below the scan it returns equals prev. *)
Lemma rfs_loop s prev :
  0 <= d_strstart s ->
  d_strstart s + MAX_MATCH < Zlength (mb_val (d_window s)) ->
  (forall i, 0 <= i <= d_strstart s + MAX_MATCH -> Znth i (mb_def (d_window s)) = true) ->
  (forall i, d_strstart s <= i <= d_strstart s + 2 -> Znth i (mb_val (d_window s)) = prev) ->
  exists sc, loop FUEL (rle_cmp_body s prev (d_strstart s + MAX_MATCH)) (d_strstart s - 1 + 3, 0) = Some sc /\
             d_strstart s + 3 <= sc <= d_strstart s + MAX_MATCH /\
             (forall i, d_strstart s <= i < sc -> Znth i (mb_val (d_window s)) = prev).
Proof.
  intros H0 Hlen Hd Heq. set (st := d_strstart s) in *.
  apply (rg_loop_measure _
    (fun a => let '(scan, k) := a in
       (exists q, scan = st + 2 + 8 * q + k /\ 0 <= q <= 31 /\ 0 <= k <= 7) /\
       (forall i, st <= i <= scan -> Znth i (mb_val (d_window s)) = prev))
    (fun sc => st + 3 <= sc <= st + MAX_MATCH /\
               (forall i, st <= i < sc -> Znth i (mb_val (d_window s)) = prev))
    (fun a => let '(scan, k) := a in st + MAX_MATCH - scan)).
  - intros [scan k] [[q (-> & Hq & Hk)] Hall]. unfold MAX_MATCH in *. split; [lia|].
    unfold rle_cmp_body.
    rewrite rs_mb_rd_ok by (try apply Hd; lia). cbn [bind].
    destruct (negb _) eqn:E1.
    { left; eexists; split; [reflexivity|]. split; [lia|]. intros i Hi. apply Hall. lia. }
    apply negb_false_iff, Z.eqb_eq in E1.
    assert (Hall' : forall i, st <= i <= st + 2 + 8 * q + k + 1 -> Znth i (mb_val (d_window s)) = prev).
    { intros i Hi. destruct (Z.eq_dec i (st + 2 + 8 * q + k + 1)) as [->|Hn]; [auto|]. apply Hall. lia. }
    destruct (Z.eqb_spec k 7) as [->|Hk7].
    + replace (st + 258 <=? Zlength (mb_val (d_window s))) with true by (symmetry; apply Z.leb_le; lia).
      cbn [guard bind].
      destruct (Z.ltb_spec (st + 2 + 8 * q + 7 + 1) (st + 258)) as [Hlt|Hge].
      * right. eexists; split; [reflexivity|]. split; [split; [exists (q + 1); lia|]|lia].
        intros i Hi. apply Hall'. lia.
      * left. eexists; split; [reflexivity|]. split; [lia|]. intros i Hi. apply Hall'. lia.
    + right. eexists; split; [reflexivity|]. split; [split; [exists q; lia|]|lia].
      intros i Hi. apply Hall'. lia.
  - split; [exists 0; lia|]. intros i Hi. apply Heq. lia.
  - unfold MAX_MATCH. change (2 ^ Z.of_nat FUEL) with (2 ^ 40). lia.
Qed.

Theorem rfscan_ok : rfscan_stmt.
Proof.
  intros s s2 HW Hfn Hr Hla E Hml.
  destruct (rs_window s HW Hr Hla) as (Hlen & Hd).
  assert (Hss : 0 <= d_strstart s) by (destruct HW as (_ & _ & (_ & H & _) & _); exact H).
  unfold rscan in E. autorewrite with fproj in E.
  destruct ((d_lookahead s >=? MIN_MATCH) && (d_strstart s >? 0)) eqn:Ec;
    [|injection E as <-; autorewrite with fproj in Hml; unfold MIN_MATCH in Hml; lia].
  apply andb_true_iff in Ec. destruct Ec as [E1 E2].
  apply Z.geb_le in E1. apply Z.gtb_lt in E2.
  unfold MAX_MATCH, MIN_MATCH in *.
  rewrite !rs_mb_rd_ok in E by (try apply Hd; lia). cbn [bind] in E.
  set (w := mb_val (d_window s)) in *.
  destruct (negb (Znth (d_strstart s - 1) w =? Znth (d_strstart s - 1 + 1) w)) eqn:C1;
    [injection E as <-; autorewrite with fproj in Hml; lia|].
  destruct (negb (Znth (d_strstart s - 1) w =? Znth (d_strstart s - 1 + 2) w)) eqn:C2;
    [injection E as <-; autorewrite with fproj in Hml; lia|].
  destruct (negb (Znth (d_strstart s - 1) w =? Znth (d_strstart s - 1 + 3) w)) eqn:C3;
    [injection E as <-; autorewrite with fproj in Hml; lia|].
  apply negb_false_iff, Z.eqb_eq in C1, C2, C3.
  set (s0 := set_d_match_length s 0) in *.
  assert (Hst0 : d_strstart s0 = d_strstart s) by reflexivity.
  assert (Hw0 : d_window s0 = d_window s) by reflexivity.
  assert (Q1 : 0 <= d_strstart s0) by (rewrite Hst0; lia).
  assert (Q2 : d_strstart s0 + MAX_MATCH < Zlength (mb_val (d_window s0)))
    by (rewrite Hst0, Hw0; fold w; unfold MAX_MATCH; lia).
  assert (Q3 : forall i, 0 <= i <= d_strstart s0 + MAX_MATCH -> Znth i (mb_def (d_window s0)) = true)
    by (rewrite Hst0, Hw0; exact Hd).
  assert (Q4 : forall i, d_strstart s0 <= i <= d_strstart s0 + 2 ->
                 Znth i (mb_val (d_window s0)) = Znth (d_strstart s - 1) w).
  { rewrite Hst0, Hw0. fold w. intros i Hi.
    assert (Hc : i = d_strstart s - 1 + 1 \/ i = d_strstart s - 1 + 2 \/ i = d_strstart s - 1 + 3) by lia.
    destruct Hc as [Hc|[Hc|Hc]]; rewrite Hc; auto. }
  destruct (rfs_loop s0 (Znth (d_strstart s - 1) w) Q1 Q2 Q3 Q4) as (sc & Esc & Hsc & Hall).
  rewrite Hst0 in Esc. unfold MAX_MATCH in Esc. rewrite Esc in E. cbn [bind] in E.
  rewrite Hst0 in Hsc, Hall. unfold MAX_MATCH in Hsc. rewrite Hw0 in Hall. fold w in Hall.
  rewrite (rs_u32_id (d_strstart s + 258 - sc)) in E by lia.
  rewrite (rs_u32_id (258 - (d_strstart s + 258 - sc))) in E by lia.
  unfold s0 in E. rewrite rs_ml_ml in E. autorewrite with fproj in E.
  assert (Hle : d_match_length s2 <= sc - d_strstart s).
  { destruct (Z.gtb_spec (258 - (d_strstart s + 258 - sc)) (d_lookahead s)) as [Hgt|Hle];
      injection E as <-; autorewrite with fproj; lia. }
  intros i Hi. apply Hall. lia.
Qed.
