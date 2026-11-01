(** * deflate_rle, part: the run scan
    Statement: LTCRleKit.v ([rscan_stmt]). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTCRleKit.
Require Import Zlib.proof.deflate.LTCRleGlue.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Lemma rs_mb_rd_ok b i : 0 <= i < Zlength (mb_val b) -> Znth i (mb_def b) = true ->
  mb_rd b i = Some (Znth i (mb_val b)).
Proof.
  intros Hi Hd. unfold mb_rd, in_range. rewrite Hd.
  replace ((0 <=? i) && (i <? Zlength (mb_val b))) with true by (symmetry; apply andb_true_iff; lia).
  reflexivity.
Qed.

Lemma rs_u32_id x : 0 <= x < 4294967296 -> u32 x = x.
Proof. intros; unfold u32; apply Z.mod_small; lia. Qed.

Lemma rs_ml_ml s x y : set_d_match_length (set_d_match_length s x) y = set_d_match_length s y.
Proof. reflexivity. Qed.

(** The window facts the scan needs. *)
Lemma rs_window s : W s -> rready s -> 1 <= d_lookahead s ->
  d_strstart s + MAX_MATCH < Zlength (mb_val (d_window s)) /\
  (forall i, 0 <= i <= d_strstart s + MAX_MATCH -> Znth i (mb_def (d_window s)) = true).
Proof.
  intros (Hp & (Hwl & _ & Hws & _) & (Hl & Hss & Hsl & _) & Hw & _) Hr Hla.
  unfold MAX_DIST, MIN_LOOKAHEAD, WIN_INIT, MAX_MATCH, MIN_MATCH in *.
  destruct Hr as [Hr|(Hr1 & Hr2)]; unfold MAX_DIST, MIN_LOOKAHEAD, WIN_INIT, MAX_MATCH, MIN_MATCH in *.
  - split; [lia|]. intros i Hi. apply Hw. lia.
  - assert (Hhw : d_strstart s + 258 < d_high_water s) by lia.
    split; [lia|]. intros i Hi. apply Hw. lia.
Qed.

(** The comparison loop from scan = strstart + 2 returns a scan in [strstart + 3, strstart + MAX_MATCH]. *)
Lemma rs_loop s prev :
  0 <= d_strstart s ->
  d_strstart s + MAX_MATCH < Zlength (mb_val (d_window s)) ->
  (forall i, 0 <= i <= d_strstart s + MAX_MATCH -> Znth i (mb_def (d_window s)) = true) ->
  exists sc, loop FUEL (rle_cmp_body s prev (d_strstart s + MAX_MATCH)) (d_strstart s - 1 + 3, 0) = Some sc /\
             d_strstart s + 3 <= sc <= d_strstart s + MAX_MATCH.
Proof.
  intros H0 Hlen Hd. set (st := d_strstart s) in *.
  apply (rg_loop_measure _
    (fun a => let '(scan, k) := a in
       exists q, scan = st + 2 + 8 * q + k /\ 0 <= q <= 31 /\ 0 <= k <= 7)
    (fun sc => st + 3 <= sc <= st + MAX_MATCH)
    (fun a => let '(scan, k) := a in st + MAX_MATCH - scan)).
  - intros [scan k] [q (-> & Hq & Hk)]. unfold MAX_MATCH in *. split; [lia|].
    unfold rle_cmp_body.
    rewrite rs_mb_rd_ok by (try apply Hd; lia). cbn [bind].
    destruct (negb _) eqn:E1; [left; eexists; split; [reflexivity|lia]|].
    destruct (Z.eqb_spec k 7) as [->|Hk7].
    + replace (st + 258 <=? Zlength (mb_val (d_window s))) with true by (symmetry; apply Z.leb_le; lia).
      cbn [guard bind].
      destruct (Z.ltb_spec (st + 2 + 8 * q + 7 + 1) (st + 258)) as [Hlt|Hge].
      * right. eexists; split; [reflexivity|]. split; [exists (q + 1); lia|lia].
      * left. eexists; split; [reflexivity|lia].
    + right. eexists; split; [reflexivity|]. split; [exists q; lia|lia].
  - exists 0. lia.
  - unfold MAX_MATCH. change (2 ^ Z.of_nat FUEL) with (2 ^ 40). lia.
Qed.

Theorem rscan_ok : rscan_stmt.
Proof.
  intros s HW Hfn Hr Hla.
  destruct (rs_window s HW Hr Hla) as (Hlen & Hd).
  assert (Hss : 0 <= d_strstart s) by (destruct HW as (_ & _ & (_ & H & _) & _); exact H).
  assert (Hml0 : RSC s (set_d_match_length s 0)).
  { exists 0. split; [reflexivity|]. unfold MAX_MATCH, MIN_MATCH. lia. }
  unfold rscan. autorewrite with fproj.
  destruct ((d_lookahead s >=? MIN_MATCH) && (d_strstart s >? 0)) eqn:Ec;
    [|exists (set_d_match_length s 0); split; [reflexivity|exact Hml0]].
  apply andb_true_iff in Ec. destruct Ec as [E1 E2].
  apply Z.geb_le in E1. apply Z.gtb_lt in E2.
  unfold MAX_MATCH, MIN_MATCH in *.
  rewrite !rs_mb_rd_ok by (try apply Hd; lia). cbn [bind].
  destruct (negb _); [exists (set_d_match_length s 0); split; [reflexivity|exact Hml0]|].
  destruct (negb _); [exists (set_d_match_length s 0); split; [reflexivity|exact Hml0]|].
  destruct (negb _); [exists (set_d_match_length s 0); split; [reflexivity|exact Hml0]|].
  set (s0 := set_d_match_length s 0).
  assert (Hst0 : d_strstart s0 = d_strstart s) by reflexivity.
  assert (Hw0 : d_window s0 = d_window s) by reflexivity.
  destruct (rs_loop s0 (Znth (d_strstart s - 1) (mb_val (d_window s))))
    as (sc & Esc & Hsc); rewrite ?Hst0, ?Hw0; unfold MAX_MATCH; try lia; [exact Hd|].
  rewrite Hst0 in Esc. unfold MAX_MATCH in Esc. rewrite Esc. cbn [bind].
  rewrite Hst0 in Hsc. unfold MAX_MATCH in Hsc.
  rewrite (rs_u32_id (d_strstart s + 258 - sc)) by lia.
  rewrite (rs_u32_id (258 - (d_strstart s + 258 - sc))) by lia.
  unfold s0. rewrite rs_ml_ml. autorewrite with fproj.
  destruct (Z.gtb_spec (258 - (d_strstart s + 258 - sc)) (d_lookahead s)) as [Hgt|Hle].
  - rewrite rs_ml_ml. exists (set_d_match_length s (d_lookahead s)). split; [reflexivity|].
    exists (d_lookahead s). split; [reflexivity|]. unfold MAX_MATCH, MIN_MATCH. lia.
  - exists (set_d_match_length s (258 - (d_strstart s + 258 - sc))). split; [reflexivity|].
    eexists. split; [reflexivity|]. unfold MAX_MATCH, MIN_MATCH. lia.
Qed.
