(* inflate_fast (BodyF5.v): what one pass does to the machine (pure). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inffast.code.
Require Import Zlib.proof.inffast.F5Kit.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Require Import Zlib.proof.inflate.MwfLemmas.

(* ---------------------------------------------------------------------------------------------- *)
(* copies                                                                                         *)

Lemma f5_Znth_byte: forall (l: list Z) i, bytes_ok l -> 0 <= Znth i l <= 255.
Proof.
  intros l i B. destruct (zlt i 0); [rewrite Znth_outofbounds by lia; cbv; split; discriminate |].
  destruct (zlt i (Zlength l)); [| rewrite Znth_outofbounds by lia; cbv; split; discriminate].
  unfold bytes_ok in B. rewrite Forall_Znth in B. specialize (B i ltac:(lia)). cbv beta in B. rep_lia.
Qed.

Lemma f5_bytes_app1: forall l x, bytes_ok l -> 0 <= x <= 255 -> bytes_ok (l ++ [x]).
Proof.
  intros l x B X. unfold bytes_ok in *. apply Forall_app. split; [auto|]. constructor; [rep_lia | constructor].
Qed.

Lemma f5_copy_f: forall n w sr ow, bytes_ok w -> bytes_ok ow ->
  Zlength (fst (copy_f n w sr ow)) = Zlength ow + Z.of_nat n /\ bytes_ok (fst (copy_f n w sr ow)).
Proof.
  induction n; intros w sr ow BW BO.
  - simpl. split; [lia | auto].
  - destruct sr as [i | i]; simpl.
    + destruct (IHn w (SWin (i + 1)) (ow ++ [Znth i w]) BW) as [L B].
      { apply f5_bytes_app1; auto. apply f5_Znth_byte; auto. }
      rewrite L, Zlength_app, Zlength_cons, Zlength_nil. split; [lia | auto].
    + destruct (IHn w (SOut (i + 1)) (ow ++ [Znth i ow]) BW) as [L B].
      { apply f5_bytes_app1; auto. apply f5_Znth_byte; auto. }
      rewrite L, Zlength_app, Zlength_cons, Zlength_nil. split; [lia | auto].
Qed.

Lemma f5_copy: forall w sr n ow ow' sr', bytes_ok w -> bytes_ok ow -> copy_bytes w sr n ow = (ow', sr') ->
  Zlength ow' = Zlength ow + Z.max 0 n /\ bytes_ok ow'.
Proof.
  intros w sr n ow ow' sr' BW BO E. unfold copy_bytes in E.
  destruct (f5_copy_f (Z.to_nat n) w sr ow BW BO) as [L B]. rewrite E in L, B. simpl in L, B.
  split; auto. rewrite L. destruct (zlt n 0); [rewrite Z_to_nat_neg by lia | rewrite Z2Nat.id by lia]; simpl; lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* mwf under the loop's machine updates                                                            *)

Lemma f5_mwf_ow: forall m ow, mwf m -> Zlength (m_ow m) <= Zlength ow <= m_aout m -> bytes_ok ow ->
  mwf (set_m_ow m ow).
Proof.
  intros m ow W L B. pose proof (mw_sow _ W). destruct W. constructor; simpl; auto; split; auto; lia.
Qed.

Lemma f5_mwf_drop: forall m b, mwf m -> 0 <= b <= m_bits m ->
  mwf (set_m_bits (set_m_hold m (Z.shiftr (m_hold m) (m_bits m - b))) b).
Proof.
  intros m b W Hb. pose proof (mw_hold _ W). destruct W. constructor; simpl; auto.
  - apply Zshiftr_range; auto. lia.
  - lia.
Qed.

Lemma f5_mwf_dropx: forall m n, mwf m -> 0 <= n <= m_bits m ->
  mwf (set_m_bits (set_m_hold m (Z.shiftr (m_hold m) n)) (u32 (m_bits m - n))).
Proof. intros m n W Hn. apply (mwf_dropbits m n W Hn). Qed.

Lemma f5_pull_bits: forall m, mwf m -> m_bits (fpull m) = m_bits m + 8.
Proof.
  intros m W. pose proof (mw_bits _ W). unfold fpull, pull; simpl. unfold u32. rewrite Z.mod_small by lia. lia.
Qed.

Lemma f5_tvalid_s: forall m m', m_s m' = m_s m -> fast_ok m -> mwf m' -> fast_ok m'.
Proof. intros m m' E [_ T] W. split; auto. rewrite E. auto. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the entries                                                                                    *)

Lemma f5_land15_len: forall op, 16 <= op <= 21 -> Z.land op 15 = op - 16.
Proof.
  intros op H. assert (op = 16 \/ op = 17 \/ op = 18 \/ op = 19 \/ op = 20 \/ op = 21) by lia.
  repeat match goal with H: _ \/ _ |- _ => destruct H as [-> | H] end; subst; reflexivity.
Qed.

Lemma f5_land15_dist: forall op, 16 <= op <= 29 -> Z.land op 15 = op - 16.
Proof.
  intros op H.
  assert (op = 16 \/ op = 17 \/ op = 18 \/ op = 19 \/ op = 20 \/ op = 21 \/ op = 22 \/ op = 23 \/
          op = 24 \/ op = 25 \/ op = 26 \/ op = 27 \/ op = 28 \/ op = 29) by lia.
  repeat match goal with H: _ \/ _ |- _ => destruct H as [-> | H] end; subst; reflexivity.
Qed.

Lemma f5_land48: forall op, Z.land op 48 = 0 -> Z.land op 16 = 0.
Proof.
  intros op H. change 16 with (Z.land 48 16). rewrite Z.land_assoc, H. reflexivity.
Qed.

Lemma f5_len_entry: forall e, final_ok LENS e -> Z.land (e_op e) 16 <> 0 ->
  16 <= e_op e <= 21 /\ 3 <= e_val e <= 258.
Proof.
  intros e F N. unfold final_ok in F. simpl in F.
  destruct F as [[F _] | [F | [F | [_ F]]]]; auto.
  - rewrite F in N. contradiction.
  - rewrite F in N. contradiction.
  - apply f5_land48 in F. contradiction.
Qed.

Lemma f5_dist_entry: forall e, final_ok DISTS e -> Z.land (e_op e) 16 <> 0 ->
  16 <= e_op e <= 29 /\ 1 <= e_val e <= 32768.
Proof.
  intros e F N. unfold final_ok in F. simpl in F.
  destruct F as [F | [_ F]]; auto.
  apply f5_land48 in F. contradiction.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the pieces of the pass                                                                         *)

Definition f5_same (m m': mst) : Prop :=
  m_s m' = m_s m /\ m_inp m' = m_inp m /\ m_aout m' = m_aout m /\ m_ow m' = m_ow m.

Lemma f5_pull_ok: forall m, fast_ok m -> 1 <= m_have m -> m_bits m <= 31 ->
  fast_ok (fpull m) /\ f5_same m (fpull m) /\ m_nx (fpull m) = m_nx m + 1 /\ m_bits (fpull m) = m_bits m + 8.
Proof.
  intros m FO H1 H2. pose proof (fast_ok_mwf _ FO) as W.
  assert (W': mwf (fpull m)) by (apply mwf_pull; auto; lia).
  split; [apply (f5_tvalid_s m); auto |]. split; [repeat split |]. split; [reflexivity |].
  apply f5_pull_bits; auto.
Qed.

Lemma f5_refill: forall m, fast_ok m -> 0 <= m_bits m <= 30 -> (m_bits m < 15 -> 2 <= m_have m) ->
  fast_ok (refill2 m) /\ f5_same m (refill2 m) /\
  ((m_bits m < 15 /\ m_nx (refill2 m) = m_nx m + 2 /\ m_bits (refill2 m) = m_bits m + 16) \/
   (15 <= m_bits m /\ m_nx (refill2 m) = m_nx m /\ m_bits (refill2 m) = m_bits m)).
Proof.
  intros m FO HB HH. unfold refill2. destruct (m_bits m <? 15) eqn:E.
  - apply Z.ltb_lt in E. specialize (HH E).
    destruct (f5_pull_ok m FO ltac:(lia) ltac:(lia)) as (F1 & (S1 & S2 & S3 & S4) & N1 & B1).
    assert (1 <= m_have (fpull m)) by (unfold m_have in *; rewrite S2, N1; lia).
    destruct (f5_pull_ok (fpull m) F1 ltac:(lia) ltac:(lia)) as (F2 & (T1 & T2 & T3 & T4) & N2 & B2).
    split; auto. split; [unfold f5_same; rewrite T1, T2, T3, T4; auto |]. left. lia.
  - apply Z.ltb_ge in E. split; auto. split; [repeat split |]. right. lia.
Qed.

Lemma f5_lenx: forall e m len m3, fast_ok m -> entry_ok e -> Z.land (e_op e) 15 <= 5 -> 0 <= m_bits m <= 30 ->
  (m_bits m < Z.land (e_op e) 15 -> 1 <= m_have m) -> lenx e m = (len, m3) ->
  fast_ok m3 /\ f5_same m m3 /\
  (exists r, 0 <= r < 2 ^ Z.land (e_op e) 15 /\ len = e_val e + r) /\
  ((m_bits m < Z.land (e_op e) 15 /\ m_nx m3 = m_nx m + 1 /\ m_bits m3 = m_bits m + 8 - Z.land (e_op e) 15) \/
   (Z.land (e_op e) 15 <= m_bits m /\ m_nx m3 = m_nx m /\ m_bits m3 = m_bits m - Z.land (e_op e) 15)).
Proof.
  intros e m len m3 FO EO X5 HB HH E. unfold lenx in E.
  assert (X0: 0 <= Z.land (e_op e) 15) by (apply Z.land_nonneg; lia).
  set (x := Z.land (e_op e) 15) in *.
  destruct (x =? 0) eqn:Ex; cbn [negb] in E.
  - apply Z.eqb_eq in Ex. inversion E; subst len m3. split; auto. split; [repeat split |].
    split; [exists 0; rewrite Ex; simpl; lia | right; lia].
  - apply Z.eqb_neq in Ex.
    set (mp := if m_bits m <? x then fpull m else m) in E.
    assert (P: fast_ok mp /\ f5_same m mp /\
      ((m_bits m < x /\ m_nx mp = m_nx m + 1 /\ m_bits mp = m_bits m + 8) \/
       (x <= m_bits m /\ m_nx mp = m_nx m /\ m_bits mp = m_bits m))).
    { subst mp. destruct (m_bits m <? x) eqn:Eb.
      - apply Z.ltb_lt in Eb. destruct (f5_pull_ok m FO ltac:(auto) ltac:(lia)) as (F1 & S1 & N1 & B1).
        refine (conj F1 (conj S1 _)). left; lia.
      - apply Z.ltb_ge in Eb. split; auto. split; [repeat split |]. right; lia. }
    destruct P as (FP & (S1 & S2 & S3 & S4) & NB).
    assert (XB: x <= m_bits mp) by lia.
    pose proof (fast_ok_mwf _ FP) as WP. pose proof (mw_hold _ WP) as HP. pose proof (mw_bits _ WP).
    inversion E; subst len m3.
    assert (Wm: mwf (set_m_bits (set_m_hold mp (Z.shiftr (m_hold mp) x)) (u32 (m_bits mp - x))))
      by (apply f5_mwf_dropx; auto; lia).
    split; [apply (f5_tvalid_s mp); auto |].
    split; [unfold f5_same; simpl; rewrite S1, S2, S3, S4; auto |].
    unfold u32. rewrite (Z.mod_small (m_bits mp - x)) by lia. simpl.
    split; [| lia].
    pose proof (Z.mod_pos_bound (m_hold mp) (2 ^ x) ltac:(apply Z.pow_pos_nonneg; lia)).
    exists (m_hold mp mod 2 ^ x). split; [lia |].
    assert (2 ^ x <= 2 ^ 5) by (apply Z.pow_le_mono_r; lia).
    destruct EO as (_ & _ & EV). rewrite Z.mod_small; [lia |]. simpl in *. lia.
Qed.

Lemma f5_distx: forall e m dist m6, fast_ok m -> Z.land (e_op e) 15 <= 13 -> 0 <= m_bits m <= 30 ->
  (m_bits m < Z.land (e_op e) 15 -> 1 <= m_have m) -> (m_bits m + 8 < Z.land (e_op e) 15 -> 2 <= m_have m) ->
  distx e m = (dist, m6) ->
  fast_ok m6 /\ f5_same m m6 /\
  ((m_bits m + 8 < Z.land (e_op e) 15 /\ m_nx m6 = m_nx m + 2 /\ m_bits m6 = m_bits m + 16 - Z.land (e_op e) 15) \/
   (m_bits m < Z.land (e_op e) 15 <= m_bits m + 8 /\ m_nx m6 = m_nx m + 1 /\ m_bits m6 = m_bits m + 8 - Z.land (e_op e) 15) \/
   (Z.land (e_op e) 15 <= m_bits m /\ m_nx m6 = m_nx m /\ m_bits m6 = m_bits m - Z.land (e_op e) 15)).
Proof.
  intros e m dist m6 FO X13 HB HH1 HH2 E. unfold distx in E.
  assert (X0: 0 <= Z.land (e_op e) 15) by (apply Z.land_nonneg; lia).
  set (x := Z.land (e_op e) 15) in *.
  set (mp := if m_bits m <? x then (let m := fpull m in if m_bits m <? x then fpull m else m) else m) in E.
  assert (P: fast_ok mp /\ f5_same m mp /\
    ((m_bits m + 8 < x /\ m_nx mp = m_nx m + 2 /\ m_bits mp = m_bits m + 16) \/
     (m_bits m < x <= m_bits m + 8 /\ m_nx mp = m_nx m + 1 /\ m_bits mp = m_bits m + 8) \/
     (x <= m_bits m /\ m_nx mp = m_nx m /\ m_bits mp = m_bits m))).
  { subst mp. destruct (m_bits m <? x) eqn:Eb.
    - apply Z.ltb_lt in Eb. destruct (f5_pull_ok m FO ltac:(auto) ltac:(lia)) as (F1 & (S1 & S2 & S3 & S4) & N1 & B1).
      cbv zeta. rewrite B1. destruct (m_bits m + 8 <? x) eqn:Eb2.
      + apply Z.ltb_lt in Eb2.
        assert (1 <= m_have (fpull m)) by (unfold m_have in *; rewrite S2, N1; specialize (HH2 Eb2); lia).
        destruct (f5_pull_ok (fpull m) F1 ltac:(auto) ltac:(lia)) as (F2 & (T1 & T2 & T3 & T4) & N2 & B2).
        split; auto. split; [unfold f5_same; rewrite T1, T2, T3, T4; auto |]. left; lia.
      + apply Z.ltb_ge in Eb2. split; auto. split; [unfold f5_same; rewrite S1, S2, S3, S4; auto |]. right; left; lia.
    - apply Z.ltb_ge in Eb. split; auto. split; [repeat split |]. right; right; lia. }
  destruct P as (FP & (S1 & S2 & S3 & S4) & NB).
  assert (XB: x <= m_bits mp) by lia.
  pose proof (fast_ok_mwf _ FP) as WP. pose proof (mw_bits _ WP).
  inversion E; subst m6.
  assert (Wm: mwf (set_m_bits (set_m_hold mp (Z.shiftr (m_hold mp) x)) (u32 (m_bits mp - x))))
    by (apply f5_mwf_dropx; auto; lia).
  split; [apply (f5_tvalid_s mp); auto |].
  split; [unfold f5_same; simpl; rewrite S1, S2, S3, S4; auto |].
  unfold u32. rewrite (Z.mod_small (m_bits mp - x)) by lia. simpl. lia.
Qed.

Lemma f5_fcopy: forall s len dist m go m', mwf m -> m_s m = s -> 1 <= len -> fcopy s len dist m = (go, m') ->
  (go = true /\ exists ow, m' = set_m_ow m ow /\ Zlength ow = Zlength (m_ow m) + len /\ bytes_ok ow) \/
  (go = false /\ m' = set_bad m F_far).
Proof.
  intros s len dist m go m' W Es L1 E. pose proof (mw_ow _ W) as [_ BO].
  pose proof (proj2 (sw_wdata _ (mw_s _ W))) as BW. pose proof (proj1 (sw_wnext _ (mw_s _ W))) as WN.
  rewrite Es in BW, WN. unfold fcopy in E.
  repeat match type of E with
  | context [match copy_bytes ?w ?sr ?n ?ow with _ => _ end] =>
      let o := fresh "o" in let x := fresh "x" in let Ec := fresh "Ec" in
      destruct (copy_bytes w sr n ow) as [o x] eqn:Ec;
      apply f5_copy in Ec; [| assumption | assumption]; destruct Ec as [?L ?B]
  | context [if ?b then _ else _] =>
      let Eb := fresh "Eb" in destruct b eqn:Eb
  end.
  all: try (inversion E; subst; right; split; reflexivity).
  all: inversion E; subst; left; split; [reflexivity |].
  all: eexists; split; [reflexivity |].
  all: split; [| assumption].
  all: repeat match goal with H: (_ <? _) = true |- _ => apply Z.ltb_lt in H
                            | H: (_ <? _) = false |- _ => apply Z.ltb_ge in H
                            | H: (_ =? _) = true |- _ => apply Z.eqb_eq in H
                            | H: (_ =? _) = false |- _ => apply Z.eqb_neq in H end.
  all: lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the conclusion, from the machine before the last update                                       *)

Definition f5_concl (m: mst) (go: bool) (m': mst) : Prop :=
  m_inp m' = m_inp m /\ m_aout m' = m_aout m /\ m_nx m <= m_nx m' <= Zlength (m_inp m) /\
  0 <= m_bits m' <= 30 /\ m_bits m' - 8 * m_nx m' <= m_bits m - 8 * m_nx m /\ lrange (m_hold m') /\
  Zlength (m_ow m) <= Zlength (m_ow m') <= m_aout m /\
  (go = true -> fast_ok m' /\ m_mode m' = LEN /\ Zlength (m_ow m) < Zlength (m_ow m')).

Lemma f5_concl_bad: forall m mb x, mwf mb -> f5_same m mb ->
  m_nx m <= m_nx mb <= Zlength (m_inp m) -> 0 <= m_bits mb <= 30 ->
  m_bits mb - 8 * m_nx mb <= m_bits m - 8 * m_nx m -> mwf m ->
  f5_concl m false (set_bad mb x).
Proof.
  intros m mb x W (S1 & S2 & S3 & S4) N B G W0. pose proof (mw_hold _ W). pose proof (mw_ow _ W0).
  unfold f5_concl; simpl. rewrite S2, S3, S4. unfold lrange in *. repeat split; try lia; try (intros D; discriminate).
Qed.

Lemma f5_concl_mode: forall m mb x, mwf mb -> f5_same m mb ->
  m_nx m <= m_nx mb <= Zlength (m_inp m) -> 0 <= m_bits mb <= 30 ->
  m_bits mb - 8 * m_nx mb <= m_bits m - 8 * m_nx m -> mwf m ->
  f5_concl m false (set_mode mb x).
Proof.
  intros m mb x W (S1 & S2 & S3 & S4) N B G W0. pose proof (mw_hold _ W). pose proof (mw_ow _ W0).
  unfold f5_concl; simpl. rewrite S2, S3, S4. unfold lrange in *. repeat split; try lia; try (intros D; discriminate).
Qed.

Lemma f5_concl_ow: forall m mb ow, fast_ok mb -> f5_same m mb -> m_mode m = LEN ->
  m_nx m <= m_nx mb <= Zlength (m_inp m) -> 0 <= m_bits mb <= 30 ->
  m_bits mb - 8 * m_nx mb <= m_bits m - 8 * m_nx m ->
  Zlength (m_ow m) < Zlength ow <= m_aout m -> bytes_ok ow ->
  f5_concl m true (set_m_ow mb ow).
Proof.
  intros m mb ow FO S MD N B G L BO. pose proof (fast_ok_mwf _ FO) as W. pose proof (mw_hold _ W).
  destruct S as (S1 & S2 & S3 & S4).
  assert (W': mwf (set_m_ow mb ow)) by (apply f5_mwf_ow; auto; rewrite S3, S4; lia).
  unfold f5_concl; simpl. rewrite S2, S3.
  refine (conj eq_refl (conj eq_refl (conj _ (conj _ (conj _ (conj H (conj _ _))))))); try lia.
  intros _. split; [apply (f5_tvalid_s mb); auto |]. split; [unfold m_mode; simpl; rewrite S1; auto | lia].
Qed.

Lemma f5_same_trans: forall a b c, f5_same a b -> f5_same b c -> f5_same a c.
Proof. intros a b c (A1 & A2 & A3 & A4) (B1 & B2 & B3 & B4). repeat split; congruence. Qed.

Lemma f5_drop_same: forall m b, f5_same m (set_m_bits (set_m_hold m (Z.shiftr (m_hold m) (m_bits m - b))) b).
Proof. intros. repeat split. Qed.

Lemma f5_iter_facts : lwalk_facts_stmt -> dwalk_facts_stmt -> iter_facts_stmt.
Proof.
  intros LW DW m go m' FO MD H6 HL HB E. change (f5_concl m go m').
  pose proof (fast_ok_mwf _ FO) as W0. pose proof (mw_bits _ W0) as B0. pose proof (mw_nx _ W0) as N0.
  unfold m_have, m_left in *.
  rewrite fast_iter_eq in E.
  (* if (bits < 15) refill *)
  destruct (f5_refill m FO ltac:(lia) ltac:(unfold m_have; lia)) as (F1 & SM1 & R1).
  set (m1 := refill2 m) in *.
  assert (MD1: m_mode m1 = LEN) by (unfold m_mode; rewrite (proj1 SM1); auto).
  (* the length/literal walk *)
  pose proof (LW m1 F1 MD1 ltac:(lia)) as LF. rewrite (proj1 SM1) in LF.
  destruct (lwalk (m_s m) m1) as [e m2] eqn:EL.
  destruct LF as (EO & FL & LO & LL & B2 & M2).
  assert (F2: fast_ok m2).
  { apply (f5_tvalid_s m1); [rewrite M2; reflexivity | auto |].
    rewrite M2. apply f5_mwf_drop; [apply fast_ok_mwf; auto | lia]. }
  assert (SM2: f5_same m m2).
  { apply (f5_same_trans m m1); auto. rewrite M2. apply f5_drop_same. }
  assert (N2: m_nx m2 = m_nx m1) by (rewrite M2; reflexivity).
  clear M2 EL.
  unfold fdisp in E.
  destruct (e_op e =? 0) eqn:Eop.
  { (* literal *)
    inversion E; subst go m'.
    pose proof (mw_ow _ (fast_ok_mwf _ F2)) as [_ BO2].
    destruct SM2 as (T1 & T2 & T3 & T4).
    apply f5_concl_ow; auto; [repeat split; auto | lia | lia | lia | | ].
    - rewrite Zlength_app, Zlength_cons, Zlength_nil, T4. lia.
    - apply f5_bytes_app1; auto. pose proof (Z.mod_pos_bound (e_val e) 256 ltac:(lia)). lia. }
  destruct (negb (Z.land (e_op e) 16 =? 0)) eqn:E16.
  2:{ destruct (negb (Z.land (e_op e) 32 =? 0)); inversion E; subst go m'.
      - apply f5_concl_mode; auto; try lia. apply fast_ok_mwf; auto.
      - apply f5_concl_bad; auto; try lia. apply fast_ok_mwf; auto. }
  (* the length branch *)
  apply negb_true_iff, Z.eqb_neq in E16.
  destruct (f5_len_entry e FL E16) as [OP VL].
  pose proof (f5_land15_len _ OP) as X15.
  unfold flen in E.
  destruct (lenx e m2) as [len m3] eqn:Elx.
  destruct (f5_lenx e m2 len m3 F2 EO ltac:(lia) ltac:(lia) ltac:(unfold m_have; destruct SM2 as (_ & T2 & _); rewrite T2; lia) Elx)
    as (F3 & SM3' & (r & Hr & Hlen) & R3).
  rewrite X15 in Hr, R3.
  pose proof (Z.pow_pos_nonneg 2 (e_op e - 16) ltac:(lia)).
  assert (LEN258: len <= 258) by (unfold len_ok in LO; specialize (LO OP); lia).
  pose proof (f5_same_trans _ _ _ SM2 SM3') as SM3. clear SM3'.
  assert (MD3: m_mode m3 = LEN) by (unfold m_mode; rewrite (proj1 SM3); auto).
  destruct (f5_refill m3 F3 ltac:(lia) ltac:(unfold m_have; destruct SM3 as (_ & T2 & _); rewrite T2; lia))
    as (F4 & SM4' & R4).
  set (m4 := refill2 m3) in *.
  pose proof (f5_same_trans _ _ _ SM3 SM4') as SM4. clear SM4'.
  assert (MD4: m_mode m4 = LEN) by (unfold m_mode; rewrite (proj1 SM4); auto).
  (* the distance walk *)
  pose proof (DW m4 F4 MD4 ltac:(lia)) as DF. rewrite (proj1 SM4) in DF.
  destruct (dwalk (m_s m) m4) as [e2 m5] eqn:ED.
  destruct DF as (EO2 & FD & DL & B5 & M5).
  assert (F5: fast_ok m5).
  { apply (f5_tvalid_s m4); [rewrite M5; reflexivity | auto |].
    rewrite M5. apply f5_mwf_drop; [apply fast_ok_mwf; auto | lia]. }
  assert (SM5: f5_same m m5).
  { apply (f5_same_trans m m4); auto. rewrite M5. apply f5_drop_same. }
  assert (N5: m_nx m5 = m_nx m4) by (rewrite M5; reflexivity).
  clear M5 ED.
  destruct (negb (Z.land (e_op e2) 16 =? 0)) eqn:E16d.
  2:{ inversion E; subst go m'. apply f5_concl_bad; auto; try lia. apply fast_ok_mwf; auto. }
  apply negb_true_iff, Z.eqb_neq in E16d.
  destruct (f5_dist_entry e2 FD E16d) as [OP2 VD].
  pose proof (f5_land15_dist _ OP2) as X15d.
  destruct (distx e2 m5) as [dist m6] eqn:EDX.
  destruct (f5_distx e2 m5 dist m6 F5 ltac:(lia) ltac:(lia)
              ltac:(unfold m_have; destruct SM5 as (_ & T2 & _); rewrite T2; lia)
              ltac:(unfold m_have; destruct SM5 as (_ & T2 & _); rewrite T2; lia) EDX)
    as (F6 & SM6' & R6).
  rewrite X15d in R6.
  pose proof (f5_same_trans _ _ _ SM5 SM6') as SM6. clear SM6'.
  (* the copy *)
  destruct (f5_fcopy (m_s m) len dist m6 go m' (fast_ok_mwf _ F6) ltac:(destruct SM6; auto) ltac:(lia) E)
    as [(-> & ow & -> & Low & Bow) | (-> & ->)].
  - apply f5_concl_ow; auto; try lia.
    destruct SM6 as (_ & _ & T3 & T4). rewrite Low, T4. lia.
  - apply f5_concl_bad; auto; try lia. apply fast_ok_mwf; auto.
Qed.

