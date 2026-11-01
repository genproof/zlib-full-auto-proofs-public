(** * cf_still, part slow: next_in never goes back during deflate_slow; FLUSH_BLOCK and the tail
    keep strstart. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDLTCStill.
Require Import Zlib.proof.roundtrip.RTDLTCSlowInv Zlib.proof.roundtrip.RTDLTCSlowRefill Zlib.proof.roundtrip.RTDLTCSlow2.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Lemma ss_fpend s z s' z' : c_flush_pending s z = Some (s', z') ->
  z_next_in z' = z_next_in z /\ d_strstart s' = d_strstart s.
Proof.
  unfold c_flush_pending, bind.
  destruct (c_tr_flush_bits (d_out s)) as [o|]; [|discriminate].
  destruct (_ =? 0); [intros H; inversion H; subst; split; reflexivity|].
  destruct (mb_read _ _ _) as [b|]; [|discriminate].
  unfold out_put. destruct (_ <=? _); [|discriminate].
  intros H. destruct (_ =? 0); inversion H; subst; split; reflexivity.
Qed.

Lemma ss_fbo s z last s' z' : c_flush_block_only s z last = Some (s', z') ->
  z_next_in z' = z_next_in z /\ d_strstart s' = d_strstart s.
Proof.
  unfold c_flush_block_only, bind.
  destruct (guard _) as [[]|]; [|discriminate].
  destruct (if d_block_start s >=? 0 then _ else _) as [buf|]; [|discriminate].
  destruct (c_tr_flush_block _ _ _ _) as [[t x]|]; [|discriminate].
  intros H. apply ss_fpend in H. exact H.
Qed.

Lemma ss_fb s z last s' z' r : c_flush_block s z last = Some (s', z', r) ->
  z_next_in z' = z_next_in z /\ d_strstart s' = d_strstart s.
Proof.
  unfold c_flush_block, bind.
  destruct (c_flush_block_only s z last) as [[s1 z1]|] eqn:E; [|discriminate].
  apply ss_fbo in E. intros H. destruct (_ && _); inversion H; subst; exact E.
Qed.

Lemma ss_tail s z flush s' z' bs : c_deflate_tail s z flush = Some (s', z', bs) ->
  z_next_in z' = z_next_in z /\ d_strstart s' = d_strstart s.
Proof.
  unfold c_deflate_tail, bind.
  destruct (flush =? Z_FINISH).
  - destruct (c_flush_block s z 1) as [[[s1 z1] r]|] eqn:E; [|discriminate].
    apply ss_fb in E. intros H. destruct r; inversion H; subst; exact E.
  - destruct (negb _).
    + destruct (c_flush_block s z 0) as [[[s1 z1] r]|] eqn:E; [|discriminate].
      apply ss_fb in E. intros H. destruct r; inversion H; subst; exact E.
    + intros H. inversion H; subst. split; reflexivity.
Qed.

Lemma ss_end s z flush s' z' bs : dsl_end s z flush = Some (s', z', bs) ->
  z_next_in z' = z_next_in z /\ (d_match_available s = 0 -> d_strstart s' = d_strstart s).
Proof.
  unfold dsl_end, bind.
  destruct (Z.eqb_spec (d_match_available s) 0) as [E0|E0]; cbn [negb].
  - intros H. apply ss_tail in H. destruct H as [H1 H2]. split; [exact H1|]. intros _. exact H2.
  - destruct (mb_rd _ _) as [c|]; [|discriminate].
    destruct (c_dtally_lit _ _) as [[s1 b]|]; [|discriminate].
    intros H. apply ss_tail in H. destruct H as [H1 H2]. split; [exact H1|]. intros E. contradiction.
Qed.

(** The stream of an iteration's result. *)
Definition ss_z (r : (dstate * strm) + dexit) : strm :=
  match r with inl (_, z) => z | inr (_, z, _) => z end.

Lemma ss_bflush s z b r : c_bflush s z b = Some r -> z_next_in (ss_z r) = z_next_in z.
Proof.
  unfold c_bflush, bind. destruct b.
  - destruct (c_flush_block s z 0) as [[[s1 z1] o]|] eqn:E; [|discriminate].
    apply ss_fb in E. intros H. destruct o; inversion H; subst; exact (proj1 E).
  - intros H. inversion H; subst. reflexivity.
Qed.

Lemma ss_step s z r : dsl_step s z = Some r -> z_next_in (ss_z r) = z_next_in z.
Proof.
  rewrite dsl_step_eq. unfold bind at 1.
  destruct (dsl_pre s) as [s1|]; [|discriminate].
  destruct (_ && _).
  - unfold dsl_match, bind.
    destruct (c_dtally_dist _ _ _) as [[s2 b]|]; [|discriminate].
    destruct (loop FUEL _ _) as [s3|]; [|discriminate].
    apply ss_bflush.
  - destruct (negb _).
    + unfold dsl_lit, bind.
      destruct (mb_rd _ _) as [c|]; [|discriminate].
      destruct (c_dtally_lit _ _) as [[s2 b]|]; [|discriminate].
      destruct (if b then _ else _) as [[s3 z3]|] eqn:E; [|discriminate].
      assert (Ez : z_next_in z3 = z_next_in z).
      { destruct b; [apply ss_fbo in E; exact (proj1 E)|inversion E; reflexivity]. }
      intros H. destruct (_ =? 0); inversion H; subst; exact Ez.
    + unfold dsl_cand. intros H. inversion H; subst. reflexivity.
Qed.

Lemma ss_fill_pre s0 z0 flush s z evs : SI s0 z0 flush s z evs ->
  fill_pre s /\ zall z /\ adler_ok (d_wrap s) (z_adler z).
Proof.
  intros HSI. pose proof HSI as (HW2 & Hq & HL & HE).
  destruct HW2 as [HW Hx].
  destruct HW as (Hp & Hws & Hpos & Hwin & Hh & Hm & H0 & syms & Ht).
  destruct HE as (Hc & Hf & Ho & Hsp & Hapi & Hza & Had & _ & _ & _).
  assert (Hlv : d_level s <> 0) by (apply rf_fn_level; rewrite (rf_fn_same s0 s Hsp); exact Hf).
  split; [|split; [exact Hza|]].
  - split; [exact Hp|]. split; [exact Hws|]. split; [exact Hpos|]. split; [exact Hwin|].
    unfold whash in Hh. destruct (Z.eqb_spec (d_level s) 0) as [E|_]; [contradiction|]. apply Hh.
  - destruct Hapi as (_ & B & _); rewrite B; exact Had.
Qed.

Lemma ss_body s0 z0 flush s z r : fill_spec -> slow_P s0 z0 flush (s, z) -> dsl_body flush (s, z) = Some r ->
  z_next_in z <= z_next_in (ss_z r).
Proof.
  intros Hfill [evs HSI]. cbn [fst snd] in HSI.
  destruct (ss_fill_pre s0 z0 flush s z evs HSI) as (Hfp & Hza & Had).
  unfold dsl_body, c_refill, need_min_lookahead.
  destruct (d_lookahead s <? MIN_LOOKAHEAD).
  - destruct (Hfill s z Hfp Hza Had) as (s' & z' & k & d & Ec & _ & _ & Hz & _).
    pose proof Hz as (_ & Hk & Hn & _).
    rewrite Ec. unfold bind.
    destruct (_ && _); [intros H; inversion H; subst; cbn; lia|].
    destruct (_ =? 0); [intros H; inversion H; subst; cbn; lia|].
    intros H. apply ss_step in H. lia.
  - unfold bind. intros H. apply ss_step in H. lia.
Qed.

Lemma ss_runs s0 z0 flush : fill_spec -> ins_spec -> lm_spec -> tally_spec2 -> fbo_spec ->
  forall a b, runs (dsl_body flush) a b -> slow_P s0 z0 flush a -> z_next_in (snd a) <= z_next_in (ss_z (inr b)).
Proof.
  intros Hfill Hins Hlm Htally Hfbo a b Hr. induction Hr as [a b E|a a' b E Hr IH]; intros HP.
  - destruct a as [s z]. exact (ss_body s0 z0 flush s z (inr b) Hfill HP E).
  - destruct a as [s z]. pose proof (ss_body s0 z0 flush s z (inl a') Hfill HP E) as H1.
    destruct (slow_body_ok Hfill Hins Hlm Htally Hfbo s0 z0 flush (s, z) HP) as (_ & r & E' & Hr').
    rewrite E in E'. inversion E'; subst r. destruct Hr' as [HP' _].
    specialize (IH HP'). destruct a' as [s' z']. cbn in *. lia.
Qed.

Lemma ss_first s z s1 z1 flush : d_lookahead s = 0 -> c_fill_window s z = Some (s1, z1) ->
  dsl_body flush (s, z) =
  if (d_lookahead s1 <? MIN_LOOKAHEAD) && (flush =? Z_NO_FLUSH) then Some (inr (s1, z1, Some need_more))
  else if d_lookahead s1 =? 0 then Some (inr (s1, z1, None))
  else dsl_step s1 z1.
Proof.
  intros EL0 Ec. unfold dsl_body, c_refill, need_min_lookahead. rewrite EL0.
  change (0 <? MIN_LOOKAHEAD) with true. cbv iota beta.
  rewrite Ec. cbn [bind].
  destruct ((d_lookahead s1 <? MIN_LOOKAHEAD) && (flush =? Z_NO_FLUSH)); [reflexivity|].
  destruct (d_lookahead s1 =? 0); reflexivity.
Qed.

Lemma ss_fill0 s z flush : fill_spec -> SI s z flush s z [] -> still_at s ->
  exists s1 z1 k, c_fill_window s z = Some (s1, z1) /\ d_strstart s1 = 0 /\ d_match_available s1 = 0 /\
    d_lookahead s1 = k /\ z_next_in z1 = z_next_in z + k /\ 0 <= k.
Proof.
  intros Hfill HI (ES0 & EB0 & EL0).
  destruct (ss_fill_pre s z flush s z [] HI) as (Hfp & Hza & Had).
  pose proof HI as ((HW & _) & _).
  destruct HW as (Hp & _ & _ & _ & _ & Hm & _).
  pose proof (rf_w512 s Hp) as Hw.
  destruct (Hfill s z Hfp Hza Had) as (s1 & z1 & k & d & Ec & _ & Hk & Hz & Hd & ES & _ & _ & _ & EL1 & _).
  pose proof (rf_fw_keep s s1 Hk) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ema & _).
  pose proof Hz as (_ & Hk0 & Hn & _).
  exists s1, z1, k. split; [exact Ec|]. split.
  { rewrite ES, ES0. destruct Hd as [Hd|[Hd Hd2]]; [lia|].
    unfold MAX_DIST, MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *. lia. }
  split.
  { rewrite Ema. destruct Hm as (_ & _ & [M|M] & _ & M5); [exact M|].
    destruct (M5 M) as (_ & M6 & _). lia. }
  split; [lia|]. split; [exact Hn|]. lia.
Qed.

Lemma ss_loop_end s2 z2 o flush s' z' bs :
  match o with
  | Some r => Some (s2, z2, r)
  | None => dsl_end s2 z2 flush
  end = Some (s', z', bs) ->
  z_next_in z' = z_next_in z2 /\
  (o = None -> d_match_available s2 = 0 -> d_strstart s' = d_strstart s2) /\
  (o <> None -> s' = s2).
Proof.
  destruct o as [r|]; intros E.
  - inversion E; subst. split; [reflexivity|]. split; [discriminate|]. intros _. reflexivity.
  - apply ss_end in E. destruct E as [E1 E2]. split; [exact E1|]. split; [intros _; exact E2|].
    intros N; contradiction.
Qed.

Lemma ss_bind_inv {A B : Type} (m : option A) (f : A -> option B) y :
  bind m f = Some y -> exists x, m = Some x /\ f x = Some y.
Proof. destruct m as [x|]; cbn [bind]; [intros H; exists x; split; [reflexivity|exact H]|discriminate]. Qed.

Lemma ss_slow_inv s z flush s' z' bs : c_deflate_slow s z flush = Some (s', z', bs) ->
  exists s2 z2 o, loop FUEL (dsl_body flush) (s, z) = Some (s2, z2, o) /\
    match o with
    | Some r => Some (s2, z2, r)
    | None => dsl_end s2 z2 flush
    end = Some (s', z', bs).
Proof.
  rewrite c_deflate_slow_eq. intros E. apply ss_bind_inv in E. destruct E as ([[s2 z2] o] & E1 & E2).
  exists s2, z2, o. split; [exact E1|exact E2].
Qed.
