(* RT-D part LM, interface v2: INSERT_STRING (ins_fspec2 of RTDFix.v) and longest_match (lm_fspec of
   RTDSpecs.v); kit RTDLmKit.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDFix.
Require Import Zlib.proof.roundtrip.RTDLmKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** INSERT_STRING, with the facts every caller (p = strstart, invariant W) has: wpos, chain_ok, p >= strstart - w_size *)
Lemma ins_fspec2_ok : ins_fspec2.
Proof.
  intros s p s' h Hprm Hws Hwp Hco Hhok [h0 Hpr] Hp Hpl Hp2 Hlim Hrun.
  destruct (prm_w s Hprm) as (Hwr & Hwm & Hwsz & Hwb).
  destruct (prm_h s Hprm) as (Hhs & Hhm & Hhb & Hsh).
  destruct Hws as (Hwl & Hwok & Hwsize & Hprl & Hhl).
  destruct Hwp as (Hla & Hst & Hwin & _).
  unfold c_insert_string in Hrun.
  replace (d_hash_shift s <? 32) with true in Hrun by (symmetry; apply Z.ltb_lt; lia). cbn [guard bind] in Hrun.
  change (p + (MIN_MATCH - 1)) with (p + 2) in Hrun. rewrite u32_id in Hrun by lia.
  destruct (mb_rd (d_window s) (p + 2)) as [c|] eqn:Ec; cbn [bind] in Hrun; [|discriminate].
  apply mb_rd_some in Ec.
  set (hv := update_hash s (d_ins_h s) c) in Hrun.
  autorewrite with dproj in Hrun.
  destruct (rd (d_head s) hv) as [h1|] eqn:Eh; cbn [bind] in Hrun; [|discriminate].
  apply rd_some in Eh. destruct Eh as [Hhv Eh].
  destruct (wr (d_prev s) (Z.land p (d_w_mask s)) h1) as [prev'|] eqn:Ep; cbn [bind] in Hrun; [|discriminate].
  apply wr_some in Ep. destruct Ep as [Hpi Ep].
  autorewrite with dproj in Hrun.
  destruct (wr (d_head s) hv (u16 p)) as [head'|] eqn:Ehd; cbn [bind] in Hrun; [|discriminate].
  apply wr_some in Ehd. destruct Ehd as [_ Ehd].
  inversion Hrun; subst s' h; clear Hrun.
  assert (Ehv : hv = h3 s p).
  { unfold hv, h3. rewrite Hpr, Ec. apply uh3. exact Hprm. }
  rewrite u16_id in Ehd by lia.
  autorewrite with dproj.
  assert (Eh3 : forall q, h3 (set_d_head (set_d_prev (set_d_ins_h s hv) prev') head') q = h3 s q)
    by reflexivity.
  assert (Elim : lim (set_d_head (set_d_prev (set_d_ins_h s hv) prev') head') = lim s) by reflexivity.
  split; [exact Ehv|]. split; [rewrite <- Ehv; exact Eh|].
  split.
  2:{ exists (update_hash s h0 (Znth p (mb_val (d_window s)))). autorewrite with dproj.
      unfold hv. rewrite Hpr, Ec. replace (p + 1 + 1) with (p + 2) by lia. reflexivity. }
  (* chain_hok *)
  destruct Hco as (G & Hg1 & Hg2 & Hg3).
  set (pi := Z.land p (d_w_mask s)) in *.
  assert (Kslot : forall q, G q -> 0 < q -> lim s <= q -> Z.land q (d_w_mask s) = pi -> q = p).
  { intros q Gq Hq0 Hql Eq. destruct (Hg1 q Gq) as [|Hqs]; [lia|].
    unfold pi in Eq. rewrite Hwm in Eq.
    replace (2 ^ d_w_bits s - 1) with (Z.ones (d_w_bits s)) in Eq by (rewrite Z.ones_equiv; lia).
    rewrite !Z.land_ones in Eq by lia. rewrite <- Hwsz in Eq.
    assert (Hlq : p - d_w_size s < q) by lia.
    pose proof (Z.div_mod q (d_w_size s) ltac:(lia)). pose proof (Z.div_mod p (d_w_size s) ltac:(lia)).
    set (W := d_w_size s) in *. set (k := q / W - p / W).
    assert (Hk : W * k = q - p) by (unfold k; lia).
    assert (k = 0).
    { destruct (Z.lt_trichotomy k 0) as [Hk0|[Hk0|Hk0]]; [|exact Hk0|]; exfalso.
      - assert (W * k <= W * (-1)) by (apply Z.mul_le_mono_nonneg_l; lia). lia.
      - assert (W * 1 <= W * k) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
    lia. }
  intros b Hb. autorewrite with dproj in Hb. destruct (Hhok b Hb) as (Gb & Gb0 & Gb1).
  exists (fun v => (v = p /\ h3 s p = b) \/ (Gb v /\ G v)).
  split.
  { autorewrite with dproj. rewrite Ehd. destruct (Z.eq_dec b hv) as [->|E].
    - rewrite upd_Znth_same by lia. left. auto.
    - rewrite upd_Znth_diff by lia. right. split; [exact Gb0|apply Hg2; lia]. }
  intros q Hq Hq0 Hql. rewrite Eh3. rewrite Elim in Hql. autorewrite with dproj. rewrite Ep.
  destruct Hq as [[-> Eb]|[Gq GGq]].
  - split; [lia|]. split; [exact Eb|].
    fold pi. rewrite upd_Znth_same by lia. right. rewrite Eh.
    assert (b = hv) by congruence. subst b.
      split; [first [exact Gb0 | rewrite Ehv; exact Gb0 | rewrite <- Ehv in Gb0; exact Gb0]|apply Hg2; lia].
  - destruct (Gb1 q Gq Hq0 Hql) as (Hq2 & Ehq & Gbn).
    split; [exact Hq2|]. split; [exact Ehq|].
    assert (Hqm : 0 <= Z.land q (d_w_mask s) < d_w_size s)
      by (rewrite Hwm, Hwsz; apply land_mask_range; lia).
    destruct (Z.eq_dec (Z.land q (d_w_mask s)) pi) as [E|E].
    + pose proof (Kslot q GGq Hq0 Hql E) as ->. rewrite E, upd_Znth_same by lia. right. rewrite Eh.
      assert (b = hv) by congruence. subst b.
      split; [first [exact Gb0 | rewrite Ehv; exact Gb0 | rewrite <- Ehv in Gb0; exact Gb0]|apply Hg2; lia].
    + rewrite upd_Znth_diff by lia. right. split; [exact Gbn|apply Hg3; auto].
Qed.

(** ** longest_match *)

(** the inner comparison loop: bytes 3 .. sc - st - 1 of the candidate equal those of the string at st *)
Lemma cmp_inv s0 st cur sc :
  loop FUEL (lm_cmp_body s0 (st + MAX_MATCH)) (st + 2, cur + 2, 0) = Some sc ->
  st + 3 <= sc /\ forall j, 3 <= j < sc - st ->
    Znth (cur + j) (mb_val (d_window s0)) = Znth (st + j) (mb_val (d_window s0)).
Proof.
  set (w := mb_val (d_window s0)).
  apply (loop_inv _
    (fun a => let '(scan, mt, k) := a in
       mt - scan = cur - st /\ st + 2 <= scan /\
       forall j, 3 <= j <= scan - st -> Znth (cur + j) w = Znth (st + j) w)
    (fun sc => st + 3 <= sc /\ forall j, 3 <= j < sc - st -> Znth (cur + j) w = Znth (st + j) w)).
  - intros [[scan mt] k] a' (H1 & H2 & H3) E. unfold lm_cmp_body in E.
    destruct (mb_rd (d_window s0) (scan + 1)) as [c1|] eqn:E1; cbn [bind] in E; [|discriminate].
    destruct (mb_rd (d_window s0) (mt + 1)) as [c2|] eqn:E2; cbn [bind] in E; [|discriminate].
    apply mb_rd_some in E1, E2. fold w in E1, E2.
    destruct (Z.eqb_spec c1 c2) as [Ec|Ec]; cbn [negb] in E; [|discriminate].
    assert (Hn : forall j, 3 <= j <= scan + 1 - st -> Znth (cur + j) w = Znth (st + j) w).
    { intros j Hj. destruct (Z.eq_dec j (scan + 1 - st)) as [->|Hne]; [|apply H3; lia].
      replace (cur + (scan + 1 - st)) with (mt + 1) by lia. replace (st + (scan + 1 - st)) with (scan + 1) by lia.
      congruence. }
    destruct (k =? 7); [destruct (scan + 1 <? st + MAX_MATCH)|]; inversion E; subst;
      (split; [lia|split; [lia|]]); intros j Hj; apply Hn; lia.
  - intros [[scan mt] k] r (H1 & H2 & H3) E. unfold lm_cmp_body in E.
    destruct (mb_rd (d_window s0) (scan + 1)) as [c1|] eqn:E1; cbn [bind] in E; [|discriminate].
    destruct (mb_rd (d_window s0) (mt + 1)) as [c2|] eqn:E2; cbn [bind] in E; [|discriminate].
    destruct (negb (c1 =? c2)); [|destruct (k =? 7); [destruct (scan + 1 <? st + MAX_MATCH)|]];
      inversion E; subst; (split; [lia|]); intros j Hj; apply H3; lia.
  - cbn. split; [lia|]. split; [lia|]. intros; lia.
Qed.

Lemma bind_some {A B : Type} (o : option A) (f : A -> option B) r :
  bind o f = Some r -> exists x, o = Some x /\ f x = Some r.
Proof. destruct o as [x|]; cbn; [eauto|discriminate]. Qed.

Lemma lim_nonneg' s : 0 <= lim s.
Proof. unfold lim. destruct (Z.gtb_spec (d_strstart s) (MAX_DIST s)); lia. Qed.

Section LMF.
Variables (s : dstate) (G : Z -> Prop).
Hypotheses (Hprm : prm s) (Hws : wstruct s) (Hwp : wpos s) (Hww : wwin s) (Hla : MIN_MATCH <= d_lookahead s)
  (HGc : forall q, G q -> 0 < q -> lim s <= q ->
     q + 2 < d_strstart s + d_lookahead s /\ h3 s q = h3 s (d_strstart s) /\
     G (Znth (Z.land q (d_w_mask s)) (d_prev s))).

Definition meq (ms n : Z) : Prop := forall i, 0 <= i < n ->
  Znth (ms + i) (mb_val (d_window s)) = Znth (d_strstart s + i) (mb_val (d_window s)).

Definition LPf (a : lm_st) : Prop := exists ms,
  lm_s a = set_d_match_start s ms /\ (d_prev_length s < lm_best a -> meq ms (lm_best a)) /\
  G (lm_cur a) /\ 0 < lm_cur a /\ lim s <= lm_cur a.

Definition LQf (r : Z * dstate) : Prop := exists ms,
  snd r = set_d_match_start s ms /\ (d_prev_length s < fst r -> meq ms (fst r)).

Definition LR (r : lm_st + (Z * dstate)) : Prop := match r with inl a => LPf a | inr q => LQf q end.

Lemma next_inv a r : LPf a -> lm_next (lim s) a = Some r -> LR r.
Proof.
  destruct a as [cur chain best e1 e s0].
  intros (ms & Hs0 & Hm & HG & Hc0 & Hcl) E. cbn [lm_s lm_cur lm_best lm_chain] in *. subst s0.
  unfold lm_next in E. cbn [lm_s lm_cur lm_chain lm_best lm_end1 lm_end] in E. autorewrite with dproj in E.
  destruct (rd (d_prev s) (Z.land cur (d_w_mask s))) as [cur'|] eqn:Er; cbn [bind] in E; [|discriminate].
  apply rd_some in Er. destruct Er as [_ Er].
  pose proof (lim_nonneg' s).
  destruct (Z.gtb_spec cur' (lim s)) as [Hgt|Hle].
  - destruct (u32 (chain - 1) =? 0); inversion E; subst; cbn [LR].
    + exists ms. cbn [fst snd]. auto.
    + exists ms. cbn [lm_s lm_cur lm_best]. split; [reflexivity|]. split; [exact Hm|].
      destruct (HGc cur HG Hc0 Hcl) as (_ & _ & Gn). split; [exact Gn|lia].
  - inversion E; subst. exists ms. cbn [fst snd]. auto.
Qed.

(** a candidate whose bytes 0, 1 and 3 .. sc - st - 1 match: all its bytes below sc - st match (byte 2 by the
    hash) *)
Lemma cand_meq cur sc :
  let w := mb_val (d_window s) in let st := d_strstart s in
  G cur -> 0 < cur -> lim s <= cur ->
  Znth cur w = Znth st w -> Znth (cur + 1) w = Znth (st + 1) w ->
  (forall j, 3 <= j < sc - st -> Znth (cur + j) w = Znth (st + j) w) ->
  meq cur (sc - st).
Proof.
  intros w st HG Hc0 Hcl E0 E1 E3 i Hi.
  destruct (HGc cur HG Hc0 Hcl) as (Hc2 & Eh & _).
  destruct Hws as (Hwl & (Hdl & Hok) & Hwsize & _).
  destruct Hwp as (Hla0 & Hst & Hwin & _).
  assert (Hb : forall k, 0 <= k < d_strstart s + d_lookahead s -> 0 <= Znth k w < 256).
  { intros k Hk. apply Hok; [unfold w; lia|]. apply Hww. lia. }
  unfold MIN_MATCH in Hla.
  destruct (Z.eq_dec i 0) as [->|]; [rewrite !Z.add_0_r; exact E0|].
  destruct (Z.eq_dec i 1) as [->|]; [exact E1|].
  destruct (Z.eq_dec i 2) as [->|]; [|apply E3; lia].
  apply (uh_third s Hprm (Znth st w) (Znth (st + 1) w)); [apply Hb; lia|apply Hb; unfold st; lia|].
  unfold h3 in Eh. fold w st in Eh. rewrite E0, E1 in Eh. exact Eh.
Qed.

Lemma body_inv nice a r : LPf a -> lm_body nice (lim s) a = Some r -> LR r.
Proof.
  intros HP E. pose proof HP as (ms & Hs0 & Hm & HG & Hc0 & Hcl).
  destruct a as [cur chain best e1 e s0]. cbn [lm_s lm_cur lm_best lm_chain] in *. subst s0.
  rewrite lm_body_eq in E. autorewrite with dproj in E.
  destruct (mb_rd (d_window s) (cur + best)) as [m0|] eqn:E0; cbn [bind] in E; [|discriminate].
  destruct (negb (m0 =? e)); [exact (next_inv _ _ HP E)|].
  destruct (mb_rd (d_window s) (cur + best - 1)) as [m1|] eqn:E1; cbn [bind] in E; [|discriminate].
  destruct (negb (m1 =? e1)); [exact (next_inv _ _ HP E)|].
  destruct (mb_rd (d_window s) cur) as [m2|] eqn:E2; cbn [bind] in E; [|discriminate].
  destruct (mb_rd (d_window s) (d_strstart s)) as [c0|] eqn:E2'; cbn [bind] in E; [|discriminate].
  (* destruct the test itself: [cbn [negb]] would leave a conversion the kernel checks by running the loop *)
  destruct (negb (m2 =? c0)) eqn:Ec0; [exact (next_inv _ _ HP E)|].
  apply negb_false_iff, Z.eqb_eq in Ec0.
  destruct (mb_rd (d_window s) (cur + 1)) as [m3|] eqn:E3; cbn [bind] in E; [|discriminate].
  destruct (mb_rd (d_window s) (d_strstart s + 1)) as [c1|] eqn:E3'; cbn [bind] in E; [|discriminate].
  destruct (negb (m3 =? c1)) eqn:Ec1; [exact (next_inv _ _ HP E)|].
  apply negb_false_iff, Z.eqb_eq in Ec1.
  apply mb_rd_some in E2, E2', E3, E3'.
  (* no destruct of the loop term: its dependent match makes the kernel unfold the loop at Qed *)
  apply bind_some in E. destruct E as (sc & Esc & E). cbn beta in E.
  apply cmp_inv in Esc. autorewrite with dproj in Esc. destruct Esc as [Hsc Heq].
  set (st := d_strstart s) in *.
  assert (Hmq : meq cur (sc - st)).
  { apply cand_meq; [exact HG|exact Hc0|exact Hcl|rewrite <- E2, Ec0, E2'; reflexivity
    |rewrite <- E3, Ec1, E3'; reflexivity|exact Heq]. }
  assert (Elen : MAX_MATCH - (st + MAX_MATCH - sc) = sc - st) by lia.
  rewrite Elen in E.
  destruct (Z.gtb_spec (sc - st) best) as [Hgt|Hle].
  - rewrite set_ms_ms in E. destruct (Z.geb_spec (sc - st) nice) as [Hge|Hlt].
    + inversion E; subst. exists cur. cbn [fst snd]. split; [reflexivity|]. intros _; exact Hmq.
    + autorewrite with dproj in E.
      destruct (mb_rd (d_window s) (st + (sc - st) - 1)) as [x1|]; cbn [bind] in E; [|discriminate].
      destruct (mb_rd (d_window s) (st + (sc - st))) as [x|]; cbn [bind] in E; [|discriminate].
      refine (next_inv (mkLM cur chain (sc - st) x1 x (set_d_match_start s cur)) r _ E).
      exists cur. cbn [lm_s lm_cur lm_best]. split; [reflexivity|]. split; [intros _; exact Hmq|]. auto.
  - exact (next_inv _ _ HP E).
Qed.
End LMF.

Lemma lm_fspec_ok : lm_fspec.
Proof.
  intros s cur s' ml G Hprm Hws Hwp Hww Hco Hla Hpl Hc0 Hcl Hcs HG HGc Hrun Hlt.
  destruct (prm_w s Hprm) as (Hwr & Hwm & Hwsz & Hwb).
  unfold c_longest_match in Hrun. cbv zeta in Hrun.
  (* peel each [let*] with [bind_some]: [cbn [bind]] would leave conversions the kernel checks by running the loop *)
  do 3 (apply bind_some in Hrun; destruct Hrun as (? & _ & Hrun); cbv beta in Hrun).
  replace (if d_strstart s >? u32 (d_w_size s - MIN_LOOKAHEAD)
           then u32 (d_strstart s - u32 (d_w_size s - MIN_LOOKAHEAD)) else NIL) with (lim s) in Hrun.
  2:{ pose proof Hws as (_ & _ & Hwsize & _). pose proof Hwp as (Hla0 & Hst & Hwin & _).
      unfold lim, MAX_DIST. change MIN_LOOKAHEAD with 262. rewrite (u32_id (d_w_size s - 262)) by lia.
      destruct (Z.gtb_spec (d_strstart s) (d_w_size s - 262)); [|reflexivity].
      rewrite u32_id by lia. reflexivity. }
  do 2 (apply bind_some in Hrun; destruct Hrun as (? & _ & Hrun); cbv beta in Hrun).
  apply bind_some in Hrun. destruct Hrun as ([best s0] & EL & Hrun). cbv beta iota in Hrun.
  match type of EL with loop FUEL (lm_body ?nc (lim s)) ?a0 = _ =>
    assert (Hq : LQf s (best, s0));
    [apply (loop_inv _ (LPf s G) (LQf s)
              (fun a a' Ha E => body_inv s G Hprm Hws Hwp Hww Hla HGc nc a (inl a') Ha E)
              (fun a r Ha E => body_inv s G Hprm Hws Hwp Hww Hla HGc nc a (inr r) Ha E) FUEL a0); [|exact EL]
    |] end.
  { exists (d_match_start s). cbn [lm_s lm_cur lm_best]. split; [destruct s; reflexivity|].
    split; [intros; lia|]. auto. }
  injection Hrun as <- <-. destruct Hq as (ms & Hs0 & Hm). cbn [fst snd] in Hs0, Hm. subst s0.
  autorewrite with dproj in Hlt.
  autorewrite with dproj. intros i Hi.
  destruct (Z.leb_spec best (d_lookahead s)); apply Hm; lia.
Qed.

Theorem rtd_lm_ok2 : ins_fspec2 /\ lm_fspec.
Proof. split; [exact ins_fspec2_ok | exact lm_fspec_ok]. Qed.
