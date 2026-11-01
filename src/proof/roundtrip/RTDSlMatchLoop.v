(* RT-D part SLOW, part MATCH: the insertion loop of deflate_slow's match branch, functionally.
   The loop (dsl_insert_body max_insert) runs with lookahead already decreased by prev_length - 1, so the loop
   states do not satisfy [p + 2 < strstart + lookahead]; the hash-chain facts are stated with the true end of
   the data S = strstart + lookahead before the branch ([chain_hokS s S]). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDSlowKit.
Require Export Zlib.proof.roundtrip.RTDLTCSlowMatch.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(* chain_hok with the end of the data S in place of strstart + lookahead *)
Definition chain_hokS (s : dstate) (S : Z) : Prop :=
  forall b, 0 <= b < d_hash_size s ->
  exists Gb : Z -> Prop,
    Gb (Znth b (d_head s)) /\
    forall q, Gb q -> 0 < q -> lim s <= q ->
      q + 2 < S /\ h3 s q = b /\ Gb (Znth (Z.land q (d_w_mask s)) (d_prev s)).

Lemma chain_hokS_iff s : chain_hok s <-> chain_hokS s (d_strstart s + d_lookahead s).
Proof. unfold chain_hok, chain_hokS. tauto. Qed.

(* INSERT_STRING does not read lookahead *)
Lemma ins_string_la x L p :
  c_insert_string (set_d_lookahead x L) p =
  option_map (fun r => (set_d_lookahead (fst r) L, snd r)) (c_insert_string x p).
Proof.
  unfold c_insert_string.
  change (d_hash_shift (set_d_lookahead x L)) with (d_hash_shift x).
  destruct (guard (d_hash_shift x <? 32)) as [[]|]; [|reflexivity]. cbn [bind].
  change (d_window (set_d_lookahead x L)) with (d_window x).
  destruct (mb_rd (d_window x) (u32 (p + (MIN_MATCH - 1)))) as [c|]; [|reflexivity]. cbn [bind].
  change (update_hash (set_d_lookahead x L) (d_ins_h (set_d_lookahead x L)) c) with (update_hash x (d_ins_h x) c).
  change (d_head (set_d_ins_h (set_d_lookahead x L) (update_hash x (d_ins_h x) c))) with (d_head x).
  change (d_head (set_d_ins_h x (update_hash x (d_ins_h x) c))) with (d_head x).
  change (d_ins_h (set_d_ins_h (set_d_lookahead x L) (update_hash x (d_ins_h x) c))) with (update_hash x (d_ins_h x) c).
  change (d_ins_h (set_d_ins_h x (update_hash x (d_ins_h x) c))) with (update_hash x (d_ins_h x) c).
  destruct (rd (d_head x) (update_hash x (d_ins_h x) c)) as [h|]; [|reflexivity]. cbn [bind].
  change (d_prev (set_d_ins_h (set_d_lookahead x L) (update_hash x (d_ins_h x) c))) with (d_prev x).
  change (d_prev (set_d_ins_h x (update_hash x (d_ins_h x) c))) with (d_prev x).
  change (d_w_mask (set_d_ins_h (set_d_lookahead x L) (update_hash x (d_ins_h x) c))) with (d_w_mask x).
  change (d_w_mask (set_d_ins_h x (update_hash x (d_ins_h x) c))) with (d_w_mask x).
  destruct (wr (d_prev x) (Z.land p (d_w_mask x)) h) as [pv|]; [|reflexivity]. cbn [bind].
  change (d_head (set_d_prev (set_d_ins_h (set_d_lookahead x L) (update_hash x (d_ins_h x) c)) pv)) with (d_head x).
  change (d_head (set_d_prev (set_d_ins_h x (update_hash x (d_ins_h x) c)) pv)) with (d_head x).
  change (d_ins_h (set_d_prev (set_d_ins_h (set_d_lookahead x L) (update_hash x (d_ins_h x) c)) pv)) with (update_hash x (d_ins_h x) c).
  change (d_ins_h (set_d_prev (set_d_ins_h x (update_hash x (d_ins_h x) c)) pv)) with (update_hash x (d_ins_h x) c).
  destruct (wr (d_head x) (update_hash x (d_ins_h x) c) (u16 p)) as [hd|]; [|reflexivity].
  reflexivity.
Qed.

(* one step of the loop, the safety part (the step of RTDLTCSlowMatch.ins_loop_ok) *)
Lemma il_step : ins_spec -> forall b mi l,
  prm b -> 1 <= d_prev_length b -> 0 <= d_strstart b -> d_strstart b + d_prev_length b < 65536 ->
  (forall p, d_strstart b < p <= mi -> p <= d_strstart b + d_prev_length b ->
     p + 2 < Zlength (mb_val (d_window b)) /\ Znth (p + 2) (mb_def (d_window b)) = true /\ p - d_w_size b < l) ->
  forall a, il_P b l a -> 0 <= d_prev_length a /\ exists r, dsl_insert_body mi a = Some r /\
     match r with inl a' => il_P b l a' /\ d_prev_length a' < d_prev_length a | inr c => il_Q b l c end.
Proof.
  intros Hins b mi l Hp H1 H0 H2 Hwin.
  intros a (Hk & Ha1 & Ha2 & Ha3 & Hwa & Ga & Hcha).
  split; [lia|].
  assert (Hpa : prm (ins_keep a)) by (rewrite Hk; exact Hp).
  assert (Ew : d_window a = d_window b) by exact (f_equal d_window Hk).
  assert (Ewz : d_w_size a = d_w_size b) by exact (f_equal d_w_size Hk).
  assert (Hwpos : 0 < d_w_size b) by (destruct Hp as (Hwb & Hw & _); rewrite Hw; apply Z.pow_pos_nonneg; lia).
  unfold dsl_insert_body.
  rewrite (u32_small (d_strstart a + 1)) by lia.
  cbv zeta.
  change (d_strstart (set_d_strstart a (d_strstart a + 1))) with (d_strstart a + 1).
  destruct (Z.leb_spec (d_strstart a + 1) mi) as [Hle|Hgt].
  - destruct (Hwin (d_strstart a + 1) ltac:(lia) ltac:(lia)) as (W1 & W2 & W3).
    destruct (Hins (set_d_strstart a (d_strstart a + 1)) (d_strstart a + 1) (d_strstart a + 1) l Ga
      Hpa Hwa Hcha ltac:(lia) ltac:(cbn [d_window set_d_strstart]; rewrite Ew; exact W1)
      ltac:(cbn [d_window set_d_strstart]; rewrite Ew; exact W2) ltac:(cbn [d_w_size set_d_strstart]; lia)
      ltac:(cbn [d_w_size set_d_strstart]; rewrite Ewz; exact W3))
      as (s' & h & Ei & Hhk & Hws' & HGh & Hch' & Hcl).
    rewrite Ei. cbn [bind].
    assert (Epl : d_prev_length s' = d_prev_length a) by exact (f_equal d_prev_length Hhk).
    assert (Est : d_strstart s' = d_strstart a + 1) by exact (f_equal d_strstart Hhk).
    rewrite Epl, (u32_small (d_prev_length a - 1)) by lia.
    change (d_prev_length (set_d_prev_length s' (d_prev_length a - 1))) with (d_prev_length a - 1).
    assert (Hk' : ins_keep (set_d_prev_length s' (d_prev_length a - 1)) = ins_keep b).
    { change (ins_keep (set_d_prev_length s' (d_prev_length a - 1))) with (ins_keep (hc_keep s')).
      rewrite Hhk. exact Hk. }
    rewrite Z.max_r in Hch' by lia.
    destruct (Z.eqb_spec (d_prev_length a - 1) 0) as [E0|E0].
    + eexists; split; [reflexivity|].
      split; [exact Hk'|]. cbn [d_strstart d_prev_length set_d_prev_length]. split; [lia|]. split; [lia|].
      split; [exact Hws'|]. exists (fun v => Ga v \/ v = d_strstart a + 1). rewrite Est. exact Hch'.
    + eexists; split; [reflexivity|]. cbn [d_prev_length set_d_prev_length].
      split; [split; [exact Hk'|]; cbn [d_strstart d_prev_length set_d_prev_length]; split; [lia|]; split; [lia|]; split; [lia|];
        split; [exact Hws'|]; exists (fun v => Ga v \/ v = d_strstart a + 1); rewrite Est; exact Hch'|].
      lia.
  - cbn [bind].
    rewrite (u32_small (d_prev_length (set_d_strstart a (d_strstart a + 1)) - 1)) by (cbn [d_prev_length set_d_strstart]; lia).
    assert (Hk' : ins_keep (set_d_prev_length (set_d_strstart a (d_strstart a + 1)) (d_prev_length (set_d_strstart a (d_strstart a + 1)) - 1)) = ins_keep b) by exact Hk.
    change (d_prev_length (set_d_strstart a (d_strstart a + 1))) with (d_prev_length a) in *.
    change (d_prev_length (set_d_prev_length (set_d_strstart a (d_strstart a + 1)) (d_prev_length a - 1))) with (d_prev_length a - 1).
    assert (Hch2 : chain_with (set_d_prev_length (set_d_strstart a (d_strstart a + 1)) (d_prev_length a - 1)) (d_strstart a + 1 + 1) l Ga)
      by (apply (chain_with_mono _ _ _ _ _ _ Hcha); lia).
    destruct (Z.eqb_spec (d_prev_length a - 1) 0) as [E0|E0].
    + eexists; split; [reflexivity|].
      split; [exact Hk'|]. cbn [d_strstart d_prev_length set_d_prev_length set_d_strstart]. split; [lia|]. split; [lia|].
      split; [exact Hwa|]. exists Ga. exact Hch2.
    + eexists; split; [reflexivity|]. cbn [d_prev_length set_d_prev_length].
      split; [split; [exact Hk'|]; cbn [d_strstart d_prev_length set_d_prev_length set_d_strstart]; split; [lia|]; split; [lia|]; split; [lia|];
        split; [exact Hwa|]; exists Ga; exact Hch2|].
      lia.
Qed.

(* the functional part of the loop invariant *)
Definition il_X (mi S : Z) (a : dstate) : Prop :=
  chain_hokS a S /\ (d_strstart a + 1 <= mi -> primed a (d_strstart a + 1)).

Lemma il_X_step : ins_spec -> ins_fspec2 -> forall b mi l S,
  prm b -> 1 <= d_prev_length b -> 0 <= d_strstart b -> d_strstart b + d_prev_length b < 65536 ->
  (forall p, d_strstart b < p <= mi -> p <= d_strstart b + d_prev_length b ->
     p + 2 < Zlength (mb_val (d_window b)) /\ Znth (p + 2) (mb_def (d_window b)) = true /\ p - d_w_size b < l) ->
  l <= lim b -> mi <= S - 3 ->
  (forall p, d_strstart b <= p <= d_strstart b + d_prev_length b ->
     wpos (set_d_lookahead (set_d_strstart b p) (S - p))) ->
  forall a r, il_P b l a -> il_X mi S a -> dsl_insert_body mi a = Some r ->
  il_X mi S (match r with inl x => x | inr x => x end).
Proof.
  intros Hins Hf2 b mi l S Hp H1 H0 H2 Hwin Hl HS Hwp a r (Hk & Ha1 & Ha2 & Ha3 & Hwa & Ga & Hcha) (Hhk & Hpr) Hr.
  assert (Hpa : prm (ins_keep a)) by (rewrite Hk; exact Hp).
  assert (Ew : d_window a = d_window b) by exact (f_equal d_window Hk).
  assert (Ewz : d_w_size a = d_w_size b) by exact (f_equal d_w_size Hk).
  assert (Hwpos : 0 < d_w_size b) by (destruct Hp as (Hwb & Hw & _); rewrite Hw; apply Z.pow_pos_nonneg; lia).
  assert (Hlab : lim b <= lim a) by (apply lim_mono; [exact Ewz|exact Ha3]).
  unfold dsl_insert_body in Hr.
  rewrite (u32_small (d_strstart a + 1)) in Hr by lia.
  cbv zeta in Hr.
  change (d_strstart (set_d_strstart a (d_strstart a + 1))) with (d_strstart a + 1) in Hr.
  assert (Hla1 : lim a <= lim (set_d_strstart a (d_strstart a + 1)))
    by (apply lim_mono; [reflexivity|cbn [d_strstart set_d_strstart]; lia]).
  destruct (Z.leb_spec (d_strstart a + 1) mi) as [Hle|Hgt].
  - destruct (Hwin (d_strstart a + 1) ltac:(lia) ltac:(lia)) as (W1 & W2 & W3).
    destruct (Hins (set_d_strstart a (d_strstart a + 1)) (d_strstart a + 1) (d_strstart a + 1) l Ga
      Hpa Hwa Hcha ltac:(lia) ltac:(cbn [d_window set_d_strstart]; rewrite Ew; exact W1)
      ltac:(cbn [d_window set_d_strstart]; rewrite Ew; exact W2) ltac:(cbn [d_w_size set_d_strstart]; lia)
      ltac:(cbn [d_w_size set_d_strstart]; rewrite Ewz; exact W3))
      as (s' & h & Ei & Hhk' & Hws' & HGh & Hch' & Hcl).
    rewrite Ei in Hr. cbn [bind] in Hr.
    assert (Er : (match r with inl x => x | inr x => x end) = set_d_prev_length s' (u32 (d_prev_length s' - 1))).
    { destruct (_ =? 0) in Hr; injection Hr as <-; reflexivity. }
    rewrite Er. clear Er Hr.
    assert (Est : d_strstart s' = d_strstart a + 1) by exact (f_equal d_strstart Hhk').
    assert (Ewz' : d_w_size s' = d_w_size a) by exact (f_equal d_w_size Hhk').
    remember (d_strstart a + 1) as p eqn:Hpdef.
    set (v := set_d_lookahead (set_d_strstart a p) (S - p)).
    assert (Ev : c_insert_string v p = Some (set_d_lookahead s' (S - p), h))
      by (unfold v; rewrite ins_string_la, Ei; reflexivity).
    assert (Hlv : lim v = lim (set_d_strstart a p)) by reflexivity.
    assert (Hwv : wpos v).
    { pose proof (Hwp p ltac:(lia)) as Hw0.
      assert (E1 : d_window_size a = d_window_size b) by exact (f_equal d_window_size Hk).
      assert (E2 : d_block_start a = d_block_start b) by exact (f_equal d_block_start Hk).
      assert (E3 : d_insert a = d_insert b) by exact (f_equal d_insert Hk).
      assert (E4 : d_high_water a = d_high_water b) by exact (f_equal d_high_water Hk).
      unfold v, wpos, MAX_DIST in *. dsimp_in Hw0. dsimp. rewrite E1, E2, E3, E4, Ewz. exact Hw0. }
    destruct (Hf2 v p (set_d_lookahead s' (S - p)) h Hpa Hwa Hwv) as (_ & _ & Hhok' & Hpr').
    + exists Ga. apply (chain_with_mono v _ _ _ _ _ Hcha); [unfold v; dsimp; lia|].
      rewrite Hlv. lia.
    + intros bb Hbb. destruct (Hhk bb Hbb) as (Gb & G1 & G2). exists Gb. split; [exact G1|].
      intros q Hq Hq0 Hql. destruct (G2 q Hq Hq0 ltac:(rewrite Hlv in Hql; lia)) as (A1 & A2 & A3).
      split; [unfold v; dsimp; lia|]. split; [exact A2|exact A3].
    + exact (Hpr Hle).
    + unfold v; dsimp; lia.
    + unfold v; dsimp; lia.
    + unfold v; dsimp; lia.
    + rewrite Hlv. unfold v; dsimp. rewrite Ewz. lia.
    + exact Ev.
    + split.
      * intros bb Hbb. destruct (Hhok' bb Hbb) as (Gb & G1 & G2). exists Gb. split; [exact G1|].
        intros q Hq Hq0 Hql. destruct (G2 q Hq Hq0 Hql) as (A1 & A2 & A3).
        split; [dsimp_in A1; lia|]. split; [exact A2|exact A3].
      * intros _. change (d_strstart (set_d_prev_length s' (u32 (d_prev_length s' - 1)))) with (d_strstart s').
        rewrite Est. exact Hpr'.
  - cbn [bind] in Hr.
    assert (Er : (match r with inl x => x | inr x => x end) =
      set_d_prev_length (set_d_strstart a (d_strstart a + 1))
        (u32 (d_prev_length (set_d_strstart a (d_strstart a + 1)) - 1))).
    { destruct (_ =? 0) in Hr; injection Hr as <-; reflexivity. }
    rewrite Er. clear Er Hr. split.
    + intros bb Hbb. destruct (Hhk bb Hbb) as (Gb & G1 & G2). exists Gb. split; [exact G1|].
      intros q Hq Hq0 Hql. apply (G2 q Hq Hq0). change (lim (set_d_strstart a (d_strstart a + 1)) <= q) in Hql. lia.
    + dsimp. lia.
Qed.

(* The insertion loop (the safety version: RTDLTCSlowMatch.ins_loop_ok, same hypotheses up to [Hwin]):
   INSERT_STRING of strstart + 1 .. while <= mi keeps the chains hash-consistent (for the data end S) and ins_h
   primed for the next position, by ins_fspec2 applied at each position p to the loop state with strstart p and
   the true lookahead S - p (c_insert_string does not read lookahead). *)
Lemma ins_loop_fok : ins_spec -> ins_fspec2 -> forall b mi l G S a,
  prm b -> wstruct b -> chain_with b (d_strstart b + 1) l G ->
  1 <= d_prev_length b -> 0 <= d_strstart b -> d_strstart b + d_prev_length b < 65536 ->
  (forall p, d_strstart b < p <= mi -> p <= d_strstart b + d_prev_length b ->
     p + 2 < Zlength (mb_val (d_window b)) /\ Znth (p + 2) (mb_def (d_window b)) = true /\ p - d_w_size b < l) ->
  l <= lim b -> mi <= S - 3 ->
  (forall p, d_strstart b <= p <= d_strstart b + d_prev_length b ->
     wpos (set_d_lookahead (set_d_strstart b p) (S - p))) ->
  chain_hokS b S ->
  (d_strstart b + 1 <= mi -> primed b (d_strstart b + 1)) ->
  loop FUEL (dsl_insert_body mi) b = Some a ->
  chain_hokS a S /\ (d_strstart a + 1 <= mi -> primed a (d_strstart a + 1)).
Proof.
  intros Hins Hf2 b mi l G S a Hp Hws Hch H1 H0 H2 Hwin Hl HS Hwp Hhk Hpr Hloop.
  destruct (mloop_measure (dsl_insert_body mi) (fun x => il_P b l x /\ il_X mi S x)
              (fun x => il_Q b l x /\ il_X mi S x) d_prev_length) with b as (c & Ec & _ & HX).
  - intros x (HPx & HXx).
    destruct (il_step Hins b mi l Hp H1 H0 H2 Hwin x HPx) as (Hm & r & Er & Hr).
    split; [exact Hm|]. exists r. split; [exact Er|].
    pose proof (il_X_step Hins Hf2 b mi l S Hp H1 H0 H2 Hwin Hl HS Hwp x r HPx HXx Er) as HX'.
    destruct r as [x'|c].
    + destruct Hr as [Hr1 Hr2]. split; [split; assumption|exact Hr2].
    + split; assumption.
  - split.
    + split; [reflexivity|]. split; [exact H1|]. split; [reflexivity|]. split; [lia|].
      split; [exact Hws|]. exists G. exact Hch.
    + split; assumption.
  - lia.
  - rewrite Hloop in Ec. injection Ec as <-. exact HX.
Qed.
