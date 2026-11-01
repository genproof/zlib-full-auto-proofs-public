(* RT-D part DICT: deflateSetDictionary's insertion loop keeps the chains hash-consistent.
   sd_insert_body inserts the positions str .. str + nn - 1 while strstart stays below them: [shf x p e] is the state
   seen with strstart = p (lookahead e - p, so strstart + lookahead = e), on which INSERT_STRING(p) is ins_fspec2's. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDV2.
Require Import Zlib.proof.roundtrip.RTDLTCDictKit Zlib.proof.roundtrip.RTDLTCDictFrame Zlib.proof.roundtrip.RTDLTCDictIns.
Require Import Zlib.proof.roundtrip.RTDLTCDictProj Zlib.proof.roundtrip.RTDLTCDict.
Import ListNotations.
Local Open Scope Z_scope.

Definition shf (x : dstate) (p e : Z) : dstate := set_d_lookahead (set_d_strstart x p) (e - p).

(* chain_hok only depends on head, prev, the window, the hash parameters, strstart + lookahead and lim *)
Lemma chain_hok_mono : forall x y,
  chain_hok x -> d_head y = d_head x -> d_prev y = d_prev x -> d_window y = d_window x ->
  d_hash_size y = d_hash_size x -> d_hash_shift y = d_hash_shift x -> d_hash_mask y = d_hash_mask x ->
  d_w_mask y = d_w_mask x -> d_w_size y = d_w_size x ->
  d_strstart y + d_lookahead y = d_strstart x + d_lookahead x -> d_strstart x <= d_strstart y ->
  chain_hok y.
Proof.
  intros x y Hc Ehd Epv Ewin Ehs Esh Ehm Ewm Ews Esl Ess b Hb.
  rewrite Ehs in Hb. destruct (Hc b Hb) as (Gb & G0 & G1).
  assert (Hlim : lim x <= lim y).
  { unfold lim, MAX_DIST. rewrite Ews.
    destruct (Z.gtb_spec (d_strstart x) (d_w_size x - MIN_LOOKAHEAD));
    destruct (Z.gtb_spec (d_strstart y) (d_w_size x - MIN_LOOKAHEAD)); lia. }
  exists Gb. split; [rewrite Ehd; exact G0|].
  intros q Gq Hq Hl. destruct (G1 q Gq Hq ltac:(lia)) as (A & B & C).
  split; [lia|]. split.
  - rewrite <- B. unfold h3, update_hash. rewrite Ewin, Esh, Ehm. reflexivity.
  - rewrite Ewm, Epv. exact C.
Qed.

(* INSERT_STRING does not look at strstart / lookahead *)
Lemma c_insert_string_shf x a e p :
  c_insert_string (shf x a e) p =
  match c_insert_string x p with Some (x', h) => Some (shf x' a e, h) | None => None end.
Proof.
  unfold c_insert_string, shf. autorewrite with dproj.
  destruct (guard _); cbn [bind]; [|reflexivity].
  destruct (mb_rd _ _); cbn [bind]; [|reflexivity].
  autorewrite with dproj.
  destruct (rd _ _); cbn [bind]; [|reflexivity].
  destruct (wr _ _ _); cbn [bind]; [|reflexivity].
  autorewrite with dproj.
  destruct (wr _ _ _); cbn [bind]; [|reflexivity].
  destruct x; reflexivity.
Qed.

(* one iteration of the insertion loop is INSERT_STRING *)
Lemma sd_insert_body_ins x p m :
  sd_insert_body (x, p, m) =
  match c_insert_string x p with
  | Some (x', _) => Some (if u32 (m - 1) =? 0 then inr (x', u32 (p + 1)) else inl (x', u32 (p + 1), u32 (m - 1)))
  | None => None
  end.
Proof.
  unfold sd_insert_body, c_insert_string.
  destruct (guard _); cbn [bind]; [|reflexivity].
  destruct (mb_rd _ _); cbn [bind]; [|reflexivity].
  destruct (rd _ _); cbn [bind]; [|reflexivity].
  destruct (wr _ _ _); cbn [bind]; [|reflexivity].
  destruct (wr _ _ _); cbn [bind]; [|reflexivity].
  destruct (_ =? 0); reflexivity.
Qed.

(* one iteration: the new chains, chain_hok and primed for the next position *)
Lemma sd_step_hok (Hins : ins_fspec2) s E h P H p m :
  prm s -> wstruct s -> E <= d_w_size s ->
  (forall i, 0 <= i < E -> Znth i (mb_def (d_window s)) = true) ->
  d_insert s = 0 -> d_block_start s = 0 -> 0 <= d_high_water s <= d_window_size s ->
  p + m + 2 = E -> 0 <= p -> 1 <= m ->
  Zlength P = Zlength (d_prev s) -> Zlength H = Zlength (d_head s) ->
  chains p H P -> chain_hok (shf (sdT s h P H) p E) -> primed (sdT s h P H) p ->
  let ih := update_hash s h (Znth (p + 2) (mb_val (d_window s))) in
  let X := sdT s ih (upd_Znth p P (Znth ih H)) (upd_Znth ih H p) in
  sd_insert_body (sdT s h P H, p, m) = Some (if m - 1 =? 0 then inr (X, p + 1) else inl (X, p + 1, m - 1)) /\
  chains (p + 1) (upd_Znth ih H p) (upd_Znth p P (Znth ih H)) /\
  chain_hok (shf X (p + 1) E) /\ primed X (p + 1).
Proof.
  intros Hp Hw HE Hdef Hi0 Hbs Hhw Hpm Hp0 Hm HP HH Hch Hk Hq ih X.
  pose proof (w_size_bound s Hp) as Hwb.
  assert (Hd : Znth (p + 2) (mb_def (d_window s)) = true) by (apply Hdef; lia).
  pose proof (sd_step s h P H p m Hp Hw ltac:(lia) ltac:(lia) ltac:(lia) HP HH Hd) as Est.
  cbv zeta in Est. fold ih in Est. fold X in Est.
  pose proof (update_hash_range s h (Znth (p + 2) (mb_val (d_window s))) Hp) as Hih. fold ih in Hih.
  pose proof Hw as Hw'.
  destruct Hw' as (Hwl & Hwok & Hws & Hpl & Hhl).
  assert (Hih' : 0 <= ih < Zlength H) by lia.
  assert (Hpp : 0 <= p < Zlength P) by lia.
  split; [exact Est|].
  split.
  { destruct Hch as [Ch Cp]. split.
    - intros i Hi. rewrite upd_Znth_Zlength in Hi by lia.
      destruct (Z.eq_dec i ih) as [->|Hne].
      + rewrite upd_Znth_same by lia. unfold inG. lia.
      + rewrite upd_Znth_diff by lia. specialize (Ch i ltac:(lia)). unfold inG in *. lia.
    - intros q Hq1.
      destruct (Z.eq_dec q p) as [->|Hne].
      + rewrite upd_Znth_same by lia. specialize (Ch ih Hih'). unfold inG in *. lia.
      + rewrite upd_Znth_diff by lia. specialize (Cp q ltac:(lia)). unfold inG in *. lia. }
  rewrite sd_insert_body_ins in Est.
  destruct (c_insert_string (sdT s h P H) p) as [[x' hh]|] eqn:Ec; [|discriminate].
  assert (x' = X) by (destruct (u32 (m - 1) =? 0), (m - 1 =? 0); congruence). subst x'.
  assert (Ec2 : c_insert_string (shf (sdT s h P H) p E) p = Some (shf X p E, hh))
    by (rewrite c_insert_string_shf, Ec; reflexivity).
  destruct Hp as (Hwb1 & Hws1 & Hwm1 & Hhb1 & Hhs1 & Hhm1 & Hrest).
  assert (Hprm : prm (shf (sdT s h P H) p E)).
  { unfold prm, shf, sdT. autorewrite with dproj. repeat split; tauto. }
  assert (Hwst : wstruct (shf (sdT s h P H) p E)).
  { unfold wstruct, shf, sdT. autorewrite with dproj. split; [lia|split; [exact Hwok|repeat split; lia]]. }
  assert (Hwp : wpos (shf (sdT s h P H) p E)).
  { unfold wpos, shf, sdT. autorewrite with dproj. rewrite Hi0, Hbs. repeat split; try lia. }
  assert (Hco : chain_ok (shf (sdT s h P H) p E)).
  { apply (chain_ok_of_chains _ p); unfold shf, sdT; autorewrite with dproj; try lia; auto. }
  assert (Hlim : p - d_w_size (shf (sdT s h P H) p E) < lim (shf (sdT s h P H) p E)).
  { unfold lim, MAX_DIST, shf, sdT. autorewrite with dproj.
    destruct (Z.gtb_spec p (d_w_size s - MIN_LOOKAHEAD)); unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *; lia. }
  assert (B1 : 0 <= p <= d_strstart (shf (sdT s h P H) p E)) by (unfold shf, sdT; autorewrite with dproj; lia).
  assert (B2 : d_strstart (shf (sdT s h P H) p E) - d_w_size (shf (sdT s h P H) p E) <= p)
    by (unfold shf, sdT; autorewrite with dproj; lia).
  assert (B3 : p + 2 < d_strstart (shf (sdT s h P H) p E) + d_lookahead (shf (sdT s h P H) p E))
    by (unfold shf, sdT; autorewrite with dproj; lia).
  destruct (Hins _ _ _ _ Hprm Hwst Hwp Hco Hk Hq B1 B2 B3 Hlim Ec2) as (_ & _ & K1 & K2).
  split.
  - apply (chain_hok_mono _ _ K1); unfold shf; autorewrite with dproj; try reflexivity; lia.
  - unfold primed, shf in *. autorewrite with dproj in K2. exact K2.
Qed.

(* the insertion loop of one round of deflateSetDictionary (positions str .. str + nn - 1, below w_size) *)
Lemma sd_ins_hok (Hins : ins_fspec2) : forall s str nn b,
  prm s -> wstruct s -> 0 <= str -> 1 <= nn -> str + nn + 2 <= d_w_size s ->
  (forall i, 0 <= i < str + nn + 2 -> Znth i (mb_def (d_window s)) = true) ->
  d_insert s = 0 -> d_block_start s = 0 -> 0 <= d_high_water s <= d_window_size s ->
  chains str (d_head s) (d_prev s) ->
  chain_hok (shf s str (str + nn + 2)) -> primed s str ->
  loop FUEL sd_insert_body (s, str, nn) = Some b ->
  chain_hok (shf (fst b) (snd b) (str + nn + 2)).
Proof.
  intros s str nn b Hp Hw Hs Hn Hb Hdef Hi0 Hbs Hhw Hch0 Hk0 Hq0 Hl.
  apply loop_runs in Hl.
  set (E := str + nn + 2) in *.
  assert (Gen : forall a r, runs sd_insert_body a r -> forall h P H p m, a = (sdT s h P H, p, m) ->
    p + m + 2 = E -> 0 <= p -> 1 <= m -> Zlength P = Zlength (d_prev s) -> Zlength H = Zlength (d_head s) ->
    chains p H P -> chain_hok (shf (sdT s h P H) p E) -> primed (sdT s h P H) p ->
    chain_hok (shf (fst r) (snd r) E)).
  { induction 1 as [a r Hr | a a' r Hr Hrun IH]; intros h P H p m -> Hpm Hp0 Hm HP HH Hc Hk Hq;
      destruct (sd_step_hok Hins s E h P H p m Hp Hw ltac:(lia) Hdef Hi0 Hbs Hhw Hpm Hp0 Hm HP HH Hc Hk Hq)
        as (Est & Ch & K & Q);
      rewrite Est in Hr.
    - destruct (m - 1 =? 0); [|discriminate]. injection Hr as <-. exact K.
    - destruct (Z.eqb_spec (m - 1) 0) as [Em|Em]; [discriminate|]. injection Hr as <-.
      eapply IH; [reflexivity| | | | | | exact Ch | exact K | exact Q]; try lia.
      + pose proof Hw as (_ & _ & _ & Hpl & _). rewrite upd_Znth_Zlength; lia.
      + pose proof (update_hash_range s h (Znth (p + 2) (mb_val (d_window s))) Hp).
        pose proof Hw as (_ & _ & _ & _ & Hhl). rewrite upd_Znth_Zlength; lia. }
  assert (Es : sdT s (d_ins_h s) (d_prev s) (d_head s) = s) by (unfold sdT; destruct s; reflexivity).
  eapply (Gen _ _ Hl (d_ins_h s) (d_prev s) (d_head s) str nn); rewrite ?Es; try reflexivity; try lia; auto.
Qed.
