(* RT-D part SLOW: the functional part fpre_part of deflate_slow (statement: RTDSlowKit.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDSlowKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** longest_match does not read head *)
Lemma fp_loop2_sim {A B : Type} (body : A -> option (A + B)) (f : A -> A) (g : B -> B) :
  (forall a, body (f a) = match body a with Some (inl a') => Some (inl (f a')) | Some (inr b) => Some (inr (g b))
                          | None => None end) ->
  forall d a, loop2 d body (f a) = match loop2 d body a with Some (inl a') => Some (inl (f a'))
                                   | Some (inr b) => Some (inr (g b)) | None => None end.
Proof.
  intros Hb d. induction d as [|d IH]; intros a.
  - simpl. apply Hb.
  - simpl. rewrite IH. destruct (loop2 d body a) as [[a'|b]|]; [apply IH|reflexivity|reflexivity].
Qed.

Definition lmf (hd : list Z) (a : lm_st) : lm_st :=
  mkLM (lm_cur a) (lm_chain a) (lm_best a) (lm_end1 a) (lm_end a) (set_d_head (lm_s a) hd).
Definition lmg (hd : list Z) (b : Z * dstate) : Z * dstate := (fst b, set_d_head (snd b) hd).

Lemma fp_cmp_frame s hd strend : lm_cmp_body (set_d_head s hd) strend = lm_cmp_body s strend.
Proof. reflexivity. Qed.

Lemma fp_prev s hd : d_prev (set_d_head s hd) = d_prev s. Proof. reflexivity. Qed.
Lemma fp_win s hd : d_window (set_d_head s hd) = d_window s. Proof. reflexivity. Qed.
Lemma fp_mask s hd : d_w_mask (set_d_head s hd) = d_w_mask s. Proof. reflexivity. Qed.
Lemma fp_ss s hd : d_strstart (set_d_head s hd) = d_strstart s. Proof. reflexivity. Qed.

Lemma fp_ms_head s hd x : set_d_match_start (set_d_head s hd) x = set_d_head (set_d_match_start s x) hd.
Proof. destruct s; reflexivity. Qed.

Lemma fp_body_frame nice limit hd a :
  lm_body nice limit (lmf hd a) =
  match lm_body nice limit a with Some (inl a') => Some (inl (lmf hd a')) | Some (inr b) => Some (inr (lmg hd b))
  | None => None end.
Proof.
  destruct a as [cur ch best e1 e s]. unfold lm_body, lmf. cbn [lm_s lm_cur lm_chain lm_best lm_end1 lm_end].
  rewrite fp_cmp_frame, !fp_ms_head, !fp_prev, !fp_win, !fp_mask, !fp_ss.
  generalize (loop FUEL (lm_cmp_body s (d_strstart s + MAX_MATCH)) (d_strstart s + 2, cur + 2, 0)) as o.
  intros o. unfold bind.
  destruct o; repeat match goal with |- context [mb_rd ?w ?i] => destruct (mb_rd w i)
                                | |- context [rd ?w ?i] => destruct (rd w i)
                                | |- context [if ?b then _ else _] => destruct b end; reflexivity.
Qed.

Lemma fp_loop_frame nice limit hd a :
  loop FUEL (lm_body nice limit) (lmf hd a) =
  match loop FUEL (lm_body nice limit) a with Some b => Some (lmg hd b) | None => None end.
Proof.
  unfold loop. rewrite (fp_loop2_sim (lm_body nice limit) (lmf hd) (lmg hd) (fp_body_frame nice limit hd)).
  destruct (loop2 FUEL (lm_body nice limit) a) as [[?|?]|]; reflexivity.
Qed.

(** the frame of c_longest_match for head (also proved in RTDFastSearch.v) *)
Lemma lm_head_frame s cur s' ml hd :
  c_longest_match s cur = Some (s', ml) -> c_longest_match (set_d_head s hd) cur = Some (set_d_head s' hd, ml).
Proof.
  unfold c_longest_match.
  change (d_prev_length (set_d_head s hd)) with (d_prev_length s).
  change (d_lookahead (set_d_head s hd)) with (d_lookahead s).
  change (d_strstart (set_d_head s hd)) with (d_strstart s).
  change (d_window (set_d_head s hd)) with (d_window s).
  change (d_max_chain_length (set_d_head s hd)) with (d_max_chain_length s).
  change (d_good_match (set_d_head s hd)) with (d_good_match s).
  change (d_nice_match (set_d_head s hd)) with (d_nice_match s).
  change (d_w_size (set_d_head s hd)) with (d_w_size s).
  unfold bind.
  destruct (guard _); [|discriminate]. destruct (guard _); [|discriminate]. destruct (guard _); [|discriminate].
  destruct (mb_rd _ _); [|discriminate]. destruct (mb_rd _ _); [|discriminate].
  match goal with |- context [loop FUEL (lm_body ?n ?l) (mkLM ?c ?ch ?b ?x1 ?x2 (set_d_head s hd))] =>
    change (mkLM c ch b x1 x2 (set_d_head s hd)) with (lmf hd (mkLM c ch b x1 x2 s)) end.
  rewrite fp_loop_frame.
  match goal with |- context [loop FUEL (lm_body ?n ?l) ?a] => generalize (loop FUEL (lm_body n l) a) as o end.
  intros o.
  destruct o as [[b s1]|]; [|discriminate]. cbn [lmg fst snd]. intros E. inversion E; subst. reflexivity.
Qed.

(** ** INSERT_STRING(p): head[ins_h] = p, prev[p & w_mask] = the old head *)
Lemma fp_wr l i v l' : wr l i v = Some l' -> l' = upd_Znth i l v /\ 0 <= i < Zlength l.
Proof.
  unfold wr, in_range. destruct ((0 <=? i) && (i <? Zlength l)) eqn:B; [|discriminate].
  intros E. inversion E. apply andb_true_iff in B. destruct B as (B1 & B2).
  apply Z.leb_le in B1. apply Z.ltb_lt in B2. split; [reflexivity|lia].
Qed.

Lemma fp_ins_model s p s' h : c_insert_string s p = Some (s', h) ->
  Znth (d_ins_h s') (d_head s') = u16 p /\ Znth (Z.land p (d_w_mask s)) (d_prev s') = h.
Proof.
  unfold c_insert_string, bind. cbv zeta.
  destruct (guard _); [|discriminate].
  destruct (mb_rd _ _) as [c|]; [|discriminate].
  destruct (rd _ _) as [hh|]; [|discriminate].
  destruct (wr (d_prev _) _ _) as [pv|] eqn:Ew; [|discriminate].
  destruct (wr (d_head _) _ _) as [hd|] eqn:Ew2; [|discriminate].
  intros E. inversion E; subst; clear E.
  apply fp_wr in Ew. apply fp_wr in Ew2. destruct Ew as (-> & Hr). destruct Ew2 as (-> & Hr2).
  cbn [d_ins_h d_head d_prev set_d_head set_d_prev set_d_ins_h] in *.
  split; apply upd_Znth_same; assumption.
Qed.

(** ** What INSERT_STRING / longest_match leave of the chains *)
Definition fp_same (s s' : dstate) : Prop :=
  d_head s' = d_head s /\ d_prev s' = d_prev s /\ d_strstart s' = d_strstart s /\
  d_lookahead s' = d_lookahead s /\ d_w_size s' = d_w_size s /\ d_w_mask s' = d_w_mask s /\
  d_window s' = d_window s /\ d_hash_size s' = d_hash_size s /\ d_hash_shift s' = d_hash_shift s /\
  d_hash_mask s' = d_hash_mask s /\ d_ins_h s' = d_ins_h s.

Ltac fps := unfold fp_same; repeat split.

Lemma fp_same_hok s s' : fp_same s s' -> chain_hok s -> chain_hok s'.
Proof.
  intros (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & _) H.
  unfold chain_hok, h3, update_hash, lim, MAX_DIST in *.
  rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10. exact H.
Qed.

Lemma fp_same_primed s s' p : fp_same s s' -> primed s p -> primed s' p.
Proof.
  intros (_ & _ & _ & _ & _ & _ & E7 & _ & E9 & E10 & E11) H.
  unfold primed, update_hash in *. rewrite E7, E9, E10, E11. exact H.
Qed.

Lemma fp_uh_range s h c : prm s -> 0 <= update_hash s h c < d_hash_size s.
Proof.
  intros (_ & _ & _ & Hb & Hs & Hm & _). unfold update_hash. rewrite Hm, Hs.
  set (x := Z.lxor _ _).
  replace (2 ^ d_hash_bits s - 1) with (Z.ones (d_hash_bits s)) by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_ones by lia.
  assert (B := Z.mod_pos_bound x (2 ^ d_hash_bits s) ltac:(apply Z.pow_pos_nonneg; lia)).
  assert (2 ^ d_hash_bits s <= 65536) by (change 65536 with (2 ^ 16); apply Z.pow_le_mono_r; lia).
  unfold u32. rewrite Z.mod_small; lia.
Qed.

Lemma fp_h3_range s p : prm s -> 0 <= h3 s p < d_hash_size s.
Proof. intros Hp. unfold h3. apply fp_uh_range. exact Hp. Qed.

Lemma fp_prm_hc s s' : hc_keep s' = hc_keep s -> prm s -> prm s'.
Proof.
  intros E Hp. assert (H : prm (hc_keep s')) by (rewrite E; exact Hp). exact H.
Qed.

Lemma fp_wsize s : prm s -> 512 <= d_w_size s <= 32768.
Proof.
  intros (Hb & Hw & _). rewrite Hw. split.
  - change 512 with (2 ^ 9). apply Z.pow_le_mono_r; lia.
  - change 32768 with (2 ^ 15). apply Z.pow_le_mono_r; lia.
Qed.

Theorem fpre_ok : fpre_part.
Proof.
  intros s0 z0 flush s z evs s1x dict H BS syms Hss Hfs HSI Hrdy Hk E.
  enough (Hex : exists s1', dsl_pre s = Some s1' /\ FMID s s1').
  { destruct Hex as (s1' & E' & HF). rewrite E in E'. inversion E'; subst. exact HF. }
  clear E.
  destruct Hss as (_ & Hins & Hlm & _). destruct Hfs as (_ & Hfins & Hflm & _).
  destruct Hk as (_ & Hkh1 & Hkh2).
  destruct HSI as ((HW & _) & _ & _ & HEI).
  destruct HEI as (_ & Hfn0 & _ & Hsp & _).
  assert (Hlev : d_level s <> 0).
  { destruct Hsp as (_ & _ & _ & _ & _ & El & _). rewrite El. intros E. unfold fn_of in Hfn0.
    rewrite E in Hfn0. cbn in Hfn0. discriminate. }
  assert (Hfn : fn_of s = 2).
  { destruct Hsp as (_ & _ & _ & _ & _ & El & Est). unfold fn_of in *. rewrite El, Est. exact Hfn0. }
  destruct HW as (Hp & Hws & Hpos & Hwin & Hhash & Hmatch & _ & _).
  assert (Hwsz := fp_wsize s Hp).
  unfold whash in Hhash.
  destruct (Z.eqb_spec (d_level s) 0) as [E0|_]; [lia|].
  destruct Hhash as (_ & G & HG).
  destruct Hmatch as (Hml & Hpl & _).
  pose proof Hws as Hws'. destruct Hws' as (Hwl & Hmb & Hwsize & Hprevl & Hheadl).
  pose proof Hpos as Hpos'. destruct Hpos' as (Hla0 & Hss0 & Hsl & _).
  destruct Hrdy as (Hla1 & Hroom & Hdef).
  assert (HMD : MAX_DIST s = d_w_size s - 262) by reflexivity.
  unfold dsl_pre, c_insert_head.
  destruct (Z.geb_spec (d_lookahead s) MIN_MATCH) as [Hge|Hlt].
  2:{ cbn [bind]. cbn [d_prev_length d_strstart set_d_match_length set_d_prev_match set_d_prev_length].
      eexists. split; [reflexivity|].
      split; [eapply fp_same_hok; [|exact Hkh1]; fps|].
      split; [intros F; lia|].
      intros F. exfalso. cbn in F. unfold MIN_MATCH in *; lia. }
  destruct (Hins s (d_strstart s) (d_strstart s) (lim s) G) as (s1 & h & Ec & Ek & Hws1 & Gh & Hch1 & Hcl1);
    [exact Hp | exact Hws | exact HG
    | unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *; lia
    | unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *; lia
    | apply Hdef; unfold MAX_MATCH in *; lia
    | lia
    | unfold lim; destruct (Z.gtb_spec (d_strstart s) (MAX_DIST s)); lia |].
  destruct (Hfins s (d_strstart s) s1 h) as (Eih & Eh & Hchk1 & Hprim1);
    [exact Hp | exact Hws | exact Hpos | exists G; exact HG | exact Hkh1
    | exact (proj2 (Hkh2 (or_intror Hfn) Hge)) | lia | lia
    | unfold MIN_MATCH in *; lia
    | unfold lim; destruct (Z.gtb_spec (d_strstart s) (MAX_DIST s)); lia | exact Ec |].
  destruct (fp_ins_model _ _ _ _ Ec) as (Ehd1 & Epv1).
  rewrite Ec. cbn [bind].
  assert (Ess := f_equal d_strstart Ek). assert (Ews := f_equal d_w_size Ek).
  assert (Ela := f_equal d_lookahead Ek). assert (Ewin := f_equal d_window Ek).
  assert (Ewsz := f_equal d_window_size Ek). assert (Epl := f_equal d_prev_length Ek).
  assert (Eml := f_equal d_match_length Ek). assert (Ems := f_equal d_match_start Ek).
  assert (Est := f_equal d_strategy Ek).
  assert (Ehs := f_equal d_hash_size Ek). assert (Ehsh := f_equal d_hash_shift Ek).
  assert (Ehm := f_equal d_hash_mask Ek). assert (Ewm := f_equal d_w_mask Ek).
  cbn in Ess, Ews, Ela, Ewin, Ewsz, Epl, Eml, Ems, Est, Ehs, Ehsh, Ehm, Ewm.
  assert (Elim : lim s1 = lim s) by (unfold lim, MAX_DIST; rewrite Ess, Ews; reflexivity).
  assert (Emd : max_dist s1 = MAX_DIST s).
  { unfold max_dist, MAX_DIST. rewrite Ews. unfold u32. apply Z.mod_small. unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH. lia. }
  rewrite Z.max_r in Hch1 by lia.
  change (d_match_start (set_d_prev_length s1 (d_match_length s1))) with (d_match_start s1).
  set (s2 := set_d_match_length (set_d_prev_match (set_d_prev_length s1 (d_match_length s1)) (d_match_start s1))
               (MIN_MATCH - 1)).
  assert (Hp1 : prm s1) by exact (fp_prm_hc s s1 Ek Hp).
  assert (E2s : d_strstart s2 = d_strstart s1) by reflexivity.
  assert (E2l : d_lookahead s2 = d_lookahead s1) by reflexivity.
  assert (E2pl : d_prev_length s2 = d_match_length s) by (subst s2; cbn; exact Eml).
  assert (E2pm : d_prev_match s2 = d_match_start s) by (subst s2; cbn; exact Ems).
  assert (E2ml : d_match_length s2 = MIN_MATCH - 1) by reflexivity.
  assert (Hsame2 : fp_same s1 s2) by fps.
  assert (Hmd2 : max_dist s2 = max_dist s1) by reflexivity.
  rewrite Hmd2, Emd, E2s, Ess.
  destruct (negb (h =? NIL) && (d_prev_length s2 <? d_max_lazy_match s2) &&
            (u32 (d_strstart s - h) <=? MAX_DIST s)) eqn:Eb.
  2:{ exists s2. split; [reflexivity|].
      split; [exact (fp_same_hok _ _ Hsame2 Hchk1)|].
      split; [intros _; exact (fp_same_primed _ _ _ Hsame2 Hprim1)|].
      rewrite E2ml. intros F. unfold MIN_MATCH in *; lia. }
  apply andb_true_iff in Eb. destruct Eb as (Eb & Ed). apply andb_true_iff in Eb. destruct Eb as (Eh0 & _).
  apply negb_true_iff, Z.eqb_neq in Eh0. apply Z.leb_le in Ed.
  destruct (proj1 HG h Gh) as [F|Hh]; [unfold NIL in Eh0; lia|].
  unfold u32 in Ed. rewrite (Z.mod_small (d_strstart s - h)) in Ed by (unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *; lia).
  assert (Hlimh : lim s <= h) by (unfold lim; destruct (Z.gtb_spec (d_strstart s) (MAX_DIST s)); lia).
  pose proof Hws1 as Hws1'. destruct Hws1' as (Hwl1 & Hmb1 & Hwsize1 & Hprevl1 & Hheadl1).
  assert (Elim2 : lim s2 = lim s) by exact Elim.
  destruct (Hlm s2 h (d_strstart s) (lim s) G) as (ms & ml & El & Hml' & Hmll & _ & Hgt);
    [ exact Hp1 | exact Hws1 | exact Hcl1
    | rewrite E2s; lia | lia
    | exact Gh | lia | rewrite Elim2; lia | rewrite E2pl; lia | rewrite E2l, Ela; exact Hge
    | rewrite E2s, E2l, Ess, Ela; change (d_window_size s2) with (d_window_size s1); lia
    | change (d_window s2) with (d_window s1); rewrite Hwl1, E2s, Ess, Ews;
      unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *; lia
    | intros i Hi; change (d_window s2) with (d_window s1); rewrite Ewin; apply Hdef; rewrite E2s, Ess in Hi; lia | ].
  rewrite El. cbn [bind].
  rewrite Elim2, E2s, Ess, E2pl in Hgt. rewrite E2l, Ela in Hmll.
  set (s3 := set_d_match_length (set_d_match_start s2 ms) ml).
  assert (E3ml : d_match_length s3 = ml) by reflexivity.
  assert (E3ms : d_match_start s3 = ms) by reflexivity.
  assert (E3st : d_strategy s3 = d_strategy s) by (subst s3; cbn; exact Est).
  assert (E3s : d_strstart s3 = d_strstart s) by (subst s3; cbn; exact Ess).
  assert (E3pl : d_prev_length s3 = d_match_length s) by exact E2pl.
  assert (Hsame3 : fp_same s1 s3) by fps.
  rewrite E3ml, E3ms, E3st, E3s.
  destruct ((ml <=? 5) && ((d_strategy s =? Z_FILTERED) ||
            ((ml =? MIN_MATCH) && (u32 (d_strstart s - ms) >? TOO_FAR)))) eqn:Ef.
  - eexists. split; [reflexivity|].
    assert (Hsame4 : fp_same s1 (set_d_match_length s3 (MIN_MATCH - 1))) by fps.
    split; [exact (fp_same_hok _ _ Hsame4 Hchk1)|].
    split; [intros _; exact (fp_same_primed _ _ _ Hsame4 Hprim1)|].
    change (d_match_length (set_d_match_length s3 (MIN_MATCH - 1))) with (MIN_MATCH - 1).
    intros F. unfold MIN_MATCH in *; lia.
  - exists s3. split; [reflexivity|].
    split; [exact (fp_same_hok _ _ Hsame3 Hchk1)|].
    split; [intros _; exact (fp_same_primed _ _ _ Hsame3 Hprim1)|].
    rewrite E3ml, E3pl, E3ms, E3s. intros Hm3 Hlt3.
    destruct (Hgt Hlt3) as (Hl1 & Hl2 & Hl3).
    assert (Elim3 : lim s3 = lim s) by exact Elim.
    rewrite Elim3. split; [exact Hl1|]. split; [lia|].
    (* the bytes: lm_fspec on the state with the old head *)
    set (hd0 := d_head s). set (s2o := set_d_head s2 hd0).
    assert (El' := lm_head_frame _ _ _ _ hd0 El).
    set (b := h3 s (d_strstart s)).
    assert (Hb : 0 <= b < d_hash_size s1) by (rewrite Ehs; exact (fp_h3_range s _ Hp)).
    destruct (Hchk1 b Hb) as (Gb & Gb0 & Gcl).
    assert (Hss65 : d_strstart s < 65536) by (unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *; lia).
    assert (Ehb : Znth b (d_head s1) = d_strstart s).
    { unfold b. rewrite <- Eih, Ehd1. unfold u16. apply Z.mod_small. lia. }
    rewrite Ehb in Gb0.
    destruct (Gcl (d_strstart s) Gb0) as (_ & _ & Gh'); [lia | rewrite Elim; lia |].
    rewrite Ewm, Epv1 in Gh'.
    assert (Eh3 : forall q, h3 s1 q = h3 s q).
    { intros q. unfold h3, update_hash. rewrite Ewin, Ehsh, Ehm. reflexivity. }
    assert (Hbytes := Hflm s2o h (set_d_head (set_d_match_start s2 ms) hd0) ml Gb).
    change (d_match_start (set_d_head (set_d_match_start s2 ms) hd0)) with ms in Hbytes.
    change (d_window s2o) with (d_window s3) in Hbytes.
    change (d_strstart s2o) with (d_strstart s3) in Hbytes.
    rewrite E3s in Hbytes. apply Hbytes; clear Hbytes.
    + exact Hp1.
    + split; [exact Hwl1|]. split; [exact Hmb1|]. split; [exact Hwsize1|]. split; [exact Hprevl1|].
      change (Zlength (d_head s) = d_hash_size s1). rewrite Ehs. exact Hheadl.
    + assert (Hpos1 : wpos (hc_keep s)) by exact Hpos. rewrite <- Ek in Hpos1. exact Hpos1.
    + assert (Hwin1 : wwin (hc_keep s)) by exact Hwin. rewrite <- Ek in Hwin1. exact Hwin1.
    + exists G. change (chain_with s2o (d_strstart s1) (lim s1) G). rewrite Ess, Elim.
      split; [exact (proj1 HG)|]. split.
      * intros hh Hhh. change (d_hash_size s1) with (d_hash_size s2o) in Ehs. 
        change (d_head s2o) with (d_head s). apply (proj1 (proj2 HG)). rewrite <- Ehs. exact Hhh.
      * exact (proj2 Hcl1).
    + change (MIN_MATCH <= d_lookahead s1). rewrite Ela. exact Hge.
    + change (0 <= d_prev_length s2 <= MAX_MATCH). rewrite E2pl. exact Hml.
    + lia.
    + change (lim s1 <= h). rewrite Elim. exact Hlimh.
    + lia.
    + exact Gh'.
    + intros q Gq Hq Hlq. change (lim s1 <= q) in Hlq.
      destruct (Gcl q Gq Hq Hlq) as (A1 & A2 & A3). split; [rewrite <- Ess; exact A1|]. split; [|exact A3].
      change (h3 s1 q = h3 s1 (d_strstart s)). rewrite A2, Eh3. reflexivity.
    + exact El'.
    + change (d_prev_length s2 < ml). rewrite E2pl. exact Hlt3.
Qed.
