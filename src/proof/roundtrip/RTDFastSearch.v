(** * RT-D part FAST, piece: fsearch_stmt (statement and definitions: RTDFastKit.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDFastKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** longest_match does not read head *)
Lemma fsr_loop2_sim {A B : Type} (body : A -> option (A + B)) (f : A -> A) (g : B -> B) :
  (forall a, body (f a) = match body a with Some (inl a') => Some (inl (f a')) | Some (inr b) => Some (inr (g b))
                          | None => None end) ->
  forall d a, loop2 d body (f a) = match loop2 d body a with Some (inl a') => Some (inl (f a'))
                                   | Some (inr b) => Some (inr (g b)) | None => None end.
Proof.
  intros Hb d. induction d as [|d IH]; intros a.
  - simpl. apply Hb.
  - simpl. rewrite IH. destruct (loop2 d body a) as [[a'|b]|]; [apply IH|reflexivity|reflexivity].
Qed.

Definition fsr_lmf (hd : list Z) (a : lm_st) : lm_st :=
  mkLM (lm_cur a) (lm_chain a) (lm_best a) (lm_end1 a) (lm_end a) (set_d_head (lm_s a) hd).
Definition fsr_lmg (hd : list Z) (b : Z * dstate) : Z * dstate := (fst b, set_d_head (snd b) hd).

Lemma fsr_cmp_frame s hd strend : lm_cmp_body (set_d_head s hd) strend = lm_cmp_body s strend.
Proof. reflexivity. Qed.

Lemma fsr_prev s hd : d_prev (set_d_head s hd) = d_prev s. Proof. reflexivity. Qed.
Lemma fsr_win s hd : d_window (set_d_head s hd) = d_window s. Proof. reflexivity. Qed.
Lemma fsr_mask s hd : d_w_mask (set_d_head s hd) = d_w_mask s. Proof. reflexivity. Qed.
Lemma fsr_ss s hd : d_strstart (set_d_head s hd) = d_strstart s. Proof. reflexivity. Qed.

Lemma fsr_ms_head s hd x : set_d_match_start (set_d_head s hd) x = set_d_head (set_d_match_start s x) hd.
Proof. destruct s; reflexivity. Qed.

Lemma fsr_body_frame nice limit hd a :
  lm_body nice limit (fsr_lmf hd a) =
  match lm_body nice limit a with Some (inl a') => Some (inl (fsr_lmf hd a')) | Some (inr b) => Some (inr (fsr_lmg hd b))
  | None => None end.
Proof.
  destruct a as [cur ch best e1 e s]. unfold lm_body, fsr_lmf. cbn [lm_s lm_cur lm_chain lm_best lm_end1 lm_end].
  rewrite fsr_cmp_frame, !fsr_ms_head, !fsr_prev, !fsr_win, !fsr_mask, !fsr_ss.
  generalize (loop FUEL (lm_cmp_body s (d_strstart s + MAX_MATCH)) (d_strstart s + 2, cur + 2, 0)) as o.
  intros o. unfold bind.
  destruct o; repeat match goal with |- context [mb_rd ?w ?i] => destruct (mb_rd w i)
                                | |- context [rd ?w ?i] => destruct (rd w i)
                                | |- context [if ?b then _ else _] => destruct b end; reflexivity.
Qed.

Lemma fsr_loop_frame nice limit hd a :
  loop FUEL (lm_body nice limit) (fsr_lmf hd a) =
  match loop FUEL (lm_body nice limit) a with Some b => Some (fsr_lmg hd b) | None => None end.
Proof.
  unfold loop. rewrite (fsr_loop2_sim (lm_body nice limit) (fsr_lmf hd) (fsr_lmg hd) (fsr_body_frame nice limit hd)).
  destruct (loop2 FUEL (lm_body nice limit) a) as [[?|?]|]; reflexivity.
Qed.

(** the frame of c_longest_match for head (also proved in RTDSlowFPre.v) *)
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
    change (mkLM c ch b x1 x2 (set_d_head s hd)) with (fsr_lmf hd (mkLM c ch b x1 x2 s)) end.
  rewrite fsr_loop_frame.
  match goal with |- context [loop FUEL (lm_body ?n ?l) ?a] => generalize (loop FUEL (lm_body n l) a) as o end.
  intros o.
  destruct o as [[b s1]|]; [|discriminate]. cbn [fsr_lmg fst snd]. intros E. inversion E; subst. reflexivity.
Qed.

(** ** INSERT_STRING(p): head[ins_h] = p, prev[p & w_mask] = the old head *)
Lemma fsr_wr l i v l' : wr l i v = Some l' -> l' = upd_Znth i l v /\ 0 <= i < Zlength l.
Proof.
  unfold wr, in_range. destruct ((0 <=? i) && (i <? Zlength l)) eqn:B; [|discriminate].
  intros E. inversion E. apply andb_true_iff in B. destruct B as (B1 & B2).
  apply Z.leb_le in B1. apply Z.ltb_lt in B2. split; [reflexivity|lia].
Qed.

Lemma fsr_ins_model s p s' h : c_insert_string s p = Some (s', h) ->
  Znth (d_ins_h s') (d_head s') = u16 p /\ Znth (Z.land p (d_w_mask s)) (d_prev s') = h.
Proof.
  unfold c_insert_string, bind. cbv zeta.
  destruct (guard _); [|discriminate].
  destruct (mb_rd _ _) as [c|]; [|discriminate].
  destruct (rd _ _) as [hh|]; [|discriminate].
  destruct (wr (d_prev _) _ _) as [pv|] eqn:Ew; [|discriminate].
  destruct (wr (d_head _) _ _) as [hd|] eqn:Ew2; [|discriminate].
  intros E. inversion E; subst; clear E.
  apply fsr_wr in Ew. apply fsr_wr in Ew2. destruct Ew as (-> & Hr). destruct Ew2 as (-> & Hr2).
  cbn [d_ins_h d_head d_prev set_d_head set_d_prev set_d_ins_h] in *.
  split; apply upd_Znth_same; assumption.
Qed.

(** ** What INSERT_STRING / longest_match leave of the chains *)
Definition fsr_same (s s' : dstate) : Prop :=
  d_head s' = d_head s /\ d_prev s' = d_prev s /\ d_strstart s' = d_strstart s /\
  d_lookahead s' = d_lookahead s /\ d_w_size s' = d_w_size s /\ d_w_mask s' = d_w_mask s /\
  d_window s' = d_window s /\ d_hash_size s' = d_hash_size s /\ d_hash_shift s' = d_hash_shift s /\
  d_hash_mask s' = d_hash_mask s /\ d_ins_h s' = d_ins_h s.

Local Ltac fps := unfold fsr_same; repeat split.

Lemma fsr_same_hok s s' : fsr_same s s' -> chain_hok s -> chain_hok s'.
Proof.
  intros (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & _) H.
  unfold chain_hok, h3, update_hash, lim, MAX_DIST in *.
  rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10. exact H.
Qed.

Lemma fsr_same_primed s s' p : fsr_same s s' -> primed s p -> primed s' p.
Proof.
  intros (_ & _ & _ & _ & _ & _ & E7 & _ & E9 & E10 & E11) H.
  unfold primed, update_hash in *. rewrite E7, E9, E10, E11. exact H.
Qed.

Lemma fsr_uh_range s h c : prm s -> 0 <= update_hash s h c < d_hash_size s.
Proof.
  intros (_ & _ & _ & Hb & Hs & Hm & _). unfold update_hash. rewrite Hm, Hs.
  set (x := Z.lxor _ _).
  replace (2 ^ d_hash_bits s - 1) with (Z.ones (d_hash_bits s)) by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_ones by lia.
  assert (B := Z.mod_pos_bound x (2 ^ d_hash_bits s) ltac:(apply Z.pow_pos_nonneg; lia)).
  assert (2 ^ d_hash_bits s <= 65536) by (change 65536 with (2 ^ 16); apply Z.pow_le_mono_r; lia).
  unfold u32. rewrite Z.mod_small; lia.
Qed.

Lemma fsr_h3_range s p : prm s -> 0 <= h3 s p < d_hash_size s.
Proof. intros Hp. unfold h3. apply fsr_uh_range. exact Hp. Qed.

Lemma fsr_prm_hc s s' : hc_keep s' = hc_keep s -> prm s -> prm s'.
Proof.
  intros E Hp. assert (H : prm (hc_keep s')) by (rewrite E; exact Hp). exact H.
Qed.

Lemma fsr_wsize s : prm s -> 512 <= d_w_size s <= 32768.
Proof.
  intros (Hb & Hw & _). rewrite Hw. split.
  - change 512 with (2 ^ 9). apply Z.pow_le_mono_r; lia.
  - change 32768 with (2 ^ 15). apply Z.pow_le_mono_r; lia.
Qed.

Theorem fsearch_ok : fsearch_stmt.
Proof.
  intros s s2x Hfins Hflm HW Hfn Hrd Hla Hkh E.
  enough (Hex : exists s2, fsearch s = Some s2 /\
    (chain_hok s2 /\
    (MIN_MATCH <= d_lookahead s -> primed s2 (d_strstart s + 1)) /\
    (MIN_MATCH <= d_match_length s2 -> forall i, 0 <= i < d_match_length s2 ->
       Znth (d_match_start s2 + i) (mb_val (d_window s)) = Znth (d_strstart s + i) (mb_val (d_window s))))).
  { destruct Hex as (s2' & E' & HF). rewrite E in E'. inversion E'; subst. exact HF. }
  clear E.
  destruct HW as (Hp & Hws & Hpos & Hwin & Hhash & Hmatch & _ & _).
  assert (Hlev := fn_of_fast s Hp Hfn).
  assert (Hwsz := fsr_wsize s Hp).
  unfold whash in Hhash.
  destruct (Z.eqb_spec (d_level s) 0) as [E0|_]; [lia|].
  destruct Hhash as (_ & G & HG).
  destruct Hkh as (Hkh1 & Hkh2).
  destruct (Z.eqb_spec (d_level s) 0) as [E0|_]; [lia|].
  destruct Hmatch as (Hml & Hpl & Hma & Hma0 & Hma1).
  assert (Ema : d_match_available s = 0).
  { destruct Hma as [E|E]; [exact E|]. destruct (Hma1 E) as (F & _). lia. }
  destruct (Hma0 Ema) as (Hml3 & Hpl3).
  pose proof Hws as Hws'. destruct Hws' as (Hwl & Hmb & Hwsize & Hprevl & Hheadl).
  pose proof Hpos as Hpos'. destruct Hpos' as (Hla0 & Hss0 & Hsl & _).
  assert (HMD : MAX_DIST s = d_w_size s - 262) by reflexivity.
  unfold fsearch, c_insert_head.
  destruct (Z.geb_spec (d_lookahead s) MIN_MATCH) as [Hge|Hlt].
  2:{ cbn [bind]. exists s. split; [reflexivity|].
      split; [exact Hkh1|]. split; [intros F; lia|].
      intros F. unfold MIN_MATCH in *; lia. }
  destruct lm_ok as (Hins & Hlm).
  destruct (Hins s (d_strstart s) (d_strstart s) (lim s) G) as (s1 & h & Ec & Ek & Hws1 & Gh & Hch1 & Hcl1);
    [exact Hp | exact Hws | exact HG | lia
    | unfold MIN_MATCH in *; lia
    | apply Hwin; unfold MIN_MATCH in *; lia
    | lia
    | unfold lim; destruct (Z.gtb_spec (d_strstart s) (MAX_DIST s)); lia |].
  destruct (Hfins s (d_strstart s) s1 h) as (Eih & Eh & Hchk1 & Hprim1);
    [exact Hp | exact Hws | exact Hpos | exists G; exact HG | exact Hkh1
    | exact (proj2 (Hkh2 (or_introl Hfn) Hge)) | lia | lia
    | unfold MIN_MATCH in *; lia
    | unfold lim; destruct (Z.gtb_spec (d_strstart s) (MAX_DIST s)); lia | exact Ec |].
  destruct (fsr_ins_model _ _ _ _ Ec) as (Ehd1 & Epv1).
  rewrite Ec. cbn [bind].
  assert (Ess := f_equal d_strstart Ek). assert (Ews := f_equal d_w_size Ek).
  assert (Ela := f_equal d_lookahead Ek). assert (Ewin := f_equal d_window Ek).
  assert (Ewsz := f_equal d_window_size Ek). assert (Epl := f_equal d_prev_length Ek).
  assert (Eml := f_equal d_match_length Ek).
  assert (Ehs := f_equal d_hash_size Ek). assert (Ehsh := f_equal d_hash_shift Ek).
  assert (Ehm := f_equal d_hash_mask Ek). assert (Ewm := f_equal d_w_mask Ek).
  cbn in Ess, Ews, Ela, Ewin, Ewsz, Epl, Eml, Ehs, Ehsh, Ehm, Ewm.
  assert (Elim : lim s1 = lim s) by (unfold lim, MAX_DIST; rewrite Ess, Ews; reflexivity).
  assert (Emd : max_dist s1 = MAX_DIST s).
  { unfold max_dist, MAX_DIST. rewrite Ews. unfold u32. apply Z.mod_small. unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH. lia. }
  rewrite Z.max_r in Hch1 by lia.
  assert (Hp1 : prm s1) by exact (fsr_prm_hc s s1 Ek Hp).
  destruct (negb (h =? NIL) && (u32 (d_strstart s1 - h) <=? max_dist s1)) eqn:Eb.
  2:{ exists s1. split; [reflexivity|].
      split; [exact Hchk1|]. split; [intros _; exact Hprim1|].
      rewrite Eml. intros F. unfold MIN_MATCH in *; lia. }
  apply andb_true_iff in Eb. destruct Eb as (Eh0 & Ed).
  apply negb_true_iff, Z.eqb_neq in Eh0. apply Z.leb_le in Ed. rewrite Emd, Ess in Ed.
  destruct (proj1 HG h Gh) as [F|Hh]; [unfold NIL in Eh0; lia|].
  unfold u32 in Ed. rewrite (Z.mod_small (d_strstart s - h)) in Ed by (unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *; lia).
  assert (Hlimh : lim s <= h) by (unfold lim; destruct (Z.gtb_spec (d_strstart s) (MAX_DIST s)); lia).
  pose proof Hws1 as Hws1'. destruct Hws1' as (Hwl1 & Hmb1 & Hwsize1 & Hprevl1 & Hheadl1).
  destruct (Hlm s1 h (d_strstart s) (lim s) G) as (ms & ml & El & Hml' & Hmll & _ & Hgt);
    [ exact Hp1 | exact Hws1 | exact Hcl1 | lia | lia
    | exact Gh | lia | lia | lia | rewrite Ela; exact Hge | lia
    | rewrite Hwl1, Ess; destruct Hrd as [Hr|(Hr1 & Hr2)]; unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *; lia
    | intros i Hi; rewrite Ewin; apply Hwin; rewrite Ess in Hi;
      destruct Hrd as [Hr|(Hr1 & Hr2)]; unfold WIN_INIT, MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *; lia | ].
  rewrite El. cbn [bind].
  set (s3 := set_d_match_length (set_d_match_start s1 ms) ml).
  exists s3. split; [reflexivity|].
  assert (Hsame3 : fsr_same s1 s3) by fps.
  split; [exact (fsr_same_hok _ _ Hsame3 Hchk1)|].
  split; [intros _; exact (fsr_same_primed _ _ _ Hsame3 Hprim1)|].
  change (d_match_length s3) with ml. change (d_match_start s3) with ms.
  intros Hm3.
  assert (Hlt3 : d_prev_length s1 < ml) by (rewrite Epl; unfold MIN_MATCH in *; lia).
  (* the bytes: lm_fspec on the state with the old head *)
  set (hd0 := d_head s). set (s1o := set_d_head s1 hd0).
  assert (El' := lm_head_frame _ _ _ _ hd0 El).
  set (b := h3 s (d_strstart s)).
  assert (Hb : 0 <= b < d_hash_size s1) by (rewrite Ehs; exact (fsr_h3_range s _ Hp)).
  destruct (Hchk1 b Hb) as (Gb & Gb0 & Gcl).
  assert (Hss65 : d_strstart s < 65536) by (unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *; lia).
  assert (Ehb : Znth b (d_head s1) = d_strstart s).
  { unfold b. rewrite <- Eih, Ehd1. unfold u16. apply Z.mod_small. lia. }
  rewrite Ehb in Gb0.
  destruct (Gcl (d_strstart s) Gb0) as (_ & _ & Gh'); [lia | rewrite Elim; lia |].
  rewrite Ewm, Epv1 in Gh'.
  assert (Eh3 : forall q, h3 s1 q = h3 s q).
  { intros q. unfold h3, update_hash. rewrite Ewin, Ehsh, Ehm. reflexivity. }
  assert (Hbytes := Hflm s1o h (set_d_head (set_d_match_start s1 ms) hd0) ml Gb).
  change (d_match_start (set_d_head (set_d_match_start s1 ms) hd0)) with ms in Hbytes.
  change (d_window s1o) with (d_window s1) in Hbytes.
  change (d_strstart s1o) with (d_strstart s1) in Hbytes.
  rewrite Ess, Ewin in Hbytes. apply Hbytes; clear Hbytes.
  + exact Hp1.
  + split; [exact Hwl1|]. split; [exact Hmb1|]. split; [exact Hwsize1|]. split; [exact Hprevl1|].
    change (Zlength (d_head s) = d_hash_size s1). rewrite Ehs. exact Hheadl.
  + assert (Hpos1 : wpos (hc_keep s)) by exact Hpos. rewrite <- Ek in Hpos1. exact Hpos1.
  + assert (Hwin1 : wwin (hc_keep s)) by exact Hwin. rewrite <- Ek in Hwin1. exact Hwin1.
  + exists G. change (chain_with s1o (d_strstart s1) (lim s1) G). rewrite Ess, Elim.
    split; [exact (proj1 HG)|]. split.
    * intros hh Hhh. change (d_hash_size s1) with (d_hash_size s1o) in Ehs.
      change (d_head s1o) with (d_head s). apply (proj1 (proj2 HG)). rewrite <- Ehs. exact Hhh.
    * exact (proj2 Hcl1).
  + change (MIN_MATCH <= d_lookahead s1). rewrite Ela. exact Hge.
  + change (0 <= d_prev_length s1 <= MAX_MATCH). rewrite Epl. exact Hpl.
  + lia.
  + change (lim s1 <= h). rewrite Elim. exact Hlimh.
  + lia.
  + exact Gh'.
  + intros q Gq Hq Hlq. change (lim s1 <= q) in Hlq.
    destruct (Gcl q Gq Hq Hlq) as (A1 & A2 & A3). split; [change (d_lookahead s1o) with (d_lookahead s1); rewrite <- Ess; exact A1|]. split; [|exact A3].
    change (h3 s1 q = h3 s1 (d_strstart s)). rewrite A2, Eh3. reflexivity.
  + exact El'.
  + exact Hlt3.
Qed.
