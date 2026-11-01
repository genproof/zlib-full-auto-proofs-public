(** * deflate_fast, part: INSERT_STRING at strstart and longest_match (fsearch).  Statement and definitions: LTCFastKit.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTCFastKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Lemma fs_sr_keep_hc s s' : hc_keep s' = hc_keep s -> sr_keep s' = sr_keep s.
Proof.
  intros E. unfold sr_keep.
  assert (X : forall t, hc_keep (set_d_match_start (set_d_match_length t 0) 0) =
                        set_d_match_start (set_d_match_length (hc_keep t) 0) 0)
    by (intros t; destruct t; reflexivity).
  rewrite !X, E. reflexivity.
Qed.

Lemma fs_sr_keep_set s ms ml : sr_keep (set_d_match_length (set_d_match_start s ms) ml) = sr_keep s.
Proof. destruct s; reflexivity. Qed.

Lemma fs_prm_hc s s' : hc_keep s' = hc_keep s -> prm s -> prm s'.
Proof.
  intros E Hp. assert (H : prm (hc_keep s')) by (rewrite E; exact Hp). exact H.
Qed.

Lemma fs_chain_set s ms ml n l G :
  chain_with s n l G -> chain_with (set_d_match_length (set_d_match_start s ms) ml) n l G.
Proof. intros H. exact H. Qed.

Lemma fs_wstruct_set s ms ml : wstruct s -> wstruct (set_d_match_length (set_d_match_start s ms) ml).
Proof. intros H. exact H. Qed.

Lemma fs_chain_mono s n n' l G : n <= n' -> chain_with s n l G -> chain_with s n' l G.
Proof.
  intros Hn (H1 & H2 & H3). split; [|split; assumption].
  intros v Hv. destruct (H1 v Hv); [left; assumption | right; lia].
Qed.

Lemma fs_wsize s : prm s -> 512 <= d_w_size s <= 32768.
Proof.
  intros (Hb & Hw & _). rewrite Hw. split.
  - change 512 with (2 ^ 9). apply Z.pow_le_mono_r; lia.
  - change 32768 with (2 ^ 15). apply Z.pow_le_mono_r; lia.
Qed.

Theorem search_ok : ins_spec -> lm_spec -> search_stmt.
Proof.
  intros Hins Hlm s HW Hfn Hrd Hla.
  destruct HW as (Hp & Hws & Hpos & Hwin & Hhash & Hmatch & _ & _).
  assert (Hlev := fn_of_fast s Hp Hfn).
  assert (Hwsz := fs_wsize s Hp).
  unfold whash in Hhash.
  destruct (Z.eqb_spec (d_level s) 0) as [E0|_]; [lia|].
  destruct Hhash as (_ & G & HG).
  destruct Hmatch as (Hml & Hpl & Hma & Hma0 & Hma1).
  assert (Ema : d_match_available s = 0).
  { destruct Hma as [E|E]; [exact E|]. destruct (Hma1 E) as (F & _). lia. }
  destruct (Hma0 Ema) as (Hml3 & Hpl3).
  pose proof Hws as Hws'. destruct Hws' as (Hwl & Hmb & Hwsize & Hprevl & Hheadl).
  destruct Hpos as (Hla0 & Hss0 & Hsl & _).
  assert (HMD : MAX_DIST s = d_w_size s - 262) by reflexivity.
  unfold fsearch, c_insert_head.
  destruct (Z.geb_spec (d_lookahead s) MIN_MATCH) as [Hge|Hlt].
  2:{ cbn [bind]. exists s. split; [reflexivity|].
      split; [reflexivity|]. split; [exact Hws|].
      split; [exists G; apply (fs_chain_mono s (d_strstart s)); [lia|exact HG]|].
      split; [exact Hml|]. intros F. unfold MIN_MATCH in *; lia. }
  destruct (Hins s (d_strstart s) (d_strstart s) (lim s) G) as (s1 & h & Ec & Ek & Hws1 & Gh & Hch1 & Hcl1);
    [exact Hp | exact Hws | exact HG | lia
    | unfold MIN_MATCH in *; lia
    | apply Hwin; unfold MIN_MATCH in *; lia
    | lia
    | unfold lim; destruct (Z.gtb_spec (d_strstart s) (MAX_DIST s)); lia |].
  rewrite Ec. cbn [bind].
  assert (Ess := f_equal d_strstart Ek). assert (Ews := f_equal d_w_size Ek).
  assert (Ela := f_equal d_lookahead Ek). assert (Ewin := f_equal d_window Ek).
  assert (Ewsz := f_equal d_window_size Ek). assert (Epl := f_equal d_prev_length Ek).
  assert (Eml := f_equal d_match_length Ek).
  cbn in Ess, Ews, Ela, Ewin, Ewsz, Epl, Eml.
  assert (Elim : lim s1 = lim s) by (unfold lim, MAX_DIST; rewrite Ess, Ews; reflexivity).
  assert (Emd : max_dist s1 = MAX_DIST s).
  { unfold max_dist, MAX_DIST. rewrite Ews. unfold u32. apply Z.mod_small. unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH. lia. }
  rewrite Z.max_r in Hch1 by lia.
  destruct (negb (h =? NIL) && (u32 (d_strstart s1 - h) <=? max_dist s1)) eqn:Eb.
  2:{ exists s1. split; [reflexivity|].
      split; [apply fs_sr_keep_hc; exact Ek|]. split; [exact Hws1|].
      split; [eexists; exact Hch1|].
      rewrite Eml. split; [exact Hml|]. intros F. unfold MIN_MATCH in *; lia. }
  apply andb_true_iff in Eb. destruct Eb as (Eh & Ed).
  apply negb_true_iff, Z.eqb_neq in Eh. apply Z.leb_le in Ed. rewrite Emd, Ess in Ed.
  destruct (proj1 HG h Gh) as [F|Hh]; [unfold NIL in Eh; lia|].
  unfold u32 in Ed. rewrite (Z.mod_small (d_strstart s - h)) in Ed by (unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *; lia).
  assert (Hlimh : lim s <= h) by (unfold lim; destruct (Z.gtb_spec (d_strstart s) (MAX_DIST s)); lia).
  pose proof Hws1 as Hws1'. destruct Hws1' as (Hwl1 & Hmb1 & Hwsize1 & Hprevl1 & Hheadl1).
  destruct (Hlm s1 h (d_strstart s) (lim s) G) as (ms & ml & El & Hml' & Hmll & _ & Hgt);
    [ apply (fs_prm_hc s s1 Ek Hp) | exact Hws1 | exact Hcl1 | lia | lia
    | exact Gh | lia | lia | lia | rewrite Ela; exact Hge | lia
    | rewrite Hwl1, Ess; destruct Hrd as [Hr|(Hr1 & Hr2)]; unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *; lia
    | intros i Hi; rewrite Ewin; apply Hwin; rewrite Ess in Hi;
      destruct Hrd as [Hr|(Hr1 & Hr2)]; unfold WIN_INIT, MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *; lia | ].
  rewrite El. cbn [bind].
  exists (set_d_match_length (set_d_match_start s1 ms) ml). split; [reflexivity|].
  split; [rewrite fs_sr_keep_set; apply fs_sr_keep_hc; exact Ek|].
  split; [apply fs_wstruct_set; exact Hws1|].
  split; [eexists; apply fs_chain_set; exact Hch1|].
  split; [exact Hml'|].
  intros F. change (d_match_length (set_d_match_length (set_d_match_start s1 ms) ml)) with ml in *.
  change (d_match_start (set_d_match_length (set_d_match_start s1 ms) ml)) with ms.
  rewrite Elim, Ess, Epl in Hgt. rewrite Ela in Hmll.
  destruct Hgt as (H1 & H2); [unfold MIN_MATCH in *; lia|]. lia.
Qed.
