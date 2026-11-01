(* RT-D part HUFF: fill_window at a huff state (model on RTDLTCHuffRefill.hrefill_ok).  Statement: RTDHuffKit.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDHuffKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** The fields fill_window keeps (as RTDLTCHuffRefill.hfwk_fields). *)
Lemma hfr_fields s s' : fw_keep s' = fw_keep s ->
  d_tr s' = d_tr s /\ d_pbm s' = d_pbm s /\ d_po s' = d_po s /\ d_w_size s' = d_w_size s /\
  d_w_bits s' = d_w_bits s /\ d_match_available s' = d_match_available s.
Proof.
  intros E.
  pose proof (f_equal d_tr E) as E1. pose proof (f_equal d_pbm E) as E2. pose proof (f_equal d_po E) as E3.
  pose proof (f_equal d_w_size E) as E4. pose proof (f_equal d_w_bits E) as E10.
  pose proof (f_equal d_match_available E) as E7.
  unfold fw_keep in *. cbn [d_tr d_pbm d_po d_w_size d_w_bits d_match_available] in *.
  repeat (split; [assumption|]). assumption.
Qed.

Lemma hfr_sublist_app (H X : list Z) n : n <= Zlength H -> sublist 0 n (H ++ X) = sublist 0 n H.
Proof.
  intros Hn. destruct (Z_lt_le_dec n 0) as [N|N].
  - rewrite !sublist_nil_gen by lia. reflexivity.
  - apply sublist_app1; lia.
Qed.

Theorem hfrefill_ok : fill_spec -> fill_fspec -> hfrefill_stmt.
Proof.
  intros Hfill Hff s z s' z' syms dict D BS HW Hfn Hz Ha Ht Hk3 Hfw.
  assert (HW0 := HW).
  destruct HW0 as (Hp & Hs & Hpos & Hw & Hh & Hm & H0 & _).
  destruct (fn_of_huff s Hp Hfn) as [Hlev _].
  assert (Hfp : fill_pre s).
  { unfold whash in Hh. destruct (Z.eqb_spec (d_level s) 0) as [E|N]; [lia|].
    destruct Hh as (_ & Hc).
    split; [exact Hp|]. split; [exact Hs|]. split; [exact Hpos|]. split; [exact Hw|exact Hc]. }
  destruct (Hfill s z Hfp Hz Ha) as (s1 & z1 & k & d & Hfw1 & Hfp' & Hk & Hst & Hd & Es & Eb & _ & _ &
    El & _).
  rewrite Hfw in Hfw1. injection Hfw1 as <- <-.
  destruct (hfr_fields s s' Hk) as (Etr & Epbm & Epo & Ews & Ewb & Ema).
  destruct Hk3 as (K1 & K2 & K3 & K4 & K5 & K6).
  destruct (Hff s z s' z' (dict ++ D) Hfp Hz Ha Hfw K1) as (k' & Hst' & Hkw & Hch & _).
  assert (Ekk : k' = k).
  { destruct Hst as (_ & _ & N1 & _). destruct Hst' as (_ & _ & N2 & _). lia. }
  subst k'.
  assert (Elv : d_level s' = d_level s) by (unfold d_level; rewrite Etr; reflexivity).
  assert (Esg : d_strategy s' = d_strategy s) by (unfold d_strategy; rewrite Etr; reflexivity).
  assert (EMD : MAX_DIST s' = MAX_DIST s) by (unfold MAX_DIST; rewrite Ews; reflexivity).
  assert (Hk0 : 0 <= k) by (destruct Hst as (_ & X & _); lia).
  destruct Hpos as (P1 & P2 & P3 & P4 & _).
  set (X := sublist (z_next_in z) (z_next_in z + k) (z_in z)) in *.
  assert (EX : Zlength X = k).
  { destruct Hz as [(_ & Hn & Hai & Hl & _) _]. destruct Hst as (_ & X1 & _).
    unfold X. rewrite Zlength_sublist by lia. lia. }
  exists k. split; [exact Hst|].
  split.
  { destruct Ht as (T1 & T2 & T3 & T4 & T5). unfold wtrees.
    split; [rewrite Etr, Epbm; exact T1|].
    split; [unfold d_L; rewrite Etr; exact T2|].
    split.
    { eapply Forall_impl; [|exact T3]. intros x (X1 & X2 & X3). unfold sym_ok.
      rewrite EMD, Elv, Esg. split; [exact X1|]. split; [exact X2|exact X3]. }
    split; [intros; lia|].
    intros _. rewrite Es, Eb, Ema. rewrite T5 by lia. lia. }
  split.
  { unfold hk3. cbv zeta. rewrite <- app_assoc in Hkw.
    assert (EL : Zlength (dict ++ D ++ X) = Zlength (dict ++ D) + k).
    { rewrite app_assoc, Zlength_app, EX. reflexivity. }
    fold X. rewrite EL, Ewb, Es, Eb, El, app_assoc.
    split; [rewrite <- app_assoc; exact Hkw|]. split; [exact K2|].
    split.
    { rewrite K3. rewrite (hfr_sublist_app (dict ++ D) X) by lia. f_equal. lia. }
    split; [exact K4|].
    split.
    { rewrite K5. rewrite (hfr_sublist_app (dict ++ D) X) by lia. f_equal. lia. }
    exact (Hch K6). }
  split.
  { unfold bibits, d_bi_valid. rewrite Etr. reflexivity. }
  { unfold pend, d_pending. rewrite Etr, Epo. reflexivity. }
Qed.
