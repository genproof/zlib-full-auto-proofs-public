(* RT-D part RLE: the refill (c_refill need_rle, fill_window) (statement: RTDRleKit.v; model on RTDLTCRleRefill.rrefill_ok). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDRleKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** a prefix of a list is a prefix of any extension *)
Lemma rfr_sublist0_app (l1 l2 : list Z) x : x <= Zlength l1 -> sublist 0 x (l1 ++ l2) = sublist 0 x l1.
Proof.
  intros Hx. unfold sublist. cbn [Z.sub Z.to_nat skipn]. replace (x - 0) with x by lia. cbn [skipn].
  rewrite List.firstn_app.
  assert (E : (Z.to_nat x - length l1)%nat = 0%nat).
  { rewrite Zlength_correct in Hx. lia. }
  rewrite E. cbn [firstn]. apply app_nil_r.
Qed.

(** the trees part is kept by fill_window *)
Lemma rfr_wtrees s s' syms d :
  fw_keep s' = fw_keep s -> d_strstart s' = d_strstart s - d -> d_block_start s' = d_block_start s - d ->
  wtrees s syms -> wtrees s' syms.
Proof.
  intros Hk Es Eb (T1 & T2 & T3 & T4 & T5).
  destruct (rfwk_fields s s' Hk) as (Etr & Epbm & Epo & Ews & Ewz & Eml & Ema & Epl & Epbs & Ewb &
    Est & Ewr & Egz & Egi & Elf & Eme).
  assert (Elv : d_level s' = d_level s) by (unfold d_level; rewrite Etr; reflexivity).
  assert (Esg : d_strategy s' = d_strategy s) by (unfold d_strategy; rewrite Etr; reflexivity).
  assert (EMD : MAX_DIST s' = MAX_DIST s) by (unfold MAX_DIST; rewrite Ews; reflexivity).
  unfold wtrees.
  split; [rewrite Etr, Epbm; exact T1|].
  split; [unfold d_L; rewrite Etr; exact T2|].
  split.
  { eapply Forall_impl; [|exact T3]. intros x (X1 & X2 & X3). unfold sym_ok.
    rewrite EMD, Elv, Esg. split; [exact X1|]. split; [exact X2|exact X3]. }
  split; [rewrite Elv; exact T4|].
  intros Hl. rewrite Elv in Hl. rewrite Es, Eb, Ema, T5 by exact Hl. lia.
Qed.

Theorem rfrefill_ok : fill_fspec -> rfrefill_stmt.
Proof.
  intros Hff s z flush r dict D BS syms HW Ho Hq Hz Ha Hfn Hfl Hwt Hrk Hr.
  unfold c_refill in Hr.
  destruct (need_rle s) eqn:Hn.
  - assert (Hfp : fill_pre s).
    { destruct HW as (Hp & Hs & Hpos & Hw & Hh & _).
      assert (Hlev := fn_of_rle s Hp Hfn).
      unfold whash in Hh. destruct (Z.eqb_spec (d_level s) 0) as [E|N]; [lia|].
      destruct Hh as (_ & Hc).
      split; [exact Hp|]. split; [exact Hs|]. split; [exact Hpos|]. split; [exact Hw|exact Hc]. }
    destruct (fill_ok s z Hfp Hz Ha) as (s' & z' & k & d & Hfw & Hfp' & Hk & Hst & Hd & Es & Eb & _ & _ &
      El & _).
    destruct Hrk as (Kw & Kb & Ke & Ks & Kd & Kc).
    destruct (Hff s z s' z' (dict ++ D) Hfp Hz Ha Hfw Kw) as (k' & Hst' & Kw' & Hc & _).
    assert (Ek : k' = k).
    { destruct Hst as (_ & _ & A & _). destruct Hst' as (_ & _ & B & _). lia. }
    subst k'.
    destruct (rfwk_fields s s' Hk) as (Etr & Epbm & Epo & Ews & Ewz & Eml & Ema & Epl & Epbs & Ewb &
      Est & Ewr & Egz & Egi & Elf & Eme).
    assert (Hrst : rst r = (s', z')).
    { rewrite Hfw in Hr. cbn [bind] in Hr.
      destruct (need_rle s' && (flush =? Z_NO_FLUSH)); [inversion Hr; reflexivity|].
      destruct (d_lookahead s' =? 0); inversion Hr; reflexivity. }
    rewrite Hrst. cbn [fst snd]. exists k.
    split; [exact Hst'|].
    split; [exact (rfr_wtrees s s' syms d Hk Es Eb Hwt)|].
    split.
    + pose proof HW as (_ & _ & Hpos & _).
      destruct Hpos as (Pl & Ps & _ & Pb & _).
      destruct Hz as [(Hb & Hni & Hai & Hil & _) _].
      destruct Hst as (_ & Hk0 & _).
      set (X := sublist (z_next_in z) (z_next_in z + k) (z_in z)) in *.
      assert (LX : Zlength X = k) by (unfold X; rewrite Zlength_sublist by lia; lia).
      destruct Kw as (Kw1 & _).
      unfold rkt. cbv zeta. rewrite app_assoc, Ewb.
      assert (E1 : Zlength ((dict ++ D) ++ X) - (d_strstart s' + d_lookahead s') + d_block_start s' =
                   Zlength (dict ++ D) - (d_strstart s + d_lookahead s) + d_block_start s)
        by (rewrite Zlength_app; lia).
      assert (E2 : Zlength ((dict ++ D) ++ X) - (d_strstart s' + d_lookahead s') + d_strstart s' =
                   Zlength (dict ++ D) - (d_strstart s + d_lookahead s) + d_strstart s)
        by (rewrite Zlength_app; lia).
      rewrite E1, E2, (rfr_sublist0_app _ X (_ + d_block_start s)), (rfr_sublist0_app _ X (_ + d_strstart s)) by lia.
      split; [exact Kw'|]. split; [exact Kb|]. split; [exact Ke|]. split; [exact Ks|].
      split; [exact Kd|]. exact (Hc Kc).
    + unfold pend, bibits, d_pending, d_bi_valid. rewrite Etr, Epo. split; reflexivity.
  - inversion Hr; subst r. cbn [rst fst snd]. exists 0.
    split; [apply zstep_refl; assumption|].
    split; [exact Hwt|].
    split; [|split; reflexivity].
    rewrite Z.add_0_r, sublist_nil, app_nil_r. exact Hrk.
Qed.
