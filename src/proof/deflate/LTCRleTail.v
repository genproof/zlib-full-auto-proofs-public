(** * deflate_rle, part: deflate_tail with insert = 0
    Statement: LTCRleKit.v ([rtail_stmt]). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTCRleKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Lemma rtail_W_ins s : W s -> W (set_d_insert s 0).
Proof.
  intros (Hp & Hs & Hpos & Hw & Hh & Hm & H0 & syms & Ht).
  unfold W. split; [exact Hp|]. split; [exact Hs|].
  split.
  { destruct Hpos as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
    unfold wpos. cbn [d_insert set_d_insert d_strstart d_w_size d_high_water d_window_size
      d_lookahead d_block_start].
    repeat (split; [assumption|]). split; [lia|]. split; [lia|exact P9]. }
  split; [exact Hw|]. split; [exact Hh|]. split; [exact Hm|]. split; [exact H0|].
  exists syms. exact Ht.
Qed.

Lemma rtail_syms_nil s syms : tree_ok (d_tr s) (d_pbm s) syms -> d_sym_next s = 0 -> syms = [].
Proof.
  intros (_ & _ & Hn & _) H0. unfold d_sym_next in H0. rewrite H0 in Hn.
  destruct syms; [reflexivity|]. rewrite Zlength_cons in Hn. pose proof (Zlength_nonneg syms). lia.
Qed.

Theorem rtail_ok : rfbw_stmt -> rtail_stmt.
Proof.
  intros Hfbw s z flush HW Ho Hq Hz Ha Hfn Hfl Hnf Hla Hai Hss.
  assert (HW1 := rtail_W_ins s HW).
  assert (Hss1 : d_strstart (set_d_insert s 0) < d_window_size (set_d_insert s 0)).
  { destruct HW as (_ & Hs & _). destruct Hs as (_ & _ & Hwsz & _).
    cbn [set_d_insert d_strstart d_window_size]. unfold MAX_DIST, MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in Hss. lia. }
  destruct (W_RTS0 (set_d_insert s 0) HW1 Ho Hq Hfn Hss1) as (syms & HT0 & HL2).
  unfold c_deflate_tail.
  destruct (Z.eqb_spec flush Z_FINISH) as [EF|EF].
  - destruct (Hfbw (set_d_insert s 0) z flush syms 1 HT0 Hz Ha Hfl ltac:(lia) ltac:(intros; exact EF)
                ltac:(intros; lia))
      as (s' & z' & e & Hfb & Hcr & Hlast & Hz' & Had & Hai' & Hla' & Hss' & Hbs & Hsn & Hbv & Hbv1 & Hpo).
    specialize (Hbv1 eq_refl).
    unfold c_flush_block. rewrite Hfb. cbn [bind].
    assert (Hcr' := Hcr). destruct Hcr' as (_ & Ho' & _ & Hapi & _).
    assert (Hub : ub s' = 0).
    { unfold ub. rewrite Hla', Hss', Hbs. cbn [set_d_insert d_lookahead]. lia. }
    assert (Hlev : last_ev [e]).
    { exists [], e. split; [reflexivity|]. split; [exact Hlast|constructor]. }
    assert (Hstarted : z_avail_out z' = 0 -> d_pending s' <> 0 \/ d_wrap s' <> 0 ->
      exists s'0 z'0 bs evs,
        (let* pat := Some (s', z', Some finish_started) in
         match pat with
         | (s0, z0, Some r0) => Some (s0, z0, r0)
         | (s0, z0, None) => Some (s0, z0, finish_done)
         end) = Some (s'0, z'0, bs) /\ crel s z flush s'0 z'0 evs /\ bpost s z flush s'0 z'0 bs evs).
    { intros E PW. eexists _, _, _, _. split; [reflexivity|]. split; [exact Hcr|].
      cbn [bpost]. split; [exact Hlev|]. split; [exact EF|]. split; [rewrite Hai'; exact Hai|].
      split; [exact Hub|]. split; [exact Hsn|]. split; [exact Hbv1|]. split; [exact E|].
      intros _. destruct PW as [P|Wr]; [left; exact P|right].
      destruct Hapi as (_ & Hw' & _). intro Hw0. apply Wr. rewrite Hw'. exact Hw0. }
    assert (Hdone : d_pending s' = 0 ->
      exists s'0 z'0 bs evs,
        (let* pat := Some (s', z', None) in
         match pat with
         | (s0, z0, Some r0) => Some (s0, z0, r0)
         | (s0, z0, None) => Some (s0, z0, finish_done)
         end) = Some (s'0, z'0, bs) /\ crel s z flush s'0 z'0 evs /\ bpost s z flush s'0 z'0 bs evs).
    { intros P0. eexists _, _, _, _. split; [reflexivity|]. split; [exact Hcr|].
      cbn [bpost]. split; [exact Hlev|]. split; [exact EF|]. split; [rewrite Hai'; exact Hai|].
      split; [exact Hub|]. split; [exact Hsn|]. split; [|exact Hbv1].
      unfold quiet. split; [exact P0|]. split; [|lia].
      destruct Ho' as (_ & _ & _ & _ & _ & Ho'). apply Ho'; exact P0. }
    destruct (Z.eqb_spec (z_avail_out z') 0) as [E|E];
      destruct (Z.eqb_spec (d_pending s') 0) as [P|P];
      destruct (Z.eqb_spec (d_wrap s') 0) as [Wr|Wr]; cbn [andb orb negb Z.eqb Pos.eqb].
    + apply Hdone; exact P.
    + apply Hstarted; auto.
    + apply Hstarted; auto.
    + apply Hstarted; auto.
    + apply Hdone; exact P.
    + apply Hdone; exact P.
    + destruct Hpo; contradiction.
    + destruct Hpo; contradiction.
  - destruct (Z.eqb_spec (d_sym_next (set_d_insert s 0)) 0) as [S0|S0]; cbn [negb].
    + assert (Hsy : syms = []).
      { destruct HT0 as (_ & _ & _ & _ & _ & _ & Ht & _). exact (rtail_syms_nil _ _ Ht S0). }
      assert (Hub : ub s = 0).
      { destruct HT0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hb & _). rewrite Hsy in Hb.
        unfold blk_len in Hb. cbn in Hb. unfold ub. rewrite Hla.
        cbn [set_d_insert d_strstart d_block_start] in Hb. lia. }
      exists (set_d_insert s 0), z, block_done, []. split; [reflexivity|].
      split.
      { unfold crel. split; [exact HW1|]. split; [exact Ho|].
        split; [unfold same_prm; repeat split; reflexivity|].
        split; [unfold api_eq; repeat split; reflexivity|].
        split; [exists 0, []; split; [apply zstep_refl; auto|split; [constructor|]]|].
        { change (ub (set_d_insert s 0)) with (ub s). cbn [sum_len fold_right]. lia. }
        split; [cbn [ev_chain]; reflexivity|constructor]. }
      cbn [bpost]. split; [constructor|]. split; [exact Hnf|]. split; [exact EF|]. split; [exact Hai|].
      split; [exact Hub|]. split; [exact Hq|]. exact S0.
    + destruct (Hfbw (set_d_insert s 0) z flush syms 0 HT0 Hz Ha Hfl ltac:(lia) ltac:(intros; lia)
                  ltac:(intros; right; split; assumption))
        as (s' & z' & e & Hfb & Hcr & Hlast & Hz' & Had & Hai' & Hla' & Hss' & Hbs & Hsn & Hbv & _ & Hpo).
      unfold c_flush_block. rewrite Hfb. cbn [bind].
      assert (Hcr' := Hcr). destruct Hcr' as (_ & Ho' & _ & Hapi & _).
      destruct (Z.eqb_spec (z_avail_out z') 0) as [E|E]; cbn [andb orb negb Z.eqb Pos.eqb].
      * eexists _, _, _, _. split; [reflexivity|]. split; [exact Hcr|].
        cbn [bpost]. split; [constructor; [exact Hlast|constructor]|]. split; [exact Hbv|]. right; left; exact E.
      * eexists _, _, _, _. split; [reflexivity|]. split; [exact Hcr|].
        assert (P0 : d_pending s' = 0) by (destruct Hpo; [assumption|contradiction]).
        cbn [bpost]. split; [constructor; [exact Hlast|constructor]|]. split; [exact Hnf|].
        split; [exact EF|]. split; [rewrite Hai'; exact Hai|].
        split; [unfold ub; rewrite Hla', Hss', Hbs; cbn [set_d_insert d_lookahead]; lia|].
        split; [|exact Hsn].
        unfold quiet. split; [exact P0|]. split; [|exact Hbv].
        destruct Ho' as (_ & _ & _ & _ & _ & Ho'). apply Ho'; exact P0.
Qed.
