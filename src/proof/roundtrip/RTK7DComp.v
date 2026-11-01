(* The compression stage of deflate() (c_deflate_compress) keeps Mid7, or ends in stuck7 when deflate_stored
   meets its defect (RTK7Defs.stored_cut): RTDDfXComp.comp_stage_ok (with RTDDfXBd.bd_tail_ok) for the streams
   of RTK7Defs, from core_facts7 and hdr_facts7. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTK7DMid.
Require Import Zlib.proof.roundtrip.RTDDfXComp.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** The compression function's run inside a call *)

(* RTDDfXComp.cs_ub0 for core_facts7 *)
Lemma cs_ub0_7 : forall W s, core_facts7 W -> W s -> ub s = 0 ->
  d_lookahead s = 0 /\ d_strstart s = d_block_start s.
Proof.
  intros W s HC HW Hub. pose proof (cf7_pos _ HC s HW) as Hp. unfold ub in Hub. lia.
Qed.

(* RTDDfXComp.cs_dz for core_facts7: without data consumed so far and in the call, everything read is in blocks *)
Lemma cs_dz7 : forall W s s' k evs flush (Dz X : list Z), core_facts7 W -> W s -> W s' ->
  Forall (ev_ok s flush) evs ->
  k + ub s = sum_len evs + ub s' -> Zlength X = k ->
  (Dz = [] -> d_lookahead s = 0 /\ d_strstart s = d_block_start s) ->
  Dz ++ X = [] -> d_lookahead s' = 0 /\ d_strstart s' = d_block_start s'.
Proof.
  intros W s s' k evs flush Dz X HC HW HW' Hev Hub HX Hdz Hnil.
  apply app_eq_nil in Hnil as [-> ->]. rewrite Zlength_nil in HX. subst k.
  destruct (Hdz eq_refl) as [La Ss].
  pose proof (cs_sum_len_nonneg s flush evs (cf7_prm _ HC s HW) Hev).
  pose proof (cf7_pos _ HC s' HW'). unfold ub in *. lia.
Qed.

(* RTDDfXComp.cs_mid_after for Mid7: the invariant after the compression function, the data grown by the [k]
   bytes consumed (total_in modulo 2^64), the output by [x] *)
Lemma cs_mid_after7 : forall W HI dict wrap D O inb aout tin tout flush s z s3 z' k x,
  Mid7 W HI dict wrap D O inb aout tin tout flush s z -> bytes inb ->
  d_pending s = 0 -> d_last_flush s <> -2 ->
  ph2 dict wrap (D ++ sublist 0 (z_next_in z) inb) (O ++ z_out z) s (z_total_in z) (z_adler z) ->
  zstep wrap z z' k x -> bytes x -> 0 <= z_avail_out z' ->
  W s3 -> outok s3 -> d_wrap s3 = wrap -> d_gzhead s3 = d_gzhead s -> d_bi_valid s3 <= 7 ->
  (d_last_flush s3 = d_last_flush s \/ d_last_flush s3 = -1) ->
  (d_status s3 = BUSY_STATE \/
   (d_status s3 = FINISH_STATE /\ d_lookahead s3 = 0 /\ d_sym_next s3 = 0 /\ flush = Z_FINISH /\
    z_avail_in z' = 0)) ->
  ((D ++ sublist 0 (z_next_in z) inb) ++ sublist (z_next_in z) (z_next_in z + k) inb = [] ->
   d_lookahead s3 = 0 /\ d_strstart s3 = d_block_start s3 /\ (dict = [] -> d_strstart s3 = 0)) ->
  Mid7 W HI dict wrap D O inb aout tin tout flush s3 z'.
Proof.
  intros W HI dict wrap D O inb aout tin tout flush s z s3 z' k x
    HM Hbin Hpend Hlf2 Hph Hzs Hbx Hao' HW3 Hok3 Hwr3 Hgz3 Hbi3 Hlf3 Hst3 Hdz3.
  destruct HM as [Hz [Hil [HDil [Hal [HOal HIa]]]]].
  destruct Hz as (Hin & Hn & Hai & Hti & Hao & Hzo & Hto & Hbo).
  destruct HIa as (HW & Hok & Hwr & Hw2 & Hbd & Hdl & Hlf & Hgz & Htout & HbO & HbD & HDl & Htin & Hfin & _).
  destruct Hzs as (Ein & Hk & En & Eai & Eti & Ead & Eo & Exle & Eao & Eto & Emsg).
  destruct Hph as (_ & _ & _ & HOne & Hchk & H & body & Hhg & HOH).
  rewrite cs_pend_nil, app_nil_r in HOH by exact Hpend.
  rewrite Hin in *.
  set (n := z_next_in z) in *.
  pose proof (Zlength_nonneg D). pose proof (Zlength_nonneg O). pose proof (Zlength_nonneg dict).
  pose proof (Zlength_nonneg x). pose proof (Zlength_nonneg (z_out z)).
  assert (Hx : Zlength x = z_avail_out z - z_avail_out z') by (rewrite Eao; lia).
  assert (HlD1 : Zlength (D ++ sublist 0 n inb) = Zlength D + n)
    by (rewrite Zlength_app, Zlength_sublist by lia; lia).
  assert (Hto' : z_total_out z' = z_total_out z + Zlength x).
  { rewrite Eto. unfold u64. apply Z.mod_small. rewrite Zlength_app in Htout. lia. }
  assert (HD2 : D ++ sublist 0 (n + k) inb = (D ++ sublist 0 n inb) ++ sublist n (n + k) inb).
  { rewrite <- app_assoc, <- (sublist_split 0 n (n + k)) by lia. reflexivity. }
  assert (HlD2 : Zlength (D ++ sublist 0 (n + k) inb) = Zlength D + n + k)
    by (rewrite Zlength_app, Zlength_sublist by lia; lia).
  assert (HbX : bytes (sublist n (n + k) inb)) by (apply Forall_sublist; exact Hbin).
  split; [|split; [exact Hil|split; [exact HDil|split; [exact Hal|split; [exact HOal|]]]]].
  { (* zrun7 *)
    unfold zrun7. rewrite Ein, En, Eai, Eo, Eao, Zlength_app, Hx.
    split; [reflexivity|]. split; [lia|]. split; [lia|].
    split; [rewrite Eti, Hti; unfold u64; rewrite Zplus_mod_idemp_l; f_equal; lia|].
    split; [lia|]. split; [lia|].
    split; [rewrite Hto', Hx; lia|]. apply cs_bytes_app; assumption. }
  rewrite En, Eo, Hto', Ead.
  split; [exact HW3|]. split; [exact Hok3|]. split; [exact Hwr|]. split; [exact Hw2|]. split; [exact Hbd|].
  split; [exact Hdl|]. split; [destruct Hlf3 as [-> | ->]; lia|].
  split; [rewrite Hgz3; exact Hgz|].
  split; [rewrite Htout, !Zlength_app; lia|].
  split; [rewrite app_assoc; apply cs_bytes_app; assumption|].
  split; [rewrite HD2; apply cs_bytes_app; assumption|].
  split; [lia|].
  split.
  { destruct Htin as (k0 & Hk0 & Ek0). exists k0. split; [exact Hk0|].
    rewrite Eti, Ek0, HlD2, HlD1. unfold u64. rewrite Zplus_mod_idemp_l. f_equal. lia. }
  split.
  { intros HF. destruct Hst3 as [HB | (_ & _ & _ & Hfl & Hai')].
    - rewrite HB in HF. discriminate.
    - unfold fin_of. rewrite Hfl, Z.eqb_refl. rewrite En, Eai in *. f_equal. apply sublist_nil_gen. lia. }
  split; [rewrite HD2; exact Hdz3|].
  right. split; [destruct Hlf3 as [-> | ->]; [exact Hlf2|discriminate]|].
  rewrite HD2.
  assert (HO2 : wrap <> 0 -> (O ++ z_out z ++ x) <> []).
  { intros Hw0 Hnil. apply (HOne Hw0). rewrite app_assoc in Hnil. apply app_eq_nil in Hnil. tauto. }
  assert (Hchk2 : chk_ok wrap ((D ++ sublist 0 n inb) ++ sublist n (n + k) inb)
                    (adler_upd wrap (z_adler z) (sublist n (n + k) inb))).
  { apply chk_ok_upd; assumption. }
  assert (HOH2 : (O ++ z_out z ++ x) ++ pend s3 = H ++ (body ++ x ++ pend s3)).
  { rewrite app_assoc, HOH, <- !app_assoc. reflexivity. }
  destruct Hst3 as [HB | (HF & Hla & Hsn & _ & _)].
  - right; left. split; [exact HB|]. split; [exact Hwr3|]. split; [exact Hbi3|]. split; [exact HO2|].
    split; [exact Hchk2|]. exists H, (body ++ x ++ pend s3). split; [exact Hhg|exact HOH2].
  - right; right. split; [exact HF|]. split; [exact Hla|]. split; [exact Hsn|]. split; [exact Hbi3|].
    split; [exact HO2|]. split; [exact Hchk2|]. exists H, (body ++ x ++ pend s3). split; [exact Hhg|].
    left. split; [exact Hwr3|exact HOH2].
Qed.

(** ** The block_done branch (RTDDfXBd for Mid7) *)

(* RTDDfXBd.bd_first_ok for core_facts7: _tr_align / the empty stored block (with the Z_FULL_FLUSH reset) *)
Lemma bd_first_ok7 : forall W s flush,
  core_facts7 W -> W s -> outok s -> quiet s -> d_sym_next s = 0 -> d_lookahead s = 0 ->
  d_strstart s = d_block_start s ->
  exists s2,
    (if flush =? Z_PARTIAL_FLUSH then
       let* om := c_tr_align (d_out s) in Some (set_d_out s om)
     else if negb (flush =? Z_BLOCK) then
       let* om := c_tr_stored_block (d_out s) [] 0 0 in
       let s := set_d_out s om in
       if flush =? Z_FULL_FLUSH then
         let* s := c_clear_hash s in
         if d_lookahead s =? 0 then
           Some (set_d_insert (set_d_block_start (set_d_strstart s 0) 0) 0)
         else Some s
       else Some s
     else Some s) = Some s2 /\
    W s2 /\ outok s2 /\ d_bi_valid s2 <= 7 /\
    d_status s2 = d_status s /\ d_wrap s2 = d_wrap s /\ d_gzhead s2 = d_gzhead s /\
    d_last_flush s2 = d_last_flush s /\ d_lookahead s2 = 0 /\ d_strstart s2 = d_block_start s2 /\
    (d_strstart s2 = d_strstart s \/ d_strstart s2 = 0).
Proof.
  intros W s flush CF HW HO Hq Hsym Hla Hss.
  pose proof (cf7_prm W CF s HW) as HP.
  destruct (flush =? Z_PARTIAL_FLUSH).
  - destruct (tr_align_ok s HP HO Hq Hsym) as (om & E & O1 & C1 & A1 & _ & B1 & _).
    rewrite E. cbn [bind]. eexists. split; [reflexivity|].
    destruct A1 as (A1 & A2 & A3 & A4 & A5 & A6).
    destruct (core_eq_fields _ _ C1) as (_ & _ & _ & _ & F5 & F6 & F7 & _).
    split; [exact (cf7_frame W CF _ _ HW C1)|]. split; [assumption|]. repeat split; first [assumption | congruence | (left; congruence) | (right; reflexivity)].
  - destruct (flush =? Z_BLOCK); cbn [negb].
    + exists s. destruct Hq as (_ & _ & Hb). split; [reflexivity|]. split; [assumption|]. split; [assumption|]. repeat split; first [assumption | (left; reflexivity)].
    + destruct (stored_empty_ok s HP HO Hq Hsym) as (om & E & O1 & C1 & A1 & _ & B1 & _).
      rewrite E. cbn [bind].
      assert (W1 : W (set_d_out s om)) by exact (cf7_frame W CF _ _ HW C1).
      destruct A1 as (A1 & A2 & A3 & A4 & A5 & A6).
      destruct (flush =? Z_FULL_FLUSH).
      * destruct (core_eq_fields _ _ C1) as (_ & _ & _ & _ & F5 & F6 & F7 & _).
        destruct (cf7_full W CF (set_d_out s om) W1 ltac:(congruence) ltac:(congruence))
          as (s1 & E2 & Wf & (G1 & G2 & G3 & G4 & G5 & G6) & Out2 & P2 & _).
        rewrite E2. cbn [bind].
        assert (Hla1 : d_lookahead s1 = 0) by (rewrite (bd_clear_hash_la _ _ E2), F7; exact Hla).
        rewrite (bd_clear_hash_la _ _ E2), F7, Hla. cbn [Z.eqb].
        exists (full_reset s1). split; [reflexivity|].
        split; [exact Wf|]. split.
        { apply bd_outok_full_reset. apply (bd_outok_out_eq _ _ O1 Out2).
          destruct P2 as (_ & _ & _ & _ & P & _). exact P. }
        destruct Out2 as (Q1 & _).
        assert (Hbv : d_bi_valid s1 = d_bi_valid (set_d_out s om)) by (unfold d_bi_valid; rewrite Q1; reflexivity).
        change (d_bi_valid (full_reset s1)) with (d_bi_valid s1).
        change (d_status (full_reset s1)) with (d_status s1).
        change (d_wrap (full_reset s1)) with (d_wrap s1).
        change (d_gzhead (full_reset s1)) with (d_gzhead s1).
        change (d_last_flush (full_reset s1)) with (d_last_flush s1).
        change (d_lookahead (full_reset s1)) with (d_lookahead s1).
        change (d_strstart (full_reset s1)) with 0. change (d_block_start (full_reset s1)) with 0.
        split; [lia|]. repeat split; first [congruence | (right; reflexivity)].
      * destruct (core_eq_fields _ _ C1) as (_ & _ & _ & _ & F5 & F6 & F7 & _).
        eexists. split; [reflexivity|]. split; [assumption|]. split; [assumption|]. split; [lia|].
        repeat split; first [assumption | congruence | (left; congruence) | (right; reflexivity)].
Qed.

(* RTDDfXBd.bd_tail_ok_gen for Mid7, when the state is not in the middle of a gzip header *)
Lemma bd_tail_ok_gen7 : forall W HI dict wrap D O inb aout tin tout flush s z,
  core_facts7 W ->
  Mid7 W HI dict wrap D O inb aout tin tout flush s z ->
  (forall a H k, ~ HI s a H k) ->
  d_status s = BUSY_STATE -> quiet s -> d_sym_next s = 0 -> d_lookahead s = 0 -> d_strstart s = d_block_start s ->
  z_avail_in z = 0 -> flush <> Z_NO_FLUSH -> flush <> Z_FINISH -> 0 <= flush <= 5 ->
  exists s' z' o, bd_tail s z flush = Some (s', z', o) /\ d_gzhead s' = d_gzhead s /\
    Mid7 W HI dict wrap D O inb aout tin tout flush s' z' /\ d_status s' = BUSY_STATE /\
    (o = Some Z_OK \/ (o = None /\ d_pending s' = 0)).
Proof.
  intros W HI dict wrap D O inb aout tin tout flush s z CF M NHI Hst Hq Hsym Hla Hss Hai Hf1 Hf2 Hfr.
  destruct M as (Zr & Sz1 & Sz2 & Sz3 & Sz4 & I).
  destruct I as (HW & HO & Hw & Hw2 & Hbd & Hld & Hlf & Hgz & Htout & HbO & HbD & HDl & Htin & Hfin & Hdz & Hph).
  assert (P2 : d_last_flush s <> -2 /\
    ph2 dict wrap (D ++ sublist 0 (z_next_in z) inb) (O ++ z_out z) s (z_total_in z) (z_adler z)).
  { destruct Hph as [P0 | [Hne [P1 | [P2 | P3]]]].
    - exfalso. destruct P0 as [[[E _]|[E _]] _]; rewrite Hst in E; discriminate.
    - exfalso. destruct P1 as (_ & _ & _ & _ & _ & H & k & HH & _). exact (NHI _ _ _ HH).
    - auto.
    - exfalso. destruct P3 as [E _]. rewrite Hst in E. discriminate. }
  clear Hph. destruct P2 as (Hne & _ & Hdw & _ & HOne & Hchk & H & body & Hhg & Hpend).
  destruct (bd_first_ok7 W s flush CF HW HO Hq Hsym Hla Hss)
    as (s2 & E2 & W2 & O2 & B2 & S2 & Wr2 & G2 & L2 & La2 & Ss2 & St2).
  destruct Zr as (Zin & Hni & Hai' & Hti & Hao0 & Hzo & Hto & Hbz).
  assert (Hzo0 : 0 <= Zlength (z_out z)) by apply Zlength_nonneg.
  assert (HO0 : 0 <= Zlength O) by apply Zlength_nonneg.
  assert (Htout' : z_total_out z = Zlength O + Zlength (z_out z)) by (rewrite Htout, Zlength_app; reflexivity).
  destruct (flush_pending_ok7 s2 z O2 B2 ltac:(lia) ltac:(lia) ltac:(lia))
    as (s3 & x & E3 & Hp & Hx & Bx & O3 & C3 & A3 & B3 & Pd3 & _).
  destruct A3 as (A31 & A32 & A33 & _ & A35 & _).
  assert (W3 : W s3) by exact (cf7_frame W CF _ _ W2 C3).
  destruct (core_eq_fields _ _ C3) as (_ & _ & _ & _ & F35 & F36 & F37 & _).
  assert (La3 : d_lookahead s3 = 0) by congruence.
  assert (Ss3 : d_strstart s3 = d_block_start s3) by congruence.
  assert (St3 : d_strstart s3 = d_strstart s \/ d_strstart s3 = 0) by (destruct St2; [left|right]; congruence).
  set (z3 := mkST (z_in z) (z_next_in z) (z_avail_in z) (z_total_in z) (z_out z ++ x)
                  (z_avail_out z - Zlength x) (z_total_out z + Zlength x) (z_adler z) (z_msg z)) in E3.
  assert (Hps : pend s = []).
  { destruct Hq as (Q1 & Q2 & _). unfold pend. rewrite Q1, Q2. apply sublist_nil. }
  rewrite Hps, app_nil_r in Hpend.
  (* the state after the call, whichever way it ends *)
  assert (MID : forall s4, W s4 -> outok s4 -> d_status s4 = BUSY_STATE -> d_wrap s4 = wrap ->
      d_gzhead s4 = d_gzhead s -> -2 <= d_last_flush s4 <= 5 -> d_last_flush s4 <> -2 -> d_bi_valid s4 <= 7 ->
      pend s4 = pend s3 -> d_lookahead s4 = 0 -> d_strstart s4 = d_block_start s4 ->
      (d_strstart s4 = d_strstart s \/ d_strstart s4 = 0) ->
      Mid7 W HI dict wrap D O inb aout tin tout flush s4 z3).
  { intros s4 W4 O4 S4 Wr4 G4 L4 L4' B4 P4 La4 Ss4 St4.
    assert (Hx0 : 0 <= Zlength x) by apply Zlength_nonneg.
    split; [|split; [exact Sz1|split; [exact Sz2|split; [exact Sz3|split; [exact Sz4|]]]]].
    { unfold zrun7, z3; cbn [z_in z_next_in z_avail_in z_total_in z_out z_avail_out z_total_out].
      rewrite Zlength_app. split; [exact Zin|]. split; [exact Hni|]. split; [exact Hai'|].
      split; [exact Hti|]. split; [lia|]. split; [lia|]. split; [lia|].
      apply Forall_app; auto. }
    assert (Hfz : fin_of flush inb z3 = fin_of flush inb z) by reflexivity.
    rewrite Hfz. unfold Iapi7, z3.
    cbn [z_in z_next_in z_avail_in z_total_in z_out z_avail_out z_total_out z_adler].
    rewrite app_assoc.
    split; [exact W4|]. split; [exact O4|]. split; [exact Hw|]. split; [exact Hw2|]. split; [exact Hbd|].
    split; [exact Hld|]. split; [exact L4|]. split; [rewrite G4; exact Hgz|].
    split; [rewrite Zlength_app; lia|]. split; [apply Forall_app; auto|]. split; [exact HbD|].
    split; [exact HDl|]. split; [exact Htin|]. split; [rewrite S4; intro E; discriminate|].
    split; [intros Hn; split; [assumption|split; [assumption|]];
            intros Hdn; destruct St4 as [E|E]; [rewrite E; exact (proj2 (proj2 (Hdz Hn)) Hdn)|exact E]|].
    right. split; [exact L4'|]. right; left.
    split; [exact S4|]. split; [exact Wr4|]. split; [exact B4|].
    split; [intros Hw0; specialize (HOne Hw0); intro E; apply app_eq_nil in E; tauto|].
    split; [exact Hchk|].
    exists H, (body ++ pend s2). split; [exact Hhg|].
    rewrite P4, <- app_assoc, <- Hp, Hpend, app_assoc. reflexivity. }
  unfold bd_tail.
  match goal with |- context [bind ?X _] => assert (E2' : X = Some s2) by exact E2 end.
  rewrite E2'. cbn [bind]. rewrite E3. cbn [bind].
  destruct (Z.eqb_spec (z_avail_out z3) 0) as [Ez|Ez];
    change (z_avail_out z3) with (z_avail_out z - Zlength x) in Ez.
  - exists (set_d_last_flush s3 (-1)), z3, (Some Z_OK). split; [reflexivity|].
    change (d_gzhead (set_d_last_flush s3 (-1))) with (d_gzhead s3).
    split; [congruence|]. split; [|split; [cbn; congruence|left; reflexivity]].
    apply MID.
    + exact (cf7_frame W CF _ _ W3 (bd_core_eq_lf s3 (-1))).
    + exact (bd_outok_lf s3 (-1) O3).
    + cbn. congruence.
    + cbn. congruence.
    + cbn. congruence.
    + cbn. lia.
    + cbn. lia.
    + change (d_bi_valid (set_d_last_flush s3 (-1))) with (d_bi_valid s3). lia.
    + reflexivity.
    + exact La3.
    + exact Ss3.
    + exact St3.
  - exists s3, z3, None. split; [reflexivity|].
    split; [congruence|]. split; [|split; [congruence|right; split; [reflexivity|lia]]].
    apply MID; try assumption; try congruence; try lia.
Qed.

(* RTDDfXBd.bd_tail_ok for Mid7: _tr_align / the empty stored block, then flush_pending *)
Lemma bd_tail_ok7 : forall W HI dict wrap D O inb aout tin tout flush s z,
  core_facts7 W -> hdr_facts7 HI ->
  Mid7 W HI dict wrap D O inb aout tin tout flush s z ->
  d_status s = BUSY_STATE -> quiet s -> d_sym_next s = 0 -> d_lookahead s = 0 -> d_strstart s = d_block_start s ->
  z_avail_in z = 0 -> flush <> Z_NO_FLUSH -> flush <> Z_FINISH -> 0 <= flush <= 5 ->
  exists s' z' o, bd_tail s z flush = Some (s', z', o) /\ d_gzhead s' = d_gzhead s /\
    Mid7 W HI dict wrap D O inb aout tin tout flush s' z' /\ d_status s' = BUSY_STATE /\
    (o = Some Z_OK \/ (o = None /\ d_pending s' = 0)).
Proof.
  intros W HI dict wrap D O inb aout tin tout flush s z CF HF M Hst.
  apply (bd_tail_ok_gen7 W HI dict wrap D O inb aout tin tout flush s z CF M); [|exact Hst].
  intros a H k HH. destruct (hf7_status HI HF s a H k HH) as (_ & _ & Hs & _).
  rewrite Hst in Hs. destruct Hs as [E|[E|[E|E]]]; discriminate.
Qed.

Ltac cs_states7 := unfold INIT_STATE, GZIP_STATE, EXTRA_STATE, NAME_STATE, COMMENT_STATE, HCRC_STATE,
  BUSY_STATE, FINISH_STATE in *; lia.

(* RTDDfXComp.comp_stage_ok for Mid7: the compression stage runs; it keeps Mid7, or deflate_stored meets its
   defect (stored_cut) and the stream is left stuck in FINISH_STATE with input *)
Lemma comp_stage_ex7 : forall W HI dict wrap D O inb aout tin tout flush s z,
  core_facts7 W -> hdr_facts7 HI -> stored_wbits_stmt -> bytes inb ->
  Mid7 W HI dict wrap D O inb aout tin tout flush s z ->
  d_pending s = 0 -> 0 <= flush <= 5 ->
  (d_status s = BUSY_STATE \/ (d_status s = FINISH_STATE /\ z_avail_in z = 0)) ->
  exists s3 z3 o, c_deflate_compress s z flush = Some (s3, z3, o) /\
  ((d_gzhead s3 = d_gzhead s /\ Mid7 W HI dict wrap D O inb aout tin tout flush s3 z3 /\
    match o with
    | Some c => c = Z_OK
    | None => d_pending s3 = 0 /\ (flush = Z_FINISH -> d_status s3 = FINISH_STATE) /\
              (d_status s3 = BUSY_STATE \/ (d_status s3 = FINISH_STATE /\ z_avail_in z3 = 0))
    end) \/
   (o = None /\ d_w_bits s3 = d_w_bits s /\ stuck7 flush s3 z3)).
Proof.
  intros W HI dict wrap D O inb aout tin tout flush s z HC HH HSW Hbin HM Hpend Hfl Hst.
  pose proof HM as HM0.
  destruct HM as [Hz [Hil [HDil [Hal [HOal HIa]]]]].
  destruct HIa as (HW & Hok & Hwr & Hw2 & Hbd & Hdl & Hlf & Hgz & Htout & HbO & HbD & HDl & HtinR & Hfin & Hdz & Hph).
  destruct Hph as [Hp0 | [Hlf2 [Hp1 | [Hp2 | Hp3]]]].
  - exfalso. destruct Hp0 as [[[Hs _]|[Hs _]] _]; destruct Hst as [Hst|[Hst _]]; cs_states7.
  - exfalso. destruct Hp1 as (_ & _ & _ & _ & _ & H & k & HHI & _).
    destruct (hf7_status HI HH _ _ _ _ HHI) as (_ & _ & Hs & _).
    destruct Hst as [Hst|[Hst _]]; cs_states7.
  - (* BUSY *)
    pose proof Hp2 as Hp2'.
    destruct Hp2' as (HB & Hwrs & Hbi & _ & Hchk & _).
    unfold c_deflate_compress.
    destruct (negb (z_avail_in z =? 0) || negb (d_lookahead s =? 0) ||
              (negb (flush =? Z_NO_FLUSH) && negb (d_status s =? FINISH_STATE))) eqn:Hc.
    2: { exists s, z, None. split; [reflexivity|]. left. split; [reflexivity|]. split; [exact HM0|].
         split; [exact Hpend|]. split; [|left; exact HB].
         intros H4. exfalso. rewrite H4, HB in Hc. simpl in Hc. rewrite orb_true_r in Hc. discriminate. }
    assert (Hq : quiet s).
    { split; [exact Hpend|split; [|exact Hbi]]. destruct Hok as (_ & _ & _ & _ & _ & Hpo). auto. }
    pose proof (mid7_zin_ok7 _ _ _ _ _ _ _ _ _ _ _ _ _ HM0 Hbin) as Hzin.
    assert (Hadp : adler_pre (d_wrap s) (z_adler z)).
    { rewrite Hwrs. eapply chk_ok_pre; eassumption. }
    destruct (cf7_compress W HC s z flush HW Hok Hq Hfl Hzin ltac:(lia) Hadp)
      as (s' & z' & bs & evs & Hcf & Hcp).
    rewrite Hcf. cbn [bind].
    destruct Hcp as [Hcp | (Hl0 & Hf4 & -> & Hai')].
    2: { (* deflate_stored meets its defect: FINISH_STATE with input left *)
         eexists _, _, _. split; [reflexivity|]. right. split; [reflexivity|].
         split; [|split; [exact Hf4|split; [reflexivity|exact Hai']]].
         change (d_w_bits s' = d_w_bits s).
         unfold c_compress_func in Hcf. rewrite Hl0, Z.eqb_refl in Hcf.
         exact (HSW _ _ _ _ _ _ Hcf). }
    destruct Hz as (Hin & Hn & Hai & Hti & Hao & Hzo & Hto & Hbo).
    destruct Hcp as (HW' & Hok' & _ & Hapi & (k & x & Hzs & Hbx & Hubk) & _ & Hev & Hbs).
    destruct Hapi as (Ast & Awr & Agz & _ & Alf & _).
    rewrite Hwrs in Hzs, Awr.
    assert (Hao' : 0 <= z_avail_out z') by (destruct Hzs as (_&_&_&_&_&_&_&Exle&Eao&_); lia).
    assert (Hdz3 : (D ++ sublist 0 (z_next_in z) inb) ++ sublist (z_next_in z) (z_next_in z + k) inb = [] ->
                   d_lookahead s' = 0 /\ d_strstart s' = d_block_start s' /\ (dict = [] -> d_strstart s' = 0)).
    { intros Hnil.
      assert (HdzO : D ++ sublist 0 (z_next_in z) inb = [] -> d_lookahead s = 0 /\ d_strstart s = d_block_start s)
        by (intros E; destruct (Hdz E) as (A & B & _); split; assumption).
      destruct (cs_dz7 W s s' k evs flush (D ++ sublist 0 (z_next_in z) inb)
                  (sublist (z_next_in z) (z_next_in z + k) inb) HC HW HW' Hev Hubk
                  ltac:(destruct Hzs as (_ & Hk & _); rewrite Zlength_sublist; lia) HdzO Hnil) as [La Ss].
      split; [exact La|]. split; [exact Ss|].
      intros Hd0.
      apply app_eq_nil in Hnil as [HD0 Hx0].
      destruct (Hdz HD0) as (La0 & Ss0 & S00).
      assert (Hk0 : k = 0).
      { destruct Hzs as (_ & Hk & _). pose proof (f_equal (@Zlength Z) Hx0) as L.
        rewrite Zlength_nil, Zlength_sublist in L by lia. lia. }
      apply (cf7_still W HC s z flush s' z' bs HW Hok Hq Hfl Hzin ltac:(lia) Hadp Hcf).
      - unfold ub; lia.
      - exact (S00 Hd0).
      - destruct Hzs as (_ & _ & En & _). lia. }
    destruct bs.
    + (* need_more *)
      assert (Hnm : d_bi_valid s' <= 7) by apply Hbs.
      destruct (z_avail_out z' =? 0); (eexists _, _, _; split; [reflexivity|]); left; split; try exact Agz;
        (split; [|reflexivity]);
        (eapply cs_mid_after7; [exact HM0|exact Hbin|exact Hpend|exact Hlf2|exact Hp2|exact Hzs
          |exact Hbx|exact Hao'| | |exact Awr|exact Agz|exact Hnm| |left; rewrite <- HB; exact Ast|exact Hdz3]);
        try exact HW'; try exact Hok'; try (left; exact Alf); try (right; reflexivity).
      eapply (cf7_frame _ HC); [exact HW'|apply cs_core_eq_lf].
    + (* block_done *)
      destruct Hbs as (_ & Hf0 & Hf4 & Hai0 & Hub & Hq' & Hsn).
      assert (HM' : Mid7 W HI dict wrap D O inb aout tin tout flush s' z').
      { eapply cs_mid_after7; [exact HM0|exact Hbin|exact Hpend|exact Hlf2|exact Hp2|exact Hzs
          |exact Hbx|exact Hao'|exact HW'|exact Hok'|exact Awr|exact Agz|apply Hq'|left; exact Alf
          |left; rewrite <- HB; exact Ast|exact Hdz3]. }
      destruct (cs_ub0_7 _ _ HC HW' Hub) as [Hla Hss].
      destruct (bd_tail_ok7 _ _ _ _ _ _ _ _ _ _ _ _ _ HC HH HM' ltac:(rewrite Ast; exact HB) Hq' Hsn Hla Hss
                  Hai0 Hf0 Hf4 Hfl)
        as (s'' & z'' & o & Hbt & Hgz'' & HM'' & Hst'' & Ho).
      exists s'', z'', o. split; [exact Hbt|]. left. split; [rewrite Hgz''; exact Agz|]. split; [exact HM''|].
      destruct Ho as [-> | [-> Hp]]; [reflexivity|].
      split; [exact Hp|]. split; [intros; contradiction|left; exact Hst''].
    + (* finish_started *)
      destruct Hbs as (_ & Hf4 & Hai0 & Hub & Hsn & Hbi0 & Hao0 & _).
      rewrite Hao0, Z.eqb_refl.
      destruct (cs_ub0_7 _ _ HC HW' Hub) as [Hla _].
      eexists _, _, _. split; [reflexivity|]. left. split; [exact Agz|]. split; [|reflexivity].
      eapply cs_mid_after7; [exact HM0|exact Hbin|exact Hpend|exact Hlf2|exact Hp2|exact Hzs
        |exact Hbx|exact Hao'| |exact Hok'|exact Awr|exact Agz| |right; reflexivity
        |right; split; [reflexivity|split; [exact Hla|split; [exact Hsn|split; [exact Hf4|exact Hai0]]]]
        |exact Hdz3].
      * eapply (cf7_frame _ HC); [exact HW'|apply cs_core_eq_status_lf].
      * change (d_bi_valid s' <= 7). lia.
    + (* finish_done *)
      destruct Hbs as (_ & Hf4 & Hai0 & Hub & Hsn & Hq' & Hbi0).
      destruct (cs_ub0_7 _ _ HC HW' Hub) as [Hla _].
      eexists _, _, _. split; [reflexivity|]. left. split; [exact Agz|]. split.
      * eapply cs_mid_after7; [exact HM0|exact Hbin|exact Hpend|exact Hlf2|exact Hp2|exact Hzs
          |exact Hbx|exact Hao'| |exact Hok'|exact Awr|exact Agz| |left; exact Alf
          |right; split; [reflexivity|split; [exact Hla|split; [exact Hsn|split; [exact Hf4|exact Hai0]]]]
          |exact Hdz3].
        -- eapply (cf7_frame _ HC); [exact HW'|apply cs_core_eq_status].
        -- change (d_bi_valid s' <= 7). lia.
      * split; [apply Hq'|]. split; [intros; reflexivity|right; split; [reflexivity|exact Hai0]].
  - (* FINISH: nothing to compress *)
    destruct Hp3 as (HF & Hla & _).
    destruct Hst as [HB | [_ Hai0]]; [exfalso; rewrite HB in HF; cs_states7|].
    unfold c_deflate_compress.
    destruct (negb (z_avail_in z =? 0) || negb (d_lookahead s =? 0) ||
              (negb (flush =? Z_NO_FLUSH) && negb (d_status s =? FINISH_STATE))) eqn:Hc.
    { exfalso. rewrite Hai0, Hla, HF in Hc. simpl in Hc. rewrite andb_false_r in Hc. discriminate. }
    exists s, z, None. split; [reflexivity|]. left. split; [reflexivity|]. split; [exact HM0|].
    split; [exact Hpend|]. split; [intros; exact HF|right; split; [exact HF|exact Hai0]].
Qed.

Lemma comp_stage_ok7 : forall W HI dict wrap D O inb aout tin tout flush s z s3 z3 o,
  core_facts7 W -> hdr_facts7 HI -> stored_wbits_stmt -> bytes inb ->
  Mid7 W HI dict wrap D O inb aout tin tout flush s z ->
  d_pending s = 0 -> 0 <= flush <= 5 ->
  (d_status s = BUSY_STATE \/ (d_status s = FINISH_STATE /\ z_avail_in z = 0)) ->
  c_deflate_compress s z flush = Some (s3, z3, o) ->
  (d_gzhead s3 = d_gzhead s /\ Mid7 W HI dict wrap D O inb aout tin tout flush s3 z3 /\
   match o with
   | Some c => c = Z_OK
   | None => d_pending s3 = 0 /\ (flush = Z_FINISH -> d_status s3 = FINISH_STATE) /\
             (d_status s3 = BUSY_STATE \/ (d_status s3 = FINISH_STATE /\ z_avail_in z3 = 0))
   end) \/
  (o = None /\ d_w_bits s3 = d_w_bits s /\ stuck7 flush s3 z3).
Proof.
  intros W HI dict wrap D O inb aout tin tout flush s z s3 z3 o HC HH HSW Hbin HM Hpend Hfl Hst R.
  destruct (comp_stage_ex7 W HI dict wrap D O inb aout tin tout flush s z HC HH HSW Hbin HM Hpend Hfl Hst)
    as (s3' & z3' & o' & R' & P).
  rewrite R in R'. injection R' as -> -> ->. exact P.
Qed.
