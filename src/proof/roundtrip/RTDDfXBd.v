(* RT-D part DEFLATE: copy of RTDLTApiBd.v with the output space bound aout <= 2097152 (kfacts) instead of 1048576. *)
(** * deflate_api theory: the block_done branch of the compression stage

    [bd_tail] (LTApiDefs): _tr_align (Z_PARTIAL_FLUSH), the empty stored block (Z_SYNC_FLUSH, Z_FULL_FLUSH, with
    CLEAR_HASH and the reset of the positions for Z_FULL_FLUSH: [cf_full]), nothing (Z_BLOCK), then
    flush_pending. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDLTApiOut Zlib.proof.roundtrip.RTDLTApiArith.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** Helpers *)

Lemma bd_outok_lf : forall s v, outok s -> outok (set_d_last_flush s v).
Proof. intros [] v H; exact H. Qed.

Lemma bd_outok_full_reset : forall s, outok s -> outok (full_reset s).
Proof. intros [] H; exact H. Qed.

Lemma bd_core_eq_lf : forall s v, core_eq s (set_d_last_flush s v).
Proof.
  intros s v. pose proof (core_eq_api_setters s (d_status s) v (d_wrap s) (d_gzhead s)) as H.
  destruct s; exact H.
Qed.

Lemma bd_outok_out_eq : forall s s', outok s -> out_eq s s' ->
  d_pending_buf_size s' = d_pending_buf_size s -> outok s'.
Proof.
  intros s s' H (E1 & E2 & E3) E4. unfold outok, d_pb, d_pending in *.
  rewrite E1, E2, E3, E4. exact H.
Qed.

Lemma bd_clear_hash_la : forall s s', c_clear_hash s = Some s' -> d_lookahead s' = d_lookahead s.
Proof.
  intros s s' H. unfold c_clear_hash, bind in H.
  destruct (wr (d_head s) (u32 (d_hash_size s - 1)) NIL); [|discriminate].
  unfold guard in H. destruct (_ && _); [|discriminate].
  inversion H; subst. destruct s; reflexivity.
Qed.

(** The first part of the block_done branch: _tr_align / the empty stored block (with the Z_FULL_FLUSH reset). *)
Lemma bd_first_ok : forall W s flush,
  core_facts W -> W s -> outok s -> quiet s -> d_sym_next s = 0 -> d_lookahead s = 0 ->
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
  pose proof (cf_prm W CF s HW) as HP.
  destruct (flush =? Z_PARTIAL_FLUSH).
  - destruct (tr_align_ok s HP HO Hq Hsym) as (om & E & O1 & C1 & A1 & _ & B1 & _).
    rewrite E. cbn [bind]. eexists. split; [reflexivity|].
    destruct A1 as (A1 & A2 & A3 & A4 & A5 & A6).
    destruct (core_eq_fields _ _ C1) as (_ & _ & _ & _ & F5 & F6 & F7 & _).
    split; [exact (cf_frame W CF _ _ HW C1)|]. split; [assumption|]. repeat split; first [assumption | congruence | (left; congruence) | (right; reflexivity)].
  - destruct (flush =? Z_BLOCK); cbn [negb].
    + exists s. destruct Hq as (_ & _ & Hb). split; [reflexivity|]. split; [assumption|]. split; [assumption|]. repeat split; first [assumption | (left; reflexivity)].
    + destruct (stored_empty_ok s HP HO Hq Hsym) as (om & E & O1 & C1 & A1 & _ & B1 & _).
      rewrite E. cbn [bind].
      assert (W1 : W (set_d_out s om)) by exact (cf_frame W CF _ _ HW C1).
      destruct A1 as (A1 & A2 & A3 & A4 & A5 & A6).
      destruct (flush =? Z_FULL_FLUSH).
      * destruct (core_eq_fields _ _ C1) as (_ & _ & _ & _ & F5 & F6 & F7 & _).
        destruct (cf_full W CF (set_d_out s om) W1 ltac:(congruence) ltac:(congruence))
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

(** [bd_tail_ok] when the state is not in the middle of a gzip header ([ph1]). *)
Lemma bd_tail_ok_gen : forall W HI dict wrap D O inb aout tin tout flush s z,
  core_facts W ->
  Mid W HI dict wrap D O inb aout tin tout flush s z ->
  (forall a H k, ~ HI s a H k) ->
  d_status s = BUSY_STATE -> quiet s -> d_sym_next s = 0 -> d_lookahead s = 0 -> d_strstart s = d_block_start s ->
  z_avail_in z = 0 -> flush <> Z_NO_FLUSH -> flush <> Z_FINISH -> 0 <= flush <= 5 -> aout <= 2097152 ->
  exists s' z' o, bd_tail s z flush = Some (s', z', o) /\ d_gzhead s' = d_gzhead s /\
    Mid W HI dict wrap D O inb aout tin tout flush s' z' /\ d_status s' = BUSY_STATE /\
    (o = Some Z_OK \/ (o = None /\ d_pending s' = 0)).
Proof.
  intros W HI dict wrap D O inb aout tin tout flush s z CF M NHI Hst Hq Hsym Hla Hss Hai Hf1 Hf2 Hfr Hao.
  destruct M as (Zr & Sz1 & Sz2 & I).
  destruct I as (HW & HO & Hw & Hw2 & Hbd & Hld & Hlf & Hgz & Htout & HbO & HbD & Htin & Hfin & Hdz & Hph).
  assert (P2 : d_last_flush s <> -2 /\
    ph2 dict wrap (D ++ sublist 0 (z_next_in z) inb) (O ++ z_out z) s (z_total_in z) (z_adler z)).
  { destruct Hph as [P0 | [Hne [P1 | [P2 | P3]]]].
    - exfalso. destruct P0 as [[[E _]|[E _]] _]; rewrite Hst in E; discriminate.
    - exfalso. destruct P1 as (_ & _ & _ & _ & _ & H & k & HH & _). exact (NHI _ _ _ HH).
    - auto.
    - exfalso. destruct P3 as [E _]. rewrite Hst in E. discriminate. }
  clear Hph. destruct P2 as (Hne & _ & Hdw & _ & HOne & Hchk & H & body & Hhg & Hpend).
  destruct (bd_first_ok W s flush CF HW HO Hq Hsym Hla Hss)
    as (s2 & E2 & W2 & O2 & B2 & S2 & Wr2 & G2 & L2 & La2 & Ss2 & St2).
  destruct Zr as (Zin & Hni & Hai' & Hti & Hao0 & Hzo & Hto & Hbz).
  assert (Hzo0 : 0 <= Zlength (z_out z)) by apply Zlength_nonneg.
  assert (HO0 : 0 <= Zlength O) by apply Zlength_nonneg.
  assert (Htout' : z_total_out z = Zlength O + Zlength (z_out z)) by (rewrite Htout, Zlength_app; reflexivity).
  destruct (flush_pending_ok s2 z O2 B2 ltac:(lia) ltac:(lia))
    as (s3 & x & E3 & Hp & Hx & Bx & O3 & C3 & A3 & B3 & Pd3 & _).
  destruct A3 as (A31 & A32 & A33 & _ & A35 & _).
  assert (W3 : W s3) by exact (cf_frame W CF _ _ W2 C3).
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
      Mid W HI dict wrap D O inb aout tin tout flush s4 z3).
  { intros s4 W4 O4 S4 Wr4 G4 L4 L4' B4 P4 La4 Ss4 St4.
    assert (Hx0 : 0 <= Zlength x) by apply Zlength_nonneg.
    split; [|split; [exact Sz1|split; [exact Sz2|]]].
    { unfold zrun, z3; cbn [z_in z_next_in z_avail_in z_total_in z_out z_avail_out z_total_out].
      rewrite Zlength_app. split; [exact Zin|]. split; [exact Hni|]. split; [exact Hai'|].
      split; [exact Hti|]. split; [lia|]. split; [lia|]. split; [lia|].
      apply Forall_app; auto. }
    assert (Hfz : fin_of flush inb z3 = fin_of flush inb z) by reflexivity.
    rewrite Hfz. unfold Iapi, z3.
    cbn [z_in z_next_in z_avail_in z_total_in z_out z_avail_out z_total_out z_adler].
    rewrite app_assoc.
    split; [exact W4|]. split; [exact O4|]. split; [exact Hw|]. split; [exact Hw2|]. split; [exact Hbd|].
    split; [exact Hld|]. split; [exact L4|]. split; [rewrite G4; exact Hgz|].
    split; [rewrite Zlength_app; lia|]. split; [apply Forall_app; auto|]. split; [exact HbD|].
    split; [exact Htin|]. split; [rewrite S4; intro E; discriminate|].
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
    + exact (cf_frame W CF _ _ W3 (bd_core_eq_lf s3 (-1))).
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

Lemma bd_tail_ok : forall W HI dict wrap D O inb aout tin tout flush s z,
  core_facts W -> hdr_facts HI ->
  Mid W HI dict wrap D O inb aout tin tout flush s z ->
  d_status s = BUSY_STATE -> quiet s -> d_sym_next s = 0 -> d_lookahead s = 0 -> d_strstart s = d_block_start s ->
  z_avail_in z = 0 -> flush <> Z_NO_FLUSH -> flush <> Z_FINISH -> 0 <= flush <= 5 -> aout <= 2097152 ->
  exists s' z' o, bd_tail s z flush = Some (s', z', o) /\ d_gzhead s' = d_gzhead s /\
    Mid W HI dict wrap D O inb aout tin tout flush s' z' /\ d_status s' = BUSY_STATE /\
    (o = Some Z_OK \/ (o = None /\ d_pending s' = 0)).
Proof.
  intros W HI dict wrap D O inb aout tin tout flush s z CF HF M Hst.
  apply (bd_tail_ok_gen W HI dict wrap D O inb aout tin tout flush s z CF M); [|exact Hst].
  intros a H k HH. destruct (hf_status HI HF s a H k HH) as (_ & _ & Hs & _).
  rewrite Hst in Hs. destruct Hs as [E|[E|[E|E]]]; discriminate.
Qed.
