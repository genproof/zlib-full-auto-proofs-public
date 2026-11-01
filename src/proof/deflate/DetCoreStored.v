(** * deflate_stored with up to 2^32 - 1 bytes of output space

    LTCStored2.stored_assembly / stored_ok2 and LTCStillStored.still_stored_ok for [compress_prew]
    (DetCoreKit.v).  The first phase is DetCoreStoredLoop.dsloop_okw (the loop for avail_out < 2^32); the
    other parts (window update, refill, second-phase block) need no output bound.  The proofs are the
    originals with the wide bound. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.DetCoreKit.
Require Import Zlib.proof.deflate.LTCStoredKit Zlib.proof.deflate.LTCStored2 Zlib.proof.deflate.DetCoreStoredLoop Zlib.proof.deflate.LTCStoredSblk Zlib.proof.deflate.LTCStoredWin Zlib.proof.deflate.LTCStoredFill Zlib.proof.deflate.LTCStoredBlk2b Zlib.proof.deflate.LTCStoredChain Zlib.proof.deflate.LTCStillStoredKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** LTCStored2.stored_assembly. *)
Lemma stored_assemblyw : dsloop_stmtw -> dswin_stmt -> fill2_stmt -> blk2_stmt -> stored_specw.
Proof.
  intros HL HWn HF HB s z flush Hpre Hfn.
  destruct Hpre as (HW & Ho & Hq & Hfl & Hz & Hwr & Ha).
  assert (H0 : d_level s = 0) by (apply level0_of; [destruct HW as (Hp & _); exact Hp|exact Hfn]).
  pose proof (zwide_zall z Hz) as Hza.
  assert (Hao : z_avail_out z <= 4294967295) by (destruct Hz as (_ & _ & _ & _ & A & _); lia).
  destruct (HL s z flush HW Ho Hq H0 Hza Ha Hfl Hao)
    as (s1 & z1 & last & evs & k & x & Eloop & K1 & B1 & O1 & Q1 & G1 & Z1 & X1 & Zo1 & A1 & P1 & C1 & F1 & L1).
  rewrite c_deflate_stored_eq. cbv zeta. rewrite Eloop. cbn [bind].
  (* the state after the first phase *)
  pose proof (ob_keep_eq s s1 K1) as E1.
  assert (HW1 : W s1).
  { rewrite E1. destruct G1 as (G1a & G1b & _). apply W_ob; auto. }
  destruct (cp_fields s s1 (cp_ob_eq s s1 K1)) as (SP1 & AP1 & Lv1 & Pb1 & Ws1 & DL1 & St1).
  assert (Ss1 : d_strstart s1 = d_strstart s) by (rewrite E1; reflexivity).
  destruct (W_level0 s1 HW1 ltac:(congruence)) as (La1 & Bs1 & Sy1).
  destruct (W_level0 s HW H0) as (La0 & Bs0 & Sy0).
  pose proof (zall_zstep _ _ _ _ _ Hza Z1 Zo1) as Hza1.
  pose proof (adler_ok_zstep _ _ _ _ _ Hza Ha Z1) as Ha1.
  pose proof Z1 as Z1'. destruct Z1' as (Zi1 & Zk1 & Zn1 & Za1 & _).
  assert (Hk : u32 (z_avail_in z - z_avail_in z1) = k).
  { rewrite Za1. replace (z_avail_in z - (z_avail_in z - k)) with k by lia. unfold u32. apply Z.mod_small.
    destruct Hz as (_ & _ & Hai & _). lia. }
  rewrite Hk.
  (* the window update *)
  pose proof Hza1 as Hza1c. destruct Hza1c as [(Hb1 & Hn1 & Hai1 & Hl1 & _) _].
  destruct (HWn s1 z1 k HW1 ltac:(congruence) Hb1 ltac:(destruct Hza as [(_ & Hn & _) _]; lia) ltac:(lia)
              ltac:(destruct Hz as (_ & _ & Hai & _); lia) ltac:(intros Hk0; rewrite Ss1; auto))
    as (s2 & E2 & HW2 & WK2 & U2).
  rewrite E2. cbn [bind].
  set (s3 := upd_high_water s2).
  pose proof (W_hw s2 HW2) as HW3. fold s3 in HW3.
  assert (CP3 : cp s3 = cp s).
  { unfold s3. rewrite cp_uhw, (cp_win_eq _ _ WK2). apply cp_ob_eq; auto. }
  assert (OP3 : op s3 = op s1). { unfold s3. rewrite op_uhw. apply op_win_eq; auto. }
  destruct (cp_fields s s3 CP3) as (SP3 & AP3 & Lv3 & Pb3 & Ws3 & DL3 & St3).
  destruct (op_fields s1 s3 OP3 ltac:(congruence)) as (Ok3 & Qk3 & Gb3 & Bv3 & Sh3 & Pd3).
  assert (U3 : ub s3 = ub s1) by (unfold s3; rewrite ub_uhw; auto).
  destruct (W_level0 s3 HW3 ltac:(congruence)) as (La3 & Bs3 & Sy3).
  destruct L1 as [(Lz & Fl0 & Hfin) | (Lz & Lev & Ffin & Ai1 & Bs1' & Bv1)].
  2:{ (* the first phase finished the stream *)
    subst last. cbn [Z.eqb negb Pos.eqb].
    destruct (bu_fields s3) as (Okb & Qkb & Gbb & Bvb & Ubb & Syb).
    exists (set_d_bi_used s3 8), z1, finish_done, evs. split; [reflexivity|].
    destruct (cp_fields s (set_d_bi_used s3 8) ltac:(rewrite cp_bu; exact CP3)) as (SPb & APb & _).
    assert (Ub1 : ub s1 = 0) by (unfold ub; lia).
    split; [apply W_bu; auto; congruence|].
    split; [auto|]. split; [exact SPb|]. split; [exact APb|].
    split; [exists k, x; split; [exact Z1|]; split; [exact X1|]; rewrite Ubb, U3; exact A1|].
    split; [rewrite Gbb, Gb3; exact C1|].
    split; [exact F1|].
    split; [exact Lev|]. split; [exact Ffin|]. split; [exact Ai1|]. split; [rewrite Ubb, U3; exact Ub1|].
    split; [rewrite Syb; exact Sy3|]. split; [auto|]. rewrite Bvb, Bv3; exact Bv1. }
  subst last. cbn [Z.eqb negb].
  destruct (negb (flush =? Z_NO_FLUSH) && negb (flush =? Z_FINISH) && (z_avail_in z1 =? 0) &&
            (d_strstart s3 =? d_block_start s3)) eqn:EB.
  { (* block_done *)
    rewrite !andb_true_iff, !negb_true_iff, !Z.eqb_neq, !Z.eqb_eq in EB.
    destruct EB as (((N1 & N2) & Ai1) & Sb3).
    exists s3, z1, block_done, evs. split; [reflexivity|].
    split; [exact HW3|]. split; [auto|]. split; [exact SP3|]. split; [exact AP3|].
    split; [exists k, x; split; [exact Z1|]; split; [exact X1|]; rewrite U3; exact A1|].
    split; [rewrite Gb3; exact C1|].
    split; [exact F1|].
    split; [exact Fl0|]. split; [exact N1|]. split; [exact N2|]. split; [exact Ai1|].
    split; [unfold ub; lia|]. split; [auto|]. exact Sy3. }
  (* the second phase *)
  assert (Wr3 : d_wrap s3 = d_wrap s) by (destruct AP3 as (_ & Wr & _); exact Wr).
  destruct (HF s3 z1 HW3 ltac:(congruence) Hza1 ltac:(rewrite Wr3; exact Ha1))
    as (s4 & z4 & k4 & EF & HW4 & WK4 & Z4 & U4).
  rewrite Wr3 in Z4. rewrite EF.
  assert (CP4 : cp s4 = cp s) by (rewrite (cp_win_eq _ _ WK4); exact CP3).
  assert (OP4 : op s4 = op s1) by (rewrite (op_win_eq _ _ WK4); exact OP3).
  destruct (cp_fields s s4 CP4) as (SP4 & AP4 & Lv4 & Pb4 & Ws4 & DL4 & St4).
  destruct (op_fields s1 s4 OP4 ltac:(congruence)) as (Ok4 & Qk4 & Gb4 & Bv4 & Sh4 & Pd4).
  destruct (W_level0 s4 HW4 ltac:(congruence)) as (La4 & Bs4 & Sy4).
  pose proof Z4 as Z4'. destruct Z4' as (Zi4 & Zk4 & Zn4 & Za4 & Zt4 & Zad4 & Zo4 & Zle4 & Zao4 & Zto4 & Zm4).
  rewrite Zlength_nil in Zao4, Zto4.
  assert (Hza4 : zall z4) by (apply (zall_zstep _ _ _ _ _ Hza1 Z4); lia).
  pose proof (adler_ok_zstep _ _ _ _ _ Hza1 Ha1 Z4) as Ha4.
  assert (Hfin4 : flush = Z_FINISH ->
            z_avail_out z4 < stored_hdr s4 + (d_strstart s4 - d_block_start s4) + z_avail_in z4).
  { intros Hf. specialize (Hfin Hf). rewrite Sh4, Zao4, Za4.
    unfold ub in U4, U3. rewrite La4, La3 in U4. rewrite La3, La1 in U3. lia. }
  assert (Wr4 : d_wrap s4 = d_wrap s) by (destruct AP4 as (_ & Wr & _); exact Wr).
  destruct (HB s4 z4 flush HW4 (Ok4 O1) (Qk4 Q1) ltac:(congruence) Hza4 ltac:(rewrite Wr4; exact Ha4) Hfl Hfin4)
    as (s5 & z5 & last2 & evs2 & x2 & EB2 & HW5 & O5 & K5 & Z5 & X5 & A5 & C5 & F5 & L5).
  rewrite Wr4 in Z5. rewrite EB2.
  assert (CP5 : cp s5 = cp s) by (rewrite (cp_ob_eq _ _ K5); exact CP4).
  destruct (cp_fields s s5 CP5) as (SP5 & AP5 & Lv5 & Pb5 & Ws5 & DL5 & St5).
  destruct (W_level0 s5 HW5 ltac:(congruence)) as (La5 & Bs5 & Sy5).
  assert (Zall : zstep (d_wrap s) z z5 (k + k4 + 0) ((x ++ []) ++ x2)).
  { destruct Hza as [Hzi _]. eapply zstep_trans; [exact Hzi|exact Ha| |exact Z5].
    eapply zstep_trans; [exact Hzi|exact Ha|exact Z1|exact Z4]. }
  assert (Xall : bytes ((x ++ []) ++ x2)) by (rewrite app_nil_r; apply Forall_app; split; [exact X1|exact X5]).
  assert (Tz4 : z_total_out z4 = z_total_out z1).
  { rewrite Zto4, Z.add_0_r. apply u64_id. destruct Hza1 as [_ (_ & T1 & T2)]. lia. }
  assert (Call : ev_chain (Gb s (z_total_out z)) (evs ++ evs2) (Gb s5 (z_total_out z5))).
  { eapply ev_chain_app; [exact C1|]. rewrite Gb4, Tz4 in C5. exact C5. }
  assert (Fall : Forall (ev_ok s flush) (evs ++ evs2)).
  { apply Forall_app. split; [exact F1|]. eapply ev_ok_cp; [exact CP4|exact F5]. }
  assert (Aall : k + k4 + 0 + ub s = sum_len (evs ++ evs2) + ub s5).
  { rewrite sum_len_app. lia. }
  destruct L5 as [(Lz2 & Fl2 & Bv2) | (Lz2 & Lev2 & Ffin & Ai4 & Ub5 & Bv5 & Ao5)].
  - subst last2. cbn [Z.eqb].
    exists s5, z5, need_more, (evs ++ evs2). split; [reflexivity|].
    split; [exact HW5|]. split; [exact O5|]. split; [exact SP5|]. split; [exact AP5|].
    split; [exists (k + k4 + 0), ((x ++ []) ++ x2); auto|].
    split; [exact Call|]. split; [exact Fall|].
    split; [apply Forall_app; auto|]. split; [exact Bv2|]. right; right; exact H0.
  - subst last2. cbn [Z.eqb].
    destruct (bu_fields s5) as (Okb & Qkb & Gbb & Bvb & Ubb & Syb).
    destruct (cp_fields s (set_d_bi_used s5 8) ltac:(rewrite cp_bu; exact CP5)) as (SPb & APb & _).
    pose proof Z5 as Z5'. destruct Z5' as (_ & _ & _ & Za5 & _).
    exists (set_d_bi_used s5 8), z5, finish_started, (evs ++ evs2). split; [reflexivity|].
    split; [apply W_bu; auto; congruence|].
    split; [auto|]. split; [exact SPb|]. split; [exact APb|].
    split; [exists (k + k4 + 0), ((x ++ []) ++ x2); rewrite Ubb; auto|].
    split; [rewrite Gbb; exact Call|]. split; [exact Fall|].
    split; [apply last_ev_app; auto|]. split; [exact Ffin|]. split; [lia|].
    split; [rewrite Ubb; exact Ub5|]. split; [rewrite Syb; exact Sy5|]. split; [rewrite Bvb; exact Bv5|].
    split; [exact Ao5|]. intros Hn; congruence.
Qed.

(** LTCStored2.stored_ok2. *)
Theorem stored_ok2w : fpend_spec2 -> stored_specw.
Proof.
  intros _. apply stored_assemblyw.
  - exact (dsloop_okw LTCStoredSblk.sblk_ok).
  - exact (LTCStoredWin.dswin_ok LTCStoredChain.chain_parts_ok).
  - exact (LTCStoredFill.fill2_ok LTCStoredChain.chain_parts_ok).
  - exact (LTCStoredBlk2b.blk2_ok2 LTCStoredSblk.sblk_ok).
Qed.

(** LTCStillStored.still_stored_ok. *)
Theorem still_stored_okw : fill_spec -> fpend_spec2 -> stored_specw ->
  forall s z flush, compress_prew s z flush -> still_at s -> fn_of s = 0 -> still_concl c_deflate_stored s z flush.
Proof.
  intros _ _ _ s z flush Hpre (Hst & Hbs & Hla) Hfn s' z' bs H Hni.
  destruct Hpre as (HW & _ & _ & _ & Hz & _).
  destruct HW as (Hprm & _).
  destruct Hprm as (Hwb & Hws & _).
  assert (Hw0 : 0 < d_w_size s) by (rewrite Hws; apply Z.pow_pos_nonneg; lia).
  destruct Hz as (_ & Hni0 & Hai & _).
  rewrite c_deflate_stored_eq in H. cbn zeta in H.
  destruct (loop FUEL _ (s, z)) as [[[s1 z1] l]|] eqn:EL; cbn [bind] in H; [|discriminate H].
  apply loop_runs in EL.
  pose proof (runs_sv (z_next_in z + z_avail_in z) (z_next_in z) (d_w_size s) _ _ _ _ EL) as Hsv.
  cbn beta iota in Hsv.
  specialize (Hsv ltac:(unfold sv; cbn [fst snd]; lia)).
  destruct Hsv as (H1 & H2 & H3 & H4 & H5 & H6); cbn [fst snd] in *.
  destruct (c_ds_window s1 z1 _) as [s2|] eqn:EW; cbn [bind] in H; [|discriminate H].
  assert (Hcase : z_next_in z1 = z_next_in z -> s2 = s1).
  { intros E. apply (win0_still _ z1). rewrite <- EW. f_equal.
    replace (z_avail_in z - z_avail_in z1) with 0 by lia. reflexivity. }
  pose proof (uhw_still s1) as (U1 & U2 & U3).
  destruct (negb (l =? 0)).
  { injection H; intros; subst. rewrite (Hcase Hni). cbn. rewrite U1. exact H1. }
  destruct (_ && _ && _ && _).
  { injection H; intros; subst. rewrite (Hcase Hni). rewrite U1. exact H1. }
  apply fill2_still in H; [|lia].
  destruct H as (s3 & z3 & H & Hz3a & Hz3b & Hz3c).
  apply blk2_still in H. destruct H as (s4 & z4 & l4 & H & Hz4 & Hs4).
  assert (E1 : z_next_in z4 = z_next_in z') by (destruct (l4 =? 0); injection H; intros; subst; reflexivity).
  assert (E2 : d_strstart s' = d_strstart s4) by (destruct (l4 =? 0); injection H; intros; subst; reflexivity).
  assert (E : z_next_in z1 = z_next_in z) by lia.
  specialize (Hcase E). subst s2.
  rewrite E2, Hs4, Hz3c; [rewrite U1; exact H1| |lia].
  rewrite U2, U3, H2, H3. rewrite Z.geb_leb; apply Z.leb_gt; lia.
Qed.
