(* RT-D part STORED, interface v2: deflate_stored's functional spec.
   Parts (statements RTDStoredKit.v): RTDStored{Chain,Loop,Win,Fill,Blk}.v; here the assembly over the
   safety theory (RTDLTCStored2.v: the same cut of c_deflate_stored). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDStoredKit.
Require Zlib.proof.roundtrip.RTDLTCStored2.
Require Zlib.proof.roundtrip.RTDStoredChain Zlib.proof.roundtrip.RTDStoredLoop Zlib.proof.roundtrip.RTDStoredWin Zlib.proof.roundtrip.RTDStoredFill Zlib.proof.roundtrip.RTDStoredBlk.
Import ListNotations.
Local Open Scope Z_scope.

Import RTDLTCStored2.

(** ** Encoding of a run of blocks cut in two *)

Lemma enc_from_app p a b fin : b <> [] \/ fin = false ->
  enc_from p (a ++ b) fin = enc_from p a false ++ enc_from (p + Zlength (enc_from p a false)) b fin.
Proof.
  revert p. induction a as [|x r IH]; intros p Hb; cbn [app enc_from].
  - rewrite Zlength_nil, Z.add_0_r. reflexivity.
  - assert (E : (fin && match r ++ b with [] => true | _ => false end) =
                (false && match r with [] => true | _ => false end)).
    { destruct Hb as [Hb|Hb]; [|subst fin; reflexivity].
      destruct (r ++ b) eqn:E; [apply app_eq_nil in E; destruct E; contradiction|].
      rewrite andb_false_r. reflexivity. }
    rewrite E, IH by exact Hb. rewrite <- app_assoc, Zlength_app, Z.add_assoc. reflexivity.
Qed.

Lemma enc_out_app p a b fin : b <> [] \/ fin = false ->
  enc_out p (a ++ b) fin = enc_out p a false ++ enc_out (p + Zlength (enc_out p a false)) b fin.
Proof.
  intros Hb. unfold enc_out. rewrite enc_from_app by exact Hb.
  destruct fin; [|reflexivity]. rewrite <- app_assoc, Zlength_app, Z.add_assoc. reflexivity.
Qed.

(** ** Stored blocks *)

Lemma expand_app out a b : F.expand out (a ++ b) = F.expand (F.expand out a) b.
Proof. unfold F.expand. apply fold_left_app. Qed.

Lemma expand_stored bl : forall out, F.expand out (map F.Stored bl) = out ++ concat bl.
Proof.
  induction bl as [|d r IH]; intros out; cbn [map concat].
  - rewrite app_nil_r. reflexivity.
  - unfold F.expand in *. cbn [fold_left F.block_data]. rewrite IH, app_assoc. reflexivity.
Qed.

Lemma blocks_ok_app w a b : forall out,
  F.blocks_ok w out a -> F.blocks_ok w (F.expand out a) b -> F.blocks_ok w out (a ++ b).
Proof.
  induction a as [|x r IH]; intros out Ha Hb; [exact Hb|].
  destruct Ha as [H1 H2]. split; [exact H1|]. apply IH; [exact H2|exact Hb].
Qed.

Lemma blocks_ok_stored w bl : forall out,
  Forall (fun d => Zlength d <= 65535) bl -> Forall F.byte_ok (concat bl) -> F.blocks_ok w out (map F.Stored bl).
Proof.
  induction bl as [|d r IH]; intros out Hl Hb; [exact I|].
  inversion Hl; subst. cbn [concat] in Hb. apply Forall_app in Hb. destruct Hb as [B1 B2].
  split; [split; assumption|]. apply IH; assumption.
Qed.

(** ** The window and the history *)

Lemma kwin_slice H s i j : kwin H s -> 0 <= i <= j -> j <= d_strstart s + d_lookahead s ->
  j <= Zlength (mb_val (d_window s)) ->
  sublist i j (mb_val (d_window s)) =
  sublist (Zlength H - (d_strstart s + d_lookahead s) + i) (Zlength H - (d_strstart s + d_lookahead s) + j) H.
Proof.
  intros [Hl Hw] Hij Hj Hz. apply list_solver.Znth_eq_ext.
  - rewrite !Zlength_sublist by lia. lia.
  - intros n Hn. rewrite Zlength_sublist in Hn by lia.
    rewrite !Znth_sublist by lia. rewrite Hw by lia. f_equal. lia.
Qed.

Lemma kwin_frame H s s' : d_strstart s' = d_strstart s -> d_lookahead s' = d_lookahead s ->
  d_window s' = d_window s -> kwin H s -> kwin H s'.
Proof. intros E1 E2 E3. unfold kwin. rewrite E1, E2, E3. auto. Qed.

Lemma khash_ob s o m po b : khash (ob_set s o m po b) <-> khash s.
Proof. apply iff_refl. Qed.

Lemma khash_uhw s : khash (upd_high_water s) <-> khash s.
Proof. unfold upd_high_water. destruct (_ <? _); apply iff_refl. Qed.

Lemma khash_bu s : khash (set_d_bi_used s 8) <-> khash s.
Proof. apply iff_refl. Qed.

Lemma uhw_fields s : d_strstart (upd_high_water s) = d_strstart s /\ d_block_start (upd_high_water s) = d_block_start s /\
  d_lookahead (upd_high_water s) = d_lookahead s /\ d_window (upd_high_water s) = d_window s /\
  d_w_bits (upd_high_water s) = d_w_bits s.
Proof. unfold upd_high_water. destruct (_ <? _); repeat split. Qed.

Lemma pend_op s s' : op s' = op s -> pend s' = pend s /\ bibits s' = bibits s.
Proof.
  unfold op. intros E. injection E. intros E3 E2 E1.
  unfold pend, bibits, d_pending, d_bi_valid. rewrite E1, E3. auto.
Qed.

Lemma pend_quiet s : quiet s -> pend s = [].
Proof. intros (P & _ & _). unfold pend. rewrite P, Z.add_0_r, sublist_nil. reflexivity. Qed.

Lemma sum_len_nonneg0 s0 flush evs : d_level s0 = 0 -> Forall (ev_ok s0 flush) evs -> 0 <= sum_len evs.
Proof.
  intros H0. induction evs as [|e r IH]; intros Hf; [unfold sum_len; cbn; lia|].
  inversion Hf; subst. unfold sum_len in *. cbn [fold_right]. specialize (IH H3).
  destruct e as [g t sy buf sl last|g len last]; cbn [ev_len]; unfold ev_ok in H2.
  - destruct H2 as (L & _). lia.
  - destruct H2 as (_ & L & _). lia.
Qed.

Lemma bytes_bits_app a b : F.bytes_bits (a ++ b) = F.bytes_bits a ++ F.bytes_bits b.
Proof. unfold F.bytes_bits. apply flat_map_app. Qed.

(** ** kcore2 at level 0 from the window, the hash state and the blocks *)

Lemma kcore2_level0 dict D BS s : W s -> d_level s = 0 -> kwin (dict ++ D) s -> khash s ->
  F.blocks_ok (2 ^ d_w_bits s) dict BS ->
  F.expand dict BS = sublist 0 (Zlength (dict ++ D) - d_strstart s + d_block_start s) (dict ++ D) ->
  kcore2 dict D BS [] s.
Proof.
  intros HW H0 Kw Kh Kb Ke. destruct (W_level0 s HW H0) as (La & _ & _).
  pose proof HW as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hm1) & _ & syms & Ht).
  assert (Ef : fn_of s = 0) by (unfold fn_of; rewrite H0; reflexivity).
  assert (Hs : syms = []) by (destruct Ht as (_ & _ & _ & T & _); exact (T H0)). subst syms.
  split; [|exact Kh].
  unfold kdata2. cbv zeta. rewrite La, Z.add_0_r, H0. cbn [Z.eqb].
  replace (Zlength (dict ++ D) - d_strstart s + d_block_start s)
    with (Zlength (dict ++ D) - d_strstart s + d_block_start s) in Ke by lia.
  split; [exact Kw|]. split.
  { intros Ha. destruct (Hm1 Ha) as (F2 & _). rewrite Ef in F2. discriminate. }
  split; [exact Ht|]. split; [exact Kb|]. split; [rewrite Ke; f_equal; lia|].
  split; [exact I|]. cbn [map]. unfold F.syms_data. cbn [fold_left]. rewrite Ke. f_equal; lia.
Qed.

Lemma sublist_prefix_app (H c : list Z) m : 0 <= m <= Zlength H -> (c = [] \/ m = Zlength H) ->
  sublist 0 (m + Zlength c) (H ++ c) = sublist 0 m H ++ c.
Proof.
  intros Hm [E|E]; rewrite E.
  - rewrite app_nil_r, Zlength_nil, Z.add_0_r, app_nil_r. reflexivity.
  - rewrite <- Zlength_app, !sublist_same by lia. reflexivity.
Qed.

Lemma sublist_prefix_le (H c : list Z) m : 0 <= m <= Zlength H -> sublist 0 m (H ++ c) = sublist 0 m H.
Proof. intros Hm. rewrite sublist_app1 by lia. reflexivity. Qed.

Lemma stored2_assembly :
  chainh_stmt -> floop_stmt -> fwin_stmt -> ffill2_stmt -> fblk2_stmt -> comp_fspec2 0 c_deflate_stored.
Proof.
  intros HC FL FW FF FB s z flush s' z' bs dict D BS syms p HW3 Ho Hq Hfl Hz Hwr Hap Hfn Hdict HD HK Hp Hpm Hrun.
  destruct HW3 as [[HW _] _].
  pose proof (adler_pre_ok _ _ Hap) as Ha.
  assert (H0 : d_level s = 0) by (apply level0_of; [exact (RTDLTCMisc.W_prm s HW)|exact Hfn]).
  pose proof (zin_ok_zall z Hz) as Hza.
  assert (Hao : z_avail_out z <= 1073741824) by (destruct Hz as (_ & _ & _ & _ & A & _); lia).
  destruct (RTDLTCStoredLoop.dsloop_ok'' RTDLTCStoredSblk.sblk_ok s z flush HW Ho Hq H0 Hza Ha Hfl Hao)
    as (s1 & z1 & last & evs & k & x & Eloop & K1 & B1 & O1 & Q1 & G1 & Z1 & X1 & Zo1 & A1 & P1 & C1 & F1 & L1).
  destruct (FL s z flush s1 z1 last p HW Ho Hq H0 Hza Ha Hfl Hao Hp Hpm Eloop)
    as (k' & x' & bl1 & Z1' & Bl1 & Cb1 & Bi1 & Ne1 & Al1).
  assert (Ek : k' = k) by (destruct Z1 as (_ & _ & N1 & _); destruct Z1' as (_ & _ & N2 & _); lia).
  subst k'.
  assert (Ex : x' = x).
  { destruct Z1 as (_ & _ & _ & _ & _ & _ & O & _); destruct Z1' as (_ & _ & _ & _ & _ & _ & O' & _).
    rewrite O in O'. symmetry. eapply app_inv_head; exact O'. }
  subst x'. clear Z1'.
  destruct HK as ((Kw & _ & Kt & Kb & Ke & _ & _) & Kh).
  rewrite c_deflate_stored_eq in Hrun. cbv zeta in Hrun. rewrite Eloop in Hrun. cbn [bind] in Hrun.
  (* the state after the first phase *)
  pose proof (ob_keep_eq s s1 K1) as E1.
  assert (HW1 : W s1).
  { rewrite E1. destruct G1 as (G1a & G1b & _). apply W_ob; auto. }
  destruct (cp_fields s s1 (cp_ob_eq s s1 K1)) as (SP1 & AP1 & Lv1 & Pb1 & Ws1 & DL1 & St1).
  assert (Ss1 : d_strstart s1 = d_strstart s) by (rewrite E1; reflexivity).
  assert (Wn1 : d_window s1 = d_window s) by (rewrite E1; reflexivity).
  assert (Wb1 : d_w_bits s1 = d_w_bits s) by (rewrite E1; reflexivity).
  destruct (W_level0 s1 HW1 ltac:(congruence)) as (La1 & Bs1 & Sy1).
  destruct (W_level0 s HW H0) as (La0 & Bs0 & Sy0).
  assert (Kw1 : kwin (dict ++ D) s1) by (apply (kwin_frame _ s); [exact Ss1|congruence|exact Wn1|exact Kw]).
  assert (Kh1 : khash s1) by (rewrite E1; apply khash_ob; exact Kh).
  pose proof (zall_zstep _ _ _ _ _ Hza Z1 Zo1) as Hza1.
  pose proof (adler_ok_zstep _ _ _ _ _ Hza Ha Z1) as Ha1.
  pose proof Z1 as Z1'. destruct Z1' as (Zi1 & Zk1 & Zn1 & Za1 & _).
  assert (Hk : u32 (z_avail_in z - z_avail_in z1) = k).
  { rewrite Za1. replace (z_avail_in z - (z_avail_in z - k)) with k by lia. unfold u32. apply Z.mod_small.
    destruct Hz as (_ & _ & Hai & _). lia. }
  rewrite Hk in Hrun.
  (* the window update *)
  pose proof Hza1 as Hza1c. destruct Hza1c as [(Hb1 & Hn1 & Hai1 & Hl1 & _) _].
  destruct (RTDLTCStoredWin.dswin_ok RTDLTCStoredChain.chain_parts_ok s1 z1 k HW1 ltac:(congruence) Hb1
              ltac:(destruct Hza as [(_ & Hn & _) _]; lia) ltac:(lia)
              ltac:(destruct Hz as (_ & _ & Hai & _); lia) ltac:(intros Hk0; rewrite Ss1; auto))
    as (s2 & E2 & HW2 & WK2 & U2).
  rewrite E2 in Hrun. cbn [bind] in Hrun.
  destruct (FW s1 z1 k s2 (dict ++ D) HW1 ltac:(congruence) Hb1
              ltac:(destruct Hza as [(_ & Hn & _) _]; lia) ltac:(lia)
              ltac:(destruct Hz as (_ & _ & Hai & _); lia) ltac:(intros Hk0; rewrite Ss1; auto) E2 Kw1 Kh1)
    as (Kw2 & Kh2 & Ed2).
  set (c1 := sublist (z_next_in z) (z_next_in z + k) (z_in z)) in *.
  assert (Ec1 : sublist (z_next_in z1 - k) (z_next_in z1) (z_in z1) = c1) by (unfold c1; rewrite Zi1, Zn1; f_equal; lia).
  rewrite Ec1 in Kw2.
  assert (Hst : d_strstart s + d_lookahead s <= Zlength (mb_val (d_window s))).
  { pose proof HW as (_ & (Hwl & _ & Hwsz & _) & (_ & _ & Hp3 & _) & _). lia. }
  assert (Hc1 : Zlength c1 = k).
  { unfold c1. destruct Hza as [(_ & Hn & _ & Hl & _) _]. rewrite Zlength_sublist; lia. }
  assert (Hc0 : k = 0 -> c1 = []) by (intros K0; unfold c1; rewrite K0, Z.add_0_r, sublist_nil; reflexivity).
  assert (Hcb : bytes c1) by (unfold c1; destruct Hza as [(Hb & _) _]; exact (bytes_sublist _ _ _ Hb)).
  assert (Ec1d : sublist (z_next_in z) (z_next_in z + k) (z_in z) = c1) by reflexivity.
  clearbody c1.
  assert (KL : d_strstart s <= Zlength (dict ++ D)) by (destruct Kw as [Kl _]; rewrite La0 in Kl; lia).
  assert (Hexp1 : F.expand dict (BS ++ map F.Stored bl1) =
                  sublist 0 (Zlength ((dict ++ D) ++ c1) - d_strstart s2 + d_block_start s2) ((dict ++ D) ++ c1)).
  { rewrite expand_app, expand_stored, Ke, Cb1.
    rewrite (kwin_slice (dict ++ D) s) by (auto; lia).
    rewrite La0, Z.add_0_r.
    rewrite app_assoc, <- sublist_split by lia.
    replace (Zlength ((dict ++ D) ++ c1) - d_strstart s2 + d_block_start s2)
      with ((Zlength (dict ++ D) - d_strstart s + d_block_start s1) + Zlength c1) by (rewrite (Zlength_app _ (dict ++ D) c1); lia).
    symmetry. apply sublist_prefix_app; [lia|].
    destruct (Z.eq_dec k 0) as [K0|K0].
    - left. exact (Hc0 K0).
    - right. rewrite P1 by lia. lia. }
  assert (Hby1 : Forall F.byte_ok (concat bl1)).
  { rewrite Cb1, (kwin_slice (dict ++ D) s) by (auto; lia). apply Forall_app. split.
    - apply Forall_sublist. apply Forall_app. split; [exact Hdict|exact HD].
    - exact Hcb. }
  assert (Hbk1 : F.blocks_ok (2 ^ d_w_bits s) dict (BS ++ map F.Stored bl1)).
  { apply blocks_ok_app; [exact Kb|]. apply blocks_ok_stored; assumption. }
  (* the state after the window update *)
  set (s3 := upd_high_water s2) in Hrun.
  pose proof (W_hw s2 HW2) as HW3. fold s3 in HW3.
  assert (CP3 : cp s3 = cp s).
  { unfold s3. rewrite cp_uhw, (cp_win_eq _ _ WK2). apply cp_ob_eq; auto. }
  assert (OP3 : op s3 = op s1). { unfold s3. rewrite op_uhw. apply op_win_eq; auto. }
  destruct (cp_fields s s3 CP3) as (SP3 & AP3 & Lv3 & Pb3 & Ws3 & DL3 & St3).
  destruct (op_fields s1 s3 OP3 ltac:(congruence)) as (Ok3 & Qk3 & Gb3 & Bv3 & Sh3 & Pd3).
  assert (U3 : ub s3 = ub s1) by (unfold s3; rewrite ub_uhw; auto).
  destruct (W_level0 s3 HW3 ltac:(congruence)) as (La3 & Bs3 & Sy3).
  destruct (uhw_fields s2) as (F3a & F3b & F3c & F3d & F3e). fold s3 in F3a, F3b, F3c, F3d, F3e.
  assert (Kw3 : kwin ((dict ++ D) ++ c1) s3) by (apply (kwin_frame _ s2); auto).
  assert (Kh3 : khash s3) by (unfold s3; apply khash_uhw; exact Kh2).
  destruct (pend_op s1 s3 OP3) as (Pe3 & Bb3).
  assert (Wb3 : d_w_bits s3 = d_w_bits s) by (destruct SP3 as (E & _); exact E).
  assert (Hexp3 : F.expand dict (BS ++ map F.Stored bl1) =
                  sublist 0 (Zlength ((dict ++ D) ++ c1) - d_strstart s3 + d_block_start s3) ((dict ++ D) ++ c1))
    by (rewrite F3a, F3b; exact Hexp1).
  rewrite pend_quiet in Bi1 by exact Q1.
  destruct L1 as [(Lz & _ & Hfin) | (Lz & _ & Ffin & Ai1 & Bs1' & Bv1)].
  2:{ (* the first phase finished the stream *)
    subst last. cbn [Z.eqb negb Pos.eqb] in Hrun. injection Hrun as <- <- <-.
    exists k, x, (map F.Stored bl1), []. rewrite Ec1d. split; [exact Z1|].
    split.
    { apply kcore2_level0.
      - apply W_bu; [exact HW3|congruence].
      - change (d_level s3 = 0). congruence.
      - change (kwin (dict ++ D ++ c1) s3). rewrite app_assoc. exact Kw3.
      - apply khash_bu. exact Kh3.
      - change (F.blocks_ok (2 ^ d_w_bits s3) dict (BS ++ map F.Stored bl1)). rewrite Wb3. exact Hbk1.
      - change (F.expand dict (BS ++ map F.Stored bl1) =
                sublist 0 (Zlength (dict ++ D ++ c1) - d_strstart s3 + d_block_start s3) (dict ++ D ++ c1)).
        rewrite app_assoc. exact Hexp3. }
    split; [|intros _ E; apply (Ne1 eq_refl); destruct bl1; [reflexivity|discriminate]].
    change (F.bytes_bits (x ++ pend s3) ++ bibits s3 = bibits s ++ enc_out p (map F.Stored bl1) true).
    rewrite Pe3, Bb3, pend_quiet by exact Q1. exact Bi1. }
  subst last. cbn [Z.eqb negb] in Hrun. cbn [Z.eqb] in Bi1, Al1.
  assert (Kc3 : kcore2 dict (D ++ c1) (BS ++ map F.Stored bl1) [] s3).
  { apply kcore2_level0.
    - exact HW3.
    - congruence.
    - rewrite app_assoc. exact Kw3.
    - exact Kh3.
    - rewrite Wb3. exact Hbk1.
    - rewrite app_assoc. exact Hexp3. }
  destruct (negb (flush =? Z_NO_FLUSH) && negb (flush =? Z_FINISH) && (z_avail_in z1 =? 0) &&
            (d_strstart s3 =? d_block_start s3)) eqn:EB.
  { (* block_done *)
    injection Hrun as <- <- <-.
    exists k, x, (map F.Stored bl1), []. rewrite Ec1d. split; [exact Z1|]. split; [exact Kc3|].
    split; [|intros E; discriminate E].
    rewrite Pe3, Bb3, pend_quiet by exact Q1. exact Bi1. }
  (* the second phase: refill *)
  assert (Wr3 : d_wrap s3 = d_wrap s) by (destruct AP3 as (_ & Wr & _); exact Wr).
  destruct (RTDLTCStoredFill.fill2_ok RTDLTCStoredChain.chain_parts_ok s3 z1 HW3 ltac:(congruence) Hza1
              ltac:(rewrite Wr3; exact Ha1))
    as (s4 & z4 & k4 & EF & HW4 & WK4 & Z4 & U4).
  destruct (FF s3 z1 s4 z4 k4 ((dict ++ D) ++ c1) HW3 ltac:(congruence) Hza1 ltac:(rewrite Wr3; exact Ha1)
              EF Z4 Kw3 Kh3) as (Kw4 & Kh4).
  rewrite Wr3 in Z4. rewrite EF in Hrun.
  assert (CP4 : cp s4 = cp s) by (rewrite (cp_win_eq _ _ WK4); exact CP3).
  assert (OP4 : op s4 = op s1) by (rewrite (op_win_eq _ _ WK4); exact OP3).
  destruct (cp_fields s s4 CP4) as (SP4 & AP4 & Lv4 & Pb4 & Ws4 & DL4 & St4).
  destruct (op_fields s1 s4 OP4 ltac:(congruence)) as (Ok4 & Qk4 & Gb4 & Bv4 & Sh4 & Pd4).
  destruct (W_level0 s4 HW4 ltac:(congruence)) as (La4 & Bs4 & Sy4).
  destruct (pend_op s1 s4 OP4) as (Pe4 & Bb4).
  pose proof Z4 as Z4'. destruct Z4' as (Zi4 & Zk4 & Zn4 & Za4 & Zt4 & Zad4 & Zo4 & Zle4 & Zao4 & Zto4 & Zm4).
  rewrite Zlength_nil in Zao4, Zto4.
  assert (Hza4 : zall z4) by (apply (zall_zstep _ _ _ _ _ Hza1 Z4); lia).
  pose proof (adler_ok_zstep _ _ _ _ _ Hza1 Ha1 Z4) as Ha4.
  assert (Hfin4 : flush = Z_FINISH ->
            z_avail_out z4 < stored_hdr s4 + (d_strstart s4 - d_block_start s4) + z_avail_in z4).
  { intros Hf. specialize (Hfin Hf). rewrite Sh4, Zao4, Za4.
    unfold ub in U4, U3. rewrite La4, La3 in U4. rewrite La3, La1 in U3. lia. }
  assert (Wr4 : d_wrap s4 = d_wrap s) by (destruct AP4 as (_ & Wr & _); exact Wr).
  set (c4 := sublist (z_next_in z1) (z_next_in z1 + k4) (z_in z1)) in *.
  (* the second phase: the block *)
  destruct (RTDLTCStoredBlk2b.blk2_ok2 RTDLTCStoredSblk.sblk_ok s4 z4 flush HW4 (Ok4 O1) (Qk4 Q1) ltac:(congruence)
              Hza4 ltac:(rewrite Wr4; exact Ha4) Hfl Hfin4)
    as (s5 & z5 & last2 & evs2 & x2 & EB2 & HW5 & O5 & K5 & Z5 & X5 & A5 & C5 & F5 & L5).
  set (p1 := p + Zlength (enc_out p (map F.Stored bl1) false)).
  destruct (FB s4 z4 flush s5 z5 last2 p1 HW4 (Ok4 O1) (Qk4 Q1) ltac:(congruence) Hza4
              ltac:(rewrite Wr4; exact Ha4) Hfl Hfin4 EB2 ltac:(unfold p1; pose proof (Zlength_nonneg (enc_out p (map F.Stored bl1) false)); lia)
              ltac:(unfold p1; rewrite Bv4; exact Al1))
    as (x5 & bl2 & Z5' & Bl2 & Cb2 & Bi2 & Ne2).
  rewrite EB2 in Hrun. rewrite Wr4 in Z5'.
  (* the final state *)
  pose proof (ob_keep_eq s4 s5 K5) as E5.
  assert (Ss5 : d_strstart s5 = d_strstart s4) by (rewrite E5; reflexivity).
  assert (La5 : d_lookahead s5 = d_lookahead s4) by (rewrite E5; reflexivity).
  assert (Wn5 : d_window s5 = d_window s4) by (rewrite E5; reflexivity).
  assert (Wb5 : d_w_bits s5 = d_w_bits s4) by (rewrite E5; reflexivity).
  assert (Lv5 : d_level s5 = d_level s4) by (rewrite E5; reflexivity).
  assert (Kw5 : kwin (((dict ++ D) ++ c1) ++ c4) s5) by (apply (kwin_frame _ s4); auto).
  assert (Kh5 : khash s5) by (rewrite E5; apply khash_ob; exact Kh4).
  assert (Wb4 : d_w_bits s4 = d_w_bits s) by (destruct SP4 as (E & _); exact E).
  assert (Hbs5 : d_block_start s4 <= d_block_start s5 <= d_strstart s4).
  { pose proof (sum_len_nonneg0 s4 flush evs2 ltac:(congruence) F5) as Sn.
    pose proof HW5 as (_ & _ & (_ & _ & _ & Bq & _) & _).
    unfold ub in A5. lia. }
  assert (Hc4 : Zlength c4 = k4).
  { unfold c4. destruct Hza1 as [(_ & Hn & _ & Hl & _) _]. rewrite Zlength_sublist; lia. }
  assert (Hcb4 : bytes c4) by (unfold c4; exact (bytes_sublist _ _ _ Hb1)).
  assert (Hst4 : d_strstart s4 + d_lookahead s4 <= Zlength (mb_val (d_window s4))).
  { pose proof HW4 as (_ & (Hwl & _ & Hwsz & _) & (_ & _ & Hp3 & _) & _). lia. }
  assert (KL4 : d_strstart s4 <= Zlength (((dict ++ D) ++ c1) ++ c4))
    by (destruct Kw4 as [Kl _]; rewrite La4 in Kl; lia).
  assert (Hbs3 : d_block_start s3 <= d_strstart s3) by (pose proof HW3 as (_ & _ & (_ & _ & _ & Bq & _) & _); lia).
  assert (Hm : Zlength ((dict ++ D) ++ c1) - d_strstart s3 + d_block_start s3 =
               Zlength (((dict ++ D) ++ c1) ++ c4) - d_strstart s4 + d_block_start s4).
  { rewrite (Zlength_app _ ((dict ++ D) ++ c1) c4). unfold ub in U4. lia. }
  assert (KL3 : d_strstart s3 <= Zlength ((dict ++ D) ++ c1)) by (destruct Kw3 as [Kl _]; rewrite La3 in Kl; lia).
  assert (Hexp5 : F.expand dict ((BS ++ map F.Stored bl1) ++ map F.Stored bl2) =
                  sublist 0 (Zlength (((dict ++ D) ++ c1) ++ c4) - d_strstart s5 + d_block_start s5)
                          (((dict ++ D) ++ c1) ++ c4)).
  { rewrite expand_app, Hexp3, expand_stored, Cb2.
    rewrite (kwin_slice (((dict ++ D) ++ c1) ++ c4) s4) by (auto; lia).
    rewrite La4, Z.add_0_r, Hm, Ss5.
    rewrite <- (sublist_prefix_le _ c4) by lia.
    rewrite <- sublist_split by lia. reflexivity. }
  assert (Hby2 : Forall F.byte_ok (concat bl2)).
  { rewrite Cb2, (kwin_slice (((dict ++ D) ++ c1) ++ c4) s4) by (auto; lia).
    apply Forall_sublist. repeat (apply Forall_app; split); assumption. }
  assert (Hbk5 : F.blocks_ok (2 ^ d_w_bits s) dict ((BS ++ map F.Stored bl1) ++ map F.Stored bl2)).
  { apply blocks_ok_app; [exact Hbk1|]. apply blocks_ok_stored; assumption. }
  assert (Zall : zstep (d_wrap s) z z5 (k + k4 + 0) ((x ++ []) ++ x5)).
  { destruct Hza as [Hzi _]. eapply zstep_trans; [exact Hzi|exact Ha| |exact Z5'].
    eapply zstep_trans; [exact Hzi|exact Ha|exact Z1|exact Z4]. }
  assert (Hsub : sublist (z_next_in z) (z_next_in z + (k + k4 + 0)) (z_in z) = c1 ++ c4).
  { rewrite <- Ec1d. unfold c4. rewrite Zi1, Zn1.
    destruct Hza1 as [(_ & Hn & _ & Hl & _) _]. rewrite Zi1, Zn1 in Hl.
    destruct Hza as [(_ & Hn0 & _) _].
    rewrite <- sublist_split by lia. f_equal. lia. }
  assert (Kc5 : kcore2 dict ((D ++ c1) ++ c4) (BS ++ map F.Stored bl1 ++ map F.Stored bl2) [] s5).
  { apply kcore2_level0.
    - exact HW5.
    - congruence.
    - rewrite !app_assoc. exact Kw5.
    - exact Kh5.
    - rewrite app_assoc, Wb5, Wb4. exact Hbk5.
    - rewrite !app_assoc. exact Hexp5. }
  assert (Hbits : forall fin, (map F.Stored bl2 <> [] \/ fin = false) ->
            F.bytes_bits (x5 ++ pend s5) ++ bibits s5 = bibits s4 ++ enc_out p1 (map F.Stored bl2) fin ->
            F.bytes_bits (((x ++ []) ++ x5) ++ pend s5) ++ bibits s5 =
            bibits s ++ enc_out p (map F.Stored bl1 ++ map F.Stored bl2) fin).
  { intros fin Hf B2. rewrite enc_out_app by exact Hf. fold p1.
    transitivity (F.bytes_bits x ++ (F.bytes_bits (x5 ++ pend s5) ++ bibits s5)).
    { rewrite app_nil_r, <- (app_assoc x x5), bytes_bits_app, <- !app_assoc. reflexivity. }
    rewrite B2, Bb4, app_assoc. rewrite app_nil_r in Bi1. rewrite Bi1, <- !app_assoc. reflexivity. }
  destruct L5 as [(Lz2 & _) | (Lz2 & _)]; subst last2; cbn [Z.eqb] in Hrun, Bi2; injection Hrun as <- <- <-.
  - exists (k + k4 + 0), ((x ++ []) ++ x5), (map F.Stored bl1 ++ map F.Stored bl2), [].
    rewrite Hsub, app_assoc. split; [exact Zall|]. split; [exact Kc5|].
    split; [|intros E; discriminate E]. apply Hbits; [right; reflexivity|exact Bi2].
  - exists (k + k4 + 0), ((x ++ []) ++ x5), (map F.Stored bl1 ++ map F.Stored bl2), [].
    rewrite Hsub, app_assoc. split; [exact Zall|].
    assert (Nb : map F.Stored bl2 <> []) by (intros E; apply (Ne2 eq_refl); destruct bl2; [reflexivity|discriminate]).
    split; [exact Kc5|]. split.
    + change (F.bytes_bits (((x ++ []) ++ x5) ++ pend s5) ++ bibits s5 =
              bibits s ++ enc_out p (map F.Stored bl1 ++ map F.Stored bl2) true).
      apply Hbits; [left; exact Nb|exact Bi2].
    + intros _ E. apply app_eq_nil in E. destruct E as [_ E]. exact (Nb E).
Qed.

Theorem rtd_stored_ok2 : Zlib.proof.huffman.Overlay.overlay_statement -> writer_fspec -> stored_block_fspec ->
  fpend_fspec2 -> comp_fspec2 0 c_deflate_stored.
Proof.
  intros _ _ Hsb Hfp. pose proof RTDStoredChain.rtds_chain_ok as Hc.
  apply stored2_assembly.
  - exact Hc.
  - exact (RTDStoredLoop.rtds_loop_ok Hsb Hfp).
  - exact (RTDStoredWin.rtds_win_ok Hc).
  - exact (RTDStoredFill.rtds_fill_ok Hc).
  - exact (RTDStoredBlk.rtds_blk_ok Hsb Hfp).
Qed.
