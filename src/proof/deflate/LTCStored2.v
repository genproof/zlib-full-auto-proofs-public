(** * Core part of the deflate law theory: deflate_stored, against the corrected specs of LTCSpecs2.v.
    With LTCSpecs2.fpend_spec_2 it also holds under the original fpend_spec of LTCSpecs.v.
    Parts: LTCStoredKit.v (statements), LTCStored{Sblk,Loop,Win,Fill,Blk2b,Chain}.v (proofs); here the assembly.
    flush_pending is LTCFlushKit.fpend_ok (proved), so the hypothesis is not even needed. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTCSpecs2 Zlib.proof.deflate.LTCStoredKit.
Require Zlib.proof.deflate.LTCStoredSblk Zlib.proof.deflate.LTCStoredLoop Zlib.proof.deflate.LTCStoredWin
  Zlib.proof.deflate.LTCStoredFill Zlib.proof.deflate.LTCStoredBlk2b Zlib.proof.deflate.LTCStoredChain.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** Frames *)

Definition ob_set (s : dstate) (o : outbuf) (m : list bool) (po b : Z) : dstate :=
  set_d_block_start (set_d_po (set_d_pbm (set_d_tr s (set_out (d_tr s) o)) m) po) b.


Ltac dproj := cbn [d_status d_po d_wrap d_gzhead d_gzindex d_method d_last_flush d_w_size d_w_bits d_w_mask
  d_window d_window_size d_prev d_head d_ins_h d_hash_size d_hash_bits d_hash_mask d_hash_shift d_block_start
  d_match_length d_prev_match d_match_available d_strstart d_match_start d_lookahead d_prev_length
  d_max_chain_length d_max_lazy_match d_good_match d_nice_match d_insert d_high_water d_slid d_pending_buf_size
  d_tr d_pbm tr_ltree tr_dtree tr_bltree tr_lmax tr_dmax tr_blmax tr_wk tr_out tr_sym_next tr_sym_end
  tr_matches tr_lit_bufsize tr_level tr_strategy tr_data_type o_buf o_pending o_bi_buf o_bi_valid o_bi_used].

Ltac unset := cbn [set_d_status set_d_po set_d_wrap set_d_gzhead set_d_gzindex set_d_method
  set_d_last_flush set_d_w_size set_d_w_bits set_d_w_mask set_d_window set_d_window_size set_d_prev
  set_d_head set_d_ins_h set_d_hash_size set_d_hash_bits set_d_hash_mask set_d_hash_shift
  set_d_block_start set_d_match_length set_d_prev_match set_d_match_available set_d_strstart
  set_d_match_start set_d_lookahead set_d_prev_length set_d_max_chain_length set_d_max_lazy_match
  set_d_good_match set_d_nice_match set_d_insert set_d_high_water set_d_slid set_d_pending_buf_size
  set_d_tr set_d_pbm set_out set_matches ob_set ob_keep fp_keep win_keep set_d_matches upd_high_water
  set_d_bi_used d_level d_strategy d_L d_matches d_pending d_bi_valid d_pb
  d_status d_po d_wrap d_gzhead d_gzindex d_method d_last_flush d_w_size d_w_bits d_w_mask
  d_window d_window_size d_prev d_head d_ins_h d_hash_size d_hash_bits d_hash_mask d_hash_shift d_block_start
  d_match_length d_prev_match d_match_available d_strstart d_match_start d_lookahead d_prev_length
  d_max_chain_length d_max_lazy_match d_good_match d_nice_match d_insert d_high_water d_slid d_pending_buf_size
  d_tr d_pbm tr_ltree tr_dtree tr_bltree tr_lmax tr_dmax tr_blmax tr_wk tr_out tr_sym_next tr_sym_end
  tr_matches tr_lit_bufsize tr_level tr_strategy tr_data_type o_buf o_pending o_bi_buf o_bi_valid o_bi_used].

Ltac unsetA := cbn [set_d_status set_d_po set_d_wrap set_d_gzhead set_d_gzindex set_d_method
  set_d_last_flush set_d_w_size set_d_w_bits set_d_w_mask set_d_window set_d_window_size set_d_prev
  set_d_head set_d_ins_h set_d_hash_size set_d_hash_bits set_d_hash_mask set_d_hash_shift
  set_d_block_start set_d_match_length set_d_prev_match set_d_match_available set_d_strstart
  set_d_match_start set_d_lookahead set_d_prev_length set_d_max_chain_length set_d_max_lazy_match
  set_d_good_match set_d_nice_match set_d_insert set_d_high_water set_d_slid set_d_pending_buf_size
  set_d_tr set_d_pbm set_out set_matches ob_set ob_keep fp_keep win_keep set_d_matches upd_high_water
  set_d_bi_used d_level d_strategy d_L d_matches d_pending d_bi_valid d_pb
  d_status d_po d_wrap d_gzhead d_gzindex d_method d_last_flush d_w_size d_w_bits d_w_mask
  d_window d_window_size d_prev d_head d_ins_h d_hash_size d_hash_bits d_hash_mask d_hash_shift d_block_start
  d_match_length d_prev_match d_match_available d_strstart d_match_start d_lookahead d_prev_length
  d_max_chain_length d_max_lazy_match d_good_match d_nice_match d_insert d_high_water d_slid d_pending_buf_size
  d_tr d_pbm tr_ltree tr_dtree tr_bltree tr_lmax tr_dmax tr_blmax tr_wk tr_out tr_sym_next tr_sym_end
  tr_matches tr_lit_bufsize tr_level tr_strategy tr_data_type o_buf o_pending o_bi_buf o_bi_valid o_bi_used] in *.

Lemma ob_keep_eq s s' : ob_keep s' = ob_keep s ->
  s' = ob_set s (tr_out (d_tr s')) (d_pbm s') (d_po s') (d_block_start s').
Proof.
  destruct s as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? [] ?],
           s' as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? [] ?].
  unset. dproj. intros H. injection H. intros. subst. reflexivity.
Qed.

Lemma W_ob s o m po b :
  W s -> d_level s = 0 -> Zlength (o_buf o) = Zlength (o_buf (tr_out (d_tr s))) -> Zlength m = Zlength (d_pbm s) ->
  d_block_start s <= b <= d_strstart s -> W (ob_set s o m po b).
Proof.
  intros (Hp & Hs & Hpos & Hw & Hh & Hm & Hl & syms & Ht) H0 Lo Lm Hb.
  unfold W, prm, wstruct, wpos, wwin, whash, wmatch, wtrees, tree_ok, sym_ok, chain_ok, chain_with, lim, slide_hc,
    fn_of, MAX_DIST in *.
  unfold d_level, d_L, d_strategy, d_matches in *. unsetA.
  destruct (Hl H0) as [Hla Hbs].
  destruct Ht as (T & HL2 & HF & Hsy & _). rewrite (Hsy H0) in *.
  destruct T as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
  rewrite Zlength_nil, Z.mul_0_r, Z.add_0_r in T5, T6. rewrite sublist_nil in T5. rewrite sublist_nil in T6.
  refine (conj _ (conj Hs (conj _ (conj Hw (conj Hh (conj Hm (conj _ _))))))).
  - destruct Hp as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12). rewrite Lo, Lm.
    repeat (split; [assumption|]). assumption.
  - destruct Hpos as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9). lia.
  - intros _. lia.
  - exists []. rewrite Zlength_nil, Z.mul_0_r, Z.add_0_r, !sublist_nil.
    split; [split; [lia|]; split; [lia|]; split; [exact T3|]; split; [exact T4|]; split; [exact T5|];
            split; [exact T6|]; exact T7|].
    split; [exact HL2|]. split; [exact HF|]. split; [intros _; reflexivity|]. intros; contradiction.
Qed.

(** ** Field transfers *)

Definition cp (s : dstate) :=
  (d_status s, d_wrap s, d_gzhead s, d_gzindex s, d_last_flush s, d_method s, d_w_bits s, d_w_size s,
   d_hash_bits s, d_L s, d_pending_buf_size s, d_level s, d_strategy s).
Definition op (s : dstate) := (tr_out (d_tr s), d_pbm s, d_po s).

Lemma cp_ob s : cp (ob_keep s) = cp s. Proof. reflexivity. Qed.
Lemma cp_win s : cp (win_keep s) = cp s. Proof. reflexivity. Qed.
Lemma op_win s : op (win_keep s) = op s. Proof. reflexivity. Qed.
Lemma cp_uhw s : cp (upd_high_water s) = cp s.
Proof. unfold upd_high_water. destruct (_ <? _); reflexivity. Qed.
Lemma op_uhw s : op (upd_high_water s) = op s.
Proof. unfold upd_high_water. destruct (_ <? _); reflexivity. Qed.
Lemma cp_bu s : cp (set_d_bi_used s 8) = cp s. Proof. reflexivity. Qed.
Lemma ub_uhw s : ub (upd_high_water s) = ub s.
Proof. unfold upd_high_water. destruct (_ <? _); reflexivity. Qed.

Lemma cp_ob_eq s s' : ob_keep s' = ob_keep s -> cp s' = cp s.
Proof. intros H. rewrite <- (cp_ob s'), <- (cp_ob s), H. reflexivity. Qed.
Lemma cp_win_eq s s' : win_keep s' = win_keep s -> cp s' = cp s.
Proof. intros H. rewrite <- (cp_win s'), <- (cp_win s), H. reflexivity. Qed.
Lemma op_win_eq s s' : win_keep s' = win_keep s -> op s' = op s.
Proof. intros H. rewrite <- (op_win s'), <- (op_win s), H. reflexivity. Qed.

Lemma cp_fields s s' : cp s' = cp s ->
  same_prm s s' /\ api_eq s s' /\ d_level s' = d_level s /\ d_pending_buf_size s' = d_pending_buf_size s /\
  d_w_size s' = d_w_size s /\ d_L s' = d_L s /\ d_strategy s' = d_strategy s.
Proof.
  unfold cp, same_prm, api_eq. intros H. injection H. intros. repeat split; congruence.
Qed.

Lemma op_fields s s' : op s' = op s -> d_pending_buf_size s' = d_pending_buf_size s ->
  (outok s -> outok s') /\ (quiet s -> quiet s') /\ (forall t, Gb s' t = Gb s t) /\
  d_bi_valid s' = d_bi_valid s /\ stored_hdr s' = stored_hdr s /\ d_pending s' = d_pending s.
Proof.
  unfold op. intros H Hp. injection H. intros E3 E2 E1.
  unfold outok, quiet, Gb, d_pb, d_pending, d_bi_valid, stored_hdr. rewrite E1, E2, E3, Hp.
  exact (conj (fun h => h) (conj (fun h => h) (conj (fun t => eq_refl) (conj eq_refl (conj eq_refl eq_refl))))).
Qed.

Lemma ev_ok_cp s s' flush evs : cp s' = cp s -> Forall (ev_ok s' flush) evs -> Forall (ev_ok s flush) evs.
Proof.
  intros H. destruct (cp_fields s s' H) as (_ & _ & E1 & E2 & E3 & E4 & E5).
  apply Forall_impl. intros e. destruct e; unfold ev_ok; rewrite ?E1, ?E2, ?E3, ?E4, ?E5; auto.
Qed.

Lemma W_level0 s : W s -> d_level s = 0 -> d_lookahead s = 0 /\ 0 <= d_block_start s /\ d_sym_next s = 0.
Proof.
  intros (_ & _ & _ & _ & _ & _ & Hl & syms & (T1 & T2 & T3 & _) & _ & _ & Hs & _) H0.
  destruct (Hl H0) as [A B]. split; [exact A|]. split; [exact B|].
  unfold d_sym_next. rewrite T3, (Hs H0). reflexivity.
Qed.

Lemma level0_of s : prm s -> fn_of s = 0 -> d_level s = 0.
Proof.
  intros Hp. destruct Hp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hl & _).
  unfold fn_of. destruct (Z.eqb_spec (d_level s) 0) as [E|E]; [auto|].
  destruct (_ =? Z_HUFFMAN_ONLY); [discriminate|]. destruct (_ =? Z_RLE); [discriminate|].
  assert (Hc : d_level s = 1 \/ d_level s = 2 \/ d_level s = 3 \/ d_level s = 4 \/ d_level s = 5 \/
               d_level s = 6 \/ d_level s = 7 \/ d_level s = 8 \/ d_level s = 9) by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]; vm_compute; discriminate.
Qed.

Lemma bu_ob s : set_d_bi_used s 8 =
  ob_set s (mkOut (o_buf (tr_out (d_tr s))) (o_pending (tr_out (d_tr s))) (o_bi_buf (tr_out (d_tr s)))
                  (o_bi_valid (tr_out (d_tr s))) 8) (d_pbm s) (d_po s) (d_block_start s).
Proof. destruct s. reflexivity. Qed.

Lemma W_bu s : W s -> d_level s = 0 -> W (set_d_bi_used s 8).
Proof.
  intros HW H0. rewrite bu_ob. pose proof HW as HW'.
  destruct HW' as (Hp & Hs & Hpos & _).
  apply W_ob; auto. destruct Hpos as (_ & _ & _ & B & _). lia.
Qed.

Lemma bu_fields s : (outok s -> outok (set_d_bi_used s 8)) /\ (quiet s -> quiet (set_d_bi_used s 8)) /\
  (forall t, Gb (set_d_bi_used s 8) t = Gb s t) /\ d_bi_valid (set_d_bi_used s 8) = d_bi_valid s /\
  ub (set_d_bi_used s 8) = ub s /\ d_sym_next (set_d_bi_used s 8) = d_sym_next s.
Proof.
  exact (conj (fun h => h) (conj (fun h => h) (conj (fun t => eq_refl) (conj eq_refl (conj eq_refl eq_refl))))).
Qed.

Lemma W_hw s : W s -> W (upd_high_water s).
Proof.
  unfold upd_high_water. destruct (Z.ltb_spec (d_high_water s) (d_strstart s)) as [L|L]; [|auto].
  intros (Hp & Hs & Hpos & Hw & Hh & Hm & Hl & syms & Ht).
  unfold W, prm, wstruct, wpos, wwin, whash, wmatch, wtrees, tree_ok, sym_ok, chain_ok, chain_with, lim, slide_hc,
    fn_of, MAX_DIST in *.
  unfold d_level, d_L, d_strategy, d_matches in *. unsetA.
  refine (conj Hp (conj Hs (conj _ (conj _ (conj Hh (conj Hm (conj Hl (ex_intro _ syms Ht)))))))).
  - destruct Hpos as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9). repeat split; lia.
  - intros i Hi. apply Hw. destruct Hpos as (Q1 & Q2 & Q3 & _). lia.
Qed.

(** ** Event lists *)

Lemma ev_chain_app g evs1 g1 evs2 g2 :
  ev_chain g evs1 g1 -> ev_chain g1 evs2 g2 -> ev_chain g (evs1 ++ evs2) g2.
Proof.
  revert g. induction evs1 as [|e r IH]; intros g H1 H2; cbn in *.
  - subst. exact H2.
  - destruct H1 as [A B]. split; [exact A|]. eapply IH; eauto.
Qed.

Lemma sum_len_app evs1 evs2 : sum_len (evs1 ++ evs2) = sum_len evs1 + sum_len evs2.
Proof. unfold sum_len. induction evs1 as [|e r IH]; cbn; [reflexivity|]. rewrite IH. lia. Qed.

Lemma last_ev_app evs1 evs2 :
  Forall (fun e => ev_last e = 0) evs1 -> last_ev evs2 -> last_ev (evs1 ++ evs2).
Proof.
  intros H1 (evs0 & e & -> & He & H0). exists (evs1 ++ evs0), e. split; [rewrite app_assoc; reflexivity|].
  split; [exact He|]. apply Forall_app; auto.
Qed.

Lemma adler_ok_zstep w z z' k x : zall z -> adler_ok w (z_adler z) -> zstep w z z' k x -> adler_ok w (z_adler z').
Proof.
  intros [(Hb & _) _] Ha (_ & _ & _ & _ & _ & E & _). rewrite E. apply adler_ok_upd; auto.
  apply bytes_sublist; auto.
Qed.

(** ** Assembly *)

(** dsloop_stmt with [0 <= z_avail_out z1] (LTCStoredLoop.dsloop_stmt', same text). *)
Definition dsloop_stmtA : Prop :=
  forall s z flush,
    W s -> outok s -> quiet s -> d_level s = 0 -> zall z -> adler_ok (d_wrap s) (z_adler z) ->
    0 <= flush <= 5 -> z_avail_out z <= 1073741824 ->
    exists s1 z1 last evs k x,
      loop FUEL (ds_body flush (ds_min_block s)) (s, z) = Some (s1, z1, last) /\
      ob_keep s1 = ob_keep s /\
      d_block_start s <= d_block_start s1 <= d_strstart s /\
      outok s1 /\ quiet s1 /\
      pb_grow (tr_out (d_tr s)) (d_pbm s) (tr_out (d_tr s1)) (d_pbm s1) /\
      zstep (d_wrap s) z z1 k x /\ bytes x /\ 0 <= z_avail_out z1 /\
      k + ub s = sum_len evs + ub s1 /\
      (0 < k -> d_block_start s1 = d_strstart s) /\
      ev_chain (Gb s (z_total_out z)) evs (Gb s1 (z_total_out z1)) /\
      Forall (ev_ok s flush) evs /\
      ((last = 0 /\ Forall (fun e => ev_last e = 0) evs /\
        (flush = Z_FINISH ->
         z_avail_out z1 < stored_hdr s1 + (d_strstart s - d_block_start s1) + z_avail_in z1)) \/
       (last = 1 /\ last_ev evs /\ flush = Z_FINISH /\ z_avail_in z1 = 0 /\
        d_block_start s1 = d_strstart s /\ d_bi_valid s1 = 0)).

Lemma stored_assembly : dsloop_stmtA -> dswin_stmt -> fill2_stmt -> blk2_stmt -> stored_spec.
Proof.
  intros HL HWn HF HB s z flush Hpre Hfn.
  destruct Hpre as (HW & Ho & Hq & Hfl & Hz & Hwr & Ha).
  assert (H0 : d_level s = 0) by (apply level0_of; [destruct HW as (Hp & _); exact Hp|exact Hfn]).
  pose proof (zin_ok_zall z Hz) as Hza.
  assert (Hao : z_avail_out z <= 1073741824) by (destruct Hz as (_ & _ & _ & _ & A & _); lia).
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

Theorem stored_ok2 : fpend_spec2 -> stored_spec.
Proof.
  intros _. apply stored_assembly.
  - exact (LTCStoredLoop.dsloop_ok'' LTCStoredSblk.sblk_ok).
  - exact (LTCStoredWin.dswin_ok LTCStoredChain.chain_parts_ok).
  - exact (LTCStoredFill.fill2_ok LTCStoredChain.chain_parts_ok).
  - exact (LTCStoredBlk2b.blk2_ok2 LTCStoredSblk.sblk_ok).
Qed.
