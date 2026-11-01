(** * Body proofs: deflate_stored.

    The target: every function's body satisfies its shared specification (see Obligations.v: ob_X =
    semax_body Vprog Gprog_X f_X X_spec; specs in src/proof/trees/TSpec.v, src/proof/deflate/DSpec.v,
    src/proof/compress/CSpec.v; checked models in src/proof/trees/CModel.v, src/proof/deflate/DModel*.v).
    Prove each body as its own lemma (in this file or in new files it imports) and conclude. *)
Require Import Zlib.proof.deflate.Obligations.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.proof.deflate.StoredKit.
Require Import Zlib.proof.deflate.StoredFacts.
Require Import Zlib.proof.deflate.StoredBody.
Require Import Zlib.proof.deflate.StoredWin.
Require Import Zlib.proof.deflate.StoredTail.
Require Zlib.trees.code.

#[export] Existing Instance DCS.CS.

(** trees.c's part of the state without the groups deflate_stored touches (out_at, sym_at, dtype_at).  Kept
    folded: it mentions trees.c's globals, which are not in deflate.c's type context (entailer refuses them). *)
Definition trees_frame (cs : tstate * list bool) (sp : val) (gv : globals) : mpred :=
  (ltree_at (tr_ltree (fst cs)) sp * dtree_at (tr_dtree (fst cs)) sp * bltree_at (tr_bltree (fst cs)) sp *
   ldesc_at (field_address t_ds (DOT Zlib.trees.code._dyn_ltree) sp) (tr_lmax (fst cs)) (gv Zlib.trees.code._static_l_desc) sp *
   ddesc_at (field_address t_ds (DOT Zlib.trees.code._dyn_dtree) sp) (tr_dmax (fst cs)) (gv Zlib.trees.code._static_d_desc) sp *
   bldesc_at (field_address t_ds (DOT Zlib.trees.code._bl_tree) sp) (tr_blmax (fst cs)) (gv Zlib.trees.code._static_bl_desc) sp *
   work_at (tr_wk (fst cs)) sp * lvl_at (fst cs) sp)%logic.

Lemma trees_at_split cs sp pbp strmp gv :
  trees_at cs sp pbp strmp gv =
  (trees_frame cs sp gv * out_at (tr_out (fst cs)) (snd cs) sp pbp * sym_at (fst cs) sp pbp *
   dtype_at (fst cs) sp strmp)%logic.
Proof. unfold trees_at, trees_frame. apply pred_ext; cancel. Qed.

(** strm_at with the allocator fields (zutil.c's globals, not in deflate.c's type context) kept folded. *)
Definition strm_zfuncs (strmp : val) (gv : globals) : mpred :=
  (@field_at DCS.CS Ews t_strm (DOT _zalloc) (gv _zcalloc) strmp *
   @field_at DCS.CS Ews t_strm (DOT _zfree) (gv _zcfree) strmp)%logic.

Lemma strm_at_split z sp strmp pin pout msgv gv :
  strm_at z sp strmp pin pout msgv gv =
  (@field_at DCS.CS Ews t_strm (DOT _next_in) (offset_val (z_next_in z) pin) strmp *
   @field_at DCS.CS Ews t_strm (DOT _avail_in) (vi (z_avail_in z)) strmp *
   @field_at DCS.CS Ews t_strm (DOT _total_in) (vl (z_total_in z)) strmp *
   @field_at DCS.CS Ews t_strm (DOT _next_out) (offset_val (Zlength (z_out z)) pout) strmp *
   @field_at DCS.CS Ews t_strm (DOT _avail_out) (vi (z_avail_out z)) strmp *
   @field_at DCS.CS Ews t_strm (DOT _total_out) (vl (z_total_out z)) strmp *
   @field_at DCS.CS Ews t_strm (DOT _msg) msgv strmp *
   @field_at DCS.CS Ews t_strm (DOT _state) sp strmp *
   strm_zfuncs strmp gv *
   @field_at DCS.CS Ews t_strm (DOT _opaque) nullval strmp *
   @field_at DCS.CS Ews t_strm (DOT _adler) (vl (z_adler z)) strmp *
   @field_at_ DCS.CS Ews t_strm (DOT _reserved) strmp)%logic.
Proof. unfold strm_at, strm_zfuncs. apply pred_ext; cancel. Qed.

Lemma u64_sub_unsigned a b :
  Int64.unsigned (Int64.sub (Int64.repr a) (Int64.repr b)) = u64 (a - b).
Proof. rewrite sub64_repr, Int64.unsigned_repr_eq. reflexivity. Qed.

Lemma u64_range x : 0 <= u64 x <= Int64.max_unsigned.
Proof. unfold u64. pose proof (Z.mod_pos_bound x 18446744073709551616 ltac:(lia)). rep_lia. Qed.

Lemma u32_range x : 0 <= u32 x <= Int.max_unsigned.
Proof. unfold u32. pose proof (Z.mod_pos_bound x 4294967296 ltac:(lia)). rep_lia. Qed.

Lemma vl_u64 x : vl (u64 x) = vl x.
Proof.
  unfold vl, u64. f_equal. change 18446744073709551616 with Int64.modulus.
  rewrite <- Int64.unsigned_repr_eq. apply Int64.repr_unsigned.
Qed.

Lemma vi_u32 x : vi (u32 x) = vi x.
Proof.
  unfold vi, u32. f_equal. change 4294967296 with Int.modulus.
  rewrite <- Int.unsigned_repr_eq. apply Int.repr_unsigned.
Qed.

Lemma RAn_loop1 Q R : RA_normal (loop1_ret_assert Q R) = Q.
Proof. destruct R; reflexivity. Qed.
Lemma RAb_loop1 Q R : RA_break (loop1_ret_assert Q R) = RA_normal R.
Proof. destruct R; reflexivity. Qed.
Lemma RAc_loop1 Q R : RA_continue (loop1_ret_assert Q R) = Q.
Proof. destruct R; reflexivity. Qed.
Lemma RAr_loop1 Q R : RA_return (loop1_ret_assert Q R) = RA_return R.
Proof. destruct R; reflexivity. Qed.
Lemma RAn_loop2 Q R : RA_normal (loop2_ret_assert Q R) = Q.
Proof. destruct R; reflexivity. Qed.
Lemma RAb_loop2 Q R : RA_break (loop2_ret_assert Q R) = RA_normal R.
Proof. destruct R; reflexivity. Qed.
Lemma RAn_override P R : RA_normal (overridePost P R) = P.
Proof. destruct R; reflexivity. Qed.

Lemma dstate_ranges_hw s x : dstate_ranges s -> u64_ok x -> dstate_ranges (set_d_high_water s x).
Proof. unfold dstate_ranges. destruct s; cbn. intuition. Qed.

Lemma dstate_ranges_bi_used s x : dstate_ranges s -> dstate_ranges (set_d_bi_used s x).
Proof. unfold dstate_ranges. destruct s; cbn. intuition. Qed.

Lemma int_eq_repr_s a b : Int.min_signed <= a <= Int.max_signed -> Int.min_signed <= b <= Int.max_signed ->
  Int.eq (Int.repr a) (Int.repr b) = (a =? b).
Proof.
  intros. destruct (Z.eqb_spec a b); [subst; apply Int.eq_true|].
  apply Int.eq_false. intro E. apply repr_inj_signed in E; auto.
Qed.

Lemma int_eq_repr_u a b : 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  Int.eq (Int.repr a) (Int.repr b) = (a =? b).
Proof.
  intros. destruct (Z.eqb_spec a b); [subst; apply Int.eq_true|].
  apply Int.eq_false. intro E. apply repr_inj_unsigned in E; auto.
Qed.

Lemma int64_eq_repr_s a b : Int64.min_signed <= a <= Int64.max_signed -> Int64.min_signed <= b <= Int64.max_signed ->
  Int64.eq (Int64.repr a) (Int64.repr b) = (a =? b).
Proof.
  intros. destruct (Z.eqb_spec a b); [subst; apply Int64.eq_true|].
  apply Int64.eq_false. intro E. apply n.
  rewrite <- (Int64.signed_repr a), <- (Int64.signed_repr b) by auto. congruence.
Qed.

Lemma eqb_zeq a b : (a =? b) = proj_sumbool (zeq a b).
Proof. destruct (zeq a b); cbn; [subst; apply Z.eqb_refl | apply Z.eqb_neq; auto]. Qed.

Ltac fin_b :=
  first [ reflexivity | (rewrite eqb_zeq; reflexivity)
        | match goal with HH : ?b = _ |- context [?b] =>
            rewrite HH; first [reflexivity | (rewrite eqb_zeq; reflexivity)] end ].

Lemma ds_fun_post_eq p pin pout ish rest gv z z1 r :
  rest_after z1 (snd (fst r)) (rest_after z z1 rest) = rest_after z (snd (fst r)) rest ->
  ds_fun_post p pin pout ish (rest_after z z1 rest) gv z1 r =
  frame_ret_assert
    (function_body_ret_assert tint
       (PROP () RETURN (vi (bstate_num (snd r)))
        SEP (dfull_post z (fst r) p pin pout ish rest gv; deflate_globals gv)))
    (stackframe_of f_deflate_stored).
Proof. intros E. unfold ds_fun_post, dfull_post. rewrite E. reflexivity. Qed.

Lemma runs_exit_det {A B} (body : A -> option (A + B)) a r r' :
  runs body a r -> body a = Some (inr r') -> r = r'.
Proof. intros H E. apply runs_inv in H as [H | [a' [H _]]]; congruence. Qed.

Lemma runs_step_det {A B} (body : A -> option (A + B)) a a' r :
  runs body a r -> body a = Some (inl a') -> runs body a' r.
Proof. intros H E. apply runs_inv in H as [H | [a'' [H R]]]; [congruence|]. congruence. Qed.

Lemma runs_last flush mb a s z l : runs (ds_body flush mb) a (s, z, l) -> l = 0 \/ l = 1.
Proof.
  intros H. remember (s, z, l) as rr eqn:Er. induction H; subst; [eapply ds_body_last; eauto | auto].
Qed.

Lemma out_inv_rest z z1 (rest : list val) : out_inv z z1 -> Zlength rest = z_avail_out z ->
  Zlength (z_out z1) - Zlength (z_out z) <= Zlength rest.
Proof. intros [[b E] [L P]] R. lia. Qed.

Lemma out_inv_grows z z1 : out_inv z z1 -> out_grows z z1.
Proof. intros [G _]. exact G. Qed.

Theorem deflate_stored_body : ob_deflate_stored.
Proof.
  unfold ob_deflate_stored.
  start_function.
  rewrite c_deflate_stored_eq in H0.
  apply bind_some in H0; destruct H0 as [[[s1 z1] lastF] [HL H0]].
  apply loop_runs in HL.
  pose proof (runs_last _ _ _ _ _ _ HL) as HlF.
  unfold dfull. Intros.
  unfold dstate_at. rewrite trees_at_split. unfold dtype_at, stat_at, win_at. Intros.
  forward.
  forward.
  set (MB64 := let a := u64 (d_pending_buf_size s - 5) in if a >? d_w_size s then d_w_size s else a).
  match goal with |- semax _ (PROPx _ (LOCALx ?L (SEPx ?S))) _ _ =>
    forward_if (PROPx [] (LOCALx (temp _t'1 (vl MB64) :: L) (SEPx S))) end.
  { forward. forward. entailer!.
    assert (Hw: 0 <= d_w_size s <= Int.max_unsigned) by (unfold dstate_ranges, u32_ok in H4; lia).
    rewrite Int.unsigned_repr in * by rep_lia. rewrite Int64.unsigned_repr in H6 by rep_lia.
    rewrite Int64.unsigned_repr_eq in H6. change Int64.modulus with 18446744073709551616 in H6.
    fold (u64 (d_pending_buf_size s - 5)) in H6.
    subst MB64. cbv zeta. destruct (Z.gtb_spec (u64 (d_pending_buf_size s - 5)) (d_w_size s)); [reflexivity | lia]. }
  { forward. forward. entailer!.
    assert (Hw: 0 <= d_w_size s <= Int.max_unsigned) by (unfold dstate_ranges, u32_ok in H4; lia).
    rewrite Int.unsigned_repr in * by rep_lia. rewrite Int64.unsigned_repr in H6 by rep_lia.
    rewrite Int64.unsigned_repr_eq in H6. change Int64.modulus with 18446744073709551616 in H6.
    fold (u64 (d_pending_buf_size s - 5)) in H6.
    subst MB64. cbv zeta. destruct (Z.gtb_spec (u64 (d_pending_buf_size s - 5)) (d_w_size s)); [lia|].
    rewrite vl_u64. reflexivity. }
  forward.
  forward.
  rewrite strm_at_split. Intros.
  forward.
  forward.
  set (mb := ds_min_block s).
  assert (Emb : u32 MB64 = mb) by reflexivity.
  set (used0 := z_avail_in z).
  unfold out_space at 1. Intros.
  match goal with Hr : Zlength rest = z_avail_out z |- _ => rename Hr into Hrest end.
  assert (Hz0 : 0 <= z_avail_out z <= Int.max_unsigned) by (unfold strm_ranges, u32_ok in H1; lia).
  forward_loop
    (EX s2 : dstate, EX z2 : strm,
     PROP (runs (ds_body flush mb) (s2, z2) (s1, z1, lastF); out_inv z z2)
     LOCAL (temp _min_block (vi mb); temp _last (vi 0); temp _used (vi used0);
            gvars gv; temp _s (p_s p); temp _flush (vi flush))
     SEP (dfull s2 z2 p pin pout ish (rest_after z z2 rest) msgv gv; deflate_globals gv))
  continue:
    (EX s2 : dstate, EX z2 : strm, EX l : Z,
     PROP ((l = 0 /\ runs (ds_body flush mb) (s2, z2) (s1, z1, lastF)) \/ (l <> 0 /\ (s2, z2, l) = (s1, z1, lastF));
           out_inv z z2)
     LOCAL (temp _min_block (vi mb); temp _last (vi l); temp _used (vi used0);
            gvars gv; temp _s (p_s p); temp _flush (vi flush))
     SEP (dfull s2 z2 p pin pout ish (rest_after z z2 rest) msgv gv; deflate_globals gv))
  break:
    (PROP (out_inv z z1)
     LOCAL (temp _min_block (vi mb); temp _last (vi lastF); temp _used (vi used0);
            gvars gv; temp _s (p_s p); temp _flush (vi flush))
     SEP (dfull s1 z1 p pin pout ish (rest_after z z1 rest) msgv gv; deflate_globals gv)).
  { (* entry *)
    Exists s z.
    assert (EM : Vint (Int.repr (Int64.unsigned (Int64.repr MB64))) = vi mb).
    { rewrite <- Emb, vi_u32. subst MB64. cbv zeta. pose proof (u64_range (d_pending_buf_size s - 5)).
      assert (Hw: 0 <= d_w_size s <= Int.max_unsigned) by (unfold dstate_ranges, u32_ok in H4; lia).
      destruct (_ >? _); rewrite Int64.unsigned_repr by rep_lia; reflexivity. }
    rewrite EM. rewrite rest_after_same.
    assert (Hi : out_inv z z) by (apply out_inv_refl; lia).
    unfold dfull, dstate_at. rewrite trees_at_split, strm_at_split. unfold dtype_at, stat_at, win_at, out_space.
    entailer!. }
  { (* the body *)
    Intros s2 z2.
    pose proof (out_inv_le _ _ H7) as Ha2.
    assert (Ha2' : 0 <= z_avail_out z2 < 4294967296) by rep_lia.
    destruct (ds_body flush mb (s2, z2)) as [res|] eqn:Eb;
      [| apply runs_inv in H6; destruct H6 as [E|[? [E _]]]; rewrite Eb in E; discriminate].
    eapply semax_post_flipped.
    { apply (ds_body_frag p pin pout ish (rest_after z z2 rest) msgv gv s2 z2 flush mb used0 res); auto.
      - unfold mb, ds_min_block. apply u32_range.
      - unfold used0. unfold strm_ranges, u32_ok in H1. lia. }
    - unfold POSTCONDITION, abbreviate. rewrite RAn_loop1. unfold body_post. cbn [RA_normal].
      Intros s3 z3 l.
      match goal with HH : res = _ |- _ => rename HH into Hres end.
      assert (I3 : out_inv z2 z3).
      { pose proof (ds_body_inv _ _ _ _ _ Ha2' Eb) as I. rewrite Hres in I. destruct (l =? 0); exact I. }
      rewrite (rest_after_trans z z2 z3 rest) by (auto using out_inv_grows, out_inv_rest).
      Exists s3 z3 l.
      assert (I13 : out_inv z z3) by (eapply out_inv_trans; eauto).
      assert (HP : (l = 0 /\ runs (ds_body flush mb) (s3, z3) (s1, z1, lastF)) \/
                   (l <> 0 /\ (s3, z3, l) = (s1, z1, lastF))).
      { subst res. destruct (Z.eqb_spec l 0) as [El|El].
        - left. split; auto. eapply runs_step_det; eauto.
        - right. split; auto. symmetry. eapply runs_exit_det; eauto. }
      entailer!.
    - unfold POSTCONDITION, abbreviate. rewrite RAb_loop1, RAn_override. unfold body_post. cbn [RA_break].
      Intros.
      match goal with HH : res = _ |- _ => rename HH into Hres end.
      subst res. pose proof (runs_exit_det _ _ _ _ H6 Eb) as E. inversion E; subst.
      entailer!.
    - unfold POSTCONDITION, abbreviate. rewrite RAc_loop1. unfold body_post. cbn [RA_continue].
      apply andp_left2, FF_left.
    - intros vl. unfold POSTCONDITION, abbreviate. rewrite RAr_loop1. unfold body_post. cbn [RA_return].
      apply andp_left2, FF_left. }
  { (* the test *)
    Intros s2 z2 l.
    forward_if.
    - forward. Exists s2 z2.
      destruct H6 as [[Hl HR] | [Hl E]]; [subst l; entailer! |].
      inversion E; subst. exfalso. destruct HlF as [-> | ->]; [lia | discriminate].
    - forward. destruct H6 as [[Hl _] | [_ E]]; [subst l; contradiction |].
      inversion E; subst. entailer!. }
  Intros.
  apply bind_some in H0; destruct H0 as [s2 [Hw H0]].
  unfold dfull at 1. Intros. unfold dstate_at at 1. rewrite trees_at_split, strm_at_split. unfold dtype_at at 1.
  Intros.
  forward. forward. forward.
  set (used1 := u32 (used0 - z_avail_in z1)) in *.
  assert (Eu : Vint (Int.sub (Int.repr used0) (Int.repr (z_avail_in z1))) = vi used1)
    by (rewrite sub_repr32; unfold used1; rewrite vi_u32; reflexivity).
  rewrite Eu.
  eapply semax_seq'.
  { eapply semax_pre;
      [| apply (ds_window_frag p pin pout ish (rest_after z z1 rest) msgv gv s1 z1 flush used1 lastF s2);
         [apply u32_range | exact Hw]].
    unfold dfull, dstate_at. rewrite trees_at_split, strm_at_split. unfold dtype_at. entailer!. }
  abbreviate_semax.
  (* if (s->high_water < s->strstart) s->high_water = s->strstart; *)
  set (s3 := upd_high_water s2) in *.
  unfold dfull at 1. Intros. unfold dstate_at at 1. unfold win_at at 1, match_at at 1. Intros.
  forward. forward.
  forward_if (PROP () LOCAL (temp _used (vi used1); temp _last (vi lastF); gvars gv; temp _s (p_s p);
                             temp _flush (vi flush))
              SEP (dfull s3 z1 p pin pout ish (rest_after z z1 rest) msgv gv; deflate_globals gv)).
  { match goal with HR : dstate_ranges s2 |- _ => pose proof HR as HR2 end.
    unfold dstate_ranges, u32_ok, u64_ok in HR2.
    assert (Hss : 0 <= d_strstart s2 <= Int.max_unsigned) by lia.
    assert (Hhw : 0 <= d_high_water s2 <= Int64.max_unsigned) by lia.
    forward. forward.
    match goal with HH : Int64.unsigned _ < Int64.unsigned _ |- _ => rename HH into Hlt end.
    rewrite Int.unsigned_repr in * by rep_lia. rewrite !Int64.unsigned_repr in Hlt by rep_lia.
    assert (E3 : s3 = set_d_high_water s2 (d_strstart s2))
      by (unfold s3, upd_high_water; rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity).
    rewrite E3. unfold dfull, dstate_at, win_at, match_at. entailer!.
    all: first [apply dstate_ranges_hw; [assumption | unfold u64_ok; rep_lia] | apply derives_refl]. }
  { match goal with HR : dstate_ranges s2 |- _ => pose proof HR as HR2 end.
    unfold dstate_ranges, u32_ok, u64_ok in HR2.
    assert (Hss : 0 <= d_strstart s2 <= Int.max_unsigned) by lia.
    assert (Hhw : 0 <= d_high_water s2 <= Int64.max_unsigned) by lia.
    forward.
    match goal with HH : Int64.unsigned _ >= Int64.unsigned _ |- _ => rename HH into Hge end.
    rewrite Int.unsigned_repr in * by rep_lia. rewrite !Int64.unsigned_repr in Hge by rep_lia.
    assert (E3 : s3 = s2)
      by (unfold s3, upd_high_water; rewrite (proj2 (Z.ltb_ge _ _)) by lia; reflexivity).
    rewrite E3. unfold dfull, dstate_at, win_at, match_at. entailer!. }
  (* if (last) { s->bi_used = 8; return finish_done; } *)
  forward_if (PROP (lastF = 0) LOCAL (temp _used (vi used1); temp _last (vi lastF); gvars gv; temp _s (p_s p);
                                      temp _flush (vi flush))
              SEP (dfull s3 z1 p pin pout ish (rest_after z z1 rest) msgv gv; deflate_globals gv)).
  { assert (El : lastF = 1) by (destruct HlF; subst; [contradiction | auto]). subst lastF.
    cbv zeta in H0. cbn in H0. inversion H0; subst r; clear H0.
    unfold dfull at 1. Intros. unfold dstate_at at 1. rewrite trees_at_split. unfold out_at at 1. Intros.
    forward. forward.
    unfold dfull_post. cbn [fst snd]. Exists msgv.
    unfold dfull, dstate_at. rewrite trees_at_split. unfold out_at.
    match goal with HR : out_ok _ _ |- _ => rename HR into Hoo end.
    assert (Hoo' : out_ok (tr_out (fst (d_trm (set_d_bi_used s3 8)))) (snd (d_trm (set_d_bi_used s3 8)))).
    { destruct (tr_out (fst (d_trm s3))) as [ob op obb obv obu] eqn:Eo.
      change (tr_out (fst (d_trm (set_d_bi_used s3 8)))) with
        (mkOut (o_buf (tr_out (d_tr s3))) (o_pending (tr_out (d_tr s3))) (o_bi_buf (tr_out (d_tr s3)))
               (o_bi_valid (tr_out (d_tr s3))) 8).
      change (fst (d_trm s3)) with (d_tr s3) in Eo. rewrite Eo. cbn [o_buf o_pending o_bi_buf o_bi_valid].
      apply (out_ok_set_bits ob op obb obv obu _ obb obv 8 Hoo);
        destruct Hoo as [_ [_ [_ [Hb [Hv _]]]]]; cbn in *; rep_lia. }
    assert (Hr3 : dstate_ranges (set_d_bi_used s3 8)) by (apply dstate_ranges_bi_used; assumption).
    entailer!.
    apply derives_refl. }
  { forward. assert (lastF = 0) by (destruct HlF; subst; [auto | discriminate]). entailer!. }
  Intros. subst lastF. cbv zeta in H0. cbn [negb Z.eqb] in H0.
  (* if (flush != Z_NO_FLUSH && flush != Z_FINISH && s->strm->avail_in == 0 &&
         (long)s->strstart == s->block_start) return block_done; *)
  set (b1 := (negb (flush =? Rep.Z_NO_FLUSH) && negb (flush =? Rep.Z_FINISH))%bool).
  set (b2 := (b1 && (z_avail_in z1 =? 0))%bool).
  set (b3 := (b2 && (d_strstart s3 =? d_block_start s3))%bool).
  change ((if b3 then Some (s3, z1, block_done) else ds_phase2 s3 z1 flush) = Some r) in H0.
  unfold dfull at 1. Intros. unfold dstate_at at 1. rewrite trees_at_split, strm_at_split.
  unfold dtype_at at 1, match_at at 1. Intros.
  match goal with HR : dstate_ranges s3 |- _ => pose proof HR as HR3 end.
  match goal with HR : strm_ranges z1 |- _ => pose proof HR as HZ1 end.
  unfold dstate_ranges, u32_ok, u64_ok, s64_ok in HR3. unfold strm_ranges, u32_ok in HZ1.
  assert (Hss : 0 <= d_strstart s3 <= Int.max_unsigned) by lia.
  assert (Hbs : Int64.min_signed <= d_block_start s3 <= Int64.max_signed) by lia.
  assert (Hai : 0 <= z_avail_in z1 <= Int.max_unsigned) by lia.
  match goal with |- semax _ (PROPx _ (LOCALx ?L (SEPx ?S))) _ _ =>
    forward_if (PROPx [] (LOCALx (temp _t'8 (bool2val b1) :: L) (SEPx S))) end.
  { forward. entailer!. rewrite int_eq_repr_s by rep_lia. unfold b1.
    change Rep.Z_NO_FLUSH with 0. change Rep.Z_FINISH with 4.
    destruct (Z.eqb_spec flush 0) as [->|]; [contradiction|]. reflexivity. }
  { forward. entailer!. }
  match goal with |- semax _ (PROPx _ (LOCALx ?L (SEPx ?S))) _ _ =>
    forward_if (PROPx [] (LOCALx (temp _t'9 (bool2val b2) :: L) (SEPx S))) end.
  { match goal with HH : b1 = true |- _ =>
      assert (Eb2 : b2 = (z_avail_in z1 =? 0)) by (unfold b2; rewrite HH; reflexivity) end.
    clearbody b2. forward. forward. forward. entailer!.
    all: try rewrite int_eq_repr_u by rep_lia; fin_b. }
  { match goal with HH : b1 = false |- _ =>
      assert (Eb2 : b2 = false) by (unfold b2; rewrite HH; reflexivity) end.
    clearbody b2. forward. entailer!. all: fin_b. }
  match goal with |- semax _ (PROPx _ (LOCALx ?L (SEPx ?S))) _ _ =>
    forward_if (PROPx [] (LOCALx (temp _t'10 (bool2val b3) :: L) (SEPx S))) end.
  { match goal with HH : b2 = true |- _ =>
      assert (Eb3 : b3 = (d_strstart s3 =? d_block_start s3)) by (unfold b3; rewrite HH; reflexivity) end.
    clearbody b3. forward. forward. forward. entailer!.
    all: try rewrite Int.unsigned_repr by rep_lia; try rewrite int64_eq_repr_s by rep_lia;
      fin_b. }
  { match goal with HH : b2 = false |- _ =>
      assert (Eb3 : b3 = false) by (unfold b3; rewrite HH; reflexivity) end.
    clearbody b3. forward. entailer!. all: fin_b. }
  forward_if (PROP (b3 = false) LOCAL (temp _last (vi 0); gvars gv; temp _s (p_s p); temp _flush (vi flush))
              SEP (dfull s3 z1 p pin pout ish (rest_after z z1 rest) msgv gv; deflate_globals gv)).
  { destruct b3; [|discriminate]. inversion H0; subst r; clear H0.
    forward.
    unfold dfull_post. cbn [fst snd]. Exists msgv.
    unfold dfull, dstate_at. rewrite trees_at_split, strm_at_split. unfold dtype_at, match_at. entailer!. }
  { forward. destruct b3; [discriminate|]. unfold dfull, dstate_at. rewrite trees_at_split, strm_at_split.
    unfold dtype_at, match_at. entailer!. }
  Intros.
  match goal with HH : b3 = false |- _ => rewrite HH in H0 end.
  (* the second phase *)
  assert (I2 : out_inv z1 (snd (fst r))).
  { eapply ds_phase2_inv; [exact H0 |]. pose proof (out_inv_le _ _ H6). lia. }
  assert (Etr : rest_after z1 (snd (fst r)) (rest_after z z1 rest) = rest_after z (snd (fst r)) rest)
    by (apply rest_after_trans; auto using out_inv_grows, out_inv_rest).
  unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
  rewrite <- (ds_fun_post_eq p pin pout ish rest gv z z1 r Etr).
  apply (ds_phase2_frag p pin pout ish (rest_after z z1 rest) msgv gv s3 z1 flush r H H0).
Qed.
