(** * The body of fill_window (deflate.c) against its shared specification DSpec.fill_window_spec (v2 base) *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.proof.deflate.Obligations.
Require Import Zlib.deflate.code.
Require Import Zlib.proof.deflate.FWKit.
Require Import Zlib.proof.deflate.FWSlide Zlib.proof.deflate.FWRead Zlib.proof.deflate.FWIns
  Zlib.proof.deflate.FWHigh.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

(** ** The fields the loop itself reads, and the rest of the stream *)
Definition fw_fields (s : dstate) (z : strm) (p : dptrs) : mpred :=
  (@field_at DCS.CS Ews t_ds (DOT _w_size) (vi (d_w_size s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _window_size) (vl (d_window_size s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _strstart) (vi (d_strstart s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _lookahead) (vi (d_lookahead s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _strm) (p_strm p) (p_s p) *
   @field_at DCS.CS Ews t_strm (DOT _avail_in) (vi (z_avail_in z)) (p_strm p))%logic.

Definition fw_rest (s : dstate) (z : strm) (p : dptrs) (pin : val) (ish : share) (msgv : val) (gv : globals)
    : mpred :=
  (ltree_at (tr_ltree (d_tr s)) (p_s p) * dtree_at (tr_dtree (d_tr s)) (p_s p) *
   bltree_at (tr_bltree (d_tr s)) (p_s p) *
   ldesc_at (field_address t_ds (DOT Zlib.trees.code._dyn_ltree) (p_s p)) (tr_lmax (d_tr s)) (gv Zlib.trees.code._static_l_desc) (p_s p) *
   ddesc_at (field_address t_ds (DOT Zlib.trees.code._dyn_dtree) (p_s p)) (tr_dmax (d_tr s)) (gv Zlib.trees.code._static_d_desc) (p_s p) *
   bldesc_at (field_address t_ds (DOT Zlib.trees.code._bl_tree) (p_s p)) (tr_blmax (d_tr s)) (gv Zlib.trees.code._static_bl_desc) (p_s p) *
   work_at (tr_wk (d_tr s)) (p_s p) * out_at (tr_out (d_tr s)) (d_pbm s) (p_s p) (p_pbuf p) *
   sym_at (d_tr s) (p_s p) (p_pbuf p) * lvl_at (d_tr s) (p_s p) *
   @field_at DCS.CS Ews t_strm (DOT _data_type) (vi (tr_data_type (d_tr s))) (p_strm p) *
   @field_at DCS.CS Ews t_ds (DOT _window) (p_window p) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _w_bits) (vi (d_w_bits s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _w_mask) (vi (d_w_mask s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _high_water) (vl (d_high_water s)) (p_s p) *
   @data_at DCS.CS Ews (tarray tuchar (Zlength (mb_val (d_window s)))) (mb_vals (d_window s)) (p_window p) *
   hash_at s p *
   @field_at DCS.CS Ews t_ds (DOT _block_start) (vl (d_block_start s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _match_length) (vi (d_match_length s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _prev_match) (vi (d_prev_match s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _match_available) (vi (d_match_available s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _match_start) (vi (d_match_start s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _prev_length) (vi (d_prev_length s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _insert) (vi (d_insert s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _slid) (vi (d_slid s)) (p_s p) *
   cfg_at s p * stat_at s p *
   @field_at DCS.CS Ews t_strm (DOT _next_in) (offset_val (z_next_in z) pin) (p_strm p) *
   @field_at DCS.CS Ews t_strm (DOT _total_in) (vl (z_total_in z)) (p_strm p) *
   @field_at DCS.CS Ews t_strm (DOT _msg) msgv (p_strm p) *
   @field_at DCS.CS Ews t_strm (DOT _state) (p_s p) (p_strm p) *
   @field_at DCS.CS Ews t_strm (DOT _zalloc) (gv _zcalloc) (p_strm p) *
   @field_at DCS.CS Ews t_strm (DOT _zfree) (gv _zcfree) (p_strm p) *
   @field_at DCS.CS Ews t_strm (DOT _opaque) nullval (p_strm p) *
   @field_at DCS.CS Ews t_strm (DOT _adler) (vl (z_adler z)) (p_strm p) *
   @field_at_ DCS.CS Ews t_strm (DOT _reserved) (p_strm p) *
   in_obj ish z pin)%logic.

Definition fw_pure (s : dstate) (z : strm) (ish : share) (msgv : val) : Prop :=
  strm_ranges z /\ msg_ok (z_msg z) msgv /\ readable_share ish /\ dstate_ranges s /\
  Int.min_signed <= tr_data_type (d_tr s) <= Int.max_signed.

Lemma dfull_in_open s z p pin ish msgv gv :
  dfull_in s z p pin ish msgv gv |-- !! fw_pure s z ish msgv && (fw_fields s z p * fw_rest s z p pin ish msgv gv).
Proof.
  unfold dfull_in, dstate_at, trees_at, dtype_at, win_at, match_at, strm_in_at, fw_fields, fw_rest, fw_pure.
  cbn [fst snd d_trm]. Intros. apply andp_right; [apply prop_right; tauto|]. cancel.
Qed.

Lemma dfull_in_close s z p pin ish msgv gv :
  fw_pure s z ish msgv ->
  fw_fields s z p * fw_rest s z p pin ish msgv gv |-- dfull_in s z p pin ish msgv gv.
Proof.
  intros (H1 & H2 & H3 & H4 & H5).
  unfold dfull_in, dstate_at, trees_at, dtype_at, win_at, match_at, strm_in_at, fw_fields, fw_rest.
  cbn [fst snd d_trm]. entailer!.
Qed.

Lemma dfull_in_close' s z p pin ish msgv gv :
  fw_pure s z ish msgv ->
  @field_at DCS.CS Ews t_ds (DOT _w_size) (vi (d_w_size s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _window_size) (vl (d_window_size s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _strstart) (vi (d_strstart s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _lookahead) (vi (d_lookahead s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _strm) (p_strm p) (p_s p) *
  @field_at DCS.CS Ews t_strm (DOT _avail_in) (vi (z_avail_in z)) (p_strm p) *
  fw_rest s z p pin ish msgv gv |-- dfull_in s z p pin ish msgv gv.
Proof. intros H. eapply derives_trans; [|apply dfull_in_close; exact H]. unfold fw_fields. cancel. Qed.

Lemma repr_u64_u32 x : Int.repr (x mod 18446744073709551616) = Int.repr (u32 x).
Proof.
  apply Int.eqm_samerepr. unfold u32. apply Int.eqm_trans with x.
  - red; red. exists (-(4294967296 * (x / 18446744073709551616))).
    rewrite Z.mod_eq by lia. change Int.modulus with 4294967296. lia.
  - change 4294967296 with Int.modulus. apply Zbits.eqmod_mod. reflexivity.
Qed.

Lemma more_eq a b c : 0 <= b <= Int.max_unsigned -> 0 <= c <= Int.max_unsigned ->
  Int.repr (Int64.unsigned (Int64.sub (Int64.sub (Int64.repr a) (Int64.repr (Int.unsigned (Int.repr b))))
     (Int64.repr (Int.unsigned (Int.repr c))))) = Int.repr (u32 (a - b - c)).
Proof.
  intros. rewrite !Int.unsigned_repr by lia. rewrite !sub64_repr, Int64.unsigned_repr_eq.
  apply repr_u64_u32.
Qed.

Lemma runs_inv' {A B} (body : A -> option (A + B)) a r :
  runs body a r -> exists res, body a = Some res /\
    match res with inl a' => runs body a' r | inr r' => r' = r end.
Proof.
  intros H. destruct (runs_inv _ _ _ H) as [E|[a' [E R]]]; eexists; split; eauto; reflexivity.
Qed.

Lemma fw_slide_more s m s' m' : 0 <= m <= Int.max_unsigned ->
  c_fw_slide s m = Some (s', m') -> 0 <= m' <= Int.max_unsigned.
Proof.
  intros Hm. unfold c_fw_slide. destruct (_ >=? _).
  - intros H. inv_bind H. inv_bind H. inv_bind H. inv_bind H. inv_bind H. inversion H; subst.
    unfold u32. pose proof (Z.mod_pos_bound (m + d_w_size s) 4294967296). rep_lia.
  - intros H; inversion H; subst; auto.
Qed.


(** ** The loop: invariants, one iteration, the test *)
Definition S_body : statement := fw_sub (fn_body f_fill_window) [1;0;0]%nat.
Definition S_incr : statement := fw_sub (fn_body f_fill_window) [1;0;1]%nat.

Definition fw_inv (s sl : dstate) (zl : strm) (p : dptrs) (pin : val) (ish : share) (msgv : val)
    (gv : globals) : environ -> mpred :=
  EX s1 : dstate, EX z1 : strm,
  PROP (runs fw_body (s1, z1) (sl, zl); d_w_size s1 = d_w_size s)
  LOCAL (temp _wsize (vi (d_w_size s)); gvars gv; temp _s (p_s p))
  SEP (dfull_in s1 z1 p pin ish msgv gv; deflate_globals gv).

Definition fw_inv' (s sl : dstate) (zl : strm) (p : dptrs) (pin : val) (ish : share) (msgv : val)
    (gv : globals) : environ -> mpred :=
  EX s1 : dstate, EX z1 : strm,
  PROP (if andb (d_lookahead s1 <? MIN_LOOKAHEAD) (negb (z_avail_in z1 =? 0))
        then runs fw_body (s1, z1) (sl, zl) else (s1, z1) = (sl, zl);
        d_w_size s1 = d_w_size s)
  LOCAL (temp _wsize (vi (d_w_size s)); gvars gv; temp _s (p_s p))
  SEP (dfull_in s1 z1 p pin ish msgv gv; deflate_globals gv).

Definition fw_brk (s sl : dstate) (zl : strm) (p : dptrs) (pin : val) (ish : share) (msgv : val)
    (gv : globals) : environ -> mpred :=
  PROP () LOCAL (temp _wsize (vi (d_w_size s)); gvars gv; temp _s (p_s p))
  SEP (dfull_in sl zl p pin ish msgv gv; deflate_globals gv).

Lemma fw_loop_body {Espec : OracleKind} s sl zl p pin ish msgv gv :
  semax Delta_fw (fw_inv s sl zl p pin ish msgv gv) S_body
    (loop1_ret_assert (fw_inv' s sl zl p pin ish msgv gv) (normal_ret_assert (fw_brk s sl zl p pin ish msgv gv))).
Proof.
  unfold fw_inv, fw_inv', fw_brk. cbv [S_body fw_sub f_fill_window fn_body]. abbreviate_semax.
  (* reserve the names the proof script below was written with *)
  pose proof I as H. pose proof I as x. pose proof I as Ha. pose proof I as Ha0.
  Intros s1 z1. rename H0 into Hrun, H1 into Hws.
    sep_apply dfull_in_open. Intros. rename H0 into Hp1. unfold fw_fields. Intros.
    Time forward. Time forward. Time forward. Time forward.
    Time sep_apply (dfull_in_close' s1 z1 p pin ish msgv gv Hp1).
    rewrite more_eq by (unfold fw_pure, dstate_ranges, u32_ok in Hp1; tauto).
    set (more := u32 (d_window_size s1 - d_lookahead s1 - d_strstart s1)).
    forward_if (PROP () LOCAL (temp _more (vi more); temp _wsize (vi (d_w_size s)); gvars gv; temp _s (p_s p))
                SEP (dfull_in s1 z1 p pin ish msgv gv; deflate_globals gv)).
    { discriminate. }
    { forward. entailer!. }
    destruct (runs_inv' _ _ _ Hrun) as [res [Hb Hres]].
    lazy beta iota zeta delta [fw_body] in Hb. fold more in Hb.
    inv_bind Hb. destruct x0 as [s2 more2]. rename Ha1 into Hsl.
    assert (Hm : 0 <= more <= Int.max_unsigned) by (unfold more, u32; pose proof (Z.mod_pos_bound (d_window_size s1 - d_lookahead s1 - d_strstart s1) 4294967296); rep_lia).
    eapply semax_seq'.
    { eapply semax_pre; [|exact (fw_slide Espec p pin ish msgv gv s1 z1 more s2 more2 Hm Hsl)].
      rewrite Hws. entailer!. }
    pose proof (fw_slide_w_size _ _ _ _ Hsl) as Hws2. rewrite Hws in Hws2.
    subst MORE_COMMANDS; unfold abbreviate; abbreviate_semax.
    sep_apply dfull_in_open. Intros. rename H0 into Hp2. unfold fw_fields. Intros.
    forward. forward.
    forward_if (PROP (z_avail_in z1 <> 0)
                LOCAL (temp _wsize (vi (d_w_size s1)); temp _more (vi more2); temp _s (p_s p); gvars gv)
                SEP (dfull_in s2 z1 p pin ish msgv gv; deflate_globals gv)).
    { assert (Hz0 : z_avail_in z1 = 0).
      { pose proof Hp2 as (Hsr & _). unfold strm_ranges, u32_ok in Hsr.
        apply repr_inj_unsigned in H0; rep_lia. }
      rewrite Hz0 in Hb. cbn in Hb. inversion Hb; subst res. inversion Hres; subst sl zl.
      sep_apply (dfull_in_close' s2 z1 p pin ish msgv gv Hp2).
      forward. rewrite Hws. entailer!. }
    { forward. sep_apply (dfull_in_close' s2 z1 p pin ish msgv gv Hp2). entailer!. }
    Intros. rewrite (proj2 (Z.eqb_neq _ _) H0) in Hb.
    inv_bind Hb. destruct x0 as [z3 data]. rename Ha1 into Hrb.
    inv_bind Hb. rename x0 into win, Ha1 into Hwin.
    inv_bind Hb. rename x0 into s4, Ha1 into Hins.
    change (d_lookahead (set_d_window s2 win)) with (d_lookahead s2) in Hins.
    pose proof (fw_slide_more _ _ _ _ Hm Hsl) as Hm2.
    apply seq_assoc.
    eapply semax_seq'.
    { eapply semax_pre; [|exact (fw_read Espec p pin ish msgv gv s2 z1 (d_w_size s1) more2 z3 data win Hm2 Hrb Hwin)].
      entailer!. }
    pose proof (fw_insert_w_size _ _ Hins) as Hws4. cbn in Hws4. rewrite Hws2 in Hws4.
    eapply semax_post_flipped'.
    { eapply semax_pre; [|exact (fw_ins Espec p pin ish msgv gv _ z3 (d_w_size s1) s4 Hins)]. entailer!. }
    Exists s4 z3. rewrite Hws. entailer!.
    destruct (andb _ _); inversion Hb; subst res; exact Hres. 
Qed.

Lemma fw_loop_incr {Espec : OracleKind} s sl zl p pin ish msgv gv :
  semax Delta_fw (fw_inv' s sl zl p pin ish msgv gv) S_incr
    (loop2_ret_assert (fw_inv s sl zl p pin ish msgv gv) (normal_ret_assert (fw_brk s sl zl p pin ish msgv gv))).
Proof.
  unfold fw_inv, fw_inv', fw_brk. cbv [S_incr fw_sub f_fill_window fn_body]. abbreviate_semax.
  pose proof I as H.
  Intros s1 z1. rename H0 into Hrun, H1 into Hws.
    sep_apply dfull_in_open. Intros. rename H0 into Hp1. unfold fw_fields. Intros.
    pose proof Hp1 as (Hsr & _ & _ & Hdr & _). unfold strm_ranges, u32_ok in Hsr. unfold dstate_ranges, u32_ok in Hdr.
    forward.
    forward_if (PROP () LOCAL (temp _t'1 (Val.of_bool (andb (d_lookahead s1 <? MIN_LOOKAHEAD) (negb (z_avail_in z1 =? 0))));
                               temp _wsize (vi (d_w_size s)); gvars gv; temp _s (p_s p))
                SEP (dfull_in s1 z1 p pin ish msgv gv; deflate_globals gv)).
    { forward. forward. forward. sep_apply (dfull_in_close' s1 z1 p pin ish msgv gv Hp1).
      rewrite (proj2 (Z.ltb_lt _ _)) by (cbv [MIN_LOOKAHEAD MAX_MATCH MIN_MATCH]; lia).
      destruct (zeq (z_avail_in z1) 0) as [E|E]; [rewrite E | rewrite (proj2 (Z.eqb_neq _ _) E)]; entailer!. }
    { forward. sep_apply (dfull_in_close' s1 z1 p pin ish msgv gv Hp1).
      rewrite (proj2 (Z.ltb_ge _ _)) by (cbv [MIN_LOOKAHEAD MAX_MATCH MIN_MATCH]; lia). entailer!. }
    destruct (andb _ _) eqn:EB.
    - forward_if.
      + forward. Exists s1 z1. entailer!.
      + inversion H0.
    - forward_if.
      + exfalso; apply H0; reflexivity.
      + inversion Hrun; subst. forward. entailer!. 
Qed.

Lemma c_fill_window_inv s z r : c_fill_window s z = Some r ->
  exists sl zl s2, runs fw_body (s, z) (sl, zl) /\ c_fw_high_water sl = Some s2 /\ r = (s2, zl).
Proof.
  unfold c_fill_window. intros H. inv_bind H. destruct x as [sl zl]. inv_bind H. inversion H; subst.
  apply loop_runs in Ha. eauto 6.
Qed.

Lemma body_fill_window : ob_fill_window.
Proof.
  unfold ob_fill_window. start_function.
  (* the model run, by a separate lemma: inverting it here makes the kernel's Qed check very slow *)
  destruct (c_fill_window_inv _ _ _ H) as (sl & zl & x & Ha & Ha0 & ->). clear H.
  sep_apply dfull_in_open. Intros. unfold fw_fields. Intros. Time forward.
  Time sep_apply (dfull_in_close' s z p pin ish msgv gv H).
  eapply semax_seq'.
  { eapply semax_pre;
      [| apply semax_loop with (Q' := fw_inv' s sl zl p pin ish msgv gv);
         [apply fw_loop_body | apply fw_loop_incr]].
    unfold fw_inv. Exists s z. entailer!. }
  unfold fw_brk. abbreviate_semax.
  eapply semax_post_flipped'.
  { eapply semax_pre; [|exact (fw_high Espec p pin ish msgv gv sl zl (d_w_size s) x Ha0)]. entailer!. }
  cbn [fst snd]. entailer!. Exists msgv. entailer!.
Qed.
