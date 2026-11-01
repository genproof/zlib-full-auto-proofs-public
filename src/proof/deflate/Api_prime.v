(** * Body proof of deflatePrime. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.deflate.DModel3 Zlib.proof.deflate.DSpec Zlib.proof.deflate.DCS.
Require Import Zlib.deflate.code.
Require Import Zlib.proof.deflate.ApiKit.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.trees.TSpec.
Require Zlib.trees.code.

#[export] Existing Instance DCS.CS.
Local Open Scope Z_scope.
Local Strategy opaque [loop loop2].

(** ** trees_at without its gv's in sight: out_at, sym_at and the rest (opaque) *)
Definition trees_rest (t : tstate) (sp strmp : val) (gv : globals) : mpred :=
  (ltree_at (tr_ltree t) sp * dtree_at (tr_dtree t) sp * bltree_at (tr_bltree t) sp *
   ldesc_at (field_address t_ds (DOT Zlib.trees.code._dyn_ltree) sp) (tr_lmax t) (gv Zlib.trees.code._static_l_desc) sp *
   ddesc_at (field_address t_ds (DOT Zlib.trees.code._dyn_dtree) sp) (tr_dmax t) (gv Zlib.trees.code._static_d_desc) sp *
   bldesc_at (field_address t_ds (DOT Zlib.trees.code._bl_tree) sp) (tr_blmax t) (gv Zlib.trees.code._static_bl_desc) sp *
   work_at (tr_wk t) sp * lvl_at t sp * dtype_at t sp strmp)%logic.

Lemma trees_at_split cs sp pbp strmp gv :
  trees_at cs sp pbp strmp gv =
  (out_at (tr_out (fst cs)) (snd cs) sp pbp * sym_at (fst cs) sp pbp * trees_rest (fst cs) sp strmp gv)%logic.
Proof. unfold trees_at, trees_rest. apply pred_ext; cancel. Qed.

(** ** Model helpers (as in TLemmas.v) *)
Lemma bind_inv' {A B} (a : option A) (f : A -> option B) r :
  bind a f = Some r -> exists x, a = Some x /\ f x = Some r.
Proof. destruct a; simpl; [eauto | discriminate]. Qed.
Lemma guard_inv' b : guard b = Some tt -> b = true.
Proof. destruct b; simpl; congruence. Qed.
Ltac inv_bind H :=
  let x := fresh "x" in let Ha := fresh "Ha" in
  apply bind_inv' in H; destruct H as [x [Ha H]].

(** ** The model: set_d_out *)
Lemma sdo_self s : set_d_out s (d_out s) = s.
Proof. destruct s as [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25
  a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 t m]. destruct t. reflexivity. Qed.
Lemma sdo_twice s x y : set_d_out (set_d_out s x) y = set_d_out s y.
Proof. reflexivity. Qed.
Lemma sdo_out s o m : tr_out (d_tr (set_d_out s (o, m))) = o.
Proof. reflexivity. Qed.
Lemma sdo_pbm s o m : d_pbm (set_d_out s (o, m)) = m.
Proof. reflexivity. Qed.
Lemma sdo_d_out s om : d_out (set_d_out s om) = om.
Proof. destruct om; reflexivity. Qed.

Definition pr_put (bv b : Z) : Z := if 16 - bv >? b then b else 16 - bv.
Definition pr_bb (o : outbuf) (v put : Z) : Z :=
  u16 (Z.lor (o_bi_buf o) (u16 (Z.shiftl (Z.land v (Z.shiftl 1 put - 1)) (o_bi_valid o)))).
Definition pr_o1 (o : outbuf) (v put : Z) : outbuf :=
  mkOut (o_buf o) (o_pending o) (pr_bb o v put) (o_bi_valid o + put) (o_bi_used o).

Lemma prime_body_inv s o m b v x :
  prime_body (set_d_out s (o, m), b, v) = Some x ->
  0 <= o_bi_valid o <= 16 /\
  exists om, c_tr_flush_bits (pr_o1 o v (pr_put (o_bi_valid o) b), m) = Some om /\
  x = (if b - pr_put (o_bi_valid o) b =? 0 then inr (set_d_out s om)
       else inl (set_d_out s om, b - pr_put (o_bi_valid o) b, Z.shiftr v (pr_put (o_bi_valid o) b))).
Proof.
  intros H. cbv beta zeta iota delta [prime_body] in H. rewrite sdo_out, sdo_pbm in H.
  inv_bind H. destruct x0. apply guard_inv' in Ha. apply andb_prop in Ha. destruct Ha as [Hg1 Hg2].
  apply Z.leb_le in Hg1. apply Z.leb_le in Hg2. unfold Buf_size in *.
  split; [lia|].
  inv_bind H. clear Ha x0.
  rewrite sdo_twice, sdo_d_out in H.
  inv_bind H. exists x0. split.
  - unfold pr_o1, pr_bb, pr_put. exact Ha.
  - rewrite sdo_twice in H. unfold pr_put.
    destruct (b - (if 16 - o_bi_valid o >? b then b else 16 - o_bi_valid o) =? 0); inversion H; reflexivity.
Qed.

Lemma put_byte_len o m c r : c_put_byte (o, m) c = Some r -> Zlength (o_buf (fst r)) = Zlength (o_buf o).
Proof.
  unfold c_put_byte, wr. intros H. destruct (in_range (o_pending o) (Zlength (o_buf o))); [|discriminate].
  cbn in H. inversion H; subst. cbn. apply Zlength_upd_Znth.
Qed.

Lemma flush_bits_len o m r : c_tr_flush_bits (o, m) = Some r -> Zlength (o_buf (fst r)) = Zlength (o_buf o).
Proof.
  unfold c_tr_flush_bits, c_bi_flush. intros H.
  destruct (o_bi_valid o =? 16).
  - inv_bind H. destruct x as [o1 m1]. unfold c_put_short in Ha. inv_bind Ha. destruct x as [o2 m2].
    apply put_byte_len in Ha0. apply put_byte_len in Ha. inversion H; subst; cbn in *. congruence.
  - destruct (o_bi_valid o >=? 8).
    + inv_bind H. destruct x as [o1 m1]. apply put_byte_len in Ha. inversion H; subst; cbn in *. congruence.
    + inversion H; subst; reflexivity.
Qed.

Lemma prime_step s o m b v sf : runs prime_body (set_d_out s (o, m), b, v) sf ->
  0 <= o_bi_valid o <= 16 /\
  exists om, c_tr_flush_bits (pr_o1 o v (pr_put (o_bi_valid o) b), m) = Some om /\
  (if b - pr_put (o_bi_valid o) b =? 0 then set_d_out s om = sf
   else runs prime_body (set_d_out s om, b - pr_put (o_bi_valid o) b, Z.shiftr v (pr_put (o_bi_valid o) b)) sf).
Proof.
  intros R. apply runs_inv in R. destruct R as [E | [a' [E R]]];
    apply prime_body_inv in E; destruct E as [Hv [om [Hf Hx]]]; (split; [exact Hv|]); exists om; (split; [exact Hf|]);
    destruct (_ =? 0); inversion Hx; subst; auto.
Qed.

Lemma pr_put_range bv b : 0 <= bv <= 16 -> 0 <= b <= 16 ->
  0 <= pr_put bv b <= b /\ bv + pr_put bv b <= 16 /\ (b - pr_put bv b = 0 \/ bv + pr_put bv b = 16).
Proof. unfold pr_put. intros. destruct (Z.gtb_spec (16 - bv) b); lia. Qed.

Lemma pr_bb_range o v put : 0 <= pr_bb o v put < 65536.
Proof. unfold pr_bb, u16. apply Z.mod_pos_bound. lia. Qed.

Lemma shiftr_s32 v k : Int.min_signed <= v <= Int.max_signed -> 0 <= k ->
  Int.min_signed <= Z.shiftr v k <= Int.max_signed.
Proof.
  intros Hv Hk. rewrite Z.shiftr_div_pow2 by lia. assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  change Int.min_signed with (-2147483648) in *. change Int.max_signed with 2147483647 in *.
  split.
  - apply Z.div_le_lower_bound; [lia|]. nia.
  - apply Z.div_le_upper_bound; [lia|]. nia.
Qed.

Lemma out_fold o m sp pbp bb bv :
  out_ok o m -> 0 <= bb < 65536 -> Int.min_signed <= bv <= Int.max_signed ->
  (@field_at DCS.CS Ews t_ds (DOT Zlib.trees.code._pending) (vl (o_pending o)) sp *
   @field_at DCS.CS Ews t_ds (DOT Zlib.trees.code._pending_buf) pbp sp *
   @field_at DCS.CS Ews t_ds (DOT Zlib.trees.code._bi_buf) (vi bb) sp *
   @field_at DCS.CS Ews t_ds (DOT Zlib.trees.code._bi_valid) (vi bv) sp *
   @field_at DCS.CS Ews t_ds (DOT Zlib.trees.code._bi_used) (vi (o_bi_used o)) sp *
   @data_at DCS.CS Ews (tarray tuchar (Zlength (o_buf o))) (pb_vals (o_buf o) m) pbp)%logic
  |-- out_at (mkOut (o_buf o) (o_pending o) bb bv (o_bi_used o)) m sp pbp.
Proof.
  intros Ho Hbb Hbv. unfold out_at. cbn [o_buf o_pending o_bi_buf o_bi_valid o_bi_used].
  apply andp_right; [|cancel]. apply prop_right.
  destruct Ho as [Hm [Hl [Hp [_ [_ Hu]]]]]. unfold out_ok. cbn [o_buf o_pending o_bi_buf o_bi_valid o_bi_used].
  refine (conj Hm _). repeat split; lia.
Qed.

Lemma dsizes_sdo s o m : dsizes s -> Zlength (o_buf o) = Zlength (o_buf (tr_out (d_tr s))) ->
  dsizes (set_d_out s (o, m)).
Proof. unfold dsizes. cbn. intuition. Qed.

Lemma dr_sdo s x : dstate_ranges s -> dstate_ranges (set_d_out s x).
Proof. intros H. destruct x. exact H. Qed.

(** ** C values *)
Lemma shl_repr32 a k : 0 <= k < 32 -> Int.shl (Int.repr a) (Int.repr k) = Int.repr (Z.shiftl a k).
Proof.
  intros Hk. unfold Int.shl. rewrite (Int.unsigned_repr k) by rep_lia.
  apply Int.eqm_samerepr. rewrite !Z.shiftl_mul_pow2 by lia.
  apply Int.eqm_mult; [apply Int.eqm_sym, Int.eqm_unsigned_repr | apply Int.eqm_refl].
Qed.

(** ** The pointer comparison [s->sym_buf < s->pending_out + 2] inside pending_buf *)
Lemma pb_test_order R sh n v b i k1 k2 :
  0 < n -> 0 <= k1 <= n -> 0 <= k2 <= n -> sepalg.nonidentity sh ->
  (@data_at DCS.CS sh (tarray tuchar n) v (Vptr b i) * R)%logic |--
  test_order_ptrs (Vptr b (Ptrofs.add i (Ptrofs.repr k1))) (Vptr b (Ptrofs.add i (Ptrofs.repr k2))).
Proof.
  intros Hn H1 H2 Hsh. unfold test_order_ptrs. simpl sameblock. destruct (peq b b); [|congruence]. simpl.
  apply andp_right; apply sepcon_weak_valid_pointer1;
  eapply derives_trans; try apply data_at_memory_block; simpl sizeof; rewrite Z.max_r by lia; rewrite Z.mul_1_l.
  - apply (memory_block_weak_valid_pointer sh n (Vptr b i) k1); auto.
  - apply (memory_block_weak_valid_pointer sh n (Vptr b i) k2); auto.
Qed.

Lemma ptr_ltu_eq i k1 k2 : 0 <= k1 -> 0 <= k2 ->
  Ptrofs.unsigned i + k1 < Ptrofs.modulus -> Ptrofs.unsigned i + k2 < Ptrofs.modulus ->
  Ptrofs.ltu (Ptrofs.add i (Ptrofs.repr k1)) (Ptrofs.add i (Ptrofs.repr k2)) = (k1 <? k2).
Proof.
  intros. pose proof (Ptrofs.unsigned_range i). unfold Ptrofs.ltu, Ptrofs.add.
  rewrite (Ptrofs.unsigned_repr k1), (Ptrofs.unsigned_repr k2) by rep_lia.
  rewrite !Ptrofs.unsigned_repr by rep_lia.
  destruct (zlt _ _); destruct (Z.ltb_spec k1 k2); try reflexivity; lia.
Qed.

Lemma bb_eq o v put : 0 <= put <= 16 -> 0 <= o_bi_valid o <= 16 ->
  Int.zero_ext 16 (Int.or (Int.repr (o_bi_buf o)) (Int.zero_ext 16 (Int.shl (Int.and (Int.repr v)
    (Int.sub (Int.shl (Int.repr 1) (Int.repr put)) (Int.repr 1))) (Int.repr (o_bi_valid o))))) =
  Int.repr (pr_bb o v put).
Proof.
  intros. rewrite (shl_repr32 1 put) by lia. rewrite sub_repr32, and_repr32.
  rewrite shl_repr32 by lia. rewrite zext16_repr, or_repr32, zext16_repr. reflexivity.
Qed.

Lemma shr_repr_s v k : Int.min_signed <= v <= Int.max_signed -> 0 <= k < 32 ->
  Int.shr (Int.repr v) (Int.repr k) = Int.repr (Z.shiftr v k).
Proof. intros. unfold Int.shr. rewrite Int.signed_repr, (Int.unsigned_repr k) by rep_lia. reflexivity. Qed.

Ltac fif_tmp id v :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp id v :: Q) (SEPx R))) end.

Lemma body_deflatePrime : ob_deflatePrime.
Proof.
  unfold ob_deflatePrime. start_function.
  destruct os as [s|].
  2:{ cbn in H1. inv H1. dcheck_none strmp gv. forward_if; [forward; entailer! | discriminate]. }
  dcheck_some s strmp gv.
  unfold on_state, c_on_state, c_deflatePrime, bad_state, c_deflateStateCheck in H1 |- *.
  destruct (status_ok (d_status s)) eqn:Hst; cbn in H1.
  2:{ inv H1. forward_if; [forward; entailer! | discriminate]. }
  forward_if; [contradiction|].
  rewrite dstream_some_eq. Intros p. rewrite dstate_at'_2; unfold dstate_at. Intros.
  rewrite trees_at_split. unfold sym_at, stat_at. cbn [fst snd d_trm]. Intros.
  assert_PROP (isptr (p_s p)) as Hps by entailer!.
  assert_PROP (isptr (p_pbuf p) /\ field_compatible (tarray tuchar (Zlength (o_buf (tr_out (d_tr s))))) [] (p_pbuf p)) as Hpb
    by (unfold out_at; Intros; entailer!).
  forward.
  destruct ((bits <? 0) || (bits >? 16))%bool eqn:Hb.
  { cbn in H1. inv H1.
    fif_tmp _t'2 (vi 1).
    { forward. entailer!. }
    { forward. entailer!. unfold s32_ok in H. rewrite Int.signed_repr in H1 by rep_lia.
      assert (16 < bits) by (apply orb_true_iff in Hb; destruct Hb as [Hb|Hb];
                             [apply Z.ltb_lt in Hb; lia | apply Z.gtb_lt in Hb; lia]).
      unfold Int.lt. rewrite !Int.signed_repr by rep_lia.
      destruct (zlt 16 bits); [reflexivity | lia]. }
    fif_tmp _t'3 (vi 1).
    { forward. entailer!. }
    { discriminate. }
    forward_if; [|discriminate].
    forward.
    rewrite dstream_some_eq. Exists p. rewrite dstate_at'_2; unfold dstate_at.
    rewrite trees_at_split. unfold sym_at, stat_at. cbn [fst snd d_trm]. entailer!. }
  unfold guard in H1. cbv beta iota delta [bind] in H1.
  set (lit := tr_lit_bufsize (d_tr s)) in *. set (n := Zlength (o_buf (tr_out (d_tr s)))) in *.
  destruct ((0 <=? lit) && (lit <=? n) && (0 <=? d_po s + 2) && (d_po s + 2 <=? n))%bool eqn:Hg;
    [|discriminate H1].
  assert (Hg' : 0 <= lit <= n /\ 0 <= d_po s + 2 <= n) by (rewrite !andb_true_iff, !Z.leb_le in Hg; lia).
  clear Hg. assert (Hpo : 0 <= d_po s) by drange H6.
  assert (Hbr : 0 <= bits <= 16) by (apply orb_false_iff in Hb; destruct Hb as [Hb1 Hb2];
                                     apply Z.ltb_ge in Hb1; rewrite Z.gtb_ltb, Z.ltb_ge in Hb2; lia).
  fif_tmp _t'2 (vi 0).
  { lia. }
  { forward. entailer!. destruct (zlt 16 bits); [lia | reflexivity]. }
  fif_tmp _t'3 (vi (Z.b2z (lit <? d_po s + 2))).
  { contradiction. }
  { Intros. forward. { entailer!. apply isptr_is_pointer_or_null; rewrite isptr_offset_val; apply Hpb. }
    forward. { entailer!. apply isptr_is_pointer_or_null; rewrite isptr_offset_val; apply Hpb. }
    forward.
    { destruct Hpb as [Hpb Hfc]. destruct (p_pbuf p) eqn:Hpp; try contradiction.
      unfold out_at. Intros. entailer!.
      change (Int.signed (Int.shr (Int.repr (16 + 7)) (Int.repr 3))) with 2.
      apply derives_trans with (@data_at DCS.CS Ews (tarray tuchar n) (pb_vals (o_buf (tr_out (d_tr s))) (d_pbm s))
                                  (Vptr b i) * TT)%logic; [cancel|].
      apply pb_test_order; auto; try lia. }
    destruct Hpb as [Hpb Hfc]. destruct (p_pbuf p) eqn:Hpp; try contradiction.
    entailer!. clear H1.
    assert (Hsz: Ptrofs.unsigned i + n < Ptrofs.modulus).
    { destruct Hfc as [_ [_ [Hs _]]]. unfold size_compatible in Hs. simpl sizeof in Hs.
      rewrite Z.max_r in Hs by lia. lia. }
    change (Int.signed (Int.shr (Int.repr (16 + 7)) (Int.repr 3))) with 2.
    unfold compare_pp. simpl. rewrite ptr_ltu_eq by lia. destruct (eq_block b b); [|congruence].
    destruct (lit <? d_po s + 2); reflexivity. }
  destruct (lit <? d_po s + 2) eqn:Hlt.
  { cbv beta iota in H1. inv H1.
    forward_if; [|discriminate].
    forward.
    rewrite dstream_some_eq. Exists p. rewrite dstate_at'_2; unfold dstate_at.
    rewrite trees_at_split. unfold sym_at, stat_at. cbn [fst snd d_trm]. entailer!. }
  destruct (loop FUEL prime_body (s, bits, value)) as [sf|] eqn:Hloop; [|discriminate H1].
  cbv beta iota in H1. inv H1.
  forward_if; [contradiction|].
  apply loop_runs in Hloop.
  assert (Hrun : runs prime_body (set_d_out s (tr_out (d_tr s), d_pbm s), bits, value) sf)
    by (change (tr_out (d_tr s), d_pbm s) with (d_out s); rewrite sdo_self; exact Hloop).
  clear Hloop.
  match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx (?A :: ?B :: out_at _ _ ?sp ?pbp :: ?R)))) _ _ =>
    forward_loop
      (EX o : outbuf, EX m : list bool, EX b : Z, EX v : Z,
        PROPx [runs prime_body (set_d_out s (o, m), b, v) sf; 0 <= b <= 16; s32_ok v; Zlength (o_buf o) = n]
        (LOCALx [temp _s sp; gvars gv; temp _strm (p_strm p); temp _bits (vi b); temp _value (vi v)]
        (SEPx (A :: B :: out_at o m sp pbp :: R))))
    continue:
      (EX o : outbuf, EX m : list bool, EX b : Z, EX v : Z,
        PROPx [if b =? 0 then set_d_out s (o, m) = sf else runs prime_body (set_d_out s (o, m), b, v) sf;
               0 <= b <= 16; s32_ok v; Zlength (o_buf o) = n]
        (LOCALx [temp _s sp; gvars gv; temp _strm (p_strm p); temp _bits (vi b); temp _value (vi v)]
        (SEPx (A :: B :: out_at o m sp pbp :: R))))
    break:
      (EX o : outbuf, EX m : list bool,
        PROPx [set_d_out s (o, m) = sf; Zlength (o_buf o) = n]
        (LOCALx [temp _s sp; gvars gv; temp _strm (p_strm p)]
        (SEPx (A :: B :: out_at o m sp pbp :: R))))
  end.
  - Exists (tr_out (d_tr s)) (d_pbm s) bits value. entailer!.
  - Intros o m b v.
    match goal with Hr : runs prime_body _ sf |- _ => apply prime_step in Hr; destruct Hr as [Hbv [om [Hfl Hnext]]] end.
    pose proof (pr_put_range (o_bi_valid o) b Hbv ltac:(lia)) as Hput.
    set (put := pr_put (o_bi_valid o) b) in *.
    unfold out_at. Intros.
    match goal with Ho : out_ok o m |- _ => pose proof Ho as (Hmb & Hlb & Hpd & Hbb & Hbvv & Hbu) end.
    forward. forward.
    match goal with |- semax _ (PROPx ?P (LOCALx (temp _put _ :: ?Q) (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp _put (vi put) :: Q) (SEPx R))) end.
    + forward. entailer!.
      unfold put, pr_put; destruct (Z.gtb_spec (16 - o_bi_valid o) b); [reflexivity | lia].
    + forward. entailer!.
      unfold put, pr_put; destruct (Z.gtb_spec (16 - o_bi_valid o) b); [lia | reflexivity].
    + forward. { entailer!. lia. }
      forward. forward.
      { entailer!. rewrite shl_repr32 by lia. rewrite Z.shiftl_1_l.
        assert (0 < 2 ^ put) by (apply Z.pow_pos_nonneg; lia).
        assert (2 ^ put <= 65536) by (change 65536 with (2 ^ 16); apply Z.pow_le_mono_r; lia).
        rewrite Int.signed_repr by rep_lia. change (Int.unsigned Int.iwordsize) with 32. rep_lia. }
      rewrite bb_eq by lia.
      forward. forward. rewrite add_repr32.
      destruct om as [o' m'].
      pose proof (flush_bits_len _ _ _ Hfl) as Hlen'. cbn [fst o_buf pr_o1] in Hlen'.
      sep_apply (out_fold o m (p_s p) (p_pbuf p) (pr_bb o v put) (o_bi_valid o + put)); [apply pr_bb_range | rep_lia |].
      change (out_at (mkOut (o_buf o) (o_pending o) (pr_bb o v put) (o_bi_valid o + put) (o_bi_used o)) m)
        with (out_at (pr_o1 o v put) m).
      forward_call (p_s p, p_pbuf p, pr_o1 o v put, m, (o', m')).
      forward.
      { entailer!. change (Int.unsigned Int.iwordsize) with 32. rep_lia. }
      forward.
      rewrite shr_repr_s by (unfold s32_ok in *; rep_lia). rewrite sub_repr32.
      Exists o' m' (b - put) (Z.shiftr v put). cbn [fst snd].
      entailer!.
      apply shiftr_s32; unfold s32_ok in *; rep_lia.
  - Intros o m b v.
    forward_if.
    + forward. Exists o m b v. entailer!.
      match goal with Hi : (if b =? 0 then _ else _) |- _ => rewrite (proj2 (Z.eqb_neq b 0)) in Hi by lia; exact Hi end.
    + forward. Exists o m. entailer!.
      match goal with Hz : Int.repr b = Int.zero |- _ =>
        apply (f_equal Int.unsigned) in Hz; rewrite Int.unsigned_repr in Hz by rep_lia;
        change (Int.unsigned Int.zero) with 0 in Hz; subst b end.
      match goal with Hi : (if 0 =? 0 then _ else _) |- _ => exact Hi end.
  - Intros o m. forward.
    try match goal with Hs : set_d_out s (o, m) = ?x |- _ => subst x end.
    assert (Hds : dsizes (set_d_out s (o, m))) by (apply dsizes_sdo; auto).
    assert (Hdr : dstate_ranges (set_d_out s (o, m))) by (apply dr_sdo; exact H6).
    rewrite dstream_some_eq. Exists p. rewrite dstate_at'_2; unfold dstate_at. dsame s.
    rewrite trees_at_split. cbn [d_trm fst snd].
    change (trees_rest (d_tr (set_d_out s (o, m)))) with (trees_rest (d_tr s)).
    change (sym_at (d_tr (set_d_out s (o, m)))) with (sym_at (d_tr s)).
    rewrite sdo_out, sdo_pbm.
    rewrite (prop_true_andp (p_strm p = p_strm p /\ _)) by auto.
    rewrite (prop_true_andp (dstate_ranges _)) by auto.
    clear Hds Hdr Hrun.
    unfold sym_at, stat_at. rewrite prop_true_andp by (subst lit; auto).
    cancel.
Qed.
