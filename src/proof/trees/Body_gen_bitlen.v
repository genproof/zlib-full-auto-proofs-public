(** * The body of trees.c's gen_bitlen against its shared specification (TSpec.v) *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.trees.TSpec.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.proof.trees.CtMode.
Require Import Zlib.trees.code.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

(** ** The static descriptor: its fields, its extra bits table and its static tree, out of trees_globals *)

Definition st_at (st : option tree) (p : val) : mpred :=
  match st with
  | Some t => tree_arr Ers (Zlength (dl t)) t p
  | None => (!! (p = nullval) && emp)%logic
  end.

Definition sd_ok (sd : stat_desc) : Prop :=
  (sd_maxlen sd = 15 \/ sd_maxlen sd = 7) /\ (sd_base sd = 0 \/ sd_base sd = 257) /\
  Forall (fun x => 0 <= x <= 13) (sd_extra sd).

Lemma sd_split gv sd statp : sdesc_ptr gv sd statp ->
  sd_ok sd /\
  exists stp ep st R, option_map dl st = sd_stree sd /\
  trees_globals gv =
  (@data_at DCS.CS Ers t_sd (stp, (ep, (vi (sd_base sd), (vi (sd_elems sd), vi (sd_maxlen sd))))) statp *
   @data_at DCS.CS Ers (tarray tint (Zlength (sd_extra sd))) (map vi (sd_extra sd)) ep * st_at st stp * R)%logic.
Proof.
  intros [[-> ->]|[[-> ->]|[-> ->]]]; (split; [unfold sd_ok, static_l_desc, static_d_desc, static_bl_desc, MAX_BITS, MAX_BL_BITS, LITERALS,
    extra_lbits, extra_dbits, extra_blbits; cbn; split; [lia|split; [lia|repeat constructor; lia]]|]).
  - exists (gv _static_ltree), (gv _extra_lbits), (Some static_ltree_t).
    exists (tree_arr Ers D_CODES static_dtree_t (gv _static_dtree) * @data_at DCS.CS Ers t_sd (gv _static_dtree, (gv _extra_dbits, (vi 0, (vi 30, vi 15)))) (gv _static_d_desc) * @data_at DCS.CS Ers t_sd (nullval, (gv _extra_blbits, (vi 0, (vi 19, vi 7)))) (gv _static_bl_desc) * @data_at DCS.CS Ers (tarray tint 30) (map vi extra_dbits) (gv _extra_dbits) * @data_at DCS.CS Ers (tarray tint 19) (map vi extra_blbits) (gv _extra_blbits) * @data_at DCS.CS Ers (tarray tuchar 512) (map vi dist_code_tab) (gv __dist_code) *
   @data_at DCS.CS Ers (tarray tuchar 256) (map vi length_code_tab) (gv __length_code) *
   @data_at DCS.CS Ers (tarray tint 29) (map vi base_length_tab) (gv _base_length) *
   @data_at DCS.CS Ers (tarray tint 30) (map vi base_dist_tab) (gv _base_dist) *
   @data_at DCS.CS Ers (tarray tuchar 19) (map vi bl_order) (gv _bl_order))%logic. split; [reflexivity|].
    unfold trees_globals, static_trees, trees_tables, st_at. cbn [sd_base sd_elems sd_maxlen sd_extra].
    change (Zlength (dl static_ltree_t)) with (L_CODES + 2). change (Zlength extra_lbits) with 29.
    change (LITERALS + 1) with 257. change L_CODES with 286. change MAX_BITS with 15.
    apply pred_ext; cancel.
  - exists (gv _static_dtree), (gv _extra_dbits), (Some static_dtree_t).
    exists (tree_arr Ers (L_CODES + 2) static_ltree_t (gv _static_ltree) * @data_at DCS.CS Ers t_sd (gv _static_ltree, (gv _extra_lbits, (vi 257, (vi 286, vi 15)))) (gv _static_l_desc) * @data_at DCS.CS Ers t_sd (nullval, (gv _extra_blbits, (vi 0, (vi 19, vi 7)))) (gv _static_bl_desc) * @data_at DCS.CS Ers (tarray tint 29) (map vi extra_lbits) (gv _extra_lbits) * @data_at DCS.CS Ers (tarray tint 19) (map vi extra_blbits) (gv _extra_blbits) * @data_at DCS.CS Ers (tarray tuchar 512) (map vi dist_code_tab) (gv __dist_code) *
   @data_at DCS.CS Ers (tarray tuchar 256) (map vi length_code_tab) (gv __length_code) *
   @data_at DCS.CS Ers (tarray tint 29) (map vi base_length_tab) (gv _base_length) *
   @data_at DCS.CS Ers (tarray tint 30) (map vi base_dist_tab) (gv _base_dist) *
   @data_at DCS.CS Ers (tarray tuchar 19) (map vi bl_order) (gv _bl_order))%logic. split; [reflexivity|].
    unfold trees_globals, static_trees, trees_tables, st_at. cbn [sd_base sd_elems sd_maxlen sd_extra].
    change (Zlength (dl static_dtree_t)) with D_CODES. change (Zlength extra_dbits) with 30.
    change D_CODES with 30. change MAX_BITS with 15.
    apply pred_ext; cancel.
  - exists nullval, (gv _extra_blbits), None.
    exists (tree_arr Ers (L_CODES + 2) static_ltree_t (gv _static_ltree) * tree_arr Ers D_CODES static_dtree_t (gv _static_dtree) * @data_at DCS.CS Ers t_sd (gv _static_ltree, (gv _extra_lbits, (vi 257, (vi 286, vi 15)))) (gv _static_l_desc) * @data_at DCS.CS Ers t_sd (gv _static_dtree, (gv _extra_dbits, (vi 0, (vi 30, vi 15)))) (gv _static_d_desc) * @data_at DCS.CS Ers (tarray tint 29) (map vi extra_lbits) (gv _extra_lbits) * @data_at DCS.CS Ers (tarray tint 30) (map vi extra_dbits) (gv _extra_dbits) * @data_at DCS.CS Ers (tarray tuchar 512) (map vi dist_code_tab) (gv __dist_code) *
   @data_at DCS.CS Ers (tarray tuchar 256) (map vi length_code_tab) (gv __length_code) *
   @data_at DCS.CS Ers (tarray tint 29) (map vi base_length_tab) (gv _base_length) *
   @data_at DCS.CS Ers (tarray tint 30) (map vi base_dist_tab) (gv _base_dist) *
   @data_at DCS.CS Ers (tarray tuchar 19) (map vi bl_order) (gv _bl_order))%logic. split; [reflexivity|].
    unfold trees_globals, static_trees, trees_tables, st_at. cbn [sd_base sd_elems sd_maxlen sd_extra].
    change (Zlength extra_blbits) with 19. change BL_CODES with 19. change MAX_BL_BITS with 7.
    rewrite prop_true_andp by reflexivity. rewrite sepcon_emp.
    apply pred_ext; cancel.
Qed.

Lemma rd_inv l i x : rd l i = Some x -> x = Znth i l /\ 0 <= i < Zlength l.
Proof.
  unfold rd, in_range. destruct (andb (0 <=? i) (i <? Zlength l)) eqn:E; [|discriminate].
  apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  intros H; inversion H; auto.
Qed.

Lemma wr_inv l i v l' : wr l i v = Some l' -> l' = upd_Znth i l v /\ 0 <= i < Zlength l.
Proof.
  unfold wr, in_range. destruct (andb (0 <=? i) (i <? Zlength l)) eqn:E; [|discriminate].
  apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  intros H; inversion H; auto.
Qed.

Lemma c_set_dl_inv t i v t' : c_set_dl t i v = Some t' ->
  t' = mkTree (fc t) (upd_Znth i (dl t) v) /\ 0 <= i < Zlength (dl t).
Proof.
  unfold c_set_dl. destruct (wr (dl t) i v) eqn:E; [|discriminate]. cbn.
  apply wr_inv in E. destruct E as [-> Hi]. intros Ht; inversion Ht; auto.
Qed.

(** ** The parts of gen_bitlen's body *)

Ltac gb_part k :=
  let b := eval cbv [f_gen_bitlen fn_body] in (fn_body f_gen_bitlen) in
  match b with
  | Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _
      (Ssequence _ (Ssequence _ (Ssequence ?pass1 (Ssequence _ (Ssequence ?repair ?reassign))))))))))) =>
    match k with
    | 1 => exact pass1
    | 2 => exact repair
    | 3 => exact reassign
    end
  end.

(** [h = s->heap_max + 1; for (; h < HEAP_SIZE; h++) ...] *)
Definition gb_pass1_stmt : statement := ltac:(gb_part 1).
(** [do { ... } while (overflow > 0);] *)
Definition gb_repair_stmt : statement := ltac:(gb_part 2).
(** [for (bits = max_length; bits != 0; bits--) { n = s->bl_count[bits]; while (n != 0) ... }] *)
Definition gb_reassign_stmt : statement := ltac:(gb_part 3).

Definition gb_Delta := func_tycontext f_gen_bitlen Vprog Gprog_gen_bitlen nil.

Lemma tree_ok_set_dl t n i v : tree_ok t n -> 0 <= i < n -> 0 <= v < 65536 ->
  tree_ok (mkTree (fc t) (upd_Znth i (dl t) v)) n.
Proof.
  intros [Hf [Hd Hr]] Hi Hv. split; [exact Hf|]. cbn. split; [rewrite Zlength_upd_Znth; auto|].
  intros j Hj. split; [apply Hr; auto|].
  destruct (Z.eq_dec j i) as [->|ne]; [rewrite upd_Znth_same by lia; auto|].
  rewrite upd_Znth_diff by lia. apply Hr; auto.
Qed.

(** [s->opt_len += (ulg)f * (unsigned)(a + b)] (f an ush), as VST computes it. *)
Lemma mul64_repr' x y : Int64.mul (Int64.repr x) (Int64.repr y) = Int64.repr (x * y).
Proof.
  unfold Int64.mul. apply Int64.eqm_samerepr.
  apply Int64.eqm_mult; apply Int64.eqm_sym, Int64.eqm_unsigned_repr.
Qed.

Lemma ulg_madd o fr a b : 0 <= fr < 65536 ->
  Int64.add (Int64.repr o)
    (Int64.mul (Int64.repr (Int.unsigned (Int.zero_ext 16 (Int.repr fr))))
       (Int64.repr (Int.unsigned (Int.add (Int.repr a) (Int.repr b))))) =
  Int64.repr (u64 (o + fr * u32 (a + b))).
Proof.
  intros Hfr. rewrite zext16_repr, Z.mod_small by lia. rewrite Int.unsigned_repr by rep_lia.
  rewrite add_repr32, Int.unsigned_repr_eq. rewrite mul64_repr', add64_repr.
  apply Int64.eqm_samerepr. unfold u64, u32. change Int.modulus with 4294967296.
  unfold Int64.eqm. change 18446744073709551616 with Int64.modulus.
  apply Zbits.eqmod_mod. reflexivity.
Qed.

Lemma repr64_u64 y : Int64.repr (u64 y) = Int64.repr y.
Proof.
  apply Int64.eqm_samerepr. unfold u64. apply Int64.eqm_sym. unfold Int64.eqm.
  change 18446744073709551616 with Int64.modulus. apply Zbits.eqmod_mod. reflexivity.
Qed.

Lemma repr64_u64_mul a c fm : Int64.repr (a + u64 c * fm) = Int64.repr (a + c * fm).
Proof.
  apply Int64.eqm_samerepr. apply Int64.eqm_add; [apply Int64.eqm_refl|].
  apply Int64.eqm_mult; [|apply Int64.eqm_refl]. unfold u64. apply Int64.eqm_sym. unfold Int64.eqm.
  change 18446744073709551616 with Int64.modulus. apply Zbits.eqmod_mod. reflexivity.
Qed.

Lemma u64_range x : 0 <= u64 x <= Int64.max_unsigned.
Proof. unfold u64. pose proof (Z.mod_pos_bound x 18446744073709551616 ltac:(lia)). rep_lia. Qed.

Lemma work_ok_set heap hl hm depth bc o s bc' o' s' :
  work_ok (mkWork heap hl hm depth bc o s) -> Zlength bc' = 16 -> Forall (fun x => 0 <= x < 65536) bc' ->
  0 <= o' <= Int64.max_unsigned -> 0 <= s' <= Int64.max_unsigned ->
  work_ok (mkWork heap hl hm depth bc' o' s').
Proof.
  intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10) ? ? ? ?.
  unfold work_ok; cbn in *. repeat split; auto; lia.
Qed.

Lemma bl_count_inc bc b : Zlength bc = 16 -> Forall (fun x => 0 <= x < 65536) bc ->
  Zlength (upd_Znth b bc (u16 (Znth b bc + 1))) = 16 /\
  Forall (fun x => 0 <= x < 65536) (upd_Znth b bc (u16 (Znth b bc + 1))).
Proof.
  intros Hl Hf. rewrite Zlength_upd_Znth. split; auto.
  apply Forall_upd_Znth; auto. unfold u16. apply Z.mod_pos_bound. lia.
Qed.

Lemma upd_map_vi16 i (l : list Z) y :
  upd_Znth i (map vi l) (Vint (Int.repr (y mod 65536))) = map vi (upd_Znth i l (u16 y)).
Proof. change (Vint (Int.repr (y mod 65536))) with (vi (u16 y)). apply upd_Znth_map. Qed.

Lemma u16_Forall_upd i (l : list Z) y : Forall (fun x => 0 <= x < 65536) l ->
  Forall (fun x => 0 <= x < 65536) (upd_Znth i l (u16 y)).
Proof. intros. apply Forall_upd_Znth; auto. unfold u16. apply Z.mod_pos_bound. lia. Qed.

(** [s->opt_len += ((ulg)bits - tree[m].Len) * tree[m].Freq], as VST computes it. *)
Lemma ulg_msub o b lm fm :
  Int64.add (Int64.repr o) (Int64.mul (Int64.sub (Int64.repr b) (Int64.repr lm)) (Int64.repr fm)) =
  Int64.repr (u64 (o + u64 (b - lm) * fm)).
Proof.
  rewrite sub64_repr, mul64_repr', add64_repr. apply Int64.eqm_samerepr.
  apply Int64.eqm_trans with (o + u64 (b - lm) * fm).
  - apply Int64.eqm_add; [apply Int64.eqm_refl|]. apply Int64.eqm_mult; [|apply Int64.eqm_refl].
    unfold u64, Int64.eqm. change 18446744073709551616 with Int64.modulus. apply Zbits.eqmod_mod. reflexivity.
  - unfold u64 at 1, Int64.eqm. change 18446744073709551616 with Int64.modulus. apply Zbits.eqmod_mod. reflexivity.
Qed.

(** The store [(tree + i -> dl).len = v] as VST leaves it, back in the canonical presentation. *)
Lemma ct_store_len sh n mf md t i x p :
  0 <= i < Zlength (fc t) -> Zlength (dl t) = Zlength (fc t) ->
  @data_at DCS.CS sh (tarray t_ct n)
    (upd_Znth i (ct_arr mf md t) (fst (Znth i (ct_arr mf md t)), inr (Vint (Int.zero_ext 16 (Int.repr x))))) p =
  @data_at DCS.CS sh (tarray t_ct n) (ct_canon (mkTree (fc t) (upd_Znth i (dl t) (u16 x)))) p.
Proof.
  intros Hi Hl. rewrite Znth_ct_arr by auto. rewrite zext16_repr.
  change (fst (ctv_of (mf i) (md i) (Znth i (fc t)) (Znth i (dl t))), inr (Vint (Int.repr (x mod 65536))))
    with (ctv_of (mf i) true (Znth i (fc t)) (u16 x)).
  rewrite ct_arr_set_dl by auto. unfold ct_canon. apply ct_arr_mode.
Qed.

(** The first pass: the bit lengths from the parents' (Dad) lengths, overflow count, bl_count, opt_len and
    static_len. *)
Lemma gb_pass1 {Espec : OracleKind} (sp tp stp ep : val) (n mc : Z) (sd : stat_desc) (st : option tree)
    (t : tree) (w : work) (t' : tree) (w' : work) (ov' : Z) (Fr : mpred) :
  sd_ok sd -> option_map dl st = sd_stree sd -> Int.min_signed <= mc <= Int.max_signed ->
  tree_ok t n -> work_ok w -> 0 <= w_heap_max w < HEAP_SIZE ->
  c_gen_bitlen_pass1 (Z.to_nat HEAP_SIZE) sd mc t w 0 (w_heap_max w + 1) = Some (t', w', ov') ->
  semax gb_Delta
    (PROP ()
     LOCAL (temp _overflow (vi 0); temp _max_length (vi (sd_maxlen sd)); temp _base (vi (sd_base sd));
            temp _extra ep; temp _stree stp; temp _max_code (vi mc); temp _tree tp; temp _s sp)
     SEP (@data_at DCS.CS Ews (tarray t_ct n) (ct_canon t) tp;
          @field_at DCS.CS Ews t_ds (DOT _heap) (map vi (w_heap w)) sp;
          @field_at DCS.CS Ews t_ds (DOT _heap_max) (vi (w_heap_max w)) sp;
          @field_at DCS.CS Ews t_ds (DOT _bl_count) (map vi (w_bl_count w)) sp;
          @field_at DCS.CS Ews t_ds (DOT _opt_len) (vl (w_opt_len w)) sp;
          @field_at DCS.CS Ews t_ds (DOT _static_len) (vl (w_static_len w)) sp;
          @data_at DCS.CS Ers (tarray tint (Zlength (sd_extra sd))) (map vi (sd_extra sd)) ep;
          st_at st stp; Fr))
    gb_pass1_stmt
    (normal_ret_assert
     (PROP (tree_ok t' n; work_ok w'; w_heap w' = w_heap w; w_heap_max w' = w_heap_max w;
            w_heap_len w' = w_heap_len w; w_depth w' = w_depth w; 0 <= ov' <= HEAP_SIZE)
      LOCAL (temp _overflow (vi ov'); temp _h (vi HEAP_SIZE); temp _max_length (vi (sd_maxlen sd));
             temp _max_code (vi mc); temp _tree tp; temp _s sp)
      SEP (@data_at DCS.CS Ews (tarray t_ct n) (ct_canon t') tp;
           @field_at DCS.CS Ews t_ds (DOT _heap) (map vi (w_heap w')) sp;
           @field_at DCS.CS Ews t_ds (DOT _heap_max) (vi (w_heap_max w')) sp;
           @field_at DCS.CS Ews t_ds (DOT _bl_count) (map vi (w_bl_count w')) sp;
           @field_at DCS.CS Ews t_ds (DOT _opt_len) (vl (w_opt_len w')) sp;
           @field_at DCS.CS Ews t_ds (DOT _static_len) (vl (w_static_len w')) sp;
           @data_at DCS.CS Ers (tarray tint (Zlength (sd_extra sd))) (map vi (sd_extra sd)) ep;
           st_at st stp; Fr))).
Proof.
  intros Hsd Hst Hmc Htok Hwok Hhm Hrun.
  unfold gb_Delta, gb_pass1_stmt. simplify_func_tycontext. abbreviate_semax.
  destruct w as [heap hl hm depth blc ol sl].
  cbn [w_heap w_heap_len w_heap_max w_depth w_bl_count w_opt_len w_static_len] in *.
  pose proof Hwok as (Hlh & Hld & Hlb & Hfh & Hhl & Hhm2 & Hfd & Hfb & Hol & Hsl).
  cbn [w_heap w_heap_len w_heap_max w_depth w_bl_count w_opt_len w_static_len] in *.
  change (2 * L_CODES + 1) with 573 in Hlh. change (MAX_BITS + 1) with 16 in Hlb. unfold HEAP_SIZE in *.
  forward. forward.
  forward_loop
    (EX f : nat, EX t1 : tree, EX bc : list Z, EX o1 : Z, EX s1 : Z, EX ov : Z, EX h : Z,
     PROP (c_gen_bitlen_pass1 f sd mc t1 (mkWork heap hl hm depth bc o1 s1) ov h = Some (t', w', ov');
           tree_ok t1 n; work_ok (mkWork heap hl hm depth bc o1 s1); hm + 1 <= h <= 573; 0 <= ov <= h)
     LOCAL (temp _h (vi h); temp _overflow (vi ov); temp _max_length (vi (sd_maxlen sd));
            temp _base (vi (sd_base sd)); temp _extra ep; temp _stree stp; temp _max_code (vi mc);
            temp _tree tp; temp _s sp)
     SEP (@data_at DCS.CS Ews (tarray t_ct n) (ct_canon t1) tp;
          @field_at DCS.CS Ews t_ds (DOT _heap) (map vi heap) sp;
          @field_at DCS.CS Ews t_ds (DOT _heap_max) (vi hm) sp;
          @field_at DCS.CS Ews t_ds (DOT _bl_count) (map vi bc) sp;
          @field_at DCS.CS Ews t_ds (DOT _opt_len) (vl o1) sp;
          @field_at DCS.CS Ews t_ds (DOT _static_len) (vl s1) sp;
          @data_at DCS.CS Ers (tarray tint (Zlength (sd_extra sd))) (map vi (sd_extra sd)) ep;
          st_at st stp; Fr))
    continue:
    (EX f : nat, EX t1 : tree, EX bc : list Z, EX o1 : Z, EX s1 : Z, EX ov : Z, EX h : Z,
     PROP (c_gen_bitlen_pass1 f sd mc t1 (mkWork heap hl hm depth bc o1 s1) ov (h + 1) = Some (t', w', ov');
           tree_ok t1 n; work_ok (mkWork heap hl hm depth bc o1 s1); hm + 1 <= h < 573; 0 <= ov <= h + 1)
     LOCAL (temp _h (vi h); temp _overflow (vi ov); temp _max_length (vi (sd_maxlen sd));
            temp _base (vi (sd_base sd)); temp _extra ep; temp _stree stp; temp _max_code (vi mc);
            temp _tree tp; temp _s sp)
     SEP (@data_at DCS.CS Ews (tarray t_ct n) (ct_canon t1) tp;
          @field_at DCS.CS Ews t_ds (DOT _heap) (map vi heap) sp;
          @field_at DCS.CS Ews t_ds (DOT _heap_max) (vi hm) sp;
          @field_at DCS.CS Ews t_ds (DOT _bl_count) (map vi bc) sp;
          @field_at DCS.CS Ews t_ds (DOT _opt_len) (vl o1) sp;
          @field_at DCS.CS Ews t_ds (DOT _static_len) (vl s1) sp;
          @data_at DCS.CS Ers (tarray tint (Zlength (sd_extra sd))) (map vi (sd_extra sd)) ep;
          st_at st stp; Fr))
    break:
    (PROP (tree_ok t' n; work_ok w'; w_heap w' = heap; w_heap_max w' = hm;
           w_heap_len w' = hl; w_depth w' = depth; 0 <= ov' <= 573)
      LOCAL (temp _overflow (vi ov'); temp _h (vi 573); temp _max_length (vi (sd_maxlen sd));
             temp _max_code (vi mc); temp _tree tp; temp _s sp)
      SEP (@data_at DCS.CS Ews (tarray t_ct n) (ct_canon t') tp;
           @field_at DCS.CS Ews t_ds (DOT _heap) (map vi (w_heap w')) sp;
           @field_at DCS.CS Ews t_ds (DOT _heap_max) (vi (w_heap_max w')) sp;
           @field_at DCS.CS Ews t_ds (DOT _bl_count) (map vi (w_bl_count w')) sp;
           @field_at DCS.CS Ews t_ds (DOT _opt_len) (vl (w_opt_len w')) sp;
           @field_at DCS.CS Ews t_ds (DOT _static_len) (vl (w_static_len w')) sp;
           @data_at DCS.CS Ers (tarray tint (Zlength (sd_extra sd))) (map vi (sd_extra sd)) ep;
           st_at st stp; Fr)).
  { Exists (Z.to_nat 573) t blc ol sl 0 (hm + 1). entailer!. }
  2: { Intros f t1 bc o1 s1 ov h. forward. Exists f t1 bc o1 s1 ov (h + 1). entailer!. }
  2: { unfold abbreviate in POSTCONDITION; subst POSTCONDITION; simpl_ret_assert. entailer!. }
  Intros f t1 bc o1 s1 ov h.
  forward_if; change (Int.signed (Int.add (Int.mul (Int.repr 2) (Int.repr (256 + 1 + 29))) (Int.repr 1))) with 573 in H4.
  2: { forward. assert (h = 573) by lia. subst h.
       destruct f; cbn [c_gen_bitlen_pass1] in H; unfold HEAP_SIZE in H; rewrite (proj2 (Z.ltb_ge 573 573)) in H by lia;
         injection H as <- <- <-; entailer!. }
  destruct f as [|f]. { cbn [c_gen_bitlen_pass1] in H. unfold HEAP_SIZE in H. rewrite (proj2 (Z.ltb_lt h 573)) in H by lia. discriminate. }
  cbn [c_gen_bitlen_pass1] in H. unfold HEAP_SIZE in H. rewrite (proj2 (Z.ltb_lt h 573)) in H by lia.
  inv_bind H. apply rd_inv in Ha. destruct Ha as [-> Hh]. cbn [w_heap] in Hh.
  inv_bind H. apply rd_inv in Ha. destruct Ha as [-> Hn].
  inv_bind H. apply rd_inv in Ha. destruct Ha as [-> Hd].
  cbn [w_heap w_bl_count w_opt_len w_static_len w_set_bl_count w_set_opt_len w_set_static_len] in H, Hn, Hd.
  assert (Int.min_signed <= Znth h heap <= Int.max_signed) by (apply (proj1 (Forall_Znth _ _) Hfh); lia).
  pose proof H0 as (Htf & Htd & Htr).
  unfold ct_canon.
  forward.
  forward.
  { entailer!. rewrite Znth_ct_arr. 2: lia. cbn [ctv_of ffalse snd].
    apply (tc_val_tushort_repr (Znth (Znth h heap) (dl t1))). pose proof (Htr (Znth h heap)). lia. }
  rewrite Znth_ct_arr. 2: lia. cbn [ctv_of ffalse snd].
  assert (Hdd : 0 <= Znth (Znth h heap) (dl t1) < 65536) by (apply Htr; lia).
  rewrite (ct_arr_mode Ews n ffalse ffalse ffalse ftrue t1 tp).
  forward.
  { entailer!. rewrite Znth_ct_arr. 2: lia. cbn [ctv_of ffalse ftrue snd].
    apply (tc_val_tushort_repr (Znth (Znth (Znth h heap) (dl t1)) (dl t1))). pose proof (Htr (Znth (Znth h heap) (dl t1))). lia. }
  rewrite Znth_ct_arr. 2: lia. cbn [ctv_of ffalse ftrue snd].
  assert (Hld1 : 0 <= Znth (Znth (Znth h heap) (dl t1)) (dl t1) < 65536) by (apply Htr; lia).
  forward.
  set (nn := Znth h heap) in *. set (ld := Znth (Znth nn (dl t1)) (dl t1)) in *.
  set (B := if ld + 1 >? sd_maxlen sd then sd_maxlen sd else ld + 1).
  set (O := if ld + 1 >? sd_maxlen sd then ov + 1 else ov).
  assert (HBO : (if ld + 1 >? sd_maxlen sd then (sd_maxlen sd, ov + 1) else (ld + 1, ov)) = (B, O))
    by (unfold B, O; destruct (ld + 1 >? sd_maxlen sd); reflexivity).
  rewrite HBO in H. cbv iota beta in H.
  assert (HB : 1 <= B <= 15 /\ B <= sd_maxlen sd) by (destruct Hsd as [Hml _]; unfold B; destruct (Z.gtb_spec (ld + 1) (sd_maxlen sd)); lia).
  assert (HO : 0 <= O <= h + 1) by (unfold O; destruct (ld + 1 >? sd_maxlen sd); lia).
  forward_if (PROP ()
     LOCAL (temp _bits (vi B); temp _overflow (vi O); temp _n (vi nn); temp _h (vi h);
            temp _max_length (vi (sd_maxlen sd)); temp _base (vi (sd_base sd)); temp _extra ep; temp _stree stp;
            temp _max_code (vi mc); temp _tree tp; temp _s sp)
     SEP (@data_at DCS.CS Ews (tarray t_ct n) (ct_arr ffalse ftrue t1) tp;
          @field_at DCS.CS Ews t_ds (DOT _heap) (map vi heap) sp;
          @field_at DCS.CS Ews t_ds (DOT _heap_max) (vi hm) sp;
          @field_at DCS.CS Ews t_ds (DOT _bl_count) (map vi bc) sp;
          @field_at DCS.CS Ews t_ds (DOT _opt_len) (vl o1) sp;
          @field_at DCS.CS Ews t_ds (DOT _static_len) (vl s1) sp;
          @data_at DCS.CS Ers (tarray tint (Zlength (sd_extra sd))) (map vi (sd_extra sd)) ep;
          st_at st stp; Fr)).
  { rewrite signed_repr_small in H6 by (destruct Hsd as [Hml _]; rep_lia).
    forward. forward. entailer!. unfold B, O. rewrite (proj2 (Z.gtb_lt _ _) H6). auto. }
  { rewrite signed_repr_small in H6 by (destruct Hsd as [Hml _]; rep_lia).
    forward. entailer!. unfold B, O. destruct (Z.gtb_spec (ld + 1) (sd_maxlen sd)); [lia | auto]. }
  forward.
  rewrite Int.zero_ext_idem by lia.
  replace_SEP 0 (@data_at DCS.CS Ews (tarray t_ct n) (ct_canon (mkTree (fc t1) (upd_Znth nn (dl t1) (u16 B)))) tp).
  { go_lower. apply derives_refl'. apply ct_store_len; lia. }
  inv_bind H. apply c_set_dl_inv in Ha. destruct Ha as [-> _].
  assert (HuB : u16 B = B) by (unfold u16; apply Z.mod_small; lia). rewrite HuB in *.
  assert (Ht2 : tree_ok (mkTree (fc t1) (upd_Znth nn (dl t1) B)) n) by (apply tree_ok_set_dl; auto; lia).
  forward_if.
  { forward. rewrite (proj2 (Z.gtb_lt nn mc) ltac:(lia)) in H.
    Exists f (mkTree (fc t1) (upd_Znth nn (dl t1) B)) bc o1 s1 O h. entailer!. }
  rewrite Z.gtb_ltb, (proj2 (Z.ltb_ge mc nn) ltac:(lia)) in H.
  inv_bind H. apply rd_inv in Ha. destruct Ha as [-> HBr].
  inv_bind H. apply wr_inv in Ha. destruct Ha as [-> _].
  pose proof H1 as (_ & _ & Hlb1 & _ & _ & _ & _ & Hfb1 & Hol1 & Hsl1).
  cbn [w_bl_count w_opt_len w_static_len] in Hlb1, Hfb1, Hol1, Hsl1.
  assert (HbcB : 0 <= Znth B bc < 65536) by (apply (proj1 (Forall_Znth _ _) Hfb1); lia).
  fwd. fwd.
  replace_SEP 3 (@field_at DCS.CS Ews t_ds (DOT _bl_count) (map vi (upd_Znth B bc (u16 (Znth B bc + 1)))) sp).
  { go_lower. rewrite add_repr32, zext16_repr.
    change (Vint (Int.repr ((Znth B bc + 1) mod 65536))) with (vi (u16 (Znth B bc + 1))).
    rewrite upd_Znth_map. apply derives_refl. }
  forward.
  inv_bind H. rename x into XB.
  destruct Hsd as (Hml & Hbase & Hext).
  assert (HXB : 0 <= XB <= 13).
  { destruct (nn >=? sd_base sd); [apply rd_inv in Ha; destruct Ha as [-> Hr];
      apply (proj1 (Forall_Znth _ _) Hext); lia | injection Ha as <-; lia]. }
  forward_if (PROP ()
     LOCAL (temp _xbits (vi XB); temp _bits (vi B); temp _overflow (vi O); temp _n (vi nn); temp _h (vi h);
            temp _max_length (vi (sd_maxlen sd)); temp _base (vi (sd_base sd)); temp _extra ep; temp _stree stp;
            temp _max_code (vi mc); temp _tree tp; temp _s sp)
     SEP (@data_at DCS.CS Ews (tarray t_ct n) (ct_canon (mkTree (fc t1) (upd_Znth nn (dl t1) B))) tp;
          @field_at DCS.CS Ews t_ds (DOT _heap) (map vi heap) sp;
          @field_at DCS.CS Ews t_ds (DOT _heap_max) (vi hm) sp;
          @field_at DCS.CS Ews t_ds (DOT _bl_count) (map vi (upd_Znth B bc (u16 (Znth B bc + 1)))) sp;
          @field_at DCS.CS Ews t_ds (DOT _opt_len) (vl o1) sp;
          @field_at DCS.CS Ews t_ds (DOT _static_len) (vl s1) sp;
          @data_at DCS.CS Ers (tarray tint (Zlength (sd_extra sd))) (map vi (sd_extra sd)) ep;
          st_at st stp; Fr)).
  { rewrite (proj2 (Z.geb_le nn (sd_base sd)) ltac:(lia)) in Ha. apply rd_inv in Ha. destruct Ha as [-> Hr].
    forward. entailer!. }
  { rewrite Z.geb_leb, (proj2 (Z.leb_gt (sd_base sd) nn) ltac:(lia)) in Ha. injection Ha as <-.
    forward. entailer!. }
  clear Ha. inv_bind H. apply rd_inv in Ha. cbn [fc] in Ha. destruct Ha as [-> _].
  assert (Hfr : 0 <= Znth nn (fc t1) < 65536) by (apply Htr; lia).
  unfold ct_canon.
  forward.
  { entailer!. rewrite Znth_ct_arr. 2: cbn [fc]; lia. cbn [ctv_of ffalse fst fc].
    apply (tc_val_tushort_repr (Znth nn (fc t1))). lia. }
  rewrite Znth_ct_arr. 2: cbn [fc]; lia. cbn [ctv_of ffalse fst fc].
  forward. forward. forward.
  replace_SEP 4 (@field_at DCS.CS Ews t_ds (DOT _opt_len) (vl (u64 (o1 + Znth nn (fc t1) * u32 (B + XB)))) sp).
  { go_lower. unfold vl. rewrite ulg_madd by lia. apply derives_refl. }
  inv_bind H.
  change MAX_BITS with 15 in Hlb1. destruct (bl_count_inc bc B ltac:(lia) Hfb1) as [Hlbc Hfbc].
  destruct st as [ts|].
  - cbn [option_map] in Hst. rewrite <- Hst in Ha. inv_bind Ha. apply rd_inv in Ha0. destruct Ha0 as [-> Hsr].
    injection Ha as <-.
    cbn [w_set_static_len w_set_opt_len w_set_bl_count w_heap w_heap_len w_heap_max w_depth w_bl_count w_opt_len
         w_static_len] in H.
    unfold st_at, tree_arr. Intros. rename H7 into Htsok.
    pose proof Htsok as (Hts1 & Hts2 & Hts3).
    assert (Hsl0 : 0 <= Znth nn (dl ts) < 65536) by (apply Hts3; lia).
    forward_if.
    + forward. unfold ct_canon.
      rewrite (ct_arr_mode Ers (Zlength (dl ts)) ffalse ffalse ffalse ftrue ts stp).
      forward.
      { entailer!. rewrite Znth_ct_arr. 2: lia. cbn [ctv_of ffalse ftrue snd].
        apply (tc_val_tushort_repr (Znth nn (dl ts))). lia. }
      rewrite Znth_ct_arr. 2: lia. cbn [ctv_of ffalse ftrue snd].
      forward.
      rewrite (ct_arr_mode Ers (Zlength (dl ts)) ffalse ftrue ffalse ffalse ts stp).
      Exists f (mkTree (fc t1) (upd_Znth nn (dl t1) B)) (upd_Znth B bc (u16 (Znth B bc + 1)))
        (u64 (o1 + Znth nn (fc t1) * u32 (B + XB))) (u64 (s1 + Znth nn (fc t1) * u32 (Znth nn (dl ts) + XB))) O h.
      unfold st_at, tree_arr, ct_canon. entailer!.
      * apply work_ok_set with bc o1 s1; auto; apply u64_range.
      * unfold vl. rewrite repr64_u64. unfold u32. rewrite (Z.mod_small (Znth nn (dl ts) + XB)) by lia.
        apply derives_refl.
    + subst stp. assert_PROP False by entailer!. contradiction.
  - cbn [option_map] in Hst. rewrite <- Hst in Ha. injection Ha as <-.
    cbn [w_set_static_len w_set_opt_len w_set_bl_count w_heap w_heap_len w_heap_max w_depth w_bl_count w_opt_len
         w_static_len] in H.
    unfold st_at. Intros. subst stp.
    forward_if.
    + exfalso. exact H7.
    + forward.
      Exists f (mkTree (fc t1) (upd_Znth nn (dl t1) B)) (upd_Znth B bc (u16 (Znth B bc + 1)))
        (u64 (o1 + Znth nn (fc t1) * u32 (B + XB))) s1 O h.
      unfold st_at, ct_canon. entailer!.
      apply work_ok_set with bc o1 s1; auto; apply u64_range.
Qed.

(** The bit length repair loop. *)
Lemma gb_repair {Espec : OracleKind} (sp tp : val) (mc ml ov : Z) (blc blc' : list Z) (Fr : mpred) :
  (ml = 7 \/ ml = 15) -> 0 < ov <= HEAP_SIZE ->
  Zlength blc = 16 -> Forall (fun x => 0 <= x < 65536) blc ->
  c_gen_bitlen_repair (Z.to_nat HEAP_SIZE) ml blc ov = Some blc' ->
  semax gb_Delta
    (PROP ()
     LOCAL (temp _overflow (vi ov); temp _max_length (vi ml); temp _h (vi HEAP_SIZE); temp _max_code (vi mc);
            temp _tree tp; temp _s sp)
     SEP (@field_at DCS.CS Ews t_ds (DOT _bl_count) (map vi blc) sp; Fr))
    gb_repair_stmt
    (normal_ret_assert
     (PROP (Zlength blc' = 16; Forall (fun x => 0 <= x < 65536) blc')
      LOCAL (temp _max_length (vi ml); temp _h (vi HEAP_SIZE); temp _max_code (vi mc); temp _tree tp; temp _s sp)
      SEP (@field_at DCS.CS Ews t_ds (DOT _bl_count) (map vi blc') sp; Fr))).
Proof.
  intros Hml Hov Hlb Hfb Hrun.
  unfold gb_Delta, gb_repair_stmt. simplify_func_tycontext. abbreviate_semax.
  unfold HEAP_SIZE in *.
  forward_loop
    (EX f : nat, EX bl : list Z, EX ov1 : Z,
     PROP (c_gen_bitlen_repair f ml bl ov1 = Some blc'; Zlength bl = 16; Forall (fun x => 0 <= x < 65536) bl;
           0 < ov1 <= 573)
     LOCAL (temp _overflow (vi ov1); temp _max_length (vi ml); temp _h (vi 573); temp _max_code (vi mc);
            temp _tree tp; temp _s sp)
     SEP (@field_at DCS.CS Ews t_ds (DOT _bl_count) (map vi bl) sp; Fr))
    continue:
    (EX f : nat, EX bl : list Z, EX ov1 : Z,
     PROP ((if ov1 >? 0 then c_gen_bitlen_repair f ml bl ov1 else Some bl) = Some blc'; Zlength bl = 16;
           Forall (fun x => 0 <= x < 65536) bl; -2 < ov1 <= 573)
     LOCAL (temp _overflow (vi ov1); temp _max_length (vi ml); temp _h (vi 573); temp _max_code (vi mc);
            temp _tree tp; temp _s sp)
     SEP (@field_at DCS.CS Ews t_ds (DOT _bl_count) (map vi bl) sp; Fr))
    break:
    (PROP (Zlength blc' = 16; Forall (fun x => 0 <= x < 65536) blc')
     LOCAL (temp _max_length (vi ml); temp _h (vi 573); temp _max_code (vi mc); temp _tree tp; temp _s sp)
     SEP (@field_at DCS.CS Ews t_ds (DOT _bl_count) (map vi blc') sp; Fr)).
  { Exists (Z.to_nat 573) blc ov. entailer!. }
  2: { Intros f bl ov1. forward_if.
       - forward. rewrite (proj2 (Z.gtb_lt ov1 0) ltac:(lia)) in H. Exists f bl ov1. entailer!.
       - forward. rewrite Z.gtb_ltb, (proj2 (Z.ltb_ge 0 ov1) ltac:(lia)) in H. injection H as ->. entailer!. }
  2: { unfold abbreviate in POSTCONDITION; subst POSTCONDITION; simpl_ret_assert. entailer!. }
  Intros f bl ov1.
  match goal with Hr : c_gen_bitlen_repair _ _ _ _ = _ |- _ => rename Hr into H end.
  match goal with Hr : Zlength bl = 16 |- _ => rename Hr into Hlbl end.
  match goal with Hr : Forall _ bl |- _ => rename Hr into Hfbl end.
  destruct f as [|f]; [discriminate|]. cbn [c_gen_bitlen_repair] in H.
  inv_bind H. rename x into bs. rename Ha into Hfind.
  forward.
  forward_loop
    (EX g : nat, EX b : Z,
     PROP (c_find_nonzero_down g bl b = Some bs; b <= 15)
     LOCAL (temp _bits (vi b); temp _overflow (vi ov1); temp _max_length (vi ml); temp _h (vi 573);
            temp _max_code (vi mc); temp _tree tp; temp _s sp)
     SEP (@field_at DCS.CS Ews t_ds (DOT _bl_count) (map vi bl) sp; Fr))
    break:
    (PROP ()
     LOCAL (temp _bits (vi bs); temp _overflow (vi ov1); temp _max_length (vi ml); temp _h (vi 573);
            temp _max_code (vi mc); temp _tree tp; temp _s sp)
     SEP (@field_at DCS.CS Ews t_ds (DOT _bl_count) (map vi bl) sp; Fr)).
  { Exists 20%nat (ml - 1). entailer!. }
  { Intros g b.
    match goal with Hr : c_find_nonzero_down g bl b = _ |- _ => rename Hr into Hg end.
    destruct g as [|g]; [discriminate|]. cbn [c_find_nonzero_down] in Hg.
    inv_bind Hg. apply rd_inv in Ha. destruct Ha as [-> Hb].
    assert (0 <= Znth b bl < 65536) by (apply (proj1 (Forall_Znth _ _) Hfbl); lia).
    fwd.
    forward_if.
    - match goal with Hr : Znth b bl = 0 |- _ => rewrite (proj2 (Z.eqb_eq _ 0) Hr) in Hg end.
      forward. Exists g (b - 1). entailer!.
    - match goal with Hr : Znth b bl <> 0 |- _ => rewrite (proj2 (Z.eqb_neq _ 0) Hr) in Hg end.
      injection Hg as <-. forward. entailer!. }
  clear Hfind.
  inv_bind H. apply rd_inv in Ha. destruct Ha as [-> Hbs].
  inv_bind H. apply wr_inv in Ha. destruct Ha as [-> _].
  assert (0 <= Znth bs bl < 65536) by (apply (proj1 (Forall_Znth _ _) Hfbl); lia).
  fwd. fwd.
  replace_SEP 0 (@field_at DCS.CS Ews t_ds (DOT _bl_count) (map vi (upd_Znth bs bl (u16 (Znth bs bl - 1)))) sp).
  { go_lower. rewrite sub_repr32, zext16_repr, upd_map_vi16. apply derives_refl. }
  set (bl1 := upd_Znth bs bl (u16 (Znth bs bl - 1))) in *.
  assert (Hl1 : Zlength bl1 = 16) by (unfold bl1; rewrite Zlength_upd_Znth; auto).
  assert (Hf1 : Forall (fun x => 0 <= x < 65536) bl1) by (apply u16_Forall_upd; auto).
  inv_bind H. apply rd_inv in Ha. destruct Ha as [-> Hbs1].
  inv_bind H. apply wr_inv in Ha. destruct Ha as [-> _].
  assert (0 <= Znth (bs + 1) bl1 < 65536) by (apply (proj1 (Forall_Znth _ _) Hf1); lia).
  fwd. fwd.
  replace_SEP 0 (@field_at DCS.CS Ews t_ds (DOT _bl_count) (map vi (upd_Znth (bs + 1) bl1 (u16 (Znth (bs + 1) bl1 + 2)))) sp).
  { go_lower. rewrite add_repr32, zext16_repr, upd_map_vi16. apply derives_refl. }
  set (bl2 := upd_Znth (bs + 1) bl1 (u16 (Znth (bs + 1) bl1 + 2))) in *.
  assert (Hl2 : Zlength bl2 = 16) by (unfold bl2; rewrite Zlength_upd_Znth; auto).
  assert (Hf2 : Forall (fun x => 0 <= x < 65536) bl2) by (apply u16_Forall_upd; auto).
  inv_bind H. apply rd_inv in Ha. destruct Ha as [-> Hml2].
  inv_bind H. apply wr_inv in Ha. destruct Ha as [-> _].
  assert (0 <= Znth ml bl2 < 65536) by (apply (proj1 (Forall_Znth _ _) Hf2); lia).
  fwd. fwd.
  replace_SEP 0 (@field_at DCS.CS Ews t_ds (DOT _bl_count) (map vi (upd_Znth ml bl2 (u16 (Znth ml bl2 - 1)))) sp).
  { go_lower. rewrite sub_repr32, zext16_repr, upd_map_vi16. apply derives_refl. }
  forward.
  Exists f (upd_Znth ml bl2 (u16 (Znth ml bl2 - 1))) (ov1 - 2).
  entailer!. split; [rewrite Zlength_upd_Znth; auto | apply u16_Forall_upd; auto].
Qed.

(** The reassignment of the bit lengths after the repair. *)
Lemma gb_reassign {Espec : OracleKind} (sp tp : val) (n mc ml : Z) (t : tree) (heap blc : list Z) (ol : Z)
    (t' : tree) (ol' : Z) (Fr : mpred) :
  (ml = 7 \/ ml = 15) -> Int.min_signed <= mc <= Int.max_signed -> tree_ok t n ->
  Zlength heap = 573 -> Forall (fun x => Int.min_signed <= x <= Int.max_signed) heap ->
  Zlength blc = 16 -> Forall (fun x => 0 <= x < 65536) blc -> 0 <= ol <= Int64.max_unsigned ->
  c_gen_bitlen_reassign 20 mc heap blc t ol HEAP_SIZE ml = Some (t', ol') ->
  semax gb_Delta
    (PROP ()
     LOCAL (temp _max_length (vi ml); temp _h (vi HEAP_SIZE); temp _max_code (vi mc); temp _tree tp; temp _s sp)
     SEP (@data_at DCS.CS Ews (tarray t_ct n) (ct_canon t) tp;
          @field_at DCS.CS Ews t_ds (DOT _heap) (map vi heap) sp;
          @field_at DCS.CS Ews t_ds (DOT _bl_count) (map vi blc) sp;
          @field_at DCS.CS Ews t_ds (DOT _opt_len) (vl ol) sp; Fr))
    gb_reassign_stmt
    (normal_ret_assert
     (PROP (tree_ok t' n; 0 <= ol' <= Int64.max_unsigned)
      LOCAL ()
      SEP (@data_at DCS.CS Ews (tarray t_ct n) (ct_canon t') tp;
           @field_at DCS.CS Ews t_ds (DOT _heap) (map vi heap) sp;
           @field_at DCS.CS Ews t_ds (DOT _bl_count) (map vi blc) sp;
           @field_at DCS.CS Ews t_ds (DOT _opt_len) (vl ol') sp; Fr))).
Proof.
  intros Hml Hmc Htok Hlh Hfh Hlb Hfb Hol Hrun.
  unfold gb_Delta, gb_reassign_stmt. simplify_func_tycontext. abbreviate_semax.
  unfold HEAP_SIZE in *.
  forward.
  forward_loop
    (EX f : nat, EX t1 : tree, EX ol1 : Z, EX h1 : Z, EX b : Z,
     PROP (c_gen_bitlen_reassign f mc heap blc t1 ol1 h1 b = Some (t', ol'); tree_ok t1 n;
           0 <= ol1 <= Int64.max_unsigned; 0 <= b <= 15; 0 <= h1 <= 573)
     LOCAL (temp _bits (vi b); temp _h (vi h1); temp _max_length (vi ml); temp _max_code (vi mc);
            temp _tree tp; temp _s sp)
     SEP (@data_at DCS.CS Ews (tarray t_ct n) (ct_canon t1) tp;
          @field_at DCS.CS Ews t_ds (DOT _heap) (map vi heap) sp;
          @field_at DCS.CS Ews t_ds (DOT _bl_count) (map vi blc) sp;
          @field_at DCS.CS Ews t_ds (DOT _opt_len) (vl ol1) sp; Fr))
    continue:
    (EX f : nat, EX t1 : tree, EX ol1 : Z, EX h1 : Z, EX b : Z,
     PROP (c_gen_bitlen_reassign f mc heap blc t1 ol1 h1 (b - 1) = Some (t', ol'); tree_ok t1 n;
           0 <= ol1 <= Int64.max_unsigned; 1 <= b <= 15; 0 <= h1 <= 573)
     LOCAL (temp _bits (vi b); temp _h (vi h1); temp _max_length (vi ml); temp _max_code (vi mc);
            temp _tree tp; temp _s sp)
     SEP (@data_at DCS.CS Ews (tarray t_ct n) (ct_canon t1) tp;
          @field_at DCS.CS Ews t_ds (DOT _heap) (map vi heap) sp;
          @field_at DCS.CS Ews t_ds (DOT _bl_count) (map vi blc) sp;
          @field_at DCS.CS Ews t_ds (DOT _opt_len) (vl ol1) sp; Fr))
    break:
    (PROP (tree_ok t' n; 0 <= ol' <= Int64.max_unsigned)
     LOCAL ()
     SEP (@data_at DCS.CS Ews (tarray t_ct n) (ct_canon t') tp;
          @field_at DCS.CS Ews t_ds (DOT _heap) (map vi heap) sp;
          @field_at DCS.CS Ews t_ds (DOT _bl_count) (map vi blc) sp;
          @field_at DCS.CS Ews t_ds (DOT _opt_len) (vl ol') sp; Fr)).
  { Exists 20%nat t ol 573 ml. entailer!. }
  2: { Intros f t1 ol1 h1 b. forward. Exists f t1 ol1 h1 (b - 1). entailer!. }
  2: { unfold abbreviate in POSTCONDITION; subst POSTCONDITION; simpl_ret_assert. entailer!. }
  Intros f t1 ol1 h1 b.
  match goal with Hr : c_gen_bitlen_reassign _ _ _ _ _ _ _ _ = _ |- _ => rename Hr into H end.
  forward_if.
  2: { forward. assert (b = 0) by lia. subst b.
       destruct f; cbn [c_gen_bitlen_reassign] in H; injection H as <- <-; entailer!. }
  destruct f as [|f]; [cbn in H; rewrite (proj2 (Z.eqb_neq b 0) ltac:(lia)) in H; discriminate|].
  cbn [c_gen_bitlen_reassign] in H. rewrite (proj2 (Z.eqb_neq b 0) ltac:(lia)) in H.
  inv_bind H. apply rd_inv in Ha. destruct Ha as [-> Hbr].
  inv_bind H. destruct x as [[t3 ol3] h3]. rename Ha into Hin.
  assert (Hk0 : 0 <= Znth b blc < 65536) by (apply (proj1 (Forall_Znth _ _) Hfb); lia).
  fwd.
  forward_loop
    (EX g : nat, EX t2 : tree, EX ol2 : Z, EX h2 : Z, EX k : Z,
     PROP (c_gen_bitlen_reassign_inner g mc b heap t2 ol2 h2 k = Some (t3, ol3, h3); tree_ok t2 n;
           0 <= ol2 <= Int64.max_unsigned; 0 <= k < 65536; 0 <= h2 <= 573)
     LOCAL (temp _n (vi k); temp _h (vi h2); temp _bits (vi b); temp _max_length (vi ml); temp _max_code (vi mc);
            temp _tree tp; temp _s sp)
     SEP (@data_at DCS.CS Ews (tarray t_ct n) (ct_canon t2) tp;
          @field_at DCS.CS Ews t_ds (DOT _heap) (map vi heap) sp;
          @field_at DCS.CS Ews t_ds (DOT _bl_count) (map vi blc) sp;
          @field_at DCS.CS Ews t_ds (DOT _opt_len) (vl ol2) sp; Fr))
    break:
    (PROP (tree_ok t3 n; 0 <= ol3 <= Int64.max_unsigned; 0 <= h3 <= 573)
     LOCAL (temp _h (vi h3); temp _bits (vi b); temp _max_length (vi ml); temp _max_code (vi mc);
            temp _tree tp; temp _s sp)
     SEP (@data_at DCS.CS Ews (tarray t_ct n) (ct_canon t3) tp;
          @field_at DCS.CS Ews t_ds (DOT _heap) (map vi heap) sp;
          @field_at DCS.CS Ews t_ds (DOT _bl_count) (map vi blc) sp;
          @field_at DCS.CS Ews t_ds (DOT _opt_len) (vl ol3) sp; Fr)).
  { Exists (Z.to_nat 573) t1 ol1 h1 (Znth b blc). entailer!. }
  { Intros g t2 ol2 h2 k.
    match goal with Hr : c_gen_bitlen_reassign_inner g _ _ _ t2 _ _ _ = _ |- _ => rename Hr into Hg end.
    forward_if.
    2: { forward. assert (k = 0) by lia. subst k.
         destruct g; cbn [c_gen_bitlen_reassign_inner] in Hg; injection Hg as <- <- <-; entailer!. }
    destruct g as [|g]; [cbn in Hg; rewrite (proj2 (Z.eqb_neq k 0) ltac:(lia)) in Hg; discriminate|].
    cbn [c_gen_bitlen_reassign_inner] in Hg. rewrite (proj2 (Z.eqb_neq k 0) ltac:(lia)) in Hg.
    inv_bind Hg. apply rd_inv in Ha. destruct Ha as [-> Hhr].
    assert (Int.min_signed <= Znth (h2 - 1) heap <= Int.max_signed) by (apply (proj1 (Forall_Znth _ _) Hfh); lia).
    forward. forward. forward.
    set (m := Znth (h2 - 1) heap) in *.
    forward_if.
    { forward. rewrite (proj2 (Z.gtb_lt m mc) ltac:(lia)) in Hg.
      Exists g t2 ol2 (h2 - 1) k. entailer!. }
    rewrite Z.gtb_ltb, (proj2 (Z.ltb_ge mc m) ltac:(lia)) in Hg.
    inv_bind Hg. apply rd_inv in Ha. destruct Ha as [-> Hmr].
    match goal with Ht : tree_ok t2 n |- _ => pose proof Ht as (Htf & Htd & Htr) end.
    assert (Hlm : 0 <= Znth m (dl t2) < 65536) by (apply Htr; lia).
    assert (Hfm : 0 <= Znth m (fc t2) < 65536) by (apply Htr; lia).
    unfold ct_canon. rewrite (ct_arr_mode Ews n ffalse ffalse ffalse ftrue t2 tp).
    forward.
    { entailer!. rewrite Znth_ct_arr. 2: lia. cbn [ctv_of ffalse ftrue snd].
      apply (tc_val_tushort_repr (Znth m (dl t2))). lia. }
    rewrite Znth_ct_arr. 2: lia. cbn [ctv_of ffalse ftrue snd].
    inv_bind Hg. destruct x as [T OL]. rename Ha into Hif.
    assert (HTOL : tree_ok T n /\ 0 <= OL <= Int64.max_unsigned /\
                   (Znth m (dl t2) = b -> T = t2 /\ OL = ol2) /\
                   (Znth m (dl t2) <> b -> T = mkTree (fc t2) (upd_Znth m (dl t2) b) /\
                      OL = u64 (ol2 + u64 (b - Znth m (dl t2)) * Znth m (fc t2)))).
    { destruct (Z.eq_dec (Znth m (dl t2)) b) as [E|E].
      - rewrite (proj2 (Z.eqb_eq _ _) E) in Hif. cbn in Hif. injection Hif as <- <-.
        split; [auto|]. split; [auto|]. split; [intros; auto|]. intros; contradiction.
      - rewrite (proj2 (Z.eqb_neq _ _) E) in Hif. cbn [negb] in Hif.
        inv_bind Hif. apply rd_inv in Ha. destruct Ha as [-> _].
        inv_bind Hif. apply c_set_dl_inv in Ha. destruct Ha as [-> _]. injection Hif as <- <-.
        assert (Hu : u16 b = b) by (unfold u16; apply Z.mod_small; lia). rewrite Hu.
        split; [apply tree_ok_set_dl; auto; lia|]. split; [apply u64_range|].
        split; [intros; contradiction | intros; split; reflexivity]. }
    destruct HTOL as (HT & HOL & HTe & HTn).
    forward_if (PROP ()
       LOCAL (temp _n (vi k); temp _h (vi (h2 - 1)); temp _bits (vi b); temp _max_length (vi ml);
              temp _max_code (vi mc); temp _tree tp; temp _s sp)
       SEP (@data_at DCS.CS Ews (tarray t_ct n) (ct_canon T) tp;
            @field_at DCS.CS Ews t_ds (DOT _heap) (map vi heap) sp;
            @field_at DCS.CS Ews t_ds (DOT _bl_count) (map vi blc) sp;
            @field_at DCS.CS Ews t_ds (DOT _opt_len) (vl OL) sp; Fr)).
    { assert (Hne : Znth m (dl t2) <> b) by assumption.
      destruct (HTn Hne) as [-> ->].
      forward. forward.
      { entailer!. rewrite Znth_ct_arr. 2: lia. cbn [ctv_of ffalse ftrue snd].
        apply (tc_val_tushort_repr (Znth m (dl t2))). lia. }
      rewrite Znth_ct_arr. 2: lia. cbn [ctv_of ffalse ftrue snd fst].
      forward.
      { entailer!. rewrite Znth_ct_arr. 2: lia. cbn [ctv_of ffalse ftrue fst].
        apply (tc_val_tushort_repr (Znth m (fc t2))). lia. }
      rewrite Znth_ct_arr. 2: lia. cbn [ctv_of ffalse ftrue snd fst].
      forward. forward.
      entailer!. apply sepcon_derives.
      - apply derives_refl'. rewrite Int.zero_ext_idem by lia.
        replace (upd_Znth m (dl t2) b) with (upd_Znth m (dl t2) (u16 b)) by (unfold u16; rewrite Z.mod_small by lia; auto).
        apply ct_store_len; lia.
      - unfold vl. rewrite repr64_u64, repr64_u64_mul. apply derives_refl. }
    { assert (He : Znth m (dl t2) = b)
        by (first [assumption | apply repr_inj_unsigned; [rep_lia | rep_lia | assumption]]).
      destruct (HTe He) as [-> ->].
      forward.
      rewrite (ct_arr_mode Ews n ffalse ftrue ffalse ffalse t2 tp). unfold ct_canon. entailer!. }
    forward.
    Exists g T OL (h2 - 1) (k - 1). entailer!. }
  Intros. unfold abbreviate in POSTCONDITION; subst POSTCONDITION; simpl_ret_assert.
  Exists f t3 ol3 h3 b. entailer!.
Qed.

(** The function's type context with any function specifications (forward makes them opaque); gen_bitlen has
    no callees, so the part lemmas above apply in it. *)
Lemma gb_Delta_sub DS :
  tycontext_sub gb_Delta
    (mk_tycontext (temp_types gb_Delta) (var_types gb_Delta) (ret_type gb_Delta) (glob_types gb_Delta) DS
       (annotations gb_Delta)).
Proof.
  unfold tycontext_sub. cbn [temp_types var_types ret_type glob_types glob_specs annotations].
  split; [intros id; destruct (Maps.PTree.get id (temp_types gb_Delta)); auto|].
  split; [auto|]. split; [auto|]. split; [intros id; destruct (Maps.PTree.get id (glob_types gb_Delta)); cbn; auto|].
  split.
  - intros id. unfold gb_Delta, func_tycontext, make_tycontext. cbn [glob_specs].
    unfold Gprog_gen_bitlen, make_tycontext_s. cbn. rewrite Maps.PTree.gempty. exact I.
  - intros id. destruct (Maps.PTree.get id (annotations gb_Delta)) as [a|]; cbn; auto. destruct a; auto.
Qed.

Ltac gb_sub := eapply semax_Delta_subsumption; [apply gb_Delta_sub|].

Lemma body_gen_bitlen : semax_body Vprog Gprog_gen_bitlen f_gen_bitlen gen_bitlen_spec.
Proof.
  start_function.
  destruct (sd_split gv sd statp H) as [Hsd [stp [ep [st [R [Hst Hgl]]]]]].
  rewrite Hgl.
  destruct w as [heap hl hm depth blc ol sl].
  unfold td_at, tree_arr, work_at. Intros.
  rename H1 into Hmc, H2 into Htok, H3 into Hwok.
  destruct Hwok as (Hlh & Hld & Hlb & Hfh & Hhl & Hhm & Hfd & Hfb & Hol & Hsl).
  cbn [w_heap w_heap_len w_heap_max w_depth w_bl_count w_opt_len w_static_len] in *.
  unfold td_val. cbn [td_dyn_tree td_max_code td_stat_desc].
  assert_PROP (is_pointer_or_null stp /\ isptr ep) as Hptr.
  { destruct st; unfold st_at, tree_arr; Intros; entailer!. }
  destruct Hptr as [Hstp Hep].
  forward. forward.
  forward. forward. forward. forward. forward. forward. forward. forward.
  forward.
  freeze [0;3;5;7;8;9;10;11;12] FR.
  forward_loop
    (EX b : Z,
     PROP (0 <= b <= 16)
     LOCAL (temp _bits (vi b); temp _overflow (vi 0); temp _max_length (vi (sd_maxlen sd)); temp _base (vi (sd_base sd));
            temp _extra ep; temp _stree stp; temp _max_code (vi max_code); temp _tree tp; gvars gv; temp _s sp)
     SEP (@field_at DCS.CS Ews t_ds (DOT _bl_count) (map vi (repeat 0 (Z.to_nat b) ++ sublist b 16 blc)) sp;
          @data_at DCS.CS Ews (tarray t_ct n) (ct_canon t) tp;
          @field_at DCS.CS Ews t_ds (DOT _heap) (map vi heap) sp;
          @field_at DCS.CS Ews t_ds (DOT _heap_max) (vi hm) sp;
          FRZL FR))
    break:
    (PROP ()
     LOCAL (temp _overflow (vi 0); temp _max_length (vi (sd_maxlen sd)); temp _base (vi (sd_base sd));
            temp _extra ep; temp _stree stp; temp _max_code (vi max_code); temp _tree tp; gvars gv; temp _s sp)
     SEP (@field_at DCS.CS Ews t_ds (DOT _bl_count) (map vi (repeat 0 16)) sp;
          @data_at DCS.CS Ews (tarray t_ct n) (ct_canon t) tp;
          @field_at DCS.CS Ews t_ds (DOT _heap) (map vi heap) sp;
          @field_at DCS.CS Ews t_ds (DOT _heap_max) (vi hm) sp;
          FRZL FR)).
  { forward. Exists 0. entailer!. rewrite sublist_same by auto. apply derives_refl. }
  { Intros b.
    forward_if.
    - forward. forward. Exists (b + 1). entailer!.
      change (Vint (Int.zero_ext 16 (Int.repr 0))) with (vi 0).
      rewrite upd_Znth_map. apply derives_refl'. f_equal. f_equal.
      rewrite Z2Nat.inj_add, repeat_app by lia. change MAX_BITS with 15 in Hlb. list_solve.
    - forward. entailer!. assert (b = 16) by lia. subst b.
      rewrite sublist_nil, app_nil_r. apply derives_refl. }
  unfold c_gen_bitlen in H0. cbn [w_heap w_heap_max w_set_bl_count] in H0.
  inv_bind H0. apply rd_inv in Ha. destruct Ha as [-> Hhm'].
  inv_bind H0. apply c_set_dl_inv in Ha. destruct Ha as [-> Hr0].
  change (2 * L_CODES + 1) with 573 in Hlh. change (MAX_BITS + 1) with 16 in Hlb.
  forward. forward.
  assert (Int.min_signed <= Znth hm heap <= Int.max_signed) by (apply (proj1 (Forall_Znth _ _) Hfh); lia).
  forward.
  { entailer!. destruct Htok as [Hf [Hd _]]. lia. }
  pose proof Htok as [Htf [Htd Htr]].
  change (ct_canon t) with (ct_arr ffalse ffalse t).
  rewrite (ct_store_len Ews n ffalse ffalse t (Znth hm heap) 0 tp) by lia.
  change (u16 0) with 0.
  inv_bind H0. destruct x as [[t2 w2] ov].
  thaw FR.
  freeze [4;5;6;9;12] FR2.
  assert (Hw1 : work_ok (mkWork heap hl hm depth (repeat 0 16) ol sl)).
  { unfold work_ok; cbn [w_heap w_heap_len w_heap_max w_depth w_bl_count w_opt_len w_static_len].
    change L_CODES with 286. change MAX_BITS with 15. repeat split; auto; try lia. repeat constructor; lia. }
  eapply semax_seq'.
  { gb_sub. eapply semax_pre; [| apply (gb_pass1 sp tp stp ep n max_code sd st
      (mkTree (fc t) (upd_Znth (Znth hm heap) (dl t) 0)) (mkWork heap hl hm depth (repeat 0 16) ol sl)
      t2 w2 ov (FRZL FR2) Hsd Hst Hmc)].
    - cbn [w_heap w_heap_max w_bl_count w_opt_len w_static_len]. entailer!.
    - apply tree_ok_set_dl; auto; lia.
    - exact Hw1.
    - cbn. unfold HEAP_SIZE. lia.
    - exact Ha. }
  Intros. destruct w2 as [heap2 hl2 hm2 depth2 bc2 ol2 sl2].
  cbn [w_heap w_heap_len w_heap_max w_depth w_bl_count w_opt_len w_static_len] in *.
  subst heap2 hl2 hm2 depth2.
  unfold abbreviate in MORE_COMMANDS; subst MORE_COMMANDS. abbreviate_semax.
  unfold HEAP_SIZE in H8.
  forward_if.
  { subst ov. cbn in H0. injection H0 as <-. forward.
    thaw FR2. unfold td_at, tree_arr, work_at. rewrite Hgl.
    cbn [fst snd w_heap w_heap_len w_heap_max w_depth w_bl_count w_opt_len w_static_len].
    entailer!. }
  rewrite (proj2 (Z.eqb_neq ov 0) H4) in H0.
  inv_bind H0. rename x into bc3. inv_bind H0. destruct x as [t3 ol3]. injection H0 as <-.
  cbn [w_opt_len w_set_bl_count] in Ha1.
  destruct H3 as (_ & _ & Hlb2 & _ & _ & _ & _ & Hfb2 & Hol2 & Hsl2). cbn in Hlb2, Hfb2, Hol2, Hsl2.
  freeze [0;1;2;4;5;6;7;8] FR3.
  eapply semax_seq'.
  { gb_sub. eapply semax_pre; [| apply (gb_repair sp tp max_code (sd_maxlen sd) ov bc2 bc3 (FRZL FR3))].
    - entailer!.
    - destruct Hsd as [Hml _]. lia.
    - unfold HEAP_SIZE. lia.
    - exact Hlb2.
    - exact Hfb2.
    - exact Ha0. }
  Intros. thaw FR3. unfold abbreviate in MORE_COMMANDS; subst MORE_COMMANDS.
  freeze [3;5;6;7;8] FR4.
  normalize_postcondition.
  eapply semax_post_flipped'.
  { gb_sub. eapply semax_pre; [| apply (gb_reassign sp tp n max_code (sd_maxlen sd) t2 heap bc3 ol2 t3 ol3 (FRZL FR4))].
    - entailer!.
    - destruct Hsd as [Hml _]. lia.
    - exact Hmc.
    - exact H2.
    - exact Hlh.
    - exact Hfh.
    - exact H0.
    - exact H3.
    - rep_lia.
    - exact Ha1. }
  thaw FR4. thaw FR2.
  simpl_ret_assert. unfold stackframe_of. simpl fn_vars. cbn [fold_right map]. rewrite sepcon_emp.
  unfold td_at, tree_arr, work_at. rewrite Hgl.
  cbn [fst snd w_set_opt_len w_set_bl_count w_heap w_heap_len w_heap_max w_depth w_bl_count w_opt_len w_static_len].
  entailer!.
  unfold work_ok; cbn [w_set_opt_len w_set_bl_count w_heap w_heap_len w_heap_max w_depth w_bl_count w_opt_len w_static_len].
  change (2 * L_CODES + 1) with 573. change (MAX_BITS + 1) with 16. repeat split; auto; rep_lia.
Qed.
