(** * The body of trees.c's build_tree against its shared specification (TSpec.v) *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.trees.TSpec.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.proof.trees.CtMode.
Require Import Zlib.proof.trees.BuildTreeKit.
Require Import Zlib.trees.code.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

Lemma Znth_ct_canon t i : 0 <= i < Zlength (fc t) ->
  Znth i (ct_canon t) = ctv_of false false (Znth i (fc t)) (Znth i (dl t)).
Proof. intros. unfold ct_canon. rewrite Znth_ct_arr by auto. reflexivity. Qed.

Lemma repr_u64 x : Int64.repr (u64 x) = Int64.repr x.
Proof.
  unfold u64. change 18446744073709551616 with Int64.modulus.
  rewrite <- Int64.unsigned_repr_eq, Int64.repr_unsigned. reflexivity.
Qed.

Lemma divs2_repr a : 0 <= a <= Int.max_signed -> Int.divs (Int.repr a) (Int.repr 2) = Int.repr (a / 2).
Proof.
  intros. unfold Int.divs. rewrite !Int.signed_repr by rep_lia.
  rewrite Z.quot_div_nonneg by lia. reflexivity.
Qed.

Lemma work_ok_heap' w l i v : work_ok w -> l = w_heap w -> Int.min_signed <= v <= Int.max_signed ->
  work_ok (w_set_heap w (upd_Znth i l v)).
Proof. intros ? -> ?. apply work_ok_heap; auto. Qed.

Lemma work_ok_depth' w l i v : work_ok w -> l = w_depth w -> 0 <= v < 256 ->
  work_ok (w_set_depth w (upd_Znth i l v)).
Proof. intros ? -> ?. apply work_ok_depth; auto. Qed.

(** [work_ok] of a work area built by stores from one that is [work_ok]. *)
Ltac work_ok_tac :=
  repeat lazymatch goal with
  | |- work_ok (w_set_heap _ (upd_Znth _ _ _)) => simple apply work_ok_heap'; [ | reflexivity | rep_lia ]
  | |- work_ok (w_set_depth _ (upd_Znth _ _ _)) =>
      simple apply work_ok_depth'; [ | reflexivity | first [apply u8_range | rep_lia] ]
  | |- work_ok (w_set_heap_len _ _) => simple apply work_ok_heap_len; [ | rep_lia ]
  | |- work_ok (w_set_heap_max _ _) => simple apply work_ok_heap_max; [ | rep_lia ]
  | |- work_ok (w_set_opt_len _ (u64 _)) => simple apply work_ok_opt_len
  | |- work_ok (w_set_static_len _ (u64 _)) => simple apply work_ok_static_len
  | |- work_ok _ => assumption
  end.

(** Stores into one member of one entry of a tree array in the canonical presentation. *)
Lemma data_at_ct_set_dl sh n t i v (x : val + val) p :
  0 <= i < Zlength (fc t) -> Zlength (dl t) = Zlength (fc t) ->
  (x = inl (vi v) \/ x = inr (vi v)) ->
  @data_at DCS.CS sh (tarray t_ct n) (upd_Znth i (ct_canon t) (fst (Znth i (ct_canon t)), x)) p =
  @data_at DCS.CS sh (tarray t_ct n) (ct_canon (mkTree (fc t) (upd_Znth i (dl t) v))) p.
Proof.
  intros Hi Hl Hx. unfold ct_canon. apply data_at_ct_ext.
  - rewrite Zlength_upd_Znth, !Zlength_ct_arr. reflexivity.
  - intros j Hj. rewrite Zlength_upd_Znth, Zlength_ct_arr in Hj.
    rewrite (Znth_ct_arr _ _ (mkTree _ _)) by (cbn; lia). cbn [fc dl].
    destruct (Z.eq_dec j i) as [->|ne].
    + rewrite upd_Znth_same by (rewrite Zlength_ct_arr; lia). rewrite Znth_ct_arr by lia.
      rewrite upd_Znth_same by lia. cbn.
      destruct Hx as [->| ->]; [exists false, false, false, false | exists false, true, false, false];
        do 2 eexists; split; reflexivity.
    + rewrite upd_Znth_diff by (rewrite ?Zlength_ct_arr; lia). rewrite Znth_ct_arr by lia.
      rewrite upd_Znth_diff by lia. do 6 eexists; split; reflexivity.
Qed.

Lemma data_at_ct_set_fc sh n t i v (x : val + val) p :
  0 <= i < Zlength (fc t) -> Zlength (dl t) = Zlength (fc t) ->
  (x = inl (vi v) \/ x = inr (vi v)) ->
  @data_at DCS.CS sh (tarray t_ct n) (upd_Znth i (ct_canon t) (x, snd (Znth i (ct_canon t)))) p =
  @data_at DCS.CS sh (tarray t_ct n) (ct_canon (mkTree (upd_Znth i (fc t) v) (dl t))) p.
Proof.
  intros Hi Hl Hx. unfold ct_canon. apply data_at_ct_ext.
  - rewrite Zlength_upd_Znth, !Zlength_ct_arr. cbn. rewrite Zlength_upd_Znth. reflexivity.
  - intros j Hj. rewrite Zlength_upd_Znth, Zlength_ct_arr in Hj.
    rewrite (Znth_ct_arr _ _ (mkTree _ _)) by (cbn; rewrite Zlength_upd_Znth; lia).
    cbn [fc dl].
    destruct (Z.eq_dec j i) as [->|ne].
    + rewrite upd_Znth_same by (rewrite Zlength_ct_arr; lia). rewrite Znth_ct_arr by lia.
      rewrite upd_Znth_same by lia. cbn.
      destruct Hx as [->| ->]; [exists false, false, false, false | exists true, false, false, false];
        do 2 eexists; split; reflexivity.
    + rewrite upd_Znth_diff by (rewrite ?Zlength_ct_arr; lia). rewrite Znth_ct_arr by lia.
      rewrite upd_Znth_diff by lia. do 6 eexists; split; reflexivity.
Qed.

(** Side conditions of a load from a tree array: the type check of the loaded union member (after
    [Znth_ct_canon]) and the index range. *)
Ltac ct_side :=
  lazymatch goal with
  | |- _ |-- local _ =>
      rewrite ?Znth_ct_canon by lia; cbn [ctv_of]; go_lower; apply prop_right;
      first [apply tc_val_tushort_repr | apply tc_val_tuchar_repr]; rep_lia
  | |- _ |-- !! _ => entailer!
  end.

Lemma body_build_tree : semax_body Vprog Gprog_build_tree f_build_tree build_tree_spec.
Proof.
  start_function.
  unfold td_at, tree_arr. Intros.
  unfold td_val; cbn [td_dyn_tree td_max_code td_stat_desc].
  destruct (sdesc_facts _ _ _ H) as [Helems Hnull].
  assert (Hel : 19 <= sd_elems sd <= 286) by (unfold L_CODES, D_CODES, BL_CODES in Helems; lia).
  apply c_build_tree_inv in H0.
  destruct H0 as (t1 & w1 & mc1 & t2 & w2 & mc2 & w3 & t4 & w4 & nd & top & heap6 & t7 & w7 & t8 &
                  Hinit & Hforce & Hheapify & Hmerge & Htop & Hheap6 & Hbitlen & Hcodes & ->).
  replace_SEP 3 (!! is_pointer_or_null (sd_stp gv sd) && trees_globals gv).
  { go_lower. rewrite ?sepcon_emp. apply (tg_stp' gv sd statp H). }
  Intros.
  replace_SEP 3 (!! (match sd_stree sd with Some _ => isptr (sd_stp gv sd)
                     | None => sd_stp gv sd = nullval end) && trees_globals gv).
  { go_lower. rewrite ?sepcon_emp. apply (tg_stp2 gv sd statp H). }
  Intros.
  match goal with Hx : match sd_stree sd with Some _ => _ | None => _ end |- _ => rename Hx into Hstp end.
  replace_SEP 3 (EX ep : val, @data_at DCS.CS Ers t_sd (sd_rep gv sd ep) statp *
                 (@data_at DCS.CS Ers t_sd (sd_rep gv sd ep) statp -* trees_globals gv)).
  { go_lower. rewrite ?sepcon_emp. apply tg_sdesc; auto. }
  Intros ep.
  unfold sd_rep.
  forward.
  forward.
  forward.
  forward.
  forward.
  forward.
  sep_apply (modus_ponens_wand (@data_at DCS.CS Ers t_sd (sd_rep gv sd ep) statp) (trees_globals gv)).
  unfold work_at. Intros.
  forward.
  forward.
  set (w0 := w_set_heap_max (w_set_heap_len w 0) HEAP_SIZE) in Hinit.
  assert (Hw0 : work_ok w0) by (apply work_ok_heap_max; [apply work_ok_heap_len; [auto|rep_lia] | unfold HEAP_SIZE; rep_lia]).
  forward_for_simple_bound (sd_elems sd)
    (EX i : Z, EX t' : tree, EX w' : work, EX mc' : Z,
      PROP (c_bt_init (Z.to_nat (sd_elems sd - i)) (sd_elems sd) t' w' mc' i = Some (t1, w1, mc1);
            tree_ok t' n; -1 <= mc' < i)
      LOCAL (temp _max_code (vi mc'); temp _elems (vi (sd_elems sd)); temp _stree (sd_stp gv sd);
             temp _tree tp; gvars gv; temp _s sp; temp _desc dp)
      SEP (trees_globals gv; @data_at DCS.CS Ews t_td (tp, (vi max_code, statp)) dp;
           @data_at DCS.CS Ews (tarray t_ct n) (ct_canon t') tp; work_at w' sp)).
  { Exists t w0 (-1). unfold work_at. rewrite Z.sub_0_r. entailer!. }
  { (* the body *)
    unfold work_at. Intros.
    rename H5 into Hrun. pose proof H6 as (Htl1 & Htl2 & Htr).
    assert (Ef : Z.to_nat (sd_elems sd - i) = S (Z.to_nat (sd_elems sd - (i + 1))))
      by (rewrite <- Z2Nat.inj_succ by lia; f_equal; lia).
    rewrite Ef in Hrun. cbn [c_bt_init] in Hrun.
    rewrite (proj2 (Z.ltb_lt i (sd_elems sd)) ltac:(lia)) in Hrun.
    inv_bind Hrun. apply rd_inv in Ha. destruct Ha as [Hi ->].
    pose proof (Htr i ltac:(lia)) as [Hfi Hdi].
    forward; try ct_side.
    rewrite Znth_ct_canon by lia. cbn [ctv_of].
    forward_if.
    - assert (Hnz : Znth i (fc t') <> 0) by (intro E; rewrite E in *; contradiction).
      rewrite (proj2 (Z.eqb_neq _ _) Hnz) in Hrun. cbn [negb] in Hrun.
      inv_bind Hrun. apply wr_inv in Ha. destruct Ha as [Hh ->].
      inv_bind Hrun. apply wr_inv in Ha. destruct Ha as [Hd ->].
      cbn [w_heap w_depth w_set_heap_len w_set_heap w_heap_len] in *.
      pose proof H8 as (Hw1 & Hw2 & Hw3 & Hw4 & Hw5 & Hw6 & Hw7 & Hw8 & Hw9 & Hw10).
      unfold L_CODES, MAX_BITS in Hw1, Hw2, Hw3.
      forward.
      forward.
      rewrite add_repr.
      forward.
      forward.
      forward.
      forward.
      forward.
      Exists t' (w_set_depth (w_set_heap (w_set_heap_len w' (w_heap_len w' + 1))
                   (upd_Znth (w_heap_len w' + 1) (w_heap w') i)) (upd_Znth i (w_depth w') 0)) i.
      assert (Hok' : work_ok (w_set_depth (w_set_heap (w_set_heap_len w' (w_heap_len w' + 1))
                   (upd_Znth (w_heap_len w' + 1) (w_heap w') i)) (upd_Znth i (w_depth w') 0)))
        by work_ok_tac.
      unfold work_at.
      cbn [w_heap w_depth w_set_heap_len w_set_heap w_set_depth w_heap_len w_heap_max w_bl_count w_opt_len
           w_static_len].
      rewrite <- !upd_Znth_map.
      change (Int.zero_ext 8 (Int.repr 0)) with (Int.repr 0).
      entailer!.
    - rewrite H5 in Hrun. cbn [Z.eqb negb] in Hrun.
      inv_bind Hrun. apply c_set_dl_inv in Ha. destruct Ha as [_ ->].
      forward.
      rewrite (data_at_ct_set_dl Ews n t' i 0) by (try right; unfold vi; rewrite ?zext16_repr; auto; lia).
      Exists (mkTree (fc t') (upd_Znth i (dl t') 0)) w' mc'.
      unfold work_at.
      entailer!.
      apply tree_ok_dl; auto; lia.
    }
  (* after the initial heap loop *)
  Intros t1' w1' mc1'.
  match goal with Hr : c_bt_init (Z.to_nat (sd_elems sd - sd_elems sd)) _ _ _ _ _ = _ |- _ =>
    rewrite Z.sub_diag in Hr; cbn [Z.to_nat c_bt_init] in Hr; rewrite Z.ltb_irrefl in Hr;
    inversion Hr; subst t1' w1' mc1'; clear Hr end.
  (* the force-two-codes loop *)
  forward_loop
   (EX f : nat, EX t' : tree, EX w' : work, EX mc' : Z,
     PROP (c_bt_force f sd t' w' mc' = Some (t2, w2, mc2); tree_ok t' n; -1 <= mc' <= 286)
     LOCAL (temp _max_code (vi mc'); temp _elems (vi (sd_elems sd)); temp _stree (sd_stp gv sd);
            temp _tree tp; gvars gv; temp _s sp; temp _desc dp)
     SEP (trees_globals gv; @data_at DCS.CS Ews t_td (tp, (vi max_code, statp)) dp;
          @data_at DCS.CS Ews (tarray t_ct n) (ct_canon t') tp; work_at w' sp))
   break:
    (PROP (2 <= w_heap_len w2; tree_ok t2 n; -1 <= mc2 <= 286)
     LOCAL (temp _max_code (vi mc2); temp _elems (vi (sd_elems sd)); temp _stree (sd_stp gv sd);
            temp _tree tp; gvars gv; temp _s sp; temp _desc dp)
     SEP (trees_globals gv; @data_at DCS.CS Ews t_td (tp, (vi max_code, statp)) dp;
          @data_at DCS.CS Ews (tarray t_ct n) (ct_canon t2) tp; work_at w2 sp)).
  { Exists 2%nat t1 w1 mc1. entailer!. }
  { Intros f t' w' mc'. unfold work_at. Intros.
    rename H4 into Hrun. pose proof H7 as (Htl1 & Htl2 & Htr).
    pose proof H9 as (Hw1 & Hw2 & Hw3 & Hw4 & Hw5 & Hw6 & Hw7 & Hw8 & Hw9 & Hw10).
    unfold L_CODES, MAX_BITS in Hw1, Hw2, Hw3.
    forward.
    forward_if.
    - destruct f as [|f].
      { cbn [c_bt_force] in Hrun. rewrite (proj2 (Z.ltb_lt (w_heap_len w') 2) ltac:(lia)) in Hrun. discriminate. }
      cbn [c_bt_force] in Hrun. rewrite (proj2 (Z.ltb_lt (w_heap_len w') 2) ltac:(lia)) in Hrun.
      forward.
      forward.
      rewrite add_repr.
      forward.
      destruct (mc' <? 2) eqn:Emc; apply semax_if_seq; forward_if.
      2: apply Z.ltb_lt in Emc; exfalso; lia.
      2: apply Z.ltb_ge in Emc; exfalso; lia.
      1: forward; forward; forward; rewrite add_repr.
      2: forward.
      all: forward.
      all: inv_bind Hrun; apply wr_inv in Ha; destruct Ha as [Hh ->].
      all: forward.
      all: forward.
      all: inv_bind Hrun; apply c_set_fc_inv in Ha; destruct Ha as [Hn ->].
      all: forward.
      all: match goal with |- context [upd_Znth ?k (ct_canon ?tt) (inl _, _)] =>
             rewrite (data_at_ct_set_fc Ews n tt k 1) by (try left; unfold vi; rewrite ?zext16_repr; auto; lia)
           end.
      all: inv_bind Hrun; apply wr_inv in Ha; destruct Ha as [Hd ->].
      all: forward.
      all: forward.
      all: forward.
      all: inv_bind Hrun.
      all: rewrite sub64_repr, Int.signed_repr by rep_lia.
      all: change (Int.zero_ext 8 (Int.repr 0)) with (Int.repr 0).
      all: match goal with Hr : c_bt_force _ _ ?tt ?ww ?mm = _ |- _ =>
        forward_if (PROP ()
          LOCAL (temp _max_code (vi mm); temp _elems (vi (sd_elems sd)); temp _stree (sd_stp gv sd);
                 temp _tree tp; gvars gv; temp _s sp; temp _desc dp)
          SEP (trees_globals gv; @data_at DCS.CS Ews t_td (tp, (vi max_code, statp)) dp;
               @data_at DCS.CS Ews (tarray t_ct n) (ct_canon tt) tp; work_at ww sp)) end.
      all: try (match goal with |- _ |-- denote_tc_test_eq _ _ =>
                  rewrite !sepcon_assoc; apply (tg_test_eq gv sd statp _ H) end).
      1: {
      destruct (sd_stree sd) as [l|] eqn:Est; [| simpl in H11; contradiction ].
      inv_bind Ha. apply rd_inv in Ha0. destruct Ha0 as [Hsl ->]. inversion Ha; subst x; clear Ha.
      replace_SEP 0 (EX st : tree, EX k : Z, !! (dl st = l /\ tree_ok st k) &&
        (@data_at DCS.CS Ers (tarray t_ct k) (ct_arr ffalse ftrue st) (sd_stp gv sd) *
         (@data_at DCS.CS Ers (tarray t_ct k) (ct_arr ffalse ftrue st) (sd_stp gv sd) -* trees_globals gv))).
      { go_lower. rewrite ?sepcon_emp. apply (tg_stree gv sd statp l H Est). }
      Intros st k.
      match goal with Hk : tree_ok st k |- _ => pose proof Hk as (Hk1 & Hk2 & Hk3) end. subst l.
      match goal with Hs : 0 <= ?nd < Zlength (dl st) |- _ => pose proof (Hk3 nd ltac:(lia)) as [Hsf Hsd] end.
      forward.
      forward.
      all: try (match goal with |- _ |-- !! _ => entailer! end).
      all: try (match goal with |- _ |-- local _ =>
        rewrite Znth_ct_arr by lia; cbn [ctv_of ffalse ftrue]; go_lower; apply prop_right;
        apply tc_val_tushort_repr; rep_lia end).
      rewrite Znth_ct_arr by lia. cbn [ctv_of ffalse ftrue].
      forward.
      rewrite Int.unsigned_repr by rep_lia. rewrite sub64_repr.
      sep_apply (modus_ponens_wand (@data_at DCS.CS Ers (tarray t_ct k) (ct_arr ffalse ftrue st) (sd_stp gv sd))
                   (trees_globals gv)).
      match goal with |- context [work_at ?ww sp] =>
        assert (Hok' : work_ok ww) by work_ok_tac end.
      unfold work_at.
      cbn [w_heap w_depth w_set_heap_len w_set_heap w_set_depth w_set_opt_len w_set_static_len w_heap_len
           w_heap_max w_bl_count w_opt_len w_static_len].
      rewrite <- !upd_Znth_map. unfold vl. rewrite !repr_u64.
      entailer!. }
      1: {
      destruct (sd_stree sd) as [l|] eqn:Est.
      { exfalso. unfold sd_stp in Hstp. rewrite Est in Hstp. rewrite H11 in Hstp. exact Hstp. }
      inversion Ha; subst x; clear Ha.
      forward.
      match goal with |- context [work_at ?ww sp] =>
        assert (Hok' : work_ok ww) by work_ok_tac end.
      unfold work_at.
      cbn [w_heap w_depth w_set_heap_len w_set_heap w_set_depth w_set_opt_len w_set_static_len w_heap_len
           w_heap_max w_bl_count w_opt_len w_static_len].
      rewrite <- !upd_Znth_map. unfold vl. rewrite !repr_u64.
      entailer!. }
      1: {
      match goal with Hr : c_bt_force ?ff _ ?tt ?ww ?mm = _ |- _ => Exists ff tt ww mm end.
      entailer!. apply tree_ok_fc; auto; lia. }
      1: {
      destruct (sd_stree sd) as [l|] eqn:Est; [| simpl in H11; contradiction ].
      inv_bind Ha. apply rd_inv in Ha0. destruct Ha0 as [Hsl ->]. inversion Ha; subst x; clear Ha.
      replace_SEP 0 (EX st : tree, EX k : Z, !! (dl st = l /\ tree_ok st k) &&
        (@data_at DCS.CS Ers (tarray t_ct k) (ct_arr ffalse ftrue st) (sd_stp gv sd) *
         (@data_at DCS.CS Ers (tarray t_ct k) (ct_arr ffalse ftrue st) (sd_stp gv sd) -* trees_globals gv))).
      { go_lower. rewrite ?sepcon_emp. apply (tg_stree gv sd statp l H Est). }
      Intros st k.
      match goal with Hk : tree_ok st k |- _ => pose proof Hk as (Hk1 & Hk2 & Hk3) end. subst l.
      match goal with Hs : 0 <= ?nd < Zlength (dl st) |- _ => pose proof (Hk3 nd ltac:(lia)) as [Hsf Hsd] end.
      forward.
      forward.
      all: try (match goal with |- _ |-- !! _ => entailer! end).
      all: try (match goal with |- _ |-- local _ =>
        rewrite Znth_ct_arr by lia; cbn [ctv_of ffalse ftrue]; go_lower; apply prop_right;
        apply tc_val_tushort_repr; rep_lia end).
      rewrite Znth_ct_arr by lia. cbn [ctv_of ffalse ftrue].
      forward.
      rewrite Int.unsigned_repr by rep_lia. rewrite sub64_repr.
      sep_apply (modus_ponens_wand (@data_at DCS.CS Ers (tarray t_ct k) (ct_arr ffalse ftrue st) (sd_stp gv sd))
                   (trees_globals gv)).
      match goal with |- context [work_at ?ww sp] =>
        assert (Hok' : work_ok ww) by work_ok_tac end.
      unfold work_at.
      cbn [w_heap w_depth w_set_heap_len w_set_heap w_set_depth w_set_opt_len w_set_static_len w_heap_len
           w_heap_max w_bl_count w_opt_len w_static_len].
      rewrite <- !upd_Znth_map. unfold vl. rewrite !repr_u64.
      entailer!. }
      1: {
      destruct (sd_stree sd) as [l|] eqn:Est.
      { exfalso. unfold sd_stp in Hstp. rewrite Est in Hstp. rewrite H11 in Hstp. exact Hstp. }
      inversion Ha; subst x; clear Ha.
      forward.
      match goal with |- context [work_at ?ww sp] =>
        assert (Hok' : work_ok ww) by work_ok_tac end.
      unfold work_at.
      cbn [w_heap w_depth w_set_heap_len w_set_heap w_set_depth w_set_opt_len w_set_static_len w_heap_len
           w_heap_max w_bl_count w_opt_len w_static_len].
      rewrite <- !upd_Znth_map. unfold vl. rewrite !repr_u64.
      entailer!. }
      1: {
      match goal with Hr : c_bt_force ?ff _ ?tt ?ww ?mm = _ |- _ => Exists ff tt ww mm end.
      entailer!. apply tree_ok_fc; auto; lia. }
    - assert (E : (t', w', mc') = (t2, w2, mc2))
        by (destruct f; cbn [c_bt_force] in Hrun; rewrite (proj2 (Z.ltb_ge (w_heap_len w') 2) ltac:(lia)) in Hrun; congruence).
      inversion E; subst t' w' mc'.
      forward.
      unfold work_at. entailer!. }
  (* desc->max_code = max_code; the heapify loop *)
  forward.
  unfold work_at. Intros.
  forward.
  forward.
  { entailer!. match goal with Hx : _ /\ Int.repr 2 = Int.mone |- _ => destruct Hx as [_ Hm] end.
    apply (f_equal Int.unsigned) in Hm. vm_compute in Hm. discriminate. }
  match goal with Hx : work_ok w2 |- _ => rename Hx into Hw2ok end.
  pose proof Hw2ok as (Hw1 & Hw2 & Hw3 & Hw4 & Hw5 & Hw6 & Hw7 & Hw8 & Hw9 & Hw10).
  rewrite divs2_repr by rep_lia.
  forward_loop
   (EX k : Z, EX w' : work,
     PROP (c_bt_heapify (Z.to_nat k) t2 w' k = Some w3; 0 <= k <= Int.max_signed)
     LOCAL (temp _n (vi k); temp _max_code (vi mc2); temp _elems (vi (sd_elems sd));
            temp _stree (sd_stp gv sd); temp _tree tp; gvars gv; temp _s sp; temp _desc dp)
     SEP (trees_globals gv; @data_at DCS.CS Ews t_td (tp, (vi mc2, statp)) dp;
          tree_arr Ews n t2 tp; work_at w' sp))
   continue:
   (EX k : Z, EX w' : work,
     PROP (c_bt_heapify (Z.to_nat (k - 1)) t2 w' (k - 1) = Some w3; 1 <= k <= Int.max_signed)
     LOCAL (temp _n (vi k); temp _max_code (vi mc2); temp _elems (vi (sd_elems sd));
            temp _stree (sd_stp gv sd); temp _tree tp; gvars gv; temp _s sp; temp _desc dp)
     SEP (trees_globals gv; @data_at DCS.CS Ews t_td (tp, (vi mc2, statp)) dp;
          tree_arr Ews n t2 tp; work_at w' sp))
   break:
   (PROP ()
     LOCAL (temp _max_code (vi mc2); temp _elems (vi (sd_elems sd));
            temp _stree (sd_stp gv sd); temp _tree tp; gvars gv; temp _s sp; temp _desc dp)
     SEP (trees_globals gv; @data_at DCS.CS Ews t_td (tp, (vi mc2, statp)) dp;
          tree_arr Ews n t2 tp; work_at w3 sp)).
  { Exists (w_heap_len w2 / 2) w2. unfold work_at, tree_arr. entailer!.
    split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; rep_lia]. }
  { Intros k w'.
    forward_if.
    - assert (Ef : Z.to_nat k = S (Z.to_nat (k - 1))) by (rewrite <- Z2Nat.inj_succ by lia; f_equal; lia).
      match goal with Hr : c_bt_heapify (Z.to_nat k) _ _ _ = _ |- _ => rename Hr into Hrun end.
      rewrite Ef in Hrun. cbn [c_bt_heapify] in Hrun.
      rewrite (proj2 (Z.geb_le k 1) ltac:(lia)) in Hrun.
      inv_bind Hrun.
      forward_call (sp, tp, Ews, n, t2, w', k, x).
      Exists k x. entailer!.
    - assert (k = 0) by lia. subst k.
      match goal with Hr : c_bt_heapify (Z.to_nat 0) _ _ _ = _ |- _ =>
        cbn in Hr; inversion Hr; subst w' end.
      forward.
      entailer!. }
  { Intros k w'. forward. Exists (k - 1) w'. entailer!. }
  (* the merge loop *)
  clear Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10.
  forward.
  assert (Hb3 : 0 <= w_heap_len w3 <= 572).
  { assert (Hl0 : Zlength (w_heap w0) = 573)
      by (destruct H3 as (Hx & _); cbn; rewrite Hx; reflexivity).
    destruct (c_bt_init_hl _ _ _ _ _ _ _ Hinit Hl0 ltac:(cbn; lia)) as [Hl1 Hh1]. cbn [fst snd] in Hl1, Hh1.
    destruct (c_bt_force_hl _ _ _ _ _ _ Hforce Hl1 Hh1) as [_ Hh2]. cbn [fst snd] in Hh2.
    rewrite (c_bt_heapify_hl _ _ _ _ _ Hheapify). exact Hh2. }
  forward_loop
   (EX f : nat, EX t' : tree, EX w' : work, EX nd' : Z,
     PROP (c_bt_merge f t' w' nd' = Some (t4, w4, nd); tree_ok t' n;
           sd_elems sd <= nd'; nd' + w_heap_len w' <= sd_elems sd + 572)
     LOCAL (temp _node (vi nd'); temp _max_code (vi mc2); temp _elems (vi (sd_elems sd));
            temp _stree (sd_stp gv sd); temp _tree tp; gvars gv; temp _s sp; temp _desc dp)
     SEP (trees_globals gv; @data_at DCS.CS Ews t_td (tp, (vi mc2, statp)) dp;
          tree_arr Ews n t' tp; work_at w' sp))
   continue:
   (EX f : nat, EX t' : tree, EX w' : work, EX nd' : Z,
     PROP ((if w_heap_len w' >=? 2 then c_bt_merge f t' w' nd' else Some (t', w', nd')) = Some (t4, w4, nd);
           tree_ok t' n; sd_elems sd <= nd'; nd' + w_heap_len w' <= sd_elems sd + 572)
     LOCAL (temp _node (vi nd'); temp _max_code (vi mc2); temp _elems (vi (sd_elems sd));
            temp _stree (sd_stp gv sd); temp _tree tp; gvars gv; temp _s sp; temp _desc dp)
     SEP (trees_globals gv; @data_at DCS.CS Ews t_td (tp, (vi mc2, statp)) dp;
          tree_arr Ews n t' tp; work_at w' sp))
   break:
   (PROP ()
     LOCAL (temp _max_code (vi mc2); temp _elems (vi (sd_elems sd));
            temp _stree (sd_stp gv sd); temp _tree tp; gvars gv; temp _s sp; temp _desc dp)
     SEP (trees_globals gv; @data_at DCS.CS Ews t_td (tp, (vi mc2, statp)) dp;
          tree_arr Ews n t4 tp; work_at w4 sp)).
  { Exists (Z.to_nat (w_heap_len w3)) t2 w3 (sd_elems sd). entailer!. }
  { (* the merge body *)
    Intros f t' w' nd'. unfold tree_arr, work_at. Intros.
    match goal with Hr : c_bt_merge f t' w' nd' = _ |- _ => rename Hr into Hrun end.
    match goal with Hx : work_ok w' |- _ => rename Hx into Hwok end.
    match goal with Hx : tree_ok t' n |- _ => rename Hx into Htok end.
    pose proof Hwok as (Hw1 & Hw2 & Hw3 & Hw4 & Hw5 & Hw6 & Hw7 & Hw8 & Hw9 & Hw10).
    unfold L_CODES, MAX_BITS in Hw1, Hw2, Hw3.
    pose proof Htok as (Htl1 & Htl2 & Htr).
    destruct f as [|f]; [discriminate Hrun|].
    cbn [c_bt_merge] in Hrun. inv_bind Hrun. destruct x as [t5 w5]. rename Ha into Hbody.
    unfold c_merge_body in Hbody.
    inv_bind Hbody. destruct x as [nn wA]. rename Ha into Hpq.
    unfold c_pqremove in Hpq.
    inv_bind Hpq. apply rd_inv in Ha. destruct Ha as [H1r ->].
    inv_bind Hpq. apply rd_inv in Ha. destruct Ha as [Hhl ->].
    inv_bind Hpq. apply wr_inv in Ha. destruct Ha as [_ ->].
    inv_bind Hpq. rename Ha into Hpq1. inversion Hpq; subst nn wA; clear Hpq.
    forward.
    forward.
    forward.
    forward.
    forward.
    change SMALLEST with 1 in *.
    rewrite sub_repr32.
    assert (Hlast : Int.min_signed <= Znth (w_heap_len w') (w_heap w') <= Int.max_signed)
      by (rewrite Forall_forall in Hw4; apply Hw4; apply Znth_In; lia).
    assert (Hn0 : Int.min_signed <= Znth 1 (w_heap w') <= Int.max_signed)
      by (rewrite Forall_forall in Hw4; apply Hw4; apply Znth_In; lia).
    set (W := w_set_heap_len (w_set_heap w' (upd_Znth 1 (w_heap w') (Znth (w_heap_len w') (w_heap w'))))
                (w_heap_len w' - 1)) in Hpq1.
    assert (HW : work_ok W) by (subst W; work_ok_tac).
    gather_SEP 3 4 5 6 7 8 9.
    replace_SEP 0 (work_at W sp).
    { unfold work_at, W.
      cbn [w_heap w_depth w_set_heap_len w_set_heap w_heap_len w_heap_max w_bl_count w_opt_len w_static_len].
      rewrite <- upd_Znth_map. entailer!. }
    replace_SEP 3 (tree_arr Ews n t' tp).
    { unfold tree_arr. entailer!. }
    forward_call (sp, tp, Ews, n, t', W, 1, x).
    pose proof (c_pqdownheap_hl _ _ _ _ Hpq1) as [Hxl Hxm]. subst W. cbn in Hxl, Hxm.
    unfold tree_arr, work_at. Intros.
    match goal with Hx : work_ok x |- _ => rename Hx into Hxok end.
    pose proof Hxok as (Hx1 & Hx2 & Hx3 & Hx4 & Hx5 & Hx6 & Hx7 & Hx8 & Hx9 & Hx10).
    unfold L_CODES, MAX_BITS in Hx1, Hx2, Hx3.
    set (n0 := Znth 1 (w_heap w')) in *.
    (* m = s->heap[SMALLEST] *)
    inv_bind Hbody. apply rd_inv in Ha. destruct Ha as [_ Hm]. rename x0 into m.
    forward.
    rewrite <- Hm.
    assert (Hmr : Int.min_signed <= m <= Int.max_signed)
      by (rewrite Hm; rewrite Forall_forall in Hx4; apply Hx4; apply Znth_In; lia).
    (* s->heap[--(s->heap_max)] = n; s->heap[--(s->heap_max)] = m; *)
    inv_bind Hbody. unfold c_store_removed in Ha. inv_bind Ha. apply wr_inv in Ha0. destruct Ha0 as [Hs1 ->].
    inversion Ha; subst x0; clear Ha.
    forward. forward. forward. forward.
    inv_bind Hbody. unfold c_store_removed in Ha. inv_bind Ha. apply wr_inv in Ha0. destruct Ha0 as [Hs2 ->].
    inversion Ha; subst x0; clear Ha.
    cbn [w_heap w_heap_max w_set_heap w_set_heap_max] in Hs1, Hs2, Hbody.
    forward. forward. forward. forward.
    rewrite !sub_repr32.
    (* the new node *)
    inv_bind Hbody. destruct x0 as [t3 w6]. unfold c_new_node in Ha.
    inv_bind Ha. apply rd_inv in Ha0. destruct Ha0 as [Hn0r ->].
    inv_bind Ha. apply rd_inv in Ha0. destruct Ha0 as [Hmr2 ->].
    inv_bind Ha. apply c_set_fc_inv in Ha0. destruct Ha0 as [Hnd ->].
    inv_bind Ha. apply rd_inv in Ha0. destruct Ha0 as [Hdn ->].
    inv_bind Ha. apply rd_inv in Ha0. destruct Ha0 as [Hdm ->].
    inv_bind Ha. apply wr_inv in Ha0. destruct Ha0 as [Hdnd ->].
    inv_bind Ha. apply c_set_dl_inv in Ha0. destruct Ha0 as [_ ->].
    inv_bind Ha. apply c_set_dl_inv in Ha0. destruct Ha0 as [_ ->].
    inversion Ha; subst t3 w6; clear Ha.
    cbn [w_depth w_heap w_set_heap w_set_heap_max fc dl] in Hdn, Hdm, Hdnd, Hbody, Hmr2, Hn0r, Hnd.
    pose proof (Htr n0 ltac:(lia)) as [Hfn _].
    pose proof (Htr m ltac:(lia)) as [Hfm _].
    forward; try ct_side.
    forward; try ct_side.
    rewrite !Znth_ct_canon by lia. cbn [ctv_of].
    forward.
    rewrite add_repr.
    rewrite (data_at_ct_set_fc Ews n t' nd' (u16 (Znth n0 (fc t') + Znth m (fc t'))))
      by (try left; unfold vi, u16; rewrite ?zext16_repr; auto; lia).
    assert (Hdn' : 0 <= Znth n0 (w_depth x) < 256)
      by (rewrite Forall_forall in Hx7; apply Hx7; apply Znth_In; lia).
    assert (Hdm' : 0 <= Znth m (w_depth x) < 256)
      by (rewrite Forall_forall in Hx7; apply Hx7; apply Znth_In; lia).
    fwd. fwd.
    destruct (Znth n0 (w_depth x) >=? Znth m (w_depth x)) eqn:Ed; apply semax_if_seq; forward_if.
    2: apply Z.geb_le in Ed; exfalso; lia.
    2: rewrite Z.geb_leb in Ed; apply Z.leb_gt in Ed; exfalso; lia.
    1, 2: fwd; forward.
    all: forward.
    all: rewrite add_repr, zext8_repr.
    all: forward.
    all: rewrite ?zext8_repr, ?Zmod_mod.
    all: forward.
    all: match goal with |- context [upd_Znth ?k (ct_canon ?tt) (fst _, inl _)] =>
           rewrite (data_at_ct_set_dl Ews n tt k (u16 nd'))
             by first [left; unfold vi, u16; rewrite ?zext16_repr, ?Zmod_mod; reflexivity
                      | cbn [fc dl]; rewrite ?Zlength_upd_Znth; lia]
         end.
    all: forward.
    all: match goal with |- context [upd_Znth ?k (ct_canon ?tt) (fst _, inl _)] =>
           rewrite (data_at_ct_set_dl Ews n tt k (u16 nd'))
             by first [left; unfold vi, u16; rewrite ?zext16_repr, ?Zmod_mod; reflexivity
                      | cbn [fc dl]; rewrite ?Zlength_upd_Znth; lia]
         end.
    all: forward.
    all: forward.
    all: forward.
    all: inv_bind Hbody; apply wr_inv in Ha; destruct Ha as [_ ->].
    all: inv_bind Hbody; rename Ha into Hpq2; injection Hbody as <- <-.
    all: match goal with Hp : c_pqdownheap ?tt ?ww 1 = Some ?rr |- _ =>
           set (TT := tt) in *; set (WW := ww) in *; set (RR := rr) in * end.
    all: assert (Hww : work_ok WW) by (unfold WW; work_ok_tac).
    all: pose proof (c_pqdownheap_hl _ _ _ _ Hpq2) as [Hrl _].
    all: gather_SEP 1 2 3 4 5 6 7.
    all: replace_SEP 0 (work_at WW sp).
    1, 3: unfold work_at, WW;
          cbn [w_heap w_depth w_set_heap_len w_set_heap w_set_depth w_set_heap_max w_heap_len w_heap_max
               w_bl_count w_opt_len w_static_len];
          rewrite <- !upd_Znth_map; entailer!.
    all: assert (Htt : tree_ok TT n)
           by (unfold TT;
               apply (tree_ok_dl (mkTree (upd_Znth nd' (fc t') (u16 (Znth n0 (fc t') + Znth m (fc t'))))
                                         (upd_Znth m (dl t') (u16 nd'))) n n0 (u16 nd'));
               [apply (tree_ok_dl (mkTree (upd_Znth nd' (fc t') (u16 (Znth n0 (fc t') + Znth m (fc t'))))
                                         (dl t')) n m (u16 nd'));
                [apply (tree_ok_fc t' n nd'); [auto|]|]|];
               unfold u16; apply Z.mod_pos_bound; lia).
    all: replace_SEP 1 (tree_arr Ews n TT tp).
    1, 3: unfold tree_arr; entailer!.
    all: forward_call (sp, tp, Ews, n, TT, WW, 1, RR).
    all: Exists f TT RR (nd' + 1).
    all: unfold WW in Hrl; cbn [w_heap_len w_set_heap w_set_depth w_set_heap_max] in Hrl.
    all: entailer!. }
  { Intros f t' w' nd'. unfold work_at. Intros.
    match goal with Hx : work_ok w' |- _ => pose proof Hx as (_ & _ & _ & _ & Hhl & _) end.
    forward.
    forward_if.
    - try rewrite Int.signed_repr in * by rep_lia.
      rewrite (proj2 (Z.geb_le (w_heap_len w') 2) ltac:(lia)) in *.
      forward.
      Exists f t' w' nd'. unfold work_at. entailer!.
    - try rewrite Int.signed_repr in * by rep_lia.
      match goal with Hr : (if w_heap_len w' >=? 2 then _ else _) = _ |- _ =>
        rewrite Z.geb_leb, (proj2 (Z.leb_gt 2 (w_heap_len w')) ltac:(lia)) in Hr; inversion Hr; subst t' w' nd' end.
      forward.
      unfold work_at. entailer!. }
  (* heap[--(heap_max)] = heap[SMALLEST]; gen_bitlen; gen_codes *)
  unfold work_at. Intros.
  match goal with Hx : work_ok w4 |- _ => rename Hx into Hw4ok end.
  pose proof Hw4ok as (Hw1 & Hw2 & Hw3 & Hw4 & Hw5 & Hw6 & Hw7 & Hw8 & Hw9 & Hw10).
  unfold L_CODES, MAX_BITS in Hw1, Hw2, Hw3.
  change SMALLEST with 1 in Htop.
  apply rd_inv in Htop. destruct Htop as [_ ->].
  apply wr_inv in Hheap6. destruct Hheap6 as [Hh6 ->].
  assert (Htop : Int.min_signed <= Znth 1 (w_heap w4) <= Int.max_signed)
    by (rewrite Forall_forall in Hw4; apply Hw4; apply Znth_In; lia).
  forward.
  forward.
  forward.
  forward.
  forward.
  rewrite sub_repr32.
  set (W6 := w_set_heap (w_set_heap_max w4 (w_heap_max w4 - 1))
               (upd_Znth (w_heap_max w4 - 1) (w_heap w4) (Znth 1 (w_heap w4)))) in Hbitlen.
  assert (HW6 : work_ok W6) by (unfold W6; work_ok_tac).
  gather_SEP 3 4 5 6 7 8 9.
  replace_SEP 0 (work_at W6 sp).
  { unfold work_at, W6.
    cbn [w_heap w_depth w_set_heap w_set_heap_max w_heap_len w_heap_max w_bl_count w_opt_len w_static_len].
    rewrite <- !upd_Znth_map. entailer!. }
  replace_SEP 2 (td_at Ews tp mc2 statp dp).
  { unfold td_at, td_val. cbn [td_dyn_tree td_max_code td_stat_desc]. entailer!. }
  forward_call (sp, dp, tp, n, t4, mc2, statp, sd, W6, (t7, w7), gv).
  cbn [fst snd].
  unfold work_at. Intros.
  match goal with Hx : work_ok w7 |- _ => rename Hx into Hw7ok end.
  pose proof Hw7ok as (Hv1 & Hv2 & Hv3 & Hv4 & Hv5 & Hv6 & Hv7 & Hv8 & Hv9 & Hv10).
  assert_PROP (field_compatible t_ds (DOT _bl_count) sp) as Hfcb by entailer!.
  rewrite (field_at_data_at Ews t_ds (DOT _bl_count) _ sp).
  change (nested_field_type t_ds (DOT _bl_count)) with (tarray tushort 16).
  forward_call (tp, n, t7, mc2, field_address t_ds (DOT _bl_count) sp, w_bl_count w7, t8).
  unfold work_at. cbn [fst snd].
  rewrite (field_at_data_at Ews t_ds (DOT _bl_count) _ sp).
  change (nested_field_type t_ds (DOT _bl_count)) with (tarray tushort 16).
  entailer!.
Qed.
