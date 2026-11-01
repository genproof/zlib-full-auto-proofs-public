(** * The body of trees.c's send_tree against its shared specification (TSpec.send_tree_spec).

    The inlined send_bits / send_code macro blocks: [SendKit.sb_block] (see SendKit.v's header). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.trees.TSpec.
Require Import Zlib.proof.trees.SendKit2.
Require Import Zlib.trees.code.
Require Import Zlib.proof.trees.SendTreeKit.
Require Import Zlib.proof.trees.SendTreeDW.
Require Import Zlib.proof.trees.SendTreeRep.
Require Import Zlib.proof.trees.SendTreeZ.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

Lemma st_loop_done f t mc blc bll om i pl nl cnt xc nc r :
  mc < i -> c_send_tree_loop f t mc blc bll om i pl nl cnt xc nc = Some r -> r = om.
Proof.
  intros Hi. destruct f; cbn [c_send_tree_loop]; rewrite (proj2 (Z.leb_gt _ _) Hi); congruence.
Qed.

(** The invariant of the main loop: the model loop from the C state gives [r]. *)
Definition st_inv (t : tree) (max_code : Z) (bl : tree) (r : cout) (sp pbp tp : val) (tsh : share) (n : Z)
    (ni i : Z) : environ -> mpred :=
  EX f : nat, EX om : cout, EX pl : Z, EX nl : Z, EX cnt : Z, EX xc : Z, EX nc : Z,
  PROPx [c_send_tree_loop f t max_code (fc bl) (dl bl) om i pl nl cnt xc nc = Some r;
         0 <= i <= Int.max_signed; -1 <= pl < 65536; 0 <= nl < 65536; 0 <= cnt < xc; xc <= 138; 3 <= nc <= 4]
  (LOCALx [temp _n (vi ni); temp _prevlen (vi pl); temp _nextlen (vi nl); temp _count (vi cnt);
           temp _max_count (vi xc); temp _min_count (vi nc); temp _s sp; temp _tree tp;
           temp _max_code (vi max_code)]
  (SEPx (st_sep om sp pbp tsh n t tp bl))).

(** The function's type context with any specs (start_function's [Delta] has an opaque [Delta_specs]). *)
Definition Delta_ds (DS : Maps.PTree.t funspec) : tycontext :=
  mk_tycontext (temp_types Delta_st) (var_types Delta_st) (ret_type Delta_st) (glob_types Delta_st) DS
    (annotations Delta_st).

Lemma st_delta_sub DS : tycontext_sub Delta_st (Delta_ds DS).
Proof.
  unfold Delta_ds. split; [|split; [|split; [|split; [|split]]]];
    cbn [temp_types var_types ret_type glob_types glob_specs annotations]; try intros id.
  - destruct (Maps.PTree.get id (temp_types Delta_st)); auto.
  - reflexivity.
  - reflexivity.
  - destruct (Maps.PTree.get id (glob_types Delta_st)); cbn; auto.
  - replace (Maps.PTree.get id (glob_specs Delta_st)) with (@None funspec); [exact I|].
    unfold Delta_st, func_tycontext, make_tycontext, Gprog_send_tree. cbn [glob_specs make_tycontext_s].
    rewrite Maps.PTree.gempty. reflexivity.
  - apply Annotation_sub_refl.
Qed.

(** Use a branch lemma (stated for [Delta_st]) at a [forward_if] branch goal. *)
Ltac st_use L :=
  first [eapply st_apply | eapply semax_pre];
  [| lazymatch goal with DS : Maps.PTree.t funspec |- semax ?D _ _ _ => change D with (Delta_ds DS) end;
     eapply semax_Delta_subsumption; [apply st_delta_sub | exact L]].

Lemma body_send_tree : semax_body Vprog Gprog_send_tree f_send_tree send_tree_spec.
Proof.
  start_function.
  rename H into Hmc, H0 into H.
  unfold c_send_tree in H. inv_bind H. destruct x. apply guard_inv, Z.ltb_lt in Ha. rename Ha into Hmx.
  inv_bind H. rename x into nl0. apply rd_inv in Ha. destruct Ha as [Hz0 ->].
  destruct (if Znth 0 (dl t) =? 0 then (138, 3) else (7, 4)) as [mc0 mn0] eqn:Emm in H.
  rename H into Hloop.
  rewrite tree_arr_len, bltree_codes. Intros. rename H into Ht, H0 into Hbl.
  pose proof Ht as (Htf & Htd & Htr).
  forward. forward.
  { rewrite Znth_ct_arr by lia. cbn [ctv_of ftrue]. go_lower. apply prop_right. apply tc_val_tushort_repr.
    specialize (Htr 0). lia. }
  rewrite Znth_ct_arr by lia. cbn [ctv_of ftrue].
  pose proof (Htr 0 ltac:(lia)) as Hr0.
  forward. forward. forward.
  forward_if (PROP ()
    LOCAL (temp _max_count (vi mc0); temp _min_count (vi mn0); temp _count (vi 0);
           temp _nextlen (vi (Znth 0 (dl t))); temp _prevlen (vi (-1));
           temp _s sp; temp _tree tp; temp _max_code (vi max_code))
    SEP (out_at o m sp pbp; @data_at DCS.CS tsh (tarray t_ct n) (ct_arr ffalse ftrue t) tp;
         @field_at DCS.CS Ews t_ds (DOT _bl_tree) (ct_arr ftrue ftrue bl) sp)).
  { forward. forward.
    assert (Znth 0 (dl t) = 0) as E0 by (first [exact H | apply repr_inj_unsigned in H; rep_lia]).
    rewrite E0 in Emm. injection Emm as <- <-. entailer!. }
  { forward.
    assert (Znth 0 (dl t) <> 0) as E0 by (first [exact H | intro E; rewrite E in H; contradiction]).
    rewrite (proj2 (Z.eqb_neq _ _) E0) in Emm. injection Emm as <- <-. entailer!. }
  forward_loop (EX i : Z, st_inv t max_code bl r sp pbp tp tsh n i i)
    continue: (EX i : Z, st_inv t max_code bl r sp pbp tp tsh n i (i + 1))
    break: (PROPx [] (LOCALx [] (SEPx (st_sep r sp pbp tsh n t tp bl)))).
  - assert (Hm0 : (mc0 = 138 /\ mn0 = 3) \/ (mc0 = 7 /\ mn0 = 4))
      by (destruct (_ =? 0); inversion Emm; auto).
    forward. Exists 0. unfold st_inv. Exists (Z.to_nat (max_code + 1)) (o, m) (-1) (Znth 0 (dl t)) 0 mc0 mn0.
    unfold st_sep. cbn [fst snd]. entailer!.
  - Intros i. unfold st_inv. Intros f om pl nl cnt xc nc. unfold st_sep.
    forward_if.
    2:{ forward. apply st_loop_done in H; [subst om|lia]. unfold st_sep. entailer!. }
    rename H into Hl.
    destruct f as [|f]; [cbn in Hl; rewrite (proj2 (Z.leb_le i max_code)) in Hl by lia; discriminate|].
    cbn [c_send_tree_loop] in Hl. rewrite (proj2 (Z.leb_le i max_code)) in Hl by lia.
    inv_bind Hl. rename x into nl', Ha into Hrd. apply rd_inv in Hrd. destruct Hrd as [Hi1 ->].
    pose proof (Htr (i + 1) ltac:(lia)) as Hri.
    forward. forward.
    { rewrite Znth_ct_arr by lia. cbn [ctv_of ftrue]. go_lower. apply prop_right. apply tc_val_tushort_repr.
      lia. }
    rewrite Znth_ct_arr by lia. cbn [ctv_of ftrue].
    set (nl' := Znth (i + 1) (dl t)) in *.
    forward. forward.
    forward_if (PROP ()
      LOCAL (temp _t'19 (Vint (if andb (cnt + 1 <? xc) (nl =? nl') then Int.one else Int.zero));
             temp _count (vi (cnt + 1)); temp _curlen (vi nl); temp _nextlen (vi nl'); temp _n (vi i);
             temp _prevlen (vi pl); temp _max_count (vi xc); temp _min_count (vi nc);
             temp _s sp; temp _tree tp; temp _max_code (vi max_code))
      SEP (out_at (fst om) (snd om) sp pbp; @data_at DCS.CS tsh (tarray t_ct n) (ct_arr ffalse ftrue t) tp;
           @field_at DCS.CS Ews t_ds (DOT _bl_tree) (ct_arr ftrue ftrue bl) sp)).
    { forward. entailer!.
      rewrite (proj2 (Z.ltb_lt (cnt + 1) xc) ltac:(lia)). cbn [andb].
      destruct (zeq nl nl') as [e|e];
        [rewrite (proj2 (Z.eqb_eq _ _) e) | rewrite (proj2 (Z.eqb_neq _ _) e)]; reflexivity. }
    { forward. entailer!. rewrite (proj2 (Z.ltb_ge (cnt + 1) xc) ltac:(lia)). reflexivity. }
    destruct (andb (cnt + 1 <? xc) (nl =? nl')) eqn:Eb.
    { forward_if (PROP (False) LOCAL () SEP ()).
      - forward. Exists i. unfold st_inv. Exists f om pl nl' (cnt + 1) xc nc.
        apply andb_prop in Eb. destruct Eb as [Eb1 Eb2]. apply Z.ltb_lt in Eb1.
        unfold st_sep. entailer!.
      - exfalso. apply Int.one_not_zero. assumption. }
    inv_bind Hl. rename x into om1, Ha into Hbr.
    destruct (if nl' =? 0 then (138, 3) else if nl =? nl' then (6, 3) else (7, 4)) as [xc' nc'] eqn:Emc in Hl.
    forward_if (PROPx [] (LOCALx (st_locals i pl nl nl' xc nc sp tp max_code)
                           (SEPx (st_sep om1 sp pbp tsh n t tp bl)))).
    { contradiction. }
    { forward_if (PROPx [] (LOCALx (st_locals i pl nl nl' xc nc sp tp max_code)
                             (SEPx (st_sep om1 sp pbp tsh n t tp bl)))).
      - rewrite (proj2 (Z.ltb_lt (cnt + 1) nc) ltac:(lia)) in Hbr.
        st_use (st_dw_ok Espec (cnt + 1) i pl nl nl' xc nc sp tp max_code om om1 pbp tsh n t bl
                      SH Hbl ltac:(lia) Hbr).
        unfold st_pre, st_locals, st_sep. entailer!.
      - rewrite (proj2 (Z.ltb_ge (cnt + 1) nc) ltac:(lia)) in Hbr.
        forward_if (PROPx [] (LOCALx (st_locals i pl nl nl' xc nc sp tp max_code)
                               (SEPx (st_sep om1 sp pbp tsh n t tp bl)))).
        + assert (nl <> 0) as E0 by (first [assumption | intro E; subst; contradiction]).
          rewrite (proj2 (Z.eqb_neq nl 0) E0) in Hbr. cbn [negb] in Hbr.
          try (unfold MORE_COMMANDS); try (unfold POSTCONDITION); try (unfold abbreviate).
          st_use (st_rep_ok Espec (cnt + 1) i pl nl nl' xc nc sp tp max_code om om1 pbp tsh n t bl
                        SH Hbl ltac:(lia) H1 H2 Hbr).
          unfold st_pre, st_locals, st_sep. entailer!.
        + assert (nl = 0) as E0 by (first [assumption | apply repr_inj_unsigned; [rep_lia | rep_lia | assumption]]).
          rewrite E0, Z.eqb_refl in Hbr. cbn [negb] in Hbr.
          forward_if (PROPx [] (LOCALx (st_locals i pl nl nl' xc nc sp tp max_code)
                                 (SEPx (st_sep om1 sp pbp tsh n t tp bl)))).
          * rewrite (proj2 (Z.leb_le (cnt + 1) 10) ltac:(lia)) in Hbr.
            try (unfold MORE_COMMANDS); try (unfold POSTCONDITION); try (unfold abbreviate).
          st_use (st_z10_ok Espec (cnt + 1) i pl nl nl' xc nc sp tp max_code om om1 pbp tsh n t bl
                          SH Hbl ltac:(lia) Hbr).
            unfold st_pre, st_locals, st_sep. entailer!.
          * rewrite (proj2 (Z.leb_gt (cnt + 1) 10) ltac:(lia)) in Hbr.
            try (unfold MORE_COMMANDS); try (unfold POSTCONDITION); try (unfold abbreviate).
          st_use (st_z138_ok Espec (cnt + 1) i pl nl nl' xc nc sp tp max_code om om1 pbp tsh n t bl
                          SH Hbl ltac:(lia) Hbr).
            unfold st_pre, st_locals, st_sep. entailer!.
      }
    unfold st_locals, st_sep.
    forward. forward.
    forward_if.
    { assert (nl' = 0) as E0 by (first [assumption | apply repr_inj_unsigned in H; rep_lia]).
      rewrite E0, Z.eqb_refl in Emc. injection Emc as <- <-.
      forward. forward. Exists i. unfold st_inv. Exists f om1 nl nl' 0 138 3.
      unfold st_sep. entailer!. }
    assert (nl' <> 0) as E0 by (first [assumption | intro E; rewrite E in H; contradiction]).
    rewrite (proj2 (Z.eqb_neq nl' 0) E0) in Emc.
    forward_if.
    { rewrite (proj2 (Z.eqb_eq nl nl') ltac:(auto)) in Emc. injection Emc as <- <-.
      forward. forward. Exists i. unfold st_inv. Exists f om1 nl nl' 0 6 3.
      unfold st_sep. entailer!. }
    { rewrite (proj2 (Z.eqb_neq nl nl') ltac:(auto)) in Emc. injection Emc as <- <-.
      forward. forward. Exists i. unfold st_inv. Exists f om1 nl nl' 0 7 4.
      unfold st_sep. entailer!. }
  - Intros i. unfold st_inv. Intros f om pl nl cnt xc nc.
    forward. Exists (i + 1). unfold st_inv. Exists f om pl nl cnt xc nc.
    entailer!.
  - unfold st_sep. unfold POSTCONDITION, abbreviate. simpl_ret_assert.
    rewrite tree_arr_len, bltree_codes. entailer!.
Qed.
