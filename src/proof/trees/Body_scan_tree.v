(** * The body of trees.c's scan_tree against TSpec.v *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.trees.TSpec.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.proof.trees.CtModeS.
Require Import Zlib.trees.code.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

(** ** Helpers *)

Lemma rd_inv l i x : rd l i = Some x -> 0 <= i < Zlength l /\ x = Znth i l.
Proof.
  unfold rd, in_range. destruct (andb (0 <=? i) (i <? Zlength l)) eqn:E; [|discriminate].
  apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  intros H; inversion H; auto.
Qed.

Lemma wr_inv l i v l' : wr l i v = Some l' -> 0 <= i < Zlength l /\ l' = upd_Znth i l v.
Proof.
  unfold wr, in_range. destruct (andb (0 <=? i) (i <? Zlength l)) eqn:E; [|discriminate].
  apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  intros H; inversion H; auto.
Qed.

(** The store [tree[i].Len = v] on the Len presentation. *)
Lemma ct_arr_set_len t i v : 0 <= i < Zlength (fc t) -> Zlength (dl t) = Zlength (fc t) ->
  upd_Znth i (ct_arr ffalse ftrue t) (fst (Znth i (ct_arr ffalse ftrue t)), inr (vi v)) =
  ct_arr ffalse ftrue (mkTree (fc t) (upd_Znth i (dl t) v)).
Proof.
  intros Hi Hl. rewrite Znth_ct_arr by lia.
  transitivity (upd_Znth i (ct_arr ffalse ftrue t) (ctv_of (ffalse i) true (Znth i (fc t)) v));
    [reflexivity|].
  rewrite (ct_arr_set_dl ffalse ftrue t i true v) by auto. apply ct_arr_ext; auto.
  intros j. unfold fupd. destruct (Z.eq_dec j i); reflexivity.
Qed.

Lemma tree_ok_set_dl t m i v : tree_ok t m -> 0 <= v < 65536 ->
  tree_ok (mkTree (fc t) (upd_Znth i (dl t) v)) m.
Proof.
  intros (Hf & Hd & Hr) Hv. split; [|split]; cbn; auto.
  - rewrite Zlength_upd_Znth. auto.
  - intros j Hj. destruct (Hr j Hj). split; auto.
    destruct (zeq j i) as [->|ne].
    + destruct (zlt i (Zlength (dl t))); [|rewrite upd_Znth_out_of_range by lia; auto].
      destruct (zlt i 0); [rewrite upd_Znth_out_of_range by lia; auto|].
      rewrite upd_Znth_same by lia. auto.
    + destruct (zlt i 0); [rewrite upd_Znth_out_of_range by lia; auto|].
      destruct (zlt i (Zlength (dl t))); [|rewrite upd_Znth_out_of_range by lia; auto].
      rewrite upd_Znth_diff by lia. auto.
Qed.

Lemma tree_ok_set_fc t m i v : tree_ok t m -> 0 <= v < 65536 ->
  tree_ok (mkTree (upd_Znth i (fc t) v) (dl t)) m.
Proof.
  intros (Hf & Hd & Hr) Hv. split; [|split]; cbn; auto.
  - rewrite Zlength_upd_Znth. auto.
  - intros j Hj. destruct (Hr j Hj). split; auto.
    destruct (zeq j i) as [->|ne].
    + destruct (zlt i (Zlength (fc t))); [|rewrite upd_Znth_out_of_range by lia; auto].
      destruct (zlt i 0); [rewrite upd_Znth_out_of_range by lia; auto|].
      rewrite upd_Znth_same by lia. auto.
    + destruct (zlt i 0); [rewrite upd_Znth_out_of_range by lia; auto|].
      destruct (zlt i (Zlength (fc t))); [|rewrite upd_Znth_out_of_range by lia; auto].
      rewrite upd_Znth_diff by lia. auto.
Qed.

Lemma Znth_canon t i : 0 <= i < Zlength (fc t) ->
  Znth i (ct_canon t) = ctv_of false false (Znth i (fc t)) (Znth i (dl t)).
Proof. intros. unfold ct_canon. rewrite Znth_ct_arr by auto. reflexivity. Qed.

(** The store [s->bl_tree[i].Freq = v] on the canonical presentation. *)
Lemma canon_set_freq t i v : 0 <= i < Zlength (fc t) -> Zlength (dl t) = Zlength (fc t) ->
  upd_Znth i (ct_canon t) (inl (Vint (Int.repr v)), snd (Znth i (ct_canon t))) =
  ct_canon (mkTree (upd_Znth i (fc t) v) (dl t)).
Proof.
  intros Hi Hl. rewrite Znth_canon by lia. unfold ct_canon.
  transitivity (upd_Znth i (ct_arr ffalse ffalse t) (ctv_of false (ffalse i) v (Znth i (dl t))));
    [reflexivity|].
  rewrite (ct_arr_set_fc ffalse ffalse t i false v) by auto. apply ct_arr_ext; auto.
  intros j. unfold fupd. destruct (Z.eq_dec j i); reflexivity.
Qed.

Lemma scan_loop_done f t mc blf i pl nl cnt xc nc r :
  mc < i -> c_scan_tree_loop f t mc blf i pl nl cnt xc nc = Some r -> r = blf.
Proof.
  intros Hi. destruct f; cbn [c_scan_tree_loop]; rewrite (proj2 (Z.leb_gt _ _) Hi); congruence.
Qed.

(** The invariant of the loop: the model loop from the C state gives [rblf]. *)
Definition scan_inv (t0 : tree) (n max_code : Z) (bd : list Z) (rblf : list Z) (sp tp : val) (ni i : Z) : environ -> mpred :=
  EX f : nat, EX pl : Z, EX nl : Z, EX cnt : Z, EX xc : Z, EX nc : Z, EX blf : list Z,
  PROP (c_scan_tree_loop f t0 max_code blf i pl nl cnt xc nc = Some rblf;
        0 <= i <= max_code + 1; -1 <= pl < 65536; 0 <= nl < 65536; 0 <= cnt < xc; xc <= 138; 0 <= nc <= 4;
        tree_ok (mkTree blf bd) (2 * BL_CODES + 1))
  LOCAL (temp _n (vi ni); temp _prevlen (vi pl); temp _nextlen (vi nl); temp _count (vi cnt);
         temp _max_count (vi xc); temp _min_count (vi nc);
         temp _s sp; temp _tree tp; temp _max_code (vi max_code))
  SEP (@data_at DCS.CS Ews (tarray t_ct n) (ct_arr ffalse ftrue t0) tp;
       @field_at DCS.CS Ews t_ds (DOT _bl_tree) (ct_canon (mkTree blf bd)) sp).

Lemma inc_ok l bd k c l' m : (let* x := rd l k in wr l k (u16 (x + c))) = Some l' ->
  tree_ok (mkTree l bd) m -> tree_ok (mkTree l' bd) m.
Proof.
  intros H Hok. inv_bind H. apply wr_inv in H. destruct H as [_ ->].
  apply (tree_ok_set_fc (mkTree l bd)); auto. unfold u16. apply Z.mod_pos_bound. lia.
Qed.

Lemma scan_upd_ok blf bd nl pl cnt nc blf0 :
  (if cnt + 1 <? nc then let* x := rd blf nl in wr blf nl (u16 (x + u16 (cnt + 1)))
   else if negb (nl =? 0) then
     let* blf0 := (if negb (nl =? pl) then let* x := rd blf nl in wr blf nl (u16 (x + 1)) else Some blf) in
     let* x := rd blf0 REP_3_6 in wr blf0 REP_3_6 (u16 (x + 1))
   else if cnt + 1 <=? 10 then let* x := rd blf REPZ_3_10 in wr blf REPZ_3_10 (u16 (x + 1))
   else let* x := rd blf REPZ_11_138 in wr blf REPZ_11_138 (u16 (x + 1))) = Some blf0 ->
  tree_ok (mkTree blf bd) 39 -> tree_ok (mkTree blf0 bd) 39.
Proof.
  intros H Hok.
  destruct (cnt + 1 <? nc); [eapply inc_ok; eauto|].
  destruct (negb (nl =? 0)); [|destruct (cnt + 1 <=? 10); eapply inc_ok; eauto].
  inv_bind H. eapply inc_ok; [exact H|].
  destruct (negb (nl =? pl)); [eapply inc_ok; eauto|]. injection Ha as <-. auto.
Qed.

(** [s->bl_tree[k].Freq = s->bl_tree[k].Freq + c] (load, then store), on the canonical presentation:
    leaves the SEP with [ct_canon] of the updated tree. *)
Ltac bl_inc :=
  forward;
  [ rewrite Znth_canon by (cbn; lia); cbn [ctv_of ffalse fc dl]; go_lower; apply prop_right;
    apply tc_val_tushort_repr; lia
  | rewrite Znth_canon by (cbn; lia); cbn [ctv_of ffalse fc dl]; forward;
    repeat (rewrite add_repr || rewrite zext16_repr); rewrite canon_set_freq by (cbn; lia); cbn [fc dl] ].

Lemma body_scan_tree : semax_body Vprog Gprog_scan_tree f_scan_tree scan_tree_spec.
Proof.
  start_function.
  rename H0 into H1, H into H0. assert (H : True) by exact I.
  destruct bl as [bf bd].
  unfold tree_arr, bltree_at. Intros.
  unfold c_scan_tree in H1. inv_bind H1. destruct x. apply guard_inv, Z.ltb_lt in Ha. rename Ha into Hmx0.
  inv_bind H1. rename x into nl0.
  unfold ct_canon at 1. rewrite (ct_canon_mode Ews n ffalse ftrue t tp).
  apply rd_inv in Ha. destruct Ha as [Hz0 ->]. destruct H2 as (Hlf & Hld & Hrg).
  destruct (if Znth 0 (dl t) =? 0 then (138, 3) else (7, 4)) as [mc0 mn0] eqn:Emm in H1.
  inv_bind H1. rename x into t0, Ha into Hset.
  unfold c_set_dl in Hset. inv_bind Hset. apply wr_inv in Ha. destruct Ha as [Hmc ->].
  injection Hset as <-.
  assert (Hmx : max_code + 1 <= Int.max_signed) by (cbn; lia).
  inv_bind H1. rename x into rblf, Ha into Hloop. injection H1 as <-.
  forward. forward.
  { rewrite Znth_ct_arr by lia. cbn [ctv_of]. go_lower. apply prop_right. apply tc_val_tushort_repr.
    specialize (Hrg 0). lia. }
  rewrite Znth_ct_arr by lia. cbn [ctv_of ftrue].
  pose proof (Hrg 0 ltac:(lia)) as Hr0.
  forward. forward. forward.
  forward_if (PROP ()
    LOCAL (temp _max_count (vi mc0); temp _min_count (vi mn0); temp _count (vi 0);
           temp _nextlen (vi (Znth 0 (dl t))); temp _prevlen (vi (-1));
           temp _s sp; temp _tree tp; temp _max_code (vi max_code))
    SEP (@data_at DCS.CS Ews (tarray t_ct n) (ct_arr ffalse ftrue t) tp;
         @field_at DCS.CS Ews t_ds (DOT _bl_tree) (ct_canon (mkTree bf bd)) sp)).
  { forward. forward.
    assert (Znth 0 (dl t) = 0) as E0 by (first [exact H1 | apply repr_inj_unsigned in H1; rep_lia]).
    rewrite E0 in Emm. injection Emm as <- <-. entailer!. }
  { forward.
    assert (Znth 0 (dl t) <> 0) as E0 by (first [exact H1 | intro E; rewrite E in H1; contradiction]).
    rewrite (proj2 (Z.eqb_neq _ _) E0) in Emm. injection Emm as <- <-. entailer!. }
  forward.
  rewrite zext16_repr, zext16_repr. change (65535 mod 65536 mod 65536) with 65535.
  change (Vint (Int.repr 65535)) with (vi 65535).
  rewrite ct_arr_set_len by lia.
  set (t0 := mkTree (fc t) (upd_Znth (max_code + 1) (dl t) 65535)) in *.
  assert (Hok0 : tree_ok t0 n) by (apply tree_ok_set_dl; [split; [|split]; auto|lia]).
  clearbody t0.
  forward_loop (EX i : Z, scan_inv t0 n max_code bd rblf sp tp i i)
    continue: (EX i : Z, scan_inv t0 n max_code bd rblf sp tp i (i + 1))
    break: (PROP (tree_ok (mkTree rblf bd) (2 * BL_CODES + 1)) LOCAL ()
            SEP (@data_at DCS.CS Ews (tarray t_ct n) (ct_arr ffalse ftrue t0) tp;
                 @field_at DCS.CS Ews t_ds (DOT _bl_tree) (ct_canon (mkTree rblf bd)) sp)).
  - assert (Hm0 : (mc0 = 138 /\ mn0 = 3) \/ (mc0 = 7 /\ mn0 = 4))
      by (destruct (_ =? 0); inversion Emm; auto).
    forward. Exists 0. unfold scan_inv. Exists (Z.to_nat (max_code + 1)) (-1) (Znth 0 (dl t)) 0 mc0 mn0 bf.
    entailer!.
  - Intros i. unfold scan_inv. Intros f pl nl cnt xc nc blf.
    forward_if.
    2:{ forward. apply scan_loop_done in H1; [subst blf|lia]. entailer!. }
    destruct f as [|f]; [cbn in H1; rewrite (proj2 (Z.leb_le i max_code)) in H1 by lia; discriminate|].
    cbn [c_scan_tree_loop] in H1. rewrite (proj2 (Z.leb_le i max_code)) in H1 by lia.
    inv_bind H1. rename x into nl', Ha into Hrd. apply rd_inv in Hrd. destruct Hrd as [Hi1 ->].
    destruct Hok0 as (Hf0 & Hd0 & Hr0').
    pose proof (Hr0' (i + 1) ltac:(lia)) as Hri.
    forward. forward.
    { rewrite Znth_ct_arr by lia. cbn [ctv_of ftrue]. go_lower. apply prop_right. apply tc_val_tushort_repr.
      lia. }
    rewrite Znth_ct_arr by lia. cbn [ctv_of ftrue].
    set (nl' := Znth (i + 1) (dl t0)) in *.
    forward. forward.
    forward_if (PROP ()
      LOCAL (temp _t'2 (Vint (if andb (cnt + 1 <? xc) (nl =? nl') then Int.one else Int.zero));
             temp _count (vi (cnt + 1)); temp _curlen (vi nl); temp _nextlen (vi nl'); temp _n (vi i);
             temp _prevlen (vi pl); temp _max_count (vi xc); temp _min_count (vi nc);
             temp _s sp; temp _tree tp; temp _max_code (vi max_code))
      SEP (@data_at DCS.CS Ews (tarray t_ct n) (ct_arr ffalse ftrue t0) tp;
           @field_at DCS.CS Ews t_ds (DOT _bl_tree) (ct_canon (mkTree blf bd)) sp)).
    { forward. entailer!.
      rewrite (proj2 (Z.ltb_lt _ _) H11). cbn [andb].
      destruct (zeq nl nl') as [e|e];
        [rewrite (proj2 (Z.eqb_eq _ _) e) | rewrite (proj2 (Z.eqb_neq _ _) e)]; reflexivity. }
    { forward. entailer!. rewrite (proj2 (Z.ltb_ge (cnt + 1) xc) ltac:(lia)). reflexivity. }
    destruct (andb (cnt + 1 <? xc) (nl =? nl')) eqn:Eb.
    { forward_if (PROP (False) LOCAL () SEP ()).
      - forward. Exists i. unfold scan_inv. Exists f pl nl' (cnt + 1) xc nc blf.
        apply andb_prop in Eb. destruct Eb as [Eb1 Eb2]. apply Z.ltb_lt in Eb1.
        entailer!.
      - exfalso. apply Int.one_not_zero. assumption. }
    inv_bind H1. rename x into blf0, Ha into Hupd.
    destruct (if nl' =? 0 then (138, 3) else if nl =? nl' then (6, 3) else (7, 4)) as [xc' nc'] eqn:Emc in H1.
    forward_if (PROP ()
      LOCAL (temp _count (vi (cnt + 1)); temp _curlen (vi nl); temp _nextlen (vi nl'); temp _n (vi i);
             temp _prevlen (vi pl); temp _max_count (vi xc); temp _min_count (vi nc);
             temp _s sp; temp _tree tp; temp _max_code (vi max_code))
      SEP (@data_at DCS.CS Ews (tarray t_ct n) (ct_arr ffalse ftrue t0) tp;
           @field_at DCS.CS Ews t_ds (DOT _bl_tree) (ct_canon (mkTree blf0 bd)) sp)).
    { contradiction. }
    { pose proof H9 as (Hbl & Hbd & Hbr). change (2 * BL_CODES + 1) with 39 in Hbl, Hbd, Hbr.
      cbn [fc dl] in Hbl, Hbd, Hbr.
      forward_if.
      - destruct (cnt + 1 <? nc) eqn:Ecn; [|apply Z.ltb_ge in Ecn; lia].
        inv_bind Hupd. apply rd_inv in Ha. destruct Ha as [Hnl ->]. apply wr_inv in Hupd.
        destruct Hupd as [_ ->].
        pose proof (Hbr nl ltac:(lia)) as Hk.
        bl_inc.
        unfold u16. entailer!.
      - destruct (cnt + 1 <? nc) eqn:Ecn; [apply Z.ltb_lt in Ecn; lia|].
        forward_if.
        + rewrite (proj2 (Z.eqb_neq nl 0) ltac:(auto)) in Hupd. cbn [negb] in Hupd.
          inv_bind Hupd. rename x into blf1, Ha into Hup1.
          assert (Hok1 : tree_ok (mkTree blf1 bd) 39).
          { destruct (negb (nl =? pl)); [eapply inc_ok; eauto|]. injection Hup1 as <-. auto. }
          forward_if (PROP ()
            LOCAL (temp _count (vi (cnt + 1)); temp _curlen (vi nl); temp _nextlen (vi nl'); temp _n (vi i);
                   temp _prevlen (vi pl); temp _max_count (vi xc); temp _min_count (vi nc);
                   temp _s sp; temp _tree tp; temp _max_code (vi max_code))
            SEP (@data_at DCS.CS Ews (tarray t_ct n) (ct_arr ffalse ftrue t0) tp;
                 @field_at DCS.CS Ews t_ds (DOT _bl_tree) (ct_canon (mkTree blf1 bd)) sp)).
          * rewrite (proj2 (Z.eqb_neq nl pl) ltac:(auto)) in Hup1. cbn [negb] in Hup1.
            inv_bind Hup1. apply rd_inv in Ha. destruct Ha as [Hnl ->]. apply wr_inv in Hup1.
            destruct Hup1 as [_ ->].
            pose proof (Hbr nl ltac:(lia)) as Hk.
            bl_inc.
            unfold u16. entailer!.
          * forward. subst nl.
            rewrite Z.eqb_refl in Hup1. cbn [negb] in Hup1. injection Hup1 as <-. entailer!.
          * destruct Hok1 as (Hbl1 & Hbd1 & Hbr1). cbn [fc dl] in Hbl1, Hbd1, Hbr1.
            inv_bind Hupd. apply rd_inv in Ha. destruct Ha as [Hnl ->]. apply wr_inv in Hupd.
            destruct Hupd as [_ ->].
            pose proof (Hbr1 16 ltac:(lia)) as Hk.
            bl_inc.
            unfold u16. entailer!.
        + assert (nl = 0) by (first [assumption | apply repr_inj_unsigned in H13; rep_lia]). subst nl.
          cbn [Z.eqb negb] in Hupd.
          forward_if.
          * rewrite (proj2 (Z.leb_le (cnt + 1) 10) ltac:(lia)) in Hupd.
            inv_bind Hupd. apply rd_inv in Ha. destruct Ha as [Hnl ->]. apply wr_inv in Hupd.
            destruct Hupd as [_ ->].
            pose proof (Hbr 17 ltac:(lia)) as Hk.
            bl_inc.
            unfold u16. entailer!.
          * rewrite (proj2 (Z.leb_gt (cnt + 1) 10) ltac:(lia)) in Hupd.
            inv_bind Hupd. apply rd_inv in Ha. destruct Ha as [Hnl ->]. apply wr_inv in Hupd.
            destruct Hupd as [_ ->].
            pose proof (Hbr 18 ltac:(lia)) as Hk.
            bl_inc.
            unfold u16. entailer!. }
    pose proof (scan_upd_ok _ _ _ _ _ _ _ Hupd H9) as Hok0.
    forward. forward.
    forward_if.
    { assert (nl' = 0) as E0 by (first [assumption | apply repr_inj_unsigned in H11; rep_lia]).
      rewrite E0, Z.eqb_refl in Emc. injection Emc as <- <-.
      forward. forward. Exists i. unfold scan_inv. Exists f nl nl' 0 138 3 blf0.
      entailer!. }
    rewrite (proj2 (Z.eqb_neq nl' 0) ltac:(auto)) in Emc.
    forward_if.
    { rewrite (proj2 (Z.eqb_eq nl nl') ltac:(auto)) in Emc. injection Emc as <- <-.
      forward. forward. Exists i. unfold scan_inv. Exists f nl nl' 0 6 3 blf0.
      entailer!. }
    { rewrite (proj2 (Z.eqb_neq nl nl') ltac:(auto)) in Emc. injection Emc as <- <-.
      forward. forward. Exists i. unfold scan_inv. Exists f nl nl' 0 7 4 blf0.
      entailer!. }
  - Intros i. unfold scan_inv. Intros f pl nl cnt xc nc blf.
    forward. Exists (i + 1). unfold scan_inv. Exists f pl nl cnt xc nc blf.
    entailer!.
  - rewrite <- (ct_canon_mode Ews n ffalse ftrue t0 tp).
    unfold POSTCONDITION, abbreviate. simpl_ret_assert. unfold tree_arr, bltree_at. cbn [fst snd].
    Intros. unfold ct_canon. entailer!.
Qed.

