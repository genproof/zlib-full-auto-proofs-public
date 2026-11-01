(** * The body of trees.c's pqdownheap against its shared specification (TSpec.v) *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.trees.TSpec.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.proof.trees.CtMode.
Require Import Zlib.trees.code.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

Lemma shiftl1 x : Z.shiftl x 1 = 2 * x.
Proof. rewrite Z.shiftl_mul_pow2 by lia. lia. Qed.

(** The value of [tree[i].fc.freq] as VST's load leaves it. *)
Lemma ct_freq_val t i : 0 <= i < Zlength (fc t) ->
  match (let (x, _) := Znth i (ct_canon t) in x) with inl f => f | inr _ => Vundef end =
  Vint (Int.repr (Znth i (fc t))).
Proof. intros. unfold ct_canon. rewrite Znth_ct_arr by auto. reflexivity. Qed.

(** A load of [tree[i].fc.freq]. *)
Ltac tload := forward;
  [go_lower; apply prop_right; rewrite ct_freq_val by lia; apply tc_val_tushort_repr; lia
  | rewrite ct_freq_val by lia].

(** ** Inversion of the model's steps *)

Lemma rd_inv l i x : rd l i = Some x -> 0 <= i < Zlength l /\ x = Znth i l.
Proof.
  unfold rd, in_range. destruct (andb (0 <=? i) (i <? Zlength l)) eqn:E; [|discriminate].
  intros Hx; inversion Hx; subst. apply andb_prop in E. destruct E as [E1 E2].
  apply Z.leb_le in E1. apply Z.ltb_lt in E2. auto.
Qed.

Lemma wr_inv l i v x : wr l i v = Some x -> 0 <= i < Zlength l /\ x = upd_Znth i l v.
Proof.
  unfold wr, in_range. destruct (andb (0 <=? i) (i <? Zlength l)) eqn:E; [|discriminate].
  intros Hx; inversion Hx; subst. apply andb_prop in E. destruct E as [E1 E2].
  apply Z.leb_le in E1. apply Z.ltb_lt in E2. auto.
Qed.

Lemma c_smaller_inv t d n m b : c_smaller t d n m = Some b ->
  0 <= n < Zlength (fc t) /\ 0 <= m < Zlength (fc t) /\
  (Znth n (fc t) < Znth m (fc t) -> b = true) /\
  (Znth n (fc t) > Znth m (fc t) -> b = false) /\
  (Znth n (fc t) = Znth m (fc t) ->
     0 <= n < Zlength d /\ 0 <= m < Zlength d /\ b = (Znth n d <=? Znth m d)).
Proof.
  unfold c_smaller. intros H.
  inv_bind H. apply rd_inv in Ha. destruct Ha as [Hn ->].
  inv_bind H. apply rd_inv in Ha. destruct Ha as [Hm ->].
  split; [auto|]. split; [auto|].
  destruct (Z.ltb_spec (Znth n (fc t)) (Znth m (fc t))).
  - inversion H. repeat split; intros; lia.
  - destruct (Z.eqb_spec (Znth n (fc t)) (Znth m (fc t))).
    + inv_bind H. apply rd_inv in Ha. destruct Ha as [Hdn ->].
      inv_bind H. apply rd_inv in Ha. destruct Ha as [Hdm ->].
      inversion H. repeat split; intros; auto; lia.
    + inversion H. repeat split; intros; auto; lia.
Qed.

Lemma pq_loop_exit f t d hl v hp k j r :
  c_pqdownheap_loop f t d hl v hp k j = Some r -> hl < j -> r = (hp, k).
Proof.
  intros H Hj. destruct f; cbn in H; rewrite (proj2 (Z.leb_gt j hl) Hj) in H; inversion H; auto.
Qed.

Lemma pq_loop_S f t d hl v hp k j r :
  c_pqdownheap_loop f t d hl v hp k j = Some r -> j <= hl ->
  exists f', f = S f'.
Proof.
  intros H Hj. destruct f; [|eauto]. cbn in H. rewrite (proj2 (Z.leb_le j hl) Hj) in H. discriminate.
Qed.

Lemma Forall_upd_Znth_Z (P : Z -> Prop) l i x : Forall P l -> P x -> Forall P (upd_Znth i l x).
Proof.
  intros Hl Hx. destruct (zlt i 0); [rewrite upd_Znth_out_of_range by lia; auto|].
  destruct (zlt i (Zlength l)); [|rewrite upd_Znth_out_of_range by lia; auto].
  apply Forall_Znth. rewrite Zlength_upd_Znth. intros j Hj.
  destruct (Z.eq_dec j i) as [->|ne].
  - rewrite upd_Znth_same by lia. auto.
  - rewrite upd_Znth_diff by lia. apply Forall_Znth; auto; lia.
Qed.

Lemma body_pqdownheap : semax_body Vprog Gprog_pqdownheap f_pqdownheap pqdownheap_spec.
Proof.
  start_function.
  unfold work_at, tree_arr. Intros.
  destruct w as [heap hl hm dep blc ol sl].
  destruct H2 as (Hlh & Hld & Hlb & Hfh & Hhl & Hhm & Hfd & Hfb & Hol & Hsl).
  destruct H1 as (Hfc & Hdl & Ht).
  cbn [w_heap w_heap_len w_heap_max w_depth w_bl_count w_opt_len w_static_len] in *.
  unfold c_pqdownheap in H0. cbn [w_heap w_depth w_heap_len] in H0.
  inv_bind H0. apply rd_inv in Ha. destruct Ha as [Hk ->].
  inv_bind H0. destruct x as [hr kr].
  inv_bind H0. apply wr_inv in Ha0. destruct Ha0 as [Hkr ->].
  inversion H0; subst r; clear H0.
  unfold vi.
  assert (Hlh' : Zlength heap = 573) by (rewrite Hlh; reflexivity).
  assert (Hld' : Zlength dep = 573) by (rewrite Hld; reflexivity).
  clear Hlh Hld.
  forward.
  forward.
  rewrite shl1_repr, shiftl1 in *.
  set (v := Znth k heap) in *.
  assert (Hv : Int.min_signed <= v <= Int.max_signed) by (apply Forall_Znth; auto; lia).
  forward_loop (EX f : nat, EX hp : list Z, EX kk : Z,
    PROP (c_pqdownheap_loop f t dep hl v hp kk (2 * kk) = Some (hr, kr); 0 <= kk < 573; Zlength hp = 573;
          Forall (fun x => Int.min_signed <= x <= Int.max_signed) hp)
    LOCAL (temp _v (Vint (Int.repr v)); temp _j (Vint (Int.repr (2 * kk))); temp _k (Vint (Int.repr kk));
           temp _s sp; temp _tree tp)
    SEP (@data_at DCS.CS tsh (tarray t_ct n) (ct_canon t) tp;
         @field_at DCS.CS Ews t_ds (DOT _heap) (map (fun z : Z => Vint (Int.repr z)) hp) sp;
         @field_at DCS.CS Ews t_ds (DOT _heap_len) (Vint (Int.repr hl)) sp;
         @field_at DCS.CS Ews t_ds (DOT _heap_max) (Vint (Int.repr hm)) sp;
         @field_at DCS.CS Ews t_ds (DOT _depth) (map (fun z : Z => Vint (Int.repr z)) dep) sp;
         @field_at DCS.CS Ews t_ds (DOT _bl_count) (map (fun z : Z => Vint (Int.repr z)) blc) sp;
         @field_at DCS.CS Ews t_ds (DOT _opt_len) (vl ol) sp;
         @field_at DCS.CS Ews t_ds (DOT _static_len) (vl sl) sp))
  break: (PROP (Zlength hr = 573; Forall (fun x => Int.min_signed <= x <= Int.max_signed) hr)
    LOCAL (temp _v (Vint (Int.repr v)); temp _k (Vint (Int.repr kr)); temp _s sp)
    SEP (@data_at DCS.CS tsh (tarray t_ct n) (ct_canon t) tp;
         @field_at DCS.CS Ews t_ds (DOT _heap) (map (fun z : Z => Vint (Int.repr z)) hr) sp;
         @field_at DCS.CS Ews t_ds (DOT _heap_len) (Vint (Int.repr hl)) sp;
         @field_at DCS.CS Ews t_ds (DOT _heap_max) (Vint (Int.repr hm)) sp;
         @field_at DCS.CS Ews t_ds (DOT _depth) (map (fun z : Z => Vint (Int.repr z)) dep) sp;
         @field_at DCS.CS Ews t_ds (DOT _bl_count) (map (fun z : Z => Vint (Int.repr z)) blc) sp;
         @field_at DCS.CS Ews t_ds (DOT _opt_len) (vl ol) sp;
         @field_at DCS.CS Ews t_ds (DOT _static_len) (vl sl) sp)).
  { Exists pq_fuel heap k. entailer!. }
  { Intros f hp kk.
    forward. forward_if.
    2: { forward. apply pq_loop_exit in H0; [|lia]. inversion H0; subst hr kr. entailer!. }
    assert (Hjl : 2 * kk <= hl) by lia.
    destruct (pq_loop_S _ _ _ _ _ _ _ _ _ H0 Hjl) as [f' ->].
    cbn [c_pqdownheap_loop] in H0. rewrite (proj2 (Z.leb_le _ _) Hjl) in H0.
    apply bind_inv in H0; destruct H0 as [j1 [Hj1 H0]].
    apply bind_inv in H0; destruct H0 as [hj [Hhj H0]]. apply rd_inv in Hhj; destruct Hhj as [Hj1r ->].
    apply bind_inv in H0; destruct H0 as [sm2 [Hsm2 H0]].
    forward.
    forward_if (PROP () LOCAL (temp _t'1 (Val.of_bool (j1 =? 2 * kk + 1)); temp _v (Vint (Int.repr v));
           temp _j (Vint (Int.repr (2 * kk))); temp _k (Vint (Int.repr kk)); temp _s sp; temp _tree tp)
      SEP (@data_at DCS.CS tsh (tarray t_ct n) (ct_canon t) tp;
         @field_at DCS.CS Ews t_ds (DOT _heap) (map (fun z : Z => Vint (Int.repr z)) hp) sp;
         @field_at DCS.CS Ews t_ds (DOT _heap_len) (Vint (Int.repr hl)) sp;
         @field_at DCS.CS Ews t_ds (DOT _heap_max) (Vint (Int.repr hm)) sp;
         @field_at DCS.CS Ews t_ds (DOT _depth) (map (fun z : Z => Vint (Int.repr z)) dep) sp;
         @field_at DCS.CS Ews t_ds (DOT _bl_count) (map (fun z : Z => Vint (Int.repr z)) blc) sp;
         @field_at DCS.CS Ews t_ds (DOT _opt_len) (vl ol) sp;
         @field_at DCS.CS Ews t_ds (DOT _static_len) (vl sl) sp)).
    - rewrite (proj2 (Z.ltb_lt _ _) H5) in Hj1.
      apply bind_inv in Hj1; destruct Hj1 as [a [Ha1 Hj1]]. apply rd_inv in Ha1; destruct Ha1 as [Har ->].
      apply bind_inv in Hj1; destruct Hj1 as [b [Hb1 Hj1]]. apply rd_inv in Hb1; destruct Hb1 as [Hbr ->].
      apply bind_inv in Hj1; destruct Hj1 as [sm [Hsm Hj1]]. apply c_smaller_inv in Hsm.
      destruct Hsm as (Hsa & Hsb & Hlt1 & Hgt1 & Heq1).
      assert (Hta : 0 <= Znth (Znth (2 * kk + 1) hp) (fc t) < 65536) by (apply Ht; lia).
      assert (Htb : 0 <= Znth (Znth (2 * kk) hp) (fc t) < 65536) by (apply Ht; lia).
      assert (Har' : Int.min_signed <= Znth (2 * kk + 1) hp <= Int.max_signed) by (apply Forall_Znth; auto; lia).
      assert (Hbr' : Int.min_signed <= Znth (2 * kk) hp <= Int.max_signed) by (apply Forall_Znth; auto; lia).
      forward. tload. forward. tload.
      forward_if.
      + assert (sm = true) by (apply Hlt1; lia). subst sm. inversion Hj1. subst j1.
        forward. entailer!. rewrite Z.eqb_refl. reflexivity.
      + forward. tload. forward. tload.
        forward_if.
        * destruct (Heq1 ltac:(lia)) as (Hda & Hdb & ->).
          assert (Hda' : 0 <= Znth (Znth (2 * kk + 1) hp) dep < 256) by (apply Forall_Znth; auto).
          assert (Hdb' : 0 <= Znth (Znth (2 * kk) hp) dep < 256) by (apply Forall_Znth; auto).
          fwd. fwd. fwd. fwd. forward. forward. forward.
          entailer!.
          inversion Hj1; subst j1.
          destruct (Z.leb_spec (Znth (Znth (2 * kk + 1) hp) dep) (Znth (Znth (2 * kk) hp) dep));
            destruct (zlt (Znth (Znth (2 * kk) hp) dep) (Znth (Znth (2 * kk + 1) hp) dep)); try lia;
            cbn [negb]; [rewrite Z.eqb_refl | rewrite (proj2 (Z.eqb_neq _ _)) by lia]; reflexivity.
        * assert (sm = false) by (apply Hgt1; lia). subst sm. inversion Hj1. subst j1.
          forward. forward. entailer!.
          rewrite (proj2 (Z.eqb_neq _ _)) by lia. reflexivity.
    - rewrite (proj2 (Z.ltb_ge _ _)) in Hj1 by lia. inversion Hj1; subst j1.
      forward. entailer!. rewrite (proj2 (Z.eqb_neq _ _)) by lia. reflexivity.
    - assert (Hj1c : j1 = 2 * kk \/ j1 = 2 * kk + 1).
      { clear -Hj1. destruct (2 * kk <? hl); [|inversion Hj1; lia].
        apply bind_inv in Hj1; destruct Hj1 as [? [_ Hj1]].
        apply bind_inv in Hj1; destruct Hj1 as [? [_ Hj1]].
        apply bind_inv in Hj1; destruct Hj1 as [sm [_ Hj1]].
        destruct sm; inversion Hj1; lia. }
      forward_if (PROP () LOCAL (temp _v (Vint (Int.repr v));
           temp _j (Vint (Int.repr j1)); temp _k (Vint (Int.repr kk)); temp _s sp; temp _tree tp)
      SEP (@data_at DCS.CS tsh (tarray t_ct n) (ct_canon t) tp;
         @field_at DCS.CS Ews t_ds (DOT _heap) (map (fun z : Z => Vint (Int.repr z)) hp) sp;
         @field_at DCS.CS Ews t_ds (DOT _heap_len) (Vint (Int.repr hl)) sp;
         @field_at DCS.CS Ews t_ds (DOT _heap_max) (Vint (Int.repr hm)) sp;
         @field_at DCS.CS Ews t_ds (DOT _depth) (map (fun z : Z => Vint (Int.repr z)) dep) sp;
         @field_at DCS.CS Ews t_ds (DOT _bl_count) (map (fun z : Z => Vint (Int.repr z)) blc) sp;
         @field_at DCS.CS Ews t_ds (DOT _opt_len) (vl ol) sp;
         @field_at DCS.CS Ews t_ds (DOT _static_len) (vl sl) sp)).
      + forward. entailer!.
        destruct (Z.eqb_spec j1 (2 * kk + 1)); [subst; reflexivity | inversion H5].
      + forward. entailer!.
        destruct (Z.eqb_spec j1 (2 * kk + 1)); [inversion H5|].
        destruct Hj1c; [subst; reflexivity | lia].
      + apply c_smaller_inv in Hsm2. destruct Hsm2 as (Hsv & Hsj & Hlt2 & Hgt2 & Heq2).
        assert (Htv : 0 <= Znth v (fc t) < 65536) by (apply Ht; lia).
        assert (Htj : 0 <= Znth (Znth j1 hp) (fc t) < 65536) by (apply Ht; lia).
        assert (Hjr' : Int.min_signed <= Znth j1 hp <= Int.max_signed) by (apply Forall_Znth; auto; lia).
        tload. forward. tload.
        forward_if (PROP () LOCAL (temp _t'2 (Val.of_bool sm2); temp _v (Vint (Int.repr v));
           temp _j (Vint (Int.repr j1)); temp _k (Vint (Int.repr kk)); temp _s sp; temp _tree tp)
          SEP (@data_at DCS.CS tsh (tarray t_ct n) (ct_canon t) tp;
           @field_at DCS.CS Ews t_ds (DOT _heap) (map (fun z : Z => Vint (Int.repr z)) hp) sp;
           @field_at DCS.CS Ews t_ds (DOT _heap_len) (Vint (Int.repr hl)) sp;
           @field_at DCS.CS Ews t_ds (DOT _heap_max) (Vint (Int.repr hm)) sp;
           @field_at DCS.CS Ews t_ds (DOT _depth) (map (fun z : Z => Vint (Int.repr z)) dep) sp;
           @field_at DCS.CS Ews t_ds (DOT _bl_count) (map (fun z : Z => Vint (Int.repr z)) blc) sp;
           @field_at DCS.CS Ews t_ds (DOT _opt_len) (vl ol) sp;
           @field_at DCS.CS Ews t_ds (DOT _static_len) (vl sl) sp)).
        * assert (sm2 = true) by (apply Hlt2; lia). subst sm2.
          forward. entailer!.
        * tload. forward. tload.
          forward_if.
          -- destruct (Heq2 ltac:(lia)) as (Hdv & Hdj & ->).
             assert (Hdv' : 0 <= Znth v dep < 256) by (apply Forall_Znth; auto).
             assert (Hdj' : 0 <= Znth (Znth j1 hp) dep < 256) by (apply Forall_Znth; auto).
             fwd. fwd. fwd. forward. forward.
             entailer!.
             destruct (Z.leb_spec (Znth v dep) (Znth (Znth j1 hp) dep));
               destruct (zlt (Znth (Znth j1 hp) dep) (Znth v dep)); try lia; reflexivity.
          -- assert (sm2 = false) by (apply Hgt2; lia). subst sm2.
             forward. entailer!.
        * forward_if.
          -- destruct sm2; [|match goal with H : typed_true _ _ |- _ => inversion H end].
             inversion H0; subst hr kr. forward. entailer!.
          -- destruct sm2; [match goal with H : typed_false _ _ |- _ => inversion H end|].
             apply bind_inv in H0; destruct H0 as [hp' [Hw H0]]. apply wr_inv in Hw. destruct Hw as [_ ->].
             forward. forward. forward. forward.
             Exists f' (upd_Znth kk hp (Znth j1 hp)) j1.
             rewrite shl1_repr, shiftl1 in *. rewrite <- upd_Znth_map. entailer!.
             split; [rewrite Zlength_upd_Znth; auto | apply Forall_upd_Znth_Z; auto]. }
  Intros. forward.
  unfold work_at, tree_arr.
  cbn [w_set_heap w_heap w_heap_len w_heap_max w_depth w_bl_count w_opt_len w_static_len].
  unfold vi. rewrite <- upd_Znth_map. entailer!.
  split; [split; [|split]; auto|].
  unfold work_ok, w_set_heap; cbn [w_heap w_heap_len w_heap_max w_depth w_bl_count w_opt_len w_static_len].
  rewrite Zlength_upd_Znth, H0, Hld'.
  repeat split; auto; try lia. apply Forall_upd_Znth_Z; auto.
Qed.
