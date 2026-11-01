(** * The body of trees.c's detect_data_type against TSpec.v *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.trees.TSpec.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.proof.trees.CtModeS.
Require Import Zlib.trees.code.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

Lemma dd_mask_bit n : 0 <= n <= 31 ->
  Int64.and (Int64.repr (Z.shiftr 4093624447 n)) (Int64.repr 1) = Int64.repr (if block_listed n then 1 else 0).
Proof.
  intros Hn.
  assert (Hk : forall k, (k < 32)%nat ->
    Int64.and (Int64.repr (Z.shiftr 4093624447 (Z.of_nat k))) (Int64.repr 1) =
    Int64.repr (if block_listed (Z.of_nat k) then 1 else 0)).
  { intros k Hk. do 32 (destruct k as [|k]; [vm_compute; reflexivity|]). lia. }
  replace n with (Z.of_nat (Z.to_nat n)) by lia. apply Hk. lia.
Qed.

Lemma dd_mask_shr n : 0 <= n <= 31 ->
  Int64.shru (Int64.repr (Z.shiftr 4093624447 n)) (Int64.repr (Int.unsigned (Int.repr 1))) =
  Int64.repr (Z.shiftr 4093624447 (n + 1)).
Proof.
  intros Hn.
  assert (Hk : forall k, (k < 32)%nat ->
    Int64.shru (Int64.repr (Z.shiftr 4093624447 (Z.of_nat k))) (Int64.repr (Int.unsigned (Int.repr 1))) =
    Int64.repr (Z.shiftr 4093624447 (Z.of_nat k + 1))).
  { intros k Hk. do 32 (destruct k as [|k]; [vm_compute; reflexivity|]). lia. }
  replace n with (Z.of_nat (Z.to_nat n)) by lia. apply Hk. lia.
Qed.

Lemma dd_rd (lf : list Z) i : Zlength lf = 573 -> 0 <= i < 573 -> rd lf i = Some (Znth i lf).
Proof.
  intros Hl Hi. unfold rd, in_range. rewrite Hl.
  rewrite (proj2 (Z.leb_le 0 i)), (proj2 (Z.ltb_lt i 573)) by lia. reflexivity.
Qed.

Lemma body_detect_data_type : semax_body Vprog Gprog_detect_data_type f_detect_data_type detect_data_type_spec.
Proof.
  start_function.
  unfold ltree_at. Intros.
  set (lf := fc lt) in *.
  pose proof H0 as Htok. destruct H0 as [Hlf [Hdl Hrng]].
  assert (Hz : forall i, 0 <= i < 573 -> Znth i (ct_canon lt) = (inl (vi (Znth i lf)), inl (vi (Znth i (dl lt))))).
  { intros i Hi. unfold ct_canon. rewrite Znth_ct_arr by (rewrite Hlf; unfold HEAP_SIZE in *; cbn; lia). reflexivity. }
  assert (Hfr : forall i, 0 <= i < 573 -> 0 <= Znth i lf < 65536).
  { intros i Hi. apply (Hrng i). unfold HEAP_SIZE in *. cbn in *. lia. }
  assert (Hlf' : Zlength lf = 573) by exact Hlf.
  unfold c_detect_data_type in H. inv_bind H. rename x into b, Ha into Hb.
  forward. forward.
  forward_loop
    (EX n : Z,
      PROP (0 <= n <= 32; c_dd_block (Z.to_nat (32 - n)) lf n = Some b)
      LOCAL (temp _n (Vint (Int.repr n)); temp _block_mask (Vlong (Int64.repr (Z.shiftr 4093624447 n)));
             temp _s sp)
      SEP (@field_at DCS.CS Ews t_ds (DOT _dyn_ltree) (ct_canon lt) sp))
    continue:
    (EX n : Z,
      PROP (0 <= n < 32; c_dd_block (Z.to_nat (32 - (n + 1))) lf (n + 1) = Some b)
      LOCAL (temp _n (Vint (Int.repr n)); temp _block_mask (Vlong (Int64.repr (Z.shiftr 4093624447 n)));
             temp _s sp)
      SEP (@field_at DCS.CS Ews t_ds (DOT _dyn_ltree) (ct_canon lt) sp))
    break:
    (PROP (b = false)
      LOCAL (temp _s sp)
      SEP (@field_at DCS.CS Ews t_ds (DOT _dyn_ltree) (ct_canon lt) sp)).
  - Exists 0. entailer!.
  - Intros n. rename H0 into Hn, H1 into Hblk.
    forward_if.
    + replace (Z.to_nat (32 - n)) with (S (Z.to_nat (32 - (n + 1)))) in Hblk by lia.
      cbn [c_dd_block] in Hblk. rewrite (proj2 (Z.leb_le n 31) ltac:(lia)) in Hblk.
      pose proof (Hfr n ltac:(lia)) as Hfn.
      forward_if (PROP () LOCAL (temp _t'1 (Vint (Int.repr (if andb (block_listed n) (negb (Znth n lf =? 0)) then 1 else 0)));
        temp _n (Vint (Int.repr n)); temp _block_mask (Vlong (Int64.repr (Z.shiftr 4093624447 n))); temp _s sp)
        SEP (@field_at DCS.CS Ews t_ds (DOT _dyn_ltree) (ct_canon lt) sp)).
      * rewrite dd_mask_bit in H1 by lia. destruct (block_listed n) eqn:Hbl; [|contradiction].
        forward.
        { setoid_rewrite (Hz n); [|lia]. unfold vi. tc_side. }
        setoid_rewrite (Hz n); [|lia]. unfold vi.
        forward.
        entailer!.
        simpl andb. unfold bool2val.
        destruct (Z.eqb_spec (Znth n lf) 0); destruct (zeq (Znth n lf) 0); try lia; reflexivity.
      * rewrite dd_mask_bit in H1 by lia. destruct (block_listed n); [discriminate|].
        forward. entailer!.
      * rewrite (dd_rd lf n Hlf' ltac:(lia)) in Hblk. cbn [bind] in Hblk.
        forward_if.
        -- destruct (block_listed n && negb (Znth n lf =? 0))%bool eqn:Ehit; [|now contradiction H1'].
           assert (Hb1 : b = true).
           { destruct (block_listed n); cbn in Ehit, Hblk; [rewrite Ehit in Hblk|discriminate]. congruence. }
           subst b. cbv beta iota in H. inversion H. subst r.
           forward. unfold ltree_at. entailer!.
        -- destruct (block_listed n && negb (Znth n lf =? 0))%bool eqn:Ehit; [now apply Int.one_not_zero in H1|].
           forward.
           Exists n. entailer!.
           destruct (block_listed n); cbn in Ehit |- *; [rewrite Ehit in Hblk|]; exact Hblk.
    + forward.
      assert (n = 32) by lia. subst n. cbn in Hblk. inversion Hblk. entailer!.
  - Intros n. forward. forward.
    Exists (n + 1). entailer!.
    rewrite dd_mask_shr by lia. reflexivity.
  - Intros. subst b. cbn [negb] in H.
    rewrite (dd_rd lf 9 Hlf' ltac:(lia)), (dd_rd lf 10 Hlf' ltac:(lia)), (dd_rd lf 13 Hlf' ltac:(lia)) in H.
    cbn [bind] in H.
    pose proof (Hfr 9 ltac:(lia)) as H9. pose proof (Hfr 10 ltac:(lia)) as H10.
    pose proof (Hfr 13 ltac:(lia)) as H13.
    forward.
    { setoid_rewrite (Hz 9); [|lia]. unfold vi. tc_side. }
    setoid_rewrite (Hz 9); [|lia]. unfold vi.
    forward_if (PROP () LOCAL (temp _t'2 (Vint (Int.repr (if (negb (Znth 9 lf =? 0) || negb (Znth 10 lf =? 0))%bool then 1 else 0)));
        temp _s sp)
        SEP (@field_at DCS.CS Ews t_ds (DOT _dyn_ltree) (ct_canon lt) sp)).
    + forward. entailer!.
      destruct (Z.eqb_spec (Znth 9 lf) 0); [rewrite e in H0; contradiction H0; reflexivity|reflexivity].
    + forward.
      { setoid_rewrite (Hz 10); [|lia]. unfold vi. tc_side. }
      setoid_rewrite (Hz 10); [|lia]. unfold vi.
      forward. entailer!.
      try (apply repr_inj_unsigned in H0; [|rep_lia|rep_lia]).
      rewrite H0. cbn [Z.eqb negb orb]. unfold bool2val.
      destruct (Z.eqb_spec (Znth 10 lf) 0); destruct (zeq (Znth 10 lf) 0); try lia; reflexivity.
    + forward_if (PROP () LOCAL (temp _t'3 (Vint (Int.repr (if (negb (Znth 9 lf =? 0) || negb (Znth 10 lf =? 0) || negb (Znth 13 lf =? 0))%bool then 1 else 0)));
        temp _s sp)
        SEP (@field_at DCS.CS Ews t_ds (DOT _dyn_ltree) (ct_canon lt) sp)).
      * forward. entailer!.
        destruct (negb (Znth 9 lf =? 0) || negb (Znth 10 lf =? 0))%bool; [reflexivity|contradiction H0; reflexivity].
      * forward.
        { setoid_rewrite (Hz 13); [|lia]. unfold vi. tc_side. }
        setoid_rewrite (Hz 13); [|lia]. unfold vi.
        forward. entailer!.
        destruct (negb (Znth 9 lf =? 0) || negb (Znth 10 lf =? 0))%bool; [discriminate|].
        cbn [orb]. unfold bool2val.
        destruct (Z.eqb_spec (Znth 13 lf) 0); destruct (zeq (Znth 13 lf) 0); try lia; reflexivity.
      * forward_if.
        -- assert (r = 1).
           { destruct (Znth 9 lf =? 0), (Znth 10 lf =? 0), (Znth 13 lf =? 0); cbn in H, H0;
               try (inversion H; reflexivity); contradiction H0; reflexivity. }
           subst r. forward. unfold ltree_at. entailer!.
        -- assert (Hz3 : Znth 9 lf =? 0 = true /\ Znth 10 lf =? 0 = true /\ Znth 13 lf =? 0 = true).
           { destruct (Znth 9 lf =? 0), (Znth 10 lf =? 0), (Znth 13 lf =? 0); cbn in H0;
               auto; exfalso; apply Int.one_not_zero; exact H0. }
           destruct Hz3 as [E9 [E10 E13]]. rewrite E9, E10, E13 in H. cbn [negb] in H.
           inv_bind H. rename x into a, Ha into Hal.
           apply -> seq_assoc. forward.
           forward_loop
             (EX n : Z,
               PROP (32 <= n <= 256; c_dd_allow (Z.to_nat (256 - n)) lf n = Some a)
               LOCAL (temp _n (Vint (Int.repr n)); temp _s sp)
               SEP (@field_at DCS.CS Ews t_ds (DOT _dyn_ltree) (ct_canon lt) sp))
             continue:
             (EX n : Z,
               PROP (32 <= n < 256; c_dd_allow (Z.to_nat (256 - (n + 1))) lf (n + 1) = Some a)
               LOCAL (temp _n (Vint (Int.repr n)); temp _s sp)
               SEP (@field_at DCS.CS Ews t_ds (DOT _dyn_ltree) (ct_canon lt) sp))
             break:
             (PROP (a = false)
               LOCAL (temp _s sp)
               SEP (@field_at DCS.CS Ews t_ds (DOT _dyn_ltree) (ct_canon lt) sp)).
           ++ Exists 32. entailer!.
           ++ Intros n. rename H1 into Hn, H2 into Hal'.
              forward_if.
              ** replace (Z.to_nat (256 - n)) with (S (Z.to_nat (256 - (n + 1)))) in Hal' by lia.
                 cbn [c_dd_allow] in Hal'. unfold LITERALS in Hal'.
                 rewrite (proj2 (Z.ltb_lt n 256) ltac:(lia)) in Hal'.
                 rewrite (dd_rd lf n Hlf' ltac:(lia)) in Hal'. cbn [bind] in Hal'.
                 pose proof (Hfr n ltac:(lia)) as Hfn.
                 forward.
                 { setoid_rewrite (Hz n); [|lia]. unfold vi. tc_side. }
                 setoid_rewrite (Hz n); [|lia]. unfold vi.
                 forward_if.
                 --- destruct (Z.eqb_spec (Znth n lf) 0) as [E|E]; [rewrite E in H2; contradiction H2; reflexivity|].
                     cbn [negb] in Hal'. inversion Hal'. subst a. inversion H. subst r.
                     forward. unfold ltree_at. entailer!.
                 --- try (apply repr_inj_unsigned in H2; [|rep_lia|rep_lia]).
                     rewrite H2 in Hal'. cbn [Z.eqb negb] in Hal'.
                     forward. Exists n. entailer!.
              ** forward. assert (n = 256) by lia. subst n. cbn in Hal'. inversion Hal'. entailer!.
           ++ Intros n. forward. Exists (n + 1). entailer!.
           ++ Intros. subst a. inversion H. subst r. forward. unfold ltree_at. entailer!.
Qed.
