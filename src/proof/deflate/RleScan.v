(** * deflate_rle: the run scan ([R_scan]). Kit: RleKit.v. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.proof.deflate.CompressKit.
Require Import Zlib.proof.deflate.RleKit.
Require Import Zlib.deflate.code.
#[export] Existing Instance DCS.CS.
Open Scope cmodel_scope.

Local Strategy opaque [loop loop2].

(** ** Pointer arithmetic in the window *)

Lemma rs_add_ptr_s (q : val) k : isptr q -> Int.min_signed <= k <= Int.max_signed ->
  force_val (sem_binary_operation' Oadd (tptr tuchar) tint q (Vint (Int.repr k))) = offset_val k q.
Proof.
  intros Hq Hk. destruct q; try contradiction. simpl.
  unfold sem_add_ptr_int. simpl. f_equal. f_equal.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one. unfold Ptrofs.of_ints. rewrite Int.signed_repr by lia. reflexivity.
Qed.

Lemma rs_win_fa q n k : field_compatible (tarray tuchar n) [] q -> 0 <= k < n ->
  offset_val k q = field_address (tarray tuchar n) [ArraySubsc k] q.
Proof.
  intros. rewrite arr_field_address by (auto; lia). simpl sizeof. f_equal. lia.
Qed.

(** [scan < strend] inside the window. *)
Lemma rs_test_order sh n vs win a b : readable_share sh -> isptr win -> 0 <= a <= n -> 0 <= b <= n -> 0 < n ->
  data_at sh (tarray tuchar n) vs win |-- denote_tc_test_order (offset_val a win) (offset_val b win).
Proof.
  intros Hsh Hp Ha Hb Hn.
  rewrite isptr_denote_tc_test_order by (apply isptr_offset_val'; auto).
  unfold test_order_ptrs. destruct win; try contradiction. simpl sameblock.
  destruct (peq b0 b0); [|congruence]. simpl.
  eapply derives_trans; [apply data_at_memory_block|].
  simpl sizeof. rewrite Z.max_r, Z.mul_1_l by lia.
  apply andp_right; [apply (memory_block_weak_valid_pointer sh n (Vptr b0 i) a) |
    apply (memory_block_weak_valid_pointer sh n (Vptr b0 i) b)]; auto; apply readable_nonidentity; auto.
Qed.

Lemma rs_lt_val n win a b : field_compatible (tarray tuchar n) [] win -> 0 <= a <= n -> 0 <= b <= n ->
  force_val (sem_cast tint tbool (eval_binop Olt (tptr tuchar) (tptr tuchar) (offset_val a win) (offset_val b win))) =
  Val.of_bool (a <? b).
Proof.
  intros Hf Ha Hb. destruct win; try (destruct Hf; contradiction).
  destruct Hf as (_ & _ & Hsz & _). simpl in Hsz. rewrite Z.max_r, Z.mul_1_l in Hsz by lia.
  pose proof (Ptrofs.unsigned_range i).
  unfold eval_binop. simpl. unfold sem_cmp_pp. simpl. rewrite peq_true. simpl.
  unfold Ptrofs.ltu, Ptrofs.add. rewrite (Ptrofs.unsigned_repr a), (Ptrofs.unsigned_repr b) by rep_lia.
  rewrite !Ptrofs.unsigned_repr by rep_lia.
  destruct (zlt _ _), (Z.ltb_spec a b); try lia; reflexivity.
Qed.

(** [mb_rd_vals] with the inhabitant VST's loads produce. *)
Lemma rs_rd_vals w k v : mb_ok w -> mb_rd w k = Some v ->
  0 <= k < Zlength (mb_val w) /\ @Znth val Vundef k (mb_vals w) = Vint (Int.repr v) /\ 0 <= v < 256.
Proof. apply mb_rd_vals. Qed.

(** ** The model, re-read for the loop invariant *)

(** The model's position inside a round of 8 comparisons starting at [i], after [c] equal comparisons. *)
Definition rs_after (s : dstate) (prev strend i c sf : Z) : Prop :=
  if c =? 8 then strend <= Zlength (mb_val (d_window s)) /\
    (if i + 8 <? strend then runs (rle_cmp_body s prev strend) (i + 8, 0) sf else sf = i + 8)
  else runs (rle_cmp_body s prev strend) (i + c, c) sf.

Lemma rs_step s prev strend i c c' sf : 0 <= c <= 7 -> c' = c + 1 -> rs_after s prev strend i c sf ->
  exists v, mb_rd (d_window s) (i + c') = Some v /\
    (prev <> v -> sf = i + c') /\ (prev = v -> rs_after s prev strend i c' sf).
Proof.
  intros Hc -> H. unfold rs_after in H.
  destruct (Z.eqb_spec c 8); [lia|].
  apply runs_inv in H.
  set (B := rle_cmp_body s prev strend) in H.
  remember (B (i + c, c)) as o eqn:Eo. unfold B, rle_cmp_body in Eo.
  rewrite <- !Z.add_assoc in Eo.
  destruct (mb_rd (d_window s) (i + (c + 1))) as [v|] eqn:E1;
    [|simpl in Eo; subst o; destruct H as [H|[? [H _]]]; discriminate].
  simpl in Eo. exists v. split; [auto|]. split.
  - intros Hn. apply Z.eqb_neq in Hn. rewrite Hn in Eo. simpl in Eo. subst o.
    destruct H as [H|[? [H _]]]; inversion H; auto.
  - intros ->. rewrite Z.eqb_refl in Eo. simpl in Eo. unfold rs_after.
    destruct (Z.eqb_spec c 7).
    + subst c. change (7 + 1) with 8 in *. simpl.
      destruct (strend <=? Zlength (mb_val (d_window s))) eqn:Eg;
        [|simpl in Eo; subst o; destruct H as [H|[? [H _]]]; discriminate].
      apply Z.leb_le in Eg. simpl in Eo. split; [exact Eg|].
      destruct (i + 8 <? strend); subst o.
      * destruct H as [H|[? [H H']]]; inversion H; subst; auto.
      * destruct H as [H|[? [H _]]]; inversion H; subst; auto.
    + destruct (Z.eqb_spec (c + 1) 8); [lia|]. subst o.
      destruct H as [H|[? [H H']]]; inversion H; subst; auto.
Qed.

Lemma rs_after_0 s prev strend i sf : runs (rle_cmp_body s prev strend) (i, 0) sf -> rs_after s prev strend i 0 sf.
Proof. unfold rs_after. simpl. rewrite !Z.add_0_r. auto. Qed.

Lemma rs_int_eq_byte v1 v2 : 0 <= v1 < 256 -> 0 <= v2 < 256 -> Int.eq (Int.repr v1) (Int.repr v2) = (v1 =? v2).
Proof.
  intros. destruct (Z.eqb_spec v1 v2).
  - subst. apply Int.eq_true.
  - apply Int.eq_false. intros E. apply repr_inj_unsigned in E; rep_lia.
Qed.

(** The join point after comparison [c] of a round (temp [t] holds the && chain so far). *)
Definition rs_JP (s : dstate) (prev strend i c sf : Z) (b : bool) (sc : Z) : Prop :=
  if b then sc = i + c /\ rs_after s prev strend i c sf else sc = sf /\ i < sf <= i + c.

Definition rs_J (s : dstate) (win : val) (prev strend i c sf : Z) (t : ident) : environ -> mpred :=
  EX b : bool, EX sc : Z,
  PROP (rs_JP s prev strend i c sf b sc)
  LOCAL (temp t (Val.of_bool b); temp _scan (offset_val sc win); temp _strend (offset_val strend win);
         temp _prev (vi prev))
  SEP (data_at Ews (tarray tuchar (Zlength (mb_val (d_window s)))) (mb_vals (d_window s)) win).

(** One comparison [++scan; t = prev == *scan] of a round, from [rs_after .. c sf] ([Ha]) with
    [scan = win + (i + c)]. *)
Ltac rs_cmp Hok s win st prev i c c' Ha :=
  let v1 := fresh "v1" in let E1 := fresh "E1" in
  let Hne := fresh "Hne" in let Heq := fresh "Heq" in
  let Hk1 := fresh "Hk1" in let Hz1 := fresh "Hz1" in let Hv1 := fresh "Hv1" in let Hq := fresh "Hq" in
  destruct (rs_step s prev (st + 258) i c c' _ ltac:(lia) eq_refl Ha) as (v1 & E1 & Hne & Heq);
  destruct (rs_rd_vals _ _ _ Hok E1) as (Hk1 & Hz1 & Hv1);
  forward; forward;
  rewrite !rs_add_ptr_s, !offset_offset_val by (auto; rep_lia);
  replace (i + c + 1) with (i + c') by lia;
  rewrite (rs_win_fa win (Zlength (mb_val (d_window s))) (i + c')) by (auto; lia);
  forward; [entailer!; rewrite Hz1; apply tc_val_tuchar_repr; lia|];
  rewrite Hz1; rewrite <- !rs_win_fa by (auto; lia);
  clear Hz1 Hk1 E1;
  forward;
  unfold rs_J; match goal with |- context [zeq ?a ?b] => destruct (zeq a b) as [Hq|Hq] end;
  [ Exists true (i + c'); entailer!; split; [reflexivity | apply Heq; auto]
  | Exists false (i + c'); entailer!; specialize (Hne Hq); unfold rs_JP; lia ].

(** The [if (t) { comparison c' } else t' = 0] step, from the join point [rs_J .. c] to [rs_J .. c']. *)
Ltac rs_join Hok s win st prev sf i c c' t' :=
  let b := fresh "b" in let sc := fresh "sc" in let Ha := fresh "Ha" in
  unfold rs_J at 1; Intros b sc;
  forward_if (rs_J s win prev (st + 258) i c' sf t');
  [ lazymatch goal with Hb : rs_JP _ _ _ _ _ _ _ _, Hc : typed_true _ _ |- _ =>
      destruct b;
      [ destruct Hb as [-> Ha]; rs_cmp Hok s win st prev i c c' Ha
      | exfalso; compute in Hc; discriminate ] end
  | lazymatch goal with Hb : rs_JP _ _ _ _ _ _ _ _, Hc : typed_false _ _ |- _ =>
      destruct b;
      [ exfalso; compute in Hc; discriminate
      | forward; unfold rs_J; Exists false sc; entailer!; unfold rs_JP in *; lia ] end
  | lazymatch goal with Hb : rs_JP _ _ _ _ _ _ _ _ |- _ => clear Hb end; clear b sc ].

(** After the test [scan < strend] of a round. *)
Definition rs_KP (s : dstate) (prev strend i sf : Z) (b : bool) (sc : Z) : Prop :=
  if b then sc = i + 8 /\ i + 8 < strend /\ runs (rle_cmp_body s prev strend) (i + 8, 0) sf
  else sc = sf /\ i < sf <= i + 8.

(** ** The do-while loop *)
Definition rs_loop := RL [0;0;1;1;1;0;1;1;1;1;1;1;1;0]%nat.

Lemma rs_loop_ok (Espec : OracleKind) (s : dstate) (win : val) (st prev sf : Z) :
  mb_ok (d_window s) ->
  field_compatible (tarray tuchar (Zlength (mb_val (d_window s)))) [] win ->
  0 <= st -> Zlength (mb_val (d_window s)) <= Int.max_unsigned -> 0 <= prev < 256 ->
  runs (rle_cmp_body s prev (st + 258)) (st + 2, 0) sf ->
  semax Delta_rle
    (PROP ()
     LOCAL (temp _scan (offset_val (st + 2) win); temp _strend (offset_val (st + 258) win); temp _prev (vi prev))
     SEP (data_at Ews (tarray tuchar (Zlength (mb_val (d_window s)))) (mb_vals (d_window s)) win))
    rs_loop
    (normal_ret_assert
      (PROP (st + 3 <= sf <= st + 258)
       LOCAL (temp _scan (offset_val sf win); temp _strend (offset_val (st + 258) win); temp _prev (vi prev))
       SEP (data_at Ews (tarray tuchar (Zlength (mb_val (d_window s)))) (mb_vals (d_window s)) win))).
Proof.
  intros Hok Hfc Hst HLu Hp Hr.
  cbv [rs_loop RL rsub f_deflate_rle fn_body].
  abbreviate_semax.
  assert_PROP (isptr win) by entailer!.
  forward_loop (EX i : Z,
    PROP (st + 2 <= i <= st + 250; (i - (st + 2)) mod 8 = 0;
          runs (rle_cmp_body s prev (st + 258)) (i, 0) sf)
    LOCAL (temp _scan (offset_val i win); temp _strend (offset_val (st + 258) win); temp _prev (vi prev))
    SEP (data_at Ews (tarray tuchar (Zlength (mb_val (d_window s)))) (mb_vals (d_window s)) win))
  break: (PROP (st + 3 <= sf <= st + 258)
       LOCAL (temp _scan (offset_val sf win); temp _strend (offset_val (st + 258) win); temp _prev (vi prev))
       SEP (data_at Ews (tarray tuchar (Zlength (mb_val (d_window s)))) (mb_vals (d_window s)) win)).
  { Exists (st + 2). entailer!. rewrite Z.sub_diag. reflexivity. }
  Intros i.
  apply rs_after_0 in H2.
  destruct (rs_step s prev (st+258) i 0 1 sf ltac:(lia) eq_refl H2) as (v1 & E1 & Hne & Heq).
  destruct (rs_rd_vals _ _ _ Hok E1) as (Hk1 & Hz1 & Hv1).
  forward. forward.
  rewrite !rs_add_ptr_s, !offset_offset_val by (auto; rep_lia).
  rewrite (rs_win_fa win (Zlength (mb_val (d_window s))) (i + 1)) by (auto; lia).
  forward; [entailer!; rewrite Hz1; apply tc_val_tuchar_repr; lia|].
  rewrite Hz1.
  rewrite <- !rs_win_fa by (auto; lia).
  clear Hz1 Hk1 E1.
  forward_if (rs_J s win prev (st + 258) i 2 sf _t'3).
  { specialize (Heq H3). rs_cmp Hok s win st prev i 1 2 Heq. }
  { forward. unfold rs_J. Exists false (i + 1). entailer!. specialize (Hne H3). unfold rs_JP. lia. }
  rs_join Hok s win st prev sf i 2 3 _t'5.
  rs_join Hok s win st prev sf i 3 4 _t'7.
  rs_join Hok s win st prev sf i 4 5 _t'9.
  rs_join Hok s win st prev sf i 5 6 _t'11.
  rs_join Hok s win st prev sf i 6 7 _t'13.
  rs_join Hok s win st prev sf i 7 8 _t'15.
  unfold rs_J at 1. Intros b sc.
  forward_if (EX b' : bool, EX sc' : Z,
    PROP (rs_KP s prev (st + 258) i sf b' sc')
    LOCAL (temp _t'17 (Val.of_bool b'); temp _scan (offset_val sc' win);
           temp _strend (offset_val (st + 258) win); temp _prev (vi prev))
    SEP (data_at Ews (tarray tuchar (Zlength (mb_val (d_window s)))) (mb_vals (d_window s)) win)).
  { destruct b; [|exfalso; compute in H4; discriminate].
    destruct H3 as [-> Ha].
    unfold rs_after in Ha. simpl in Ha. destruct Ha as [Hg Ha].
    forward.
    { entailer!. apply rs_test_order; auto; lia. }
    rewrite (rs_lt_val (Zlength (mb_val (d_window s)))) by (auto; lia).
    destruct (Z.ltb_spec (i + 8) (st + 258)).
    - Exists true (i + 8). entailer!; unfold rs_KP; repeat split; auto; try lia.
    - Exists false (i + 8). entailer!; unfold rs_KP; repeat split; auto; try lia. }
  { destruct b; [exfalso; compute in H4; discriminate|].
    forward. Exists false sc. entailer!; unfold rs_JP, rs_KP in *; lia. }
  clear b sc H3.
  Intros b' sc'. rename H3 into Hk.
  forward_if.
  - match goal with Hc : typed_true _ _ |- _ => destruct b'; [|exfalso; compute in Hc; discriminate] end.
    destruct Hk as (-> & Hlt & Hr').
    apply Z.mod_divide in H1; [|lia]. destruct H1 as [k Hk].
    forward. Exists (i + 8). entailer!.
    replace (i + 8 - (st + 2)) with ((k + 1) * 8) by lia. apply Z_mod_mult.
  - match goal with Hc : typed_false _ _ |- _ => destruct b'; [exfalso; compute in Hc; discriminate|] end.
    unfold rs_KP in Hk. destruct Hk as [-> Hk].
    forward. entailer!.
Qed.

(** The variables the loop modifies, computed once. *)
Definition rs_mods : Maps.PTree.t unit := ltac:(let x := eval vm_compute in (modifiedvars' rs_loop idset0) in exact x).

Lemma rs_mods_eq : modifiedvars' rs_loop idset0 = rs_mods.
Proof. vm_compute. reflexivity. Qed.

(** [rs_loop_ok] with a frame of further locals and resources. *)
Lemma rs_loop_framed (Espec : OracleKind) (s : dstate) (win : val) (st prev sf : Z) Q2 R2 :
  mb_ok (d_window s) ->
  field_compatible (tarray tuchar (Zlength (mb_val (d_window s)))) [] win ->
  0 <= st -> Zlength (mb_val (d_window s)) <= Int.max_unsigned -> 0 <= prev < 256 ->
  runs (rle_cmp_body s prev (st + 258)) (st + 2, 0) sf ->
  closed_wrt_vars (fun i => isSome (Maps.PTree.get i rs_mods)) (LOCALx Q2 (SEPx R2)) ->
  semax Delta_rle
    (PROPx []
     (LOCALx (temp _scan (offset_val (st + 2) win) :: temp _strend (offset_val (st + 258) win) ::
              temp _prev (vi prev) :: Q2)
     (SEPx (data_at Ews (tarray tuchar (Zlength (mb_val (d_window s)))) (mb_vals (d_window s)) win :: R2))))
    rs_loop
    (normal_ret_assert
      (PROPx [st + 3 <= sf <= st + 258]
       (LOCALx (temp _scan (offset_val sf win) :: temp _strend (offset_val (st + 258) win) ::
                temp _prev (vi prev) :: Q2)
       (SEPx (data_at Ews (tarray tuchar (Zlength (mb_val (d_window s)))) (mb_vals (d_window s)) win :: R2))))).
Proof.
  intros Hok Hfc Hst HLu Hp Hr Hcl0.
  assert (Hcl : closed_wrt_modvars rs_loop (LOCALx Q2 (SEPx R2))).
  { unfold closed_wrt_modvars, modifiedvars. rewrite rs_mods_eq. exact Hcl0. }
  apply (semax_frame_PQR Q2 R2 Espec _
          [data_at Ews (tarray tuchar (Zlength (mb_val (d_window s)))) (mb_vals (d_window s)) win] []
          [temp _scan (offset_val (st + 2) win); temp _strend (offset_val (st + 258) win); temp _prev (vi prev)]
          [st + 3 <= sf <= st + 258]
          [temp _scan (offset_val sf win); temp _strend (offset_val (st + 258) win); temp _prev (vi prev)]
          [data_at Ews (tarray tuchar (Zlength (mb_val (d_window s)))) (mb_vals (d_window s)) win]); auto.
  apply rs_loop_ok; auto.
Qed.

(** ** The model of the scan, re-read *)

(** After the three first comparisons succeeded. *)
Definition rs_tail (s : dstate) (prev : Z) : option dstate :=
  let strend := d_strstart s + MAX_MATCH in
  let* scan := loop FUEL (rle_cmp_body s prev strend) (d_strstart s - 1 + 3, 0) in
  let s := set_d_match_length s (u32 (MAX_MATCH - u32 (strend - scan))) in
  Some (if d_match_length s >? d_lookahead s then set_d_match_length s (d_lookahead s) else s).

Definition rs_K3 (s s' : dstate) (prev : Z) : Prop :=
  exists c3, mb_rd (d_window s) (d_strstart s + 2) = Some c3 /\ (prev <> c3 -> s' = s) /\
    (prev = c3 -> rs_tail s prev = Some s').

Definition rs_K2 (s s' : dstate) (prev : Z) : Prop :=
  exists c2, mb_rd (d_window s) (d_strstart s + 1) = Some c2 /\ (prev <> c2 -> s' = s) /\
    (prev = c2 -> rs_K3 s s' prev).

Definition rs_P1 (s s' : dstate) (prev : Z) (b : bool) (sc : Z) : Prop :=
  if b then sc = d_strstart s + 1 /\ rs_K3 s s' prev else s' = s.

Definition rs_P2 (s s' : dstate) (prev : Z) (b : bool) (sc : Z) : Prop :=
  if b then sc = d_strstart s + 2 /\ rs_tail s prev = Some s' else s' = s.

(** The join points of the three first comparisons. *)
Definition rs_H (s s' : dstate) (prev : Z) (p : dptrs) (gv : globals) (flush : Z) (F : mpred)
    (Pr : dstate -> dstate -> Z -> bool -> Z -> Prop) (t : ident) : environ -> mpred :=
  @exp (environ -> mpred) _ bool (fun b => @exp (environ -> mpred) _ Z (fun sc =>
  PROP (Pr s s' prev b sc)
  LOCAL (temp t (Val.of_bool b); temp _scan (offset_val sc (p_window p)); temp _prev (Vint (Int.repr prev));
         gvars gv; temp _s (p_s p); temp _flush (vi flush))
  SEP (F; field_at Ews t_ds (DOT _window) (p_window p) (p_s p);
       data_at Ews (tarray tuchar (Zlength (mb_val (d_window s)))) (mb_vals (d_window s)) (p_window p);
       field_at Ews t_ds (DOT _match_length) (vi (d_match_length s)) (p_s p);
       field_at Ews t_ds (DOT _strstart) (vi (d_strstart s)) (p_s p);
       field_at Ews t_ds (DOT _lookahead) (vi (d_lookahead s)) (p_s p)))).

Lemma rs_head s s' : rle_scan_m s = Some s' -> 3 <= d_lookahead s -> 0 < d_strstart s ->
  exists prev, mb_rd (d_window s) (d_strstart s - 1) = Some prev /\
  exists c1, mb_rd (d_window s) (d_strstart s) = Some c1 /\ (prev <> c1 -> s' = s) /\
    (prev = c1 -> rs_K2 s s' prev).
Proof.
  intros H Hl Hs. unfold rle_scan_m in H.
  rewrite (proj2 (Z.geb_le (d_lookahead s) MIN_MATCH) ltac:(unfold MIN_MATCH; lia)) in H.
  rewrite (proj2 (Z.gtb_lt (d_strstart s) 0) Hs) in H. simpl in H.
  destruct (mb_rd (d_window s) (d_strstart s - 1)) as [prev|] eqn:E0; [|discriminate]. simpl in H.
  exists prev. split; [first [reflexivity|assumption]|].
  replace (d_strstart s - 1 + 1) with (d_strstart s) in H by lia.
  destruct (mb_rd (d_window s) (d_strstart s)) as [c1|] eqn:E1; [|discriminate]. simpl in H.
  exists c1. split; [first [reflexivity|assumption]|]. split.
  { intros Hn. apply Z.eqb_neq in Hn. rewrite Hn in H. simpl in H. congruence. }
  intros <-. rewrite Z.eqb_refl in H. simpl in H.
  replace (d_strstart s - 1 + 2) with (d_strstart s + 1) in H by lia.
  destruct (mb_rd (d_window s) (d_strstart s + 1)) as [c2|] eqn:E2; [|discriminate]. simpl in H.
  exists c2. split; [first [reflexivity|assumption]|]. split.
  { intros Hn. apply Z.eqb_neq in Hn. rewrite Hn in H. simpl in H. congruence. }
  intros <-. rewrite Z.eqb_refl in H. simpl in H.
  replace (d_strstart s - 1 + 3) with (d_strstart s + 2) in H at 1 by lia.
  destruct (mb_rd (d_window s) (d_strstart s + 2)) as [c3|] eqn:E3; [|discriminate]. simpl in H.
  exists c3. split; [first [reflexivity|assumption]|]. split.
  { intros Hn. apply Z.eqb_neq in Hn. rewrite Hn in H. simpl in H. congruence. }
  intros <-. rewrite Z.eqb_refl in H. simpl in H. exact H.
Qed.

Lemma rs_noscan s s' : rle_scan_m s = Some s' -> ~ (3 <= d_lookahead s /\ 0 < d_strstart s) -> s' = s.
Proof.
  intros H Hn. unfold rle_scan_m in H.
  destruct (d_lookahead s >=? MIN_MATCH) eqn:E1; [destruct (d_strstart s >? 0) eqn:E2|].
  - exfalso. apply Hn. unfold MIN_MATCH in E1. split; lia.
  - simpl in H. congruence.
  - simpl in H. congruence.
Qed.

Lemma rs_add_ptr_u (q : val) k : isptr q ->
  force_val (sem_binary_operation' Oadd (tptr tuchar) tuint q (Vint (Int.repr k))) = offset_val (u32 k) q.
Proof.
  intros Hq. destruct q; try contradiction. simpl.
  unfold sem_add_ptr_int. simpl. f_equal. f_equal.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one. unfold Ptrofs.of_intu, Ptrofs.of_int.
  rewrite Int.unsigned_repr_eq. reflexivity.
Qed.

Lemma rs_add_ptr_u' (q : val) k : isptr q -> 0 <= k <= Int.max_unsigned ->
  eval_binop Oadd (tptr tuchar) tuint q (vi k) = offset_val k q.
Proof.
  intros Hq Hk. destruct q; try contradiction. simpl. unfold sem_add_ptr_int. simpl. f_equal. f_equal.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one. unfold Ptrofs.of_intu, Ptrofs.of_int.
  rewrite Int.unsigned_repr by auto. reflexivity.
Qed.

Lemma rs_sub_ptr_1 (q : val) a : isptr q ->
  force_val (sem_binary_operation' Osub (tptr tuchar) tint (offset_val a q) (Vint (Int.repr 1))) = offset_val (a - 1) q.
Proof.
  intros Hq. destruct q; try contradiction. simpl.
  unfold sem_sub, sem_sub_pi. simpl. f_equal. unfold Ptrofs.of_ints. rewrite Int.signed_repr by rep_lia.
  rewrite Ptrofs.mul_one. rewrite Ptrofs.sub_add_opp, Ptrofs.add_assoc, <- Ptrofs.sub_add_opp. f_equal.
  unfold Ptrofs.sub. apply Ptrofs.eqm_samerepr. apply Ptrofs.eqm_sub; apply Ptrofs.eqm_sym, Ptrofs.eqm_unsigned_repr.
Qed.

Lemma rs_sameblock (q : val) a b : isptr q -> is_true (sameblock (offset_val a q) (offset_val b q)).
Proof. intros Hq. destruct q; try contradiction. simpl. destruct (peq b0 b0); [reflexivity|congruence]. Qed.

Lemma rs_ml_val (q : val) st sf : isptr q -> 0 <= st + 258 - sf <= 258 ->
  force_val (sem_cast_i2i I32 Unsigned (force_val (sem_sub_default tint tuint (Vint (Int.repr 258))
    (force_val (sem_cast_l2i I32 Unsigned (force_val (sem_sub_pp tuchar (offset_val (st + 258) q)
      (offset_val sf q)))))))) = Vint (Int.repr (sf - st)).
Proof.
  intros Hq Hr. destruct q; try contradiction. simpl.
  unfold sem_sub_pp. simpl. rewrite peq_true. simpl.
  rewrite !(Ptrofs.add_commut i), Ptrofs.sub_shifted.
  replace (Ptrofs.sub (Ptrofs.repr (st + 258)) (Ptrofs.repr sf)) with (Ptrofs.repr (st + 258 - sf)).
  2: { unfold Ptrofs.sub. apply Ptrofs.eqm_samerepr. apply Ptrofs.eqm_sub; apply Ptrofs.eqm_unsigned_repr. }
  change (Ptrofs.repr 1) with Ptrofs.one. rewrite Ptrofs.divs_one by (compute; reflexivity).
  rewrite Ptrofs.unsigned_repr by rep_lia.
  rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia.
  unfold Int.sub. rewrite !Int.unsigned_repr by rep_lia. f_equal. f_equal. lia.
Qed.

Lemma rs_ranges s m : dstate_ranges s -> 0 <= m <= Int.max_unsigned -> dstate_ranges (set_d_match_length s m).
Proof.
  intros Hs Hm. unfold dstate_ranges, u32_ok, u64_ok, s32_ok, s64_ok in *. dsimpl.
  decompose [and] Hs.
  repeat match goal with |- _ /\ _ => split end; try assumption; lia.
Qed.

Lemma rle_scan_ok : rle_scan_stmt.
Proof.
  intros Espec p pin pout ish R msgv gv flush s s' z Hm.
  unfold R_scan. cbv [RL rsub f_deflate_rle fn_body].
  unfold dfull, dstate_at. Intros. abbreviate_semax.
  unfold match_at, win_at. Intros.
  assert (Hla : 0 <= d_lookahead s <= Int.max_unsigned) by drange.
  assert (Hss : 0 <= d_strstart s <= Int.max_unsigned) by drange.
  assert (Hwok : mb_ok (d_window s)) by (open_dranges H2; assumption).
  pose proof (Zlength_mb_vals _ Hwok) as Hwl.
  forward.
  apply semax_if_seq. forward_if.
  - try rewrite Int.unsigned_repr in H3 by lia.
    forward. forward.
    forward_if.
    + (* the scan *)
      assert (Hst : 0 < d_strstart s) by (destruct (zlt 0 (d_strstart s)); [lia|discriminate]).
      destruct (rs_head s s' Hm ltac:(lia) Hst) as (prev & E0 & c1 & E1 & Hne1 & Heq1).
      destruct (rs_rd_vals _ _ _ Hwok E0) as (Hk0 & Hz0 & Hv0).
      assert_PROP (field_compatible (tarray tuchar (Zlength (mb_val (d_window s)))) [] (p_window p)) as Hfc
        by entailer!.
      assert (Hwp : isptr (p_window p)) by (destruct Hfc; auto).
      forward. forward. forward.
      rewrite rs_add_ptr_u', rs_sub_ptr_1 by (auto; lia).
      rewrite (rs_win_fa (p_window p) (Zlength (mb_val (d_window s))) (d_strstart s - 1)) by (auto; lia).
      forward; [entailer!; rewrite Hz0; apply tc_val_tuchar_repr; lia|].
      rewrite Hz0. rewrite <- rs_win_fa by (auto; lia).
      freeze [0;2;3;4;5;6;8;9;11;12;14;16;17;18;19;20;21;22;23;24] FR.
      (* prev == *++scan *)
      destruct (rs_rd_vals _ _ _ Hwok E1) as (Hk1 & Hz1 & Hv1).
      forward. forward.
      rewrite rs_add_ptr_s, offset_offset_val by (auto; rep_lia).
      replace (d_strstart s - 1 + 1) with (d_strstart s) by lia.
      rewrite (rs_win_fa (p_window p) (Zlength (mb_val (d_window s))) (d_strstart s)) by (auto; lia).
      forward; [entailer!; rewrite Hz1; apply tc_val_tuchar_repr; lia|].
      rewrite Hz1. rewrite <- rs_win_fa by (auto; lia).
      forward_if (rs_H s s' prev p gv flush (FRZL FR) rs_P1 _t'19).
      { destruct (Heq1 H5) as (c2 & E2 & Hne2 & Heq2).
        destruct (rs_rd_vals _ _ _ Hwok E2) as (Hk2 & Hz2 & Hv2).
        forward. forward.
        rewrite rs_add_ptr_s, offset_offset_val by (auto; rep_lia).
        rewrite (rs_win_fa (p_window p) (Zlength (mb_val (d_window s))) (d_strstart s + 1)) by (auto; lia).
        forward; [entailer!; rewrite Hz2; apply tc_val_tuchar_repr; lia|].
        rewrite Hz2. rewrite <- rs_win_fa by (auto; lia).
        forward.
        destruct (zeq prev c2) as [Hq|Hq].
        - unfold rs_H. Exists true (d_strstart s + 1). entailer!; unfold rs_P1, rs_P2 in *; auto.
        - unfold rs_H. Exists false (d_strstart s + 1). entailer!; unfold rs_P1, rs_P2 in *; auto. }
      { forward. unfold rs_H. Exists false (d_strstart s). entailer!; unfold rs_P1, rs_P2 in *; auto. }
      (* && prev == *++scan *)
      unfold rs_H at 1. Intros b sc. rename H5 into HP.
      forward_if (rs_H s s' prev p gv flush (FRZL FR) rs_P2 _t'21).
      { destruct b; [|exfalso; match goal with Hc : typed_true _ _ |- _ => compute in Hc; discriminate end].
        destruct HP as [-> (c3 & E3 & Hne3 & Heq3)].
        destruct (rs_rd_vals _ _ _ Hwok E3) as (Hk3 & Hz3 & Hv3).
        forward. forward.
        rewrite rs_add_ptr_s, offset_offset_val by (auto; rep_lia).
        replace (d_strstart s + 1 + 1) with (d_strstart s + 2) by lia.
        rewrite (rs_win_fa (p_window p) (Zlength (mb_val (d_window s))) (d_strstart s + 2)) by (auto; lia).
        forward; [entailer!; rewrite Hz3; apply tc_val_tuchar_repr; lia|].
        rewrite Hz3. rewrite <- rs_win_fa by (auto; lia).
        forward.
        destruct (zeq prev c3) as [Hq|Hq].
        - unfold rs_H. Exists true (d_strstart s + 2). entailer!; unfold rs_P1, rs_P2 in *; auto.
        - unfold rs_H. Exists false (d_strstart s + 2). entailer!; unfold rs_P1, rs_P2 in *; auto. }
      { destruct b; [exfalso; match goal with Hc : typed_false _ _ |- _ => compute in Hc; discriminate end|].
        forward. unfold rs_H. Exists false sc. entailer!; unfold rs_P1, rs_P2 in *; auto. }
      clear b sc HP. unfold rs_H at 1. Intros b sc. rename H5 into HP.
      forward_if.
      2: { destruct b; [exfalso; match goal with Hc : typed_false _ _ |- _ => compute in Hc; discriminate end|].
           unfold rs_P2 in HP. subst s'.
           forward. thaw FR. unfold dfull, dstate_at, match_at, win_at. entailer!. }
      destruct b; [|exfalso; match goal with Hc : typed_true _ _ |- _ => compute in Hc; discriminate end].
      destruct HP as [-> Htail].
      unfold rs_tail in Htail. inv_bind Htail. rename x into sf, Ha into Hl. apply loop_runs in Hl.
      forward. forward. forward.
      rewrite rs_add_ptr_u', rs_add_ptr_s, offset_offset_val by (auto; rep_lia).
      replace (d_strstart s - 1 + 3) with (d_strstart s + 2) in Hl by lia. unfold MAX_MATCH in Hl.
      assert (HwL : Zlength (mb_val (d_window s)) <= Int.max_unsigned) by drange.
      match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx (?a :: ?b :: _ :: ?rest)))) _ _ =>
        eapply semax_seq';
        [ eapply semax_pre; [ | eapply (rs_loop_framed Espec s (p_window p) (d_strstart s) prev sf
             [gvars gv; temp _s (p_s p); temp _flush (vi flush)] (a :: b :: rest)) ] | ] end.
      { entailer!. }
      all: auto; try lia; try (auto 50 with closed).
      abbreviate_semax. Intros.
      forward.
      { entailer!. apply prop_right. apply rs_sameblock; auto. }
      rewrite rs_ml_val by (auto; lia).
      assert (Em : u32 (MAX_MATCH - u32 (d_strstart s + MAX_MATCH - sf)) = sf - d_strstart s).
      { unfold MAX_MATCH. rewrite (u32_small (d_strstart s + 258 - sf)) by rep_lia.
        rewrite u32_small by rep_lia. lia. }
      rewrite Em in Htail. dsimpl in Htail. inversion Htail as [Es']. clear Htail.
      forward. forward.
      forward_if.
      * forward. forward.
        try rewrite !Int.unsigned_repr in H7 by rep_lia.
        rewrite Z.gtb_ltb, (proj2 (Z.ltb_lt (d_lookahead s) (sf - d_strstart s)) ltac:(lia)) in Es'. subst s'.
        pose proof (rs_ranges s (d_lookahead s) H2 Hla) as Hr.
        thaw FR. unfold dfull, dstate_at, match_at, win_at, hash_at, cfg_at, stat_at. dsimpl.
        entailer!; try apply derives_refl.
      * forward.
        try rewrite !Int.unsigned_repr in H7 by rep_lia.
        rewrite Z.gtb_ltb, (proj2 (Z.ltb_ge (d_lookahead s) (sf - d_strstart s)) ltac:(lia)) in Es'. subst s'.
        pose proof (rs_ranges s (sf - d_strstart s) H2 ltac:(rep_lia)) as Hr.
        thaw FR. unfold dfull, dstate_at, match_at, win_at, hash_at, cfg_at, stat_at. dsimpl.
        entailer!; try apply derives_refl.
    + assert (s' = s) by (apply (rs_noscan s s' Hm); intros [_ Hc]; destruct (zlt 0 (d_strstart s)); [discriminate|lia]).
      subst s'. forward. unfold dfull, dstate_at, match_at, win_at. entailer!.
  - assert (s' = s) by (apply (rs_noscan s s' Hm); intros [Hc _]; try rewrite Int.unsigned_repr in H3 by lia; lia).
    subst s'. forward. forward_if.
    { exfalso. lia. }
    forward. unfold dfull, dstate_at, match_at, win_at. entailer!.
Qed.
