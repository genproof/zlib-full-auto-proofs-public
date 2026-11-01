(** * build_tree before gen_bitlen: initialisation, forced nodes, heapify, merge loop *)

From Coq Require Import ZArith List Lia Bool Permutation.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.huffman.Model Zlib.proof.huffman.HuffAbs Zlib.proof.huffman.Heap
               Zlib.proof.huffman.BuildTree Zlib.proof.huffman.BuildKids.
Import ListNotations.
Local Open Scope Z_scope.

(** ** Initialisation: bt_init, bt_force, bt_heapify *)

Definition nzl (fr : list Z) (n : Z) : list Z := filter (fun i => negb (Znth i fr =? 0)) (zseq 0 (Z.to_nat n)).

Lemma nzl_succ : forall fr n, 0 <= n ->
  nzl fr (n + 1) = nzl fr n ++ (if negb (Znth n fr =? 0) then [n] else []).
Proof.
  intros fr n Hn. unfold nzl. replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)) by lia.
  rewrite zseq_succ_r, filter_app. cbn [filter]. replace (0 + Z.of_nat (Z.to_nat n)) with n by lia.
  destruct (negb (Znth n fr =? 0)); reflexivity.
Qed.

Lemma reg_snoc : forall heap len x, 0 <= len -> len + 1 < Zlength heap ->
  reg (upd_Znth (len + 1) heap x) (len + 1) = reg heap len ++ [x].
Proof.
  intros heap len x H0 HL. unfold reg. replace (Z.to_nat (len + 1)) with (S (Z.to_nat len)) by lia.
  rewrite zseq_succ_r, map_app. cbn [map]. replace (1 + Z.of_nat (Z.to_nat len)) with (len + 1) by lia.
  rewrite upd_Znth_same by lia. f_equal. apply map_zseq_ext. intros i Hi. rewrite upd_Znth_diff by lia. reflexivity.
Qed.

Lemma in_nzl : forall fr n i, In i (nzl fr n) <-> 0 <= i < n /\ Znth i fr <> 0.
Proof.
  intros. unfold nzl. rewrite filter_In, in_zseq, negb_true_iff, Z.eqb_neq. lia.
Qed.

Lemma nzl_nodup : forall fr n, NoDup (nzl fr n).
Proof. intros. apply NoDup_filter, zseq_nodup. Qed.

Lemma zseq_length : forall n a, length (zseq a n) = n.
Proof. induction n; intros; simpl; auto. Qed.

Lemma nzl_len : forall fr n, 0 <= n -> 0 <= Zlength (nzl fr n) <= n.
Proof.
  intros fr n Hn. split; [apply Zlength_nonneg|]. unfold nzl. rewrite Zlength_correct.
  assert (H := filter_length_le (fun i => negb (Znth i fr =? 0)) (zseq 0 (Z.to_nat n))).
  rewrite zseq_length in H. lia.
Qed.

Definition init_push (w : work) (n : Z) : work :=
  w_set_depth (w_set_heap (w_set_heap_len w (w_heap_len w + 1)) (upd_Znth (w_heap_len w + 1) (w_heap w) n))
              (upd_Znth n (w_depth w) 0).

Lemma bt_init_step : forall f elems t w mc n,
  bt_init (S f) elems t w mc n =
  if n <? elems then
    if negb (Znth n (fc t) =? 0) then bt_init f elems t (init_push w n) n (n + 1)
    else bt_init f elems (set_dl t n 0) w mc (n + 1)
  else (t, w, mc).
Proof. reflexivity. Qed.

Lemma bt_init_spec : forall elems fuel t w mc n,
  0 <= n <= elems -> elems <= Z.of_nat fuel + n -> elems < 573 ->
  Zlength (w_heap w) = HEAP_SIZE -> Zlength (w_depth w) = HEAP_SIZE -> elems <= Zlength (dl t) ->
  w_heap_len w = Zlength (nzl (fc t) n) -> reg (w_heap w) (w_heap_len w) = nzl (fc t) n ->
  (forall i, 0 <= i < n -> Znth i (fc t) = 0 -> Znth i (dl t) = 0) ->
  (mc = -1 /\ nzl (fc t) n = [] \/ In mc (nzl (fc t) n) /\ forall i, In i (nzl (fc t) n) -> i <= mc) ->
  let '(t', w', mc') := bt_init fuel elems t w mc n in
  fc t' = fc t /\ Zlength (dl t') = Zlength (dl t) /\
  w_heap_len w' = Zlength (nzl (fc t) elems) /\ reg (w_heap w') (w_heap_len w') = nzl (fc t) elems /\
  w_heap_max w' = w_heap_max w /\ w_bl_count w' = w_bl_count w /\ w_opt_len w' = w_opt_len w /\
  w_static_len w' = w_static_len w /\ Zlength (w_heap w') = HEAP_SIZE /\ Zlength (w_depth w') = HEAP_SIZE /\
  (forall i, 0 <= i < elems -> Znth i (fc t) = 0 -> Znth i (dl t') = 0) /\
  (mc' = -1 /\ nzl (fc t) elems = [] \/ In mc' (nzl (fc t) elems) /\ forall i, In i (nzl (fc t) elems) -> i <= mc').
Proof.
  intros elems fuel. induction fuel as [|fuel IH]; intros t w mc n Hn Hf H573 Hh Hd Hdl Hlen Hreg Hz Hmc.
  - simpl. assert (n = elems) by lia. subst n.
    repeat split; auto; try lia.
  - rewrite bt_init_step. destruct (Z.ltb_spec n elems) as [Hlt|Hge].
    + assert (Hnz := nzl_succ (fc t) n ltac:(lia)).
      assert (HnL := nzl_len (fc t) n ltac:(lia)).
      destruct (negb (Znth n (fc t) =? 0)) eqn:Ez.
      * apply negb_true_iff, Z.eqb_neq in Ez.
        remember (init_push w n) as w' eqn:Ew'.
        assert (Hlen0 : 0 <= w_heap_len w <= n) by lia.
        specialize (IH t w' n (n + 1)).
        destruct (bt_init fuel elems t w' n (n + 1)) as [[t' w''] mc'] eqn:E.
        destruct IH as [I1 [I2 [I3 [I4 [I5 [I6 [I7 [I8 [I9 [I10 [I11 I12]]]]]]]]]]]; try lia.
        -- subst w'; unfold init_push; simpl. rewrite Zlength_upd. exact Hh.
        -- subst w'; unfold init_push; simpl. rewrite Zlength_upd. exact Hd.
        -- subst w'; unfold init_push; simpl. rewrite Hnz, Zlength_app, <- Hlen. change (Zlength [n]) with 1. lia.
        -- subst w'; unfold init_push; simpl. rewrite reg_snoc by (unfold HEAP_SIZE in *; lia).
           rewrite Hreg, Hnz. reflexivity.
        -- intros i Hi Hfi. destruct (Z.eq_dec i n) as [->|Hin]; [contradiction|]. apply Hz; auto; lia.
        -- right. rewrite Hnz. split; [apply in_or_app; right; left; auto|].
           intros i Hi. apply in_app_or in Hi. destruct Hi as [Hi|[<-|[]]]; [|lia].
           apply in_nzl in Hi. lia.
        -- subst w'; unfold init_push in *; simpl in *. repeat split; auto.
      * apply negb_false_iff, Z.eqb_eq in Ez.
        specialize (IH (set_dl t n 0) w mc (n + 1)).
        destruct (bt_init fuel elems (set_dl t n 0) w mc (n + 1)) as [[t' w''] mc'] eqn:E.
        unfold set_dl in IH, E |- *. simpl in IH.
        destruct IH as [I1 [I2 [I3 [I4 [I5 [I6 [I7 [I8 [I9 [I10 [I11 I12]]]]]]]]]]]; try lia; auto.
        -- simpl. rewrite Zlength_upd. lia.
        -- rewrite Hnz, app_nil_r. exact Hlen.
        -- rewrite Hnz, app_nil_r. exact Hreg.
        -- intros i Hi Hfi. simpl. destruct (Z.eq_dec i n) as [->|Hin].
           ++ rewrite upd_Znth_same by lia. reflexivity.
           ++ rewrite upd_Znth_diff by lia. apply Hz; auto; lia.
        -- rewrite Hnz, app_nil_r. exact Hmc.
        -- repeat split; auto. rewrite I2. simpl. apply Zlength_upd.
    + simpl. assert (n = elems) by lia. subst n.
      repeat split; auto; try lia.
Qed.

(** bt_force: at most two forced nodes of frequency 1. *)
Definition force_push (sd : stat_desc) (w : work) (node : Z) : work :=
  let w := w_set_depth (w_set_heap (w_set_heap_len w (w_heap_len w + 1)) (upd_Znth (w_heap_len w + 1) (w_heap w) node))
                       (upd_Znth node (w_depth w) 0) in
  let w := w_set_opt_len w (u64 (w_opt_len w - 1)) in
  match sd_stree sd with
  | Some stree => w_set_static_len w (u64 (w_static_len w - Znth node stree))
  | None => w
  end.

Definition force_node (mc : Z) : Z * Z := if mc <? 2 then (mc + 1, mc + 1) else (0, mc).

Lemma force_node_lt : forall mc, mc < 2 -> force_node mc = (mc + 1, mc + 1).
Proof. intros. unfold force_node. replace (mc <? 2) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.
Lemma force_node_ge : forall mc, 2 <= mc -> force_node mc = (0, mc).
Proof. intros. unfold force_node. replace (mc <? 2) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. Qed.

Lemma bt_force_step : forall f sd t w mc,
  bt_force (S f) sd t w mc =
  if w_heap_len w <? 2 then
    bt_force f sd (set_fc t (fst (force_node mc)) 1) (force_push sd w (fst (force_node mc))) (snd (force_node mc))
  else (t, w, mc).
Proof. intros. unfold force_node. simpl. destruct (w_heap_len w <? 2); [|reflexivity].
  destruct (mc <? 2); reflexivity. Qed.

Lemma force_push_fields : forall sd w node,
  w_heap (force_push sd w node) = upd_Znth (w_heap_len w + 1) (w_heap w) node /\
  w_heap_len (force_push sd w node) = w_heap_len w + 1 /\
  w_heap_max (force_push sd w node) = w_heap_max w /\
  w_depth (force_push sd w node) = upd_Znth node (w_depth w) 0 /\
  w_bl_count (force_push sd w node) = w_bl_count w /\
  w_opt_len (force_push sd w node) = u64 (w_opt_len w - 1) /\
  w_static_len (force_push sd w node) =
    match sd_stree sd with Some stree => u64 (w_static_len w - Znth node stree) | None => w_static_len w end.
Proof. intros. unfold force_push. destruct (sd_stree sd); simpl; repeat split; reflexivity. Qed.

Lemma u64_sub_sub : forall a b c, u64 (u64 (a - b) - c) = u64 (a - b - c).
Proof. intros. unfold u64. rewrite Zminus_mod_idemp_l. reflexivity. Qed.

Lemma reg_len : forall heap len, 0 <= len -> Zlength (reg heap len) = len.
Proof. intros. unfold reg. rewrite Zlength_correct, length_map, zseq_length. lia. Qed.

Lemma bt_force_spec : forall sd t w mc,
  3 <= sd_elems sd <= 286 ->
  Zlength (w_heap w) = HEAP_SIZE -> Zlength (w_depth w) = HEAP_SIZE -> sd_elems sd <= Zlength (fc t) ->
  0 <= w_heap_len w ->
  0 <= w_opt_len w < 18446744073709551616 -> 0 <= w_static_len w < 18446744073709551616 ->
  NoDup (reg (w_heap w) (w_heap_len w)) ->
  (forall x, In x (reg (w_heap w) (w_heap_len w)) -> 0 <= x < sd_elems sd /\ Znth x (fc t) <> 0) ->
  (forall x, 0 <= x < sd_elems sd -> Znth x (fc t) <> 0 -> In x (reg (w_heap w) (w_heap_len w))) ->
  (mc = -1 /\ reg (w_heap w) (w_heap_len w) = [] \/
   In mc (reg (w_heap w) (w_heap_len w)) /\ forall i, In i (reg (w_heap w) (w_heap_len w)) -> i <= mc) ->
  let Z0 := reg (w_heap w) (w_heap_len w) in
  let '(t', w', mc') := bt_force 2 sd t w mc in
  exists F, reg (w_heap w') (w_heap_len w') = Z0 ++ F /\ 2 <= w_heap_len w' /\
    (2 <= w_heap_len w -> F = []) /\ Zlength F <= 2 /\
    NoDup (Z0 ++ F) /\ (forall x, In x F -> 0 <= x < sd_elems sd /\ Znth x (fc t) = 0) /\
    (forall x, Znth x (fc t') = if in_dec Z.eq_dec x F then 1 else Znth x (fc t)) /\
    dl t' = dl t /\ Zlength (fc t') = Zlength (fc t) /\
    In mc' (Z0 ++ F) /\ (forall i, In i (Z0 ++ F) -> i <= mc') /\
    w_opt_len w' = u64 (w_opt_len w - Zlength F) /\
    w_static_len w' = (match sd_stree sd with
                       | Some stree => u64 (w_static_len w - sumZ (map (fun x => Znth x stree) F))
                       | None => w_static_len w end) /\
    w_heap_max w' = w_heap_max w /\ w_bl_count w' = w_bl_count w /\
    Zlength (w_heap w') = HEAP_SIZE /\ Zlength (w_depth w') = HEAP_SIZE /\
    (forall x, In x F -> Znth x (w_depth w') = 0).
Proof.
  intros sd t w mc Hel Hh Hd Hfc Hl0 Hol Hsl Hnd Hz Hall Hmc Z0.
  assert (HZ0 : Zlength Z0 = w_heap_len w) by (apply reg_len; lia).
  destruct (Z_lt_ge_dec (w_heap_len w) 2) as [Hlt|Hge].
  2:{ rewrite bt_force_step. replace (w_heap_len w <? 2) with false by (symmetry; apply Z.ltb_ge; lia).
      assert (Hmc' : In mc Z0 /\ forall i, In i Z0 -> i <= mc).
      { destruct Hmc as [[_ Hm]|Hm]; [|exact Hm]. exfalso. fold Z0 in Hm. rewrite Hm, Zlength_nil in HZ0. lia. }
      exists []. rewrite app_nil_r. split; [reflexivity|]. split; [lia|]. split; [auto|].
      split; [rewrite Zlength_nil; lia|]. split; [exact Hnd|]. split; [intros x []|].
      split; [intros x; destruct (in_dec Z.eq_dec x []) as [[]|]; reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [apply Hmc'|]. split; [apply Hmc'|].
      split; [unfold u64; rewrite Z.sub_0_r; symmetry; apply Z.mod_small; lia|].
      split; [destruct (sd_stree sd); auto; simpl; unfold u64; rewrite Z.sub_0_r; symmetry; apply Z.mod_small; lia|].
      repeat split; auto. intros x []. }
  assert (Hfc0 : forall x, 0 <= x < sd_elems sd -> ~ In x Z0 -> Znth x (fc t) = 0).
  { intros x Hx Hn. destruct (Z.eq_dec (Znth x (fc t)) 0) as [|Hne]; auto. exfalso; apply Hn, Hall; auto. }
  assert (Hlen01 : w_heap_len w = 0 \/ w_heap_len w = 1) by lia.
  destruct Hlen01 as [H0|H1].
  - (* no used code: two forced nodes 0 and 1 *)
    assert (EZ0 : Z0 = []) by (apply Zlength_nil_inv; lia).
    assert (Emc : mc = -1) by (destruct Hmc as [[Hm _]|[Hm _]]; auto; fold Z0 in Hm; rewrite EZ0 in Hm; destruct Hm).
    subst mc. rewrite bt_force_step. replace (w_heap_len w <? 2) with true by (symmetry; apply Z.ltb_lt; lia).
    rewrite (force_node_lt (-1)) by lia. cbn [fst snd]. replace (-1 + 1) with 0 by lia.
    rewrite bt_force_step. destruct (force_push_fields sd w 0) as [E1 [E2 [E3 [E4 [E5 [E6 E7]]]]]].
    rewrite E2. replace (w_heap_len w + 1 <? 2) with true by (symmetry; apply Z.ltb_lt; lia).
    rewrite (force_node_lt 0) by lia. cbn [fst snd]. replace (0 + 1) with 1 by lia. cbn [bt_force].
    destruct (force_push_fields sd (force_push sd w 0) 1) as [G1 [G2 [G3 [G4 [G5 [G6 G7]]]]]].
    exists [0; 1]. rewrite EZ0. simpl app.
    assert (Hz0 : Znth 0 (fc t) = 0) by (apply Hfc0; [lia|rewrite EZ0; intros []]).
    assert (Hz1 : Znth 1 (fc t) = 0) by (apply Hfc0; [lia|rewrite EZ0; intros []]).
    split.
    { rewrite G1, G2, E1, E2, H0. replace (0 + 1 + 1) with 2 by lia. replace (0 + 1) with 1 by lia.
      unfold reg. change (zseq 1 (Z.to_nat 2)) with [1; 2]. cbn [map].
      rewrite upd_Znth_same by (rewrite ?Zlength_upd; unfold HEAP_SIZE in *; lia).
      rewrite upd_Znth_diff by (rewrite ?Zlength_upd; unfold HEAP_SIZE in *; lia).
      rewrite upd_Znth_same by (unfold HEAP_SIZE in *; lia). reflexivity. }
    split; [rewrite G2, E2; lia|]. split; [intros; exfalso; lia|]. split; [change (Zlength [0; 1]) with 2; lia|].
    split; [repeat constructor; simpl; lia|].
    split; [intros x [<-|[<-|[]]]; split; auto; lia|].
    split.
    { intros x. unfold set_fc; cbn [fc]. destruct (in_dec Z.eq_dec x [0; 1]) as [Hx|Hx].
      - destruct Hx as [<-|[<-|[]]].
        + rewrite upd_Znth_diff by (rewrite ?Zlength_upd; lia). rewrite upd_Znth_same by lia. reflexivity.
        + rewrite upd_Znth_same by (rewrite ?Zlength_upd; lia). reflexivity.
      - destruct (Z_le_gt_dec 0 x); [destruct (Z_lt_ge_dec x (Zlength (fc t)))|].
        + rewrite !upd_Znth_diff by (rewrite ?Zlength_upd; try lia; intros ->; apply Hx; simpl; auto). reflexivity.
        + rewrite !Znth_overflow by (rewrite ?Zlength_upd; lia). reflexivity.
        + rewrite !Znth_underflow by lia. reflexivity. }
    split; [reflexivity|]. split; [unfold set_fc; simpl; rewrite !Zlength_upd; reflexivity|].
    split; [simpl; auto|]. split; [intros i [<-|[<-|[]]]; lia|].
    split; [rewrite G6, E6, u64_sub_sub; f_equal; change (Zlength [0; 1]) with 2; lia|].
    split.
    { rewrite G7. destruct (sd_stree sd) as [st|] eqn:Est; rewrite E7; auto.
      rewrite u64_sub_sub. f_equal. cbn [map sumZ]. lia. }
    split; [rewrite G3, E3; reflexivity|]. split; [rewrite G5, E5; reflexivity|].
    split; [rewrite G1, E1, !Zlength_upd; exact Hh|].
    split; [rewrite G4, E4, !Zlength_upd; exact Hd|].
    intros x [<-|[<-|[]]]; rewrite G4, E4.
    + rewrite upd_Znth_diff by (rewrite ?Zlength_upd; unfold HEAP_SIZE in *; lia). rewrite upd_Znth_same by
        (unfold HEAP_SIZE in *; lia). reflexivity.
    + rewrite upd_Znth_same by (rewrite ?Zlength_upd; unfold HEAP_SIZE in *; lia). reflexivity.
  - (* one used code x0: one forced node *)
    set (x0 := Znth 1 (w_heap w)).
    assert (EZ0 : Z0 = [x0]) by (unfold Z0, reg; rewrite H1; reflexivity).
    assert (Emc : mc = x0) by (destruct Hmc as [[_ Hm]|[Hm _]]; fold Z0 in Hm; rewrite EZ0 in Hm;
                                 [discriminate|destruct Hm as [->|[]]; reflexivity]).
    subst mc.
    assert (Hx0 := Hz x0 ltac:(fold Z0; rewrite EZ0; left; auto)).
    set (node := fst (force_node x0)). set (mc1 := snd (force_node x0)).
    assert (Hnode : 0 <= node < sd_elems sd /\ node <> x0 /\ mc1 = Z.max x0 node).
    { unfold node, mc1. destruct (Z_lt_ge_dec x0 2).
      - rewrite force_node_lt by lia. simpl. lia.
      - rewrite force_node_ge by lia. simpl. lia. }
    assert (Hzn : Znth node (fc t) = 0) by (apply Hfc0; [lia|rewrite EZ0; intros [Hc|[]]; lia]).
    rewrite bt_force_step. replace (w_heap_len w <? 2) with true by (symmetry; apply Z.ltb_lt; lia).
    fold node mc1. rewrite bt_force_step.
    destruct (force_push_fields sd w node) as [E1 [E2 [E3 [E4 [E5 [E6 E7]]]]]].
    rewrite E2. replace (w_heap_len w + 1 <? 2) with false by (symmetry; apply Z.ltb_ge; lia).
    exists [node]. rewrite EZ0.
    split.
    { rewrite E1, E2, H1. replace (1 + 1) with 2 by lia.
      unfold reg. change (zseq 1 (Z.to_nat 2)) with [1; 2]. cbn [map].
      rewrite upd_Znth_same by (unfold HEAP_SIZE in *; lia).
      rewrite upd_Znth_diff by (unfold HEAP_SIZE in *; lia). reflexivity. }
    split; [rewrite E2; lia|]. split; [intros; exfalso; lia|]. split; [change (Zlength [node]) with 1; lia|].
    split; [repeat constructor; simpl; intuition lia|].
    split; [intros x [<-|[]]; split; auto; lia|].
    split.
    { intros x. unfold set_fc; cbn [fc]. destruct (in_dec Z.eq_dec x [node]) as [Hx|Hx].
      - destruct Hx as [<-|[]]. rewrite upd_Znth_same by lia. reflexivity.
      - destruct (Z_le_gt_dec 0 x); [destruct (Z_lt_ge_dec x (Zlength (fc t)))|].
        + rewrite upd_Znth_diff by (try lia; intros ->; apply Hx; simpl; auto). reflexivity.
        + rewrite !Znth_overflow by (rewrite ?Zlength_upd; lia). reflexivity.
        + rewrite !Znth_underflow by lia. reflexivity. }
    split; [reflexivity|]. split; [unfold set_fc; cbn [fc]; rewrite Zlength_upd; reflexivity|].
    split; [destruct (Z_lt_ge_dec x0 node); [right; left|left]; lia|].
    split; [intros i [<-|[<-|[]]]; lia|].
    split; [rewrite E6; f_equal; change (Zlength [node]) with 1; lia|].
    split.
    { destruct (sd_stree sd) as [st|] eqn:Est; rewrite E7; auto. f_equal. cbn [map sumZ]. lia. }
    split; [rewrite E3; reflexivity|]. split; [rewrite E5; reflexivity|].
    split; [rewrite E1, Zlength_upd; exact Hh|].
    split; [rewrite E4, Zlength_upd; exact Hd|].
    intros x [<-|[]]. rewrite E4. rewrite upd_Znth_same by (unfold HEAP_SIZE in *; lia). reflexivity.
Qed.

Lemma bt_heapify_spec : forall fuel t w k,
  0 <= k <= w_heap_len w -> k <= Z.of_nat fuel -> w_heap_len w < HEAP_SIZE ->
  Zlength (w_heap w) = HEAP_SIZE -> hp t (w_depth w) (w_heap w) (w_heap_len w) (k + 1) ->
  let w' := bt_heapify fuel t w k in
  hp t (w_depth w) (w_heap w') (w_heap_len w) 1 /\ Permutation (reg (w_heap w) (w_heap_len w)) (reg (w_heap w') (w_heap_len w)) /\
  w_heap_len w' = w_heap_len w /\ w_heap_max w' = w_heap_max w /\ w_depth w' = w_depth w /\
  w_bl_count w' = w_bl_count w /\ w_opt_len w' = w_opt_len w /\ w_static_len w' = w_static_len w /\
  Zlength (w_heap w') = HEAP_SIZE.
Proof.
  induction fuel as [|fuel IH]; intros t w k Hk Hf Hl Hh Hhp.
  - simpl. assert (k = 0) by lia. subst k. repeat split; auto.
  - cbn [bt_heapify]. destruct (Z.geb_spec k 1) as [H1|H1].
    + destruct (pqdownheap_correct t w k) as [P1 [P2 [P3 [P4 [P5 [P6 [P7 [P8 [P9 P10]]]]]]]]];
        try (unfold HEAP_SIZE in *; lia); auto.
      set (w1 := pqdownheap t w k) in *.
      assert (A1 : 0 <= k - 1 <= w_heap_len w1) by lia.
      assert (A2 : k - 1 <= Z.of_nat fuel) by lia.
      assert (A3 : w_heap_len w1 < HEAP_SIZE) by lia.
      assert (A4 : Zlength (w_heap w1) = HEAP_SIZE) by lia.
      assert (A5 : hp t (w_depth w1) (w_heap w1) (w_heap_len w1) (k - 1 + 1))
        by (rewrite P1, P3; replace (k - 1 + 1) with k by lia; exact P8).
      destruct (IH t w1 (k - 1) A1 A2 A3 A4 A5) as [Q1 [Q2 [Q3 [Q4 [Q5 [Q6 [Q7 [Q8 Q9]]]]]]]].
      rewrite P1, P3 in *. split; [exact Q1|]. split; [eapply Permutation_trans; [exact P9|exact Q2]|].
      repeat split; congruence.
    + assert (k = 0) by lia. subst k. repeat split; auto.
Qed.

(** ** build_tree up to gen_bitlen *)

Definition bt_pre (sd : stat_desc) (t : tree) (w : work) : tree * work * Z :=
  let w := w_set_heap_len w 0 in
  let w := w_set_heap_max w HEAP_SIZE in
  let '(t, w, max_code) := bt_init (Z.to_nat (sd_elems sd)) (sd_elems sd) t w (-1) 0 in
  let '(t, w, max_code) := bt_force 2 sd t w max_code in
  let w := bt_heapify (Z.to_nat (w_heap_len w / 2)) t w (w_heap_len w / 2) in
  let '(t, w, _) := bt_merge (Z.to_nat (w_heap_len w)) t w (sd_elems sd) in
  (t, store_removed w (Znth SMALLEST (w_heap w)), max_code).

Lemma build_tree_eq : forall sd t w,
  build_tree sd t w =
  let '(t1, w1, mc) := bt_pre sd t w in
  let '(t2, w2) := gen_bitlen sd mc t1 w1 in
  (gen_codes t2 mc (w_bl_count w2), mc, w2).
Proof.
  intros. unfold build_tree, bt_pre.
  destruct (bt_init _ _ _ _ _ _) as [[t1 w1] m1].
  destruct (bt_force _ _ _ _ _) as [[t2 w2] m2].
  destruct (bt_merge _ _ _ _) as [[t3 w3] m3].
  reflexivity.
Qed.

(** The invariant holds after bt_heapify, with singleton items. *)
Lemma init_minv : forall TS elems S f0 t w,
  (forall c, 0 <= c < elems -> ~ In c S -> Znth c (dl t) = 0) ->
  3 <= elems -> 2 * elems + 1 <= TS <= HEAP_SIZE -> Zlength (fc t) = TS -> Zlength (dl t) = TS ->
  Zlength (w_heap w) = HEAP_SIZE -> Zlength (w_depth w) = HEAP_SIZE -> w_heap_max w = HEAP_SIZE ->
  2 <= w_heap_len w -> Zlength S = w_heap_len w ->
  Permutation S (reg (w_heap w) (w_heap_len w)) -> NoDup S ->
  (forall x, In x S -> 0 <= x < elems /\ Znth x (fc t) = f0 x /\ 0 <= f0 x) ->
  hp t (w_depth w) (w_heap w) (w_heap_len w) 1 ->
  minv TS elems (sumZ (map f0 S)) S f0 t w elems (fun x => [(x, f0 x, 0)]) (P0 S f0).
Proof.
  intros TS elems S f0 t w Hunused Hel3 HTS Hfc Hdl Hh Hd Hhm H2 HS Hp Hnd HSx Hhp.
  assert (HSr : forall y, In y (reg (w_heap w) (w_heap_len w)) <-> In y S)
    by (intros y; split; intros Hy; [apply (Permutation_in _ (Permutation_sym Hp))|apply (Permutation_in _ Hp)]; auto).
  assert (Hrem0 : removed (w_heap w) (w_heap_max w) = []) by (rewrite Hhm; reflexivity).
  assert (Hlen573 : w_heap_len w <= elems).
  { rewrite <- HS. assert (incl S (zseq 0 (Z.to_nat elems))) by (intros x Hx; apply in_zseq; specialize (HSx x Hx); lia).
    rewrite Zlength_correct. assert (H' := NoDup_incl_length Hnd H). rewrite zseq_length in H'. lia. }
  constructor; auto.
  - lia.
  - unfold HEAP_SIZE in *; lia.
  - split; [lia|]. split; lia.
  - constructor.
  - unfold P0. replace (map (fun x => [(x, f0 x, 0)]) (reg (w_heap w) (w_heap_len w)))
      with (map (fun x : Z => [(x, f0 x, 0)] : item) (reg (w_heap w) (w_heap_len w))) by reflexivity.
    apply Permutation_map; auto.
  - intros y Hy. apply HSr in Hy. destruct (HSx y Hy) as [H0 [H1 H3]]. unfold weight, lf; simpl. lia.
  - rewrite <- (sumZ_perm' _ _ _ Hp). apply f_equal. apply map_ext_in. intros y Hy. apply HSx; auto.
  - rewrite Hrem0, app_nil_r. eapply Permutation_NoDup; eauto.
  - intros y x Hy [<-|[]]. unfold ld, lid; simpl. apply HSr in Hy. split; [lia|]. split; auto. split; auto.
    intros e He. lia.
  - intros p Hp'. rewrite Hhm in Hp'. lia.
  - intros x Hx. destruct (HSx x Hx) as [H0 [H1 H3]]. auto.
  - intros y Hy. discriminate.
  - intros p Hp'. rewrite Hhm in Hp'. lia.
  - intros y Hy. left. split; auto. apply HSr; auto.
  - intros p Hp'. rewrite Hhm in Hp'. lia.
Qed.

(** ** The state before gen_bitlen *)

Lemma hp_half : forall t d heap len, hp t d heap len (len / 2 + 1).
Proof.
  intros t d heap len i Hi Hlo. exfalso.
  assert (H1 := Z.mul_div_le len 2 ltac:(lia)). assert (H2 := Z.mul_div_le i 2 ltac:(lia)).
  assert (H3 : 2 * (i / 2) <= i) by lia. assert (H4 : 2 * (len / 2 + 1) <= 2 * (i / 2)) by lia.
  assert (H5 := Z.mod_pos_bound len 2 ltac:(lia)). assert (H6 := Z.div_mod len 2 ltac:(lia)). lia.
Qed.

Record pre_ok (sd : stat_desc) (t0 : tree) (w0 : work) (S F : list Z) (R : item) (t : tree) (w : work) (mc : Z) : Prop := {
  po_heap : Zlength (w_heap w) = HEAP_SIZE;
  po_hm : 1 <= w_heap_max w < HEAP_SIZE;
  po_nodup : NoDup (removed (w_heap w) (w_heap_max w));
  po_dad : forall p, w_heap_max w < p < HEAP_SIZE ->
             exists q, w_heap_max w <= q < p /\ Znth q (w_heap w) = Znth (Znth p (w_heap w)) (dl t);
  po_inS : forall x, In x S -> In x (removed (w_heap w) (w_heap_max w));
  po_kind : forall p, w_heap_max w <= p < HEAP_SIZE ->
             In (Znth p (w_heap w)) S \/ sd_elems sd <= Znth p (w_heap w) < Zlength (dl t);
  po_S : S = nzl (fc t0) (sd_elems sd) ++ F /\ NoDup S /\ (forall x, In x S -> 0 <= x < sd_elems sd) /\
         (forall x, In x F -> Znth x (fc t0) = 0) /\ Zlength F <= 2 /\
         (2 <= Zlength (nzl (fc t0) (sd_elems sd)) -> F = []);
  po_huff : huff (map (fun x => [(x, Znth x (fc t), 0)]) S) R;
  po_depth : forall x, In x R -> 1 <= ld x /\ iter (dl t) (Z.to_nat (ld x)) (lid x) = Znth (w_heap_max w) (w_heap w) /\
               forall e, (e < Z.to_nat (ld x))%nat -> iter (dl t) e (lid x) <> Znth (w_heap_max w) (w_heap w);
  po_desc : forall p, w_heap_max w <= p < HEAP_SIZE -> exists x r, In x S /\ iter (dl t) r x = Znth p (w_heap w);
  po_fc : forall x, In x S -> Znth x (fc t) = if in_dec Z.eq_dec x F then 1 else Znth x (fc t0);
  po_len : Zlength (fc t) = Zlength (fc t0) /\ Zlength (dl t) = Zlength (dl t0) /\ Zlength (w_depth w) = HEAP_SIZE;
  po_mc : In mc S /\ forall x, In x S -> x <= mc;
  po_unused : forall c, 0 <= c < sd_elems sd -> ~ In c S -> Znth c (dl t) = 0;
  po_opt : w_opt_len w = u64 (w_opt_len w0 - Zlength F);
  po_static : w_static_len w = match sd_stree sd with
                | Some stree => u64 (w_static_len w0 - sumZ (map (fun x => Znth x stree) F))
                | None => w_static_len w0 end;
  po_blc : w_bl_count w = w_bl_count w0;
  po_kids : forall y, In y (removed (w_heap w) (w_heap_max w)) ->
              kids (dl t) (w_heap w) (w_heap_max w + 1) y = if sd_elems sd <=? y then 2 else 0;
  po_sorted : forall i j, w_heap_max w + 1 <= i <= j -> j < HEAP_SIZE ->
              Znth (Znth j (w_heap w)) (fc t) <= Znth (Znth i (w_heap w)) (fc t)
}.

Lemma sumZ_filter_nz : forall (g : Z -> Z) l,
  sumZ (map g (filter (fun i => negb (g i =? 0)) l)) = sumZ (map g l).
Proof.
  intros g l; induction l as [|a l IH]; simpl; auto.
  destruct (g a =? 0) eqn:E; simpl; rewrite IH; auto. apply Z.eqb_eq in E. lia.
Qed.

Lemma NoDup_incl_Zlength : forall (l1 l2 : list Z), NoDup l1 -> incl l1 l2 -> Zlength l1 <= Zlength l2.
Proof. intros. rewrite !Zlength_correct. apply inj_le. apply NoDup_incl_length; auto. Qed.

Lemma leaves_P0 : forall S f0, leaves (P0 S f0) = map (fun x => (x, f0 x, 0)) S.
Proof. intros S f0. unfold leaves, P0. induction S as [|a l IH]; simpl; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma huff_leaf_of : forall S f0 R x, huff (P0 S f0) R -> In x S -> exists l, In l R /\ lid l = x.
Proof.
  intros S f0 R x H Hx. assert (Hp := huff_idf _ _ H). rewrite leaves_P0, map_map in Hp.
  assert (Hin : In (x, f0 x) (map (fun y => idf (y, f0 y, 0)) S)) by (apply in_map_iff; exists x; split; auto).
  apply (Permutation_in _ Hp) in Hin. apply in_map_iff in Hin. destruct Hin as [l [Hl HlR]].
  exists l. split; auto. unfold lid. unfold idf in Hl. rewrite Hl. reflexivity.
Qed.

Lemma huff_length : forall S f0 R, huff (P0 S f0) R -> length R = length S.
Proof.
  intros S f0 R H. assert (Hp := huff_idf _ _ H). apply Permutation_length in Hp.
  rewrite !length_map, leaves_P0, length_map in Hp. lia.
Qed.

Theorem bt_pre_spec : forall sd t w,
  3 <= sd_elems sd <= 286 ->
  Zlength (fc t) = Zlength (dl t) -> 2 * sd_elems sd + 1 <= Zlength (fc t) <= HEAP_SIZE ->
  Zlength (w_heap w) = HEAP_SIZE -> Zlength (w_depth w) = HEAP_SIZE ->
  0 <= w_opt_len w < 18446744073709551616 -> 0 <= w_static_len w < 18446744073709551616 ->
  (forall x, 0 <= x < sd_elems sd -> 0 <= Znth x (fc t)) ->
  sumZ (map (fun x => Znth x (fc t)) (zseq 0 (Z.to_nat (sd_elems sd)))) + 2 < 65536 ->
  let '(t', w', mc) := bt_pre sd t w in
  exists S F R, pre_ok sd t w S F R t' w' mc.
Proof.
  intros sd t w Hel HTS HTS2 Hh Hd Hol Hsl Hfc0 Hsum.
  set (elems := sd_elems sd) in *.
  unfold bt_pre. fold elems.
  set (w0 := w_set_heap_max (w_set_heap_len w 0) HEAP_SIZE).
  (* bt_init *)
  assert (I := bt_init_spec elems (Z.to_nat elems) t w0 (-1) 0).
  assert (Hw0h : Zlength (w_heap w0) = HEAP_SIZE) by exact Hh.
  assert (Hw0d : Zlength (w_depth w0) = HEAP_SIZE) by exact Hd.
  specialize (I ltac:(lia) ltac:(lia) ltac:(lia) Hw0h Hw0d ltac:(lia) eq_refl eq_refl
                ltac:(intros i Hi; lia) (or_introl (conj eq_refl eq_refl))).
  destruct (bt_init (Z.to_nat elems) elems t w0 (-1) 0) as [[t1 w1] mc1] eqn:Einit.
  destruct I as [I1 [I2 [I3 [I4 [I5 [I6 [I7 [I8 [I9 [I10 [I11 I12]]]]]]]]]]].
  (* bt_force *)
  assert (Fz := bt_force_spec sd t1 w1 mc1).
  assert (A4 : elems <= Zlength (fc t1)) by (rewrite I1; lia).
  assert (A5 : 0 <= w_heap_len w1) by (rewrite I3; apply Zlength_nonneg).
  assert (A6 : 0 <= w_opt_len w1 < 18446744073709551616) by (rewrite I7; exact Hol).
  assert (A7 : 0 <= w_static_len w1 < 18446744073709551616) by (rewrite I8; exact Hsl).
  assert (A8 : NoDup (reg (w_heap w1) (w_heap_len w1))) by (rewrite I4; apply nzl_nodup).
  assert (A9 : forall x, In x (reg (w_heap w1) (w_heap_len w1)) -> 0 <= x < elems /\ Znth x (fc t1) <> 0)
    by (intros x Hx; rewrite I4 in Hx; rewrite I1; apply in_nzl in Hx; lia).
  assert (A10 : forall x, 0 <= x < elems -> Znth x (fc t1) <> 0 -> In x (reg (w_heap w1) (w_heap_len w1)))
    by (intros x Hx Hz; rewrite I4; rewrite I1 in Hz; apply in_nzl; lia).
  assert (A11 : mc1 = -1 /\ reg (w_heap w1) (w_heap_len w1) = [] \/
                In mc1 (reg (w_heap w1) (w_heap_len w1)) /\ forall i, In i (reg (w_heap w1) (w_heap_len w1)) -> i <= mc1)
    by (rewrite I4; exact I12).
  specialize (Fz Hel I9 I10 A4 A5 A6 A7 A8 A9 A10 A11). cbv zeta in Fz.
  destruct (bt_force 2 sd t1 w1 mc1) as [[t2 w2] mc2] eqn:Eforce.
  destruct Fz as [F [F1 [F2 [F3 [F4 [F5 [F6 [F7 [F8 [F9 [F10 [F11 [F12 [F13 [F14 [F15 [F16 [F17 F18]]]]]]]]]]]]]]]]]].
  rewrite I4 in F1, F5, F10, F11.
  set (S := nzl (fc t) elems ++ F) in *.
  assert (HSel : forall x, In x S -> 0 <= x < elems).
  { intros x Hx. apply in_app_or in Hx. destruct Hx as [Hx|Hx]; [apply in_nzl in Hx; lia|apply F6; auto]. }
  assert (HSlen : Zlength S <= elems).
  { assert (H := NoDup_incl_Zlength S (zseq 0 (Z.to_nat elems)) F5 ltac:(intros x Hx; apply in_zseq; specialize (HSel x Hx); lia)).
    rewrite (Zlength_correct (zseq _ _)), zseq_length in H. lia. }
  assert (Hlen2 : w_heap_len w2 = Zlength S) by (rewrite <- F1; symmetry; apply reg_len; lia).
  (* bt_heapify *)
  set (k := w_heap_len w2 / 2).
  assert (Hk : 0 <= k <= w_heap_len w2) by (unfold k; split; [apply Z.div_pos|apply Z.div_le_upper_bound]; lia).
  assert (Hy := bt_heapify_spec (Z.to_nat k) t2 w2 k Hk ltac:(lia) ltac:(unfold HEAP_SIZE; lia) F16
                  ltac:(unfold k; apply hp_half)).
  cbv zeta in Hy.
  set (w3 := bt_heapify (Z.to_nat k) t2 w2 k) in *.
  destruct Hy as [Y1 [Y2 [Y3 [Y4 [Y5 [Y6 [Y7 [Y8 Y9]]]]]]]].
  (* initial invariant *)
  set (f0 := fun x => Znth x (fc t2)).
  assert (Hf0 : forall x, In x S -> 1 <= f0 x).
  { intros x Hx. unfold f0. rewrite F7. destruct (in_dec Z.eq_dec x F) as [|Hn]; [lia|].
    apply in_app_or in Hx. destruct Hx as [Hx|Hx]; [|contradiction]. apply in_nzl in Hx. rewrite I1.
    specialize (Hfc0 x ltac:(lia)). lia. }
  assert (B1 : 3 <= elems) by lia.
  assert (B2 : 2 * elems + 1 <= Zlength (fc t2) <= HEAP_SIZE) by (rewrite F9, I1; lia).
  assert (B3 : Zlength (dl t2) = Zlength (fc t2)) by (rewrite F8, F9, I1, I2; lia).
  assert (B4 : Zlength (w_depth w3) = HEAP_SIZE) by (rewrite Y5; exact F17).
  assert (B5 : w_heap_max w3 = HEAP_SIZE) by (rewrite Y4, F14, I5; reflexivity).
  assert (B6 : 2 <= w_heap_len w3) by (rewrite Y3; lia).
  assert (B7 : Zlength S = w_heap_len w3) by (rewrite Y3; lia).
  assert (B8 : Permutation S (reg (w_heap w3) (w_heap_len w3))) by (rewrite Y3, <- F1; exact Y2).
  assert (B9 : forall x, In x S -> 0 <= x < elems /\ Znth x (fc t2) = f0 x /\ 0 <= f0 x)
    by (intros x Hx; specialize (Hf0 x Hx); split; [apply HSel; auto|split; [reflexivity|lia]]).
  assert (B10 : hp t2 (w_depth w3) (w_heap w3) (w_heap_len w3) 1) by (rewrite Y3, Y5; exact Y1).
  assert (B0 : forall c, 0 <= c < elems -> ~ In c S -> Znth c (dl t2) = 0).
  { intros c Hc HcS. rewrite F8. apply I11; auto. destruct (Z.eq_dec (Znth c (fc t)) 0) as [|Hne]; auto.
    exfalso. apply HcS. unfold S. apply in_or_app; left. apply in_nzl. split; auto. }
  assert (Hm0 := init_minv (Zlength (fc t2)) elems S f0 t2 w3 B0 B1 B2 eq_refl B3 Y9 B4 B5 B6 B7 B8 F5 B9 B10).
  (* the total weight *)
  assert (Hdisj : forall x, In x F -> ~ In x (nzl (fc t) elems)).
  { intros x HxF Hxn. exact (nodup_app_disj (nzl (fc t) elems) F x F5 Hxn HxF). }
  assert (Htot : sumZ (map f0 S) < 65536).
  { unfold S. rewrite map_app, sumZ_app.
    replace (map f0 (nzl (fc t) elems)) with (map (fun i => Znth i (fc t)) (nzl (fc t) elems)).
    2:{ apply map_ext_in. intros x Hx. unfold f0. rewrite F7, I1.
        destruct (in_dec Z.eq_dec x F) as [Hc|]; [exfalso; exact (Hdisj x Hc Hx)|reflexivity]. }
    unfold nzl. rewrite sumZ_filter_nz.
    replace (map f0 F) with (map (fun _ => 1) F).
    2:{ apply map_ext_in. intros x Hx. unfold f0. rewrite F7. destruct (in_dec Z.eq_dec x F); [reflexivity|contradiction]. }
    assert (sumZ (map (fun _ : Z => 1) F) = Zlength F).
    { clear. induction F as [|a F IH]; cbn [map sumZ]; [reflexivity|]. rewrite IH, Zlength_cons. lia. }
    lia. }
  (* the merge loop *)
  assert (Hmerge := bt_merge_inv (Zlength (fc t2)) elems (sumZ (map f0 S)) S f0 Htot
                      (Z.to_nat (w_heap_len w3)) t2 w3 elems _ _ Hm0 B6 ltac:(lia)).
  assert (HK := bt_merge_kinv (Zlength (fc t2)) elems (sumZ (map f0 S)) S f0 Htot
                  (Z.to_nat (w_heap_len w3)) t2 w3 elems _ _ Hm0 (kinv_init elems t2 w3 B5) B6 ltac:(lia)).
  destruct (bt_merge (Z.to_nat (w_heap_len w3)) t2 w3 elems) as [[t4 w4] node4] eqn:Emerge.
  destruct Hmerge as [it4 [Q4 [Hm4 [Hlen4 Hnode4]]]].
  (* the final state *)
  assert (Hfields := bt_merge_fields (Z.to_nat (w_heap_len w3)) t2 w3 elems). rewrite Emerge in Hfields.
  cbn [fst snd] in Hfields. destruct Hfields as [Fo [Fs Fb]].
  destruct Hm4 as [Hh4 Hd4 Hfc4 Hdl4 Hlen4' Hroom4 Hnode4' Hhp4 Hst4 Hperm4 Hpool4 Htot4 Hnd4 Hch4 Hrem4 Hleaf4
                   Hnonem4 Hdesc4 Hkind4 Hrkind4 Hunused4].
  rewrite Hlen4 in *.
  set (heap4 := w_heap w4) in *. set (hm4 := w_heap_max w4) in *.
  set (root := Znth 1 heap4).
  assert (Hreg1 : reg heap4 1 = [root]) by reflexivity.
  rewrite Hreg1 in *.
  assert (Hroot_in : In root [root]) by (left; reflexivity).
  set (R := it4 root).
  assert (Hhuff : huff (P0 S f0) R).
  { apply (steps_huff_perm (P0 S f0) Q4 R Hst4). exact Hperm4. }
  assert (Hidf := huff_idf _ _ Hhuff).
  assert (HSlen2 : 2 <= Zlength S) by lia.
  (* the root is an internal node and every leaf of R has depth >= 1 *)
  assert (Hroot_int : elems <= root /\ forall x, In x R -> 1 <= ld x).
  { destruct (Hkind4 root Hroot_in) as [[HS HR]|HR]; [|exact HR].
    exfalso. assert (Hl := huff_length S f0 R Hhuff). unfold R in Hl. rewrite HR in Hl.
    rewrite Zlength_correct in HSlen2. simpl in Hl. lia. }
  assert (Hhm4 : 3 <= hm4 <= HEAP_SIZE) by lia.
  set (heap5 := upd_Znth (hm4 - 1) heap4 root).
  assert (H5same : Znth (hm4 - 1) heap5 = root) by (unfold heap5; rewrite upd_Znth_same by (unfold HEAP_SIZE in *; lia); reflexivity).
  assert (H5diff : forall p, hm4 <= p < HEAP_SIZE -> Znth p heap5 = Znth p heap4)
    by (intros p Hp; unfold heap5; rewrite upd_Znth_diff by (unfold HEAP_SIZE in *; lia); reflexivity).
  assert (Erem5 : removed heap5 (hm4 - 1) = root :: removed heap4 hm4).
  { rewrite removed_cons by lia. rewrite H5same. f_equal. apply removed_frame. intros p Hp. apply H5diff; lia. }
  assert (Hnd5 : ~ In root (removed heap4 hm4)) by (simpl in Hnd4; apply NoDup_cons_iff in Hnd4; tauto).
  cbv beta iota zeta. unfold SMALLEST. fold root.
  set (w5 := store_removed w4 root).
  assert (E5h : w_heap w5 = heap5) by reflexivity.
  assert (E5m : w_heap_max w5 = hm4 - 1) by reflexivity.
  exists S, F, R. constructor.
  - rewrite E5h. unfold heap5. rewrite Zlength_upd. exact Hh4.
  - rewrite E5m. lia.
  - rewrite E5h, E5m, Erem5. simpl in Hnd4. exact Hnd4.
  - rewrite E5h, E5m. intros p Hp. rewrite H5diff by lia.
    destruct (Hrem4 p ltac:(lia)) as [_ [_ [Hin|[q [Hq Hq']]]]].
    + exists (hm4 - 1). split; [lia|]. rewrite H5same. destruct Hin as [Hin|[]]. exact Hin.
    + exists q. split; [lia|]. rewrite H5diff by lia. exact Hq'.
  - rewrite E5h, E5m, Erem5. intros x Hx. right.
    destruct (huff_leaf_of S f0 R x Hhuff Hx) as [l [Hl Hlx]].
    destruct (Hch4 root l Hroot_in Hl) as [_ [_ [_ Hrm]]].
    assert (H1 := proj2 Hroot_int l Hl).
    specialize (Hrm 0%nat ltac:(lia)). rewrite <- Hlx. exact Hrm.
  - rewrite E5h, E5m. intros p Hp. destruct (Z.eq_dec p (hm4 - 1)) as [->|Hne].
    + rewrite H5same. right. destruct (Hpool4 root Hroot_in) as [Hr _]. split; [apply Hroot_int|]. lia.
    + rewrite H5diff by lia. destruct (Hrem4 p ltac:(lia)) as [Hr _].
      destruct (Hrkind4 p ltac:(lia)) as [HS|He]; [left; exact HS|right; lia].
  - split; [reflexivity|]. split; [exact F5|]. split; [exact HSel|].
    split; [intros x Hx; destruct (F6 x Hx) as [_ Hz]; rewrite I1 in Hz; exact Hz|].
    split; [exact F4|]. intros H2. apply F3. rewrite I3. exact H2.
  - replace (map (fun x => [(x, Znth x (fc t4), 0)]) S) with (P0 S f0); [exact Hhuff|].
    unfold P0. apply map_ext_in. intros x Hx. destruct (Hleaf4 x Hx) as [E _]. rewrite E. reflexivity.
  - rewrite E5h, E5m, H5same. intros x Hx. destruct (Hch4 root x Hroot_in Hx) as [_ [_ [Hit Hrm]]].
    split; [apply Hroot_int; exact Hx|]. split; [exact Hit|].
    intros e He Heq. specialize (Hrm e He). rewrite Heq in Hrm. exact (Hnd5 Hrm).
  - rewrite E5h, E5m. intros p Hp. destruct (Z.eq_dec p (hm4 - 1)) as [->|Hne].
    + rewrite H5same. assert (Hne := Hnonem4 root Hroot_in).
      destruct (it4 root) as [|l rr] eqn:ER; [contradiction|].
      assert (Hl : In l (it4 root)) by (rewrite ER; left; reflexivity).
      destruct (Hch4 root l Hroot_in Hl) as [_ [HlS [Hit _]]].
      exists (lid l), (Z.to_nat (ld l)). split; [exact HlS|exact Hit].
    + rewrite H5diff by lia. destruct (Hdesc4 p ltac:(lia)) as [x [r [HxS [Hxr _]]]].
      exists x, r. split; [exact HxS|exact Hxr].
  - intros x Hx. destruct (Hleaf4 x Hx) as [E _]. rewrite E. change (f0 x) with (Znth x (fc t2)).
    rewrite F7, I1. reflexivity.
  - split; [rewrite Hfc4, F9, I1; reflexivity|]. split; [rewrite Hdl4, F9, I1; exact HTS|]. exact Hd4.
  - split; [exact F10|exact F11].
  - exact Hunused4.
  - change (w_opt_len w5) with (w_opt_len w4). rewrite Fo, Y7, F12, I7. reflexivity.
  - change (w_static_len w5) with (w_static_len w4). rewrite Fs, Y8, F13, I8. reflexivity.
  - change (w_bl_count w5) with (w_bl_count w4). rewrite Fb, Y6, F15, I6. reflexivity.
  - rewrite E5h, E5m. replace (hm4 - 1 + 1) with hm4 by lia. intros y Hy. rewrite Erem5 in Hy.
    destruct HK as [K1 K2 K3].
    assert (Hylt : y < node4).
    { destruct Hy as [<-|Hy]; [destruct (Hpool4 root Hroot_in) as [Hr _]; lia|].
      apply in_removed in Hy. destruct Hy as [p [Hp <-]]. destruct (Hrem4 p Hp) as [Hr _]. lia. }
    unfold kids. rewrite (removed_frame heap5 heap4 hm4) by (intros p Hp; apply H5diff; lia).
    assert (K := K1 y). unfold kids in K. fold heap4 hm4 in K. rewrite K.
    change (sd_elems sd) with elems. destruct (Z.leb_spec elems y); [|reflexivity]. replace (y <? node4) with true by (symmetry; apply Z.ltb_lt; lia).
    reflexivity.
  - rewrite E5h, E5m. intros i j Hij Hj. destruct HK as [K1 K2 K3].
    rewrite !H5diff by lia. apply K2; lia.
Qed.
