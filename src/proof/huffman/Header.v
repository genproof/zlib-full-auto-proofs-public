(** * The dynamic block header: the bit-length symbol stream of scan_tree / send_tree

    [tree_syms lens max_code] is the list of (bit-length symbol, number of extra bits) that send_tree emits for
    the code lengths [lens[0 .. max_code]] (with the guard [lens[max_code + 1]] stored by scan_tree): it follows
    send_tree's loop statement by statement.  Proved here:
    - scan_tree adds to the bit-length frequencies exactly the symbol counts of the stream (no 16-bit wrap);
    - send_tree / send_all_trees add exactly the stream's bits (lengths of the bit-length codes plus extra bits);
    - the stream's cost under any nonnegative bit-length code [tau] is at most a sum over the used codes of an
      entry cost and the cost of the zero run before the code (the per-code bound of the LP certificate);
    - with bit-length codes of at most 7 bits the stream costs at most 7 bits per entry. *)

From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.huffman.Model.
Import ListNotations.
Local Open Scope Z_scope.

(** ** Bit positions *)

Definition bitpos (o : outbuf) : Z := 8 * o_pending o + o_bi_valid o.

Lemma bitpos_put_byte : forall o c, bitpos (put_byte o c) = bitpos o + 8.
Proof. intros; unfold bitpos, put_byte; cbn [o_pending o_bi_valid]; lia. Qed.

Lemma bitpos_put_short : forall o w, bitpos (put_short o w) = bitpos o + 16.
Proof. intros; unfold put_short; rewrite !bitpos_put_byte; lia. Qed.

(** send_bits always adds [length] bits (pending counts every byte written, in range or not). *)
Lemma put_short_fields : forall o w,
  o_pending (put_short o w) = o_pending o + 2 /\ o_bi_valid (put_short o w) = o_bi_valid o.
Proof. intros; unfold put_short, put_byte; cbn [o_pending o_bi_valid]; split; lia. Qed.

Lemma send_bits_bitpos : forall o v l, bitpos (send_bits o v l) = bitpos o + l.
Proof.
  intros o v l. unfold send_bits, Buf_size.
  destruct (o_bi_valid o >? 16 - l).
  - set (bb := u16 (Z.lor (o_bi_buf o) (Z.shiftl (u16 v) (o_bi_valid o)))).
    destruct (put_short_fields (set_bits o bb (o_bi_valid o)) bb) as [H1 H2].
    unfold bitpos. unfold set_bits at 1. cbn [o_pending o_bi_valid]. rewrite H1.
    unfold set_bits; cbn [o_pending o_bi_valid]. lia.
  - unfold bitpos, set_bits; cbn [o_pending o_bi_valid]; lia.
Qed.

Lemma send_code_bitpos : forall o c codes lens, bitpos (send_code o c codes lens) = bitpos o + Znth c lens.
Proof. intros; unfold send_code; apply send_bits_bitpos. Qed.

Lemma iter_send_code_bitpos : forall m o c codes lens,
  bitpos (Nat.iter m (fun o => send_code o c codes lens) o) = bitpos o + Z.of_nat m * Znth c lens.
Proof.
  induction m as [|m IH]; intros.
  - change (Nat.iter 0 (fun o => send_code o c codes lens) o) with o. lia.
  - change (Nat.iter (S m) (fun o => send_code o c codes lens) o)
      with (send_code (Nat.iter m (fun o => send_code o c codes lens) o) c codes lens).
    rewrite send_code_bitpos, IH. lia.
Qed.

(** ** The stream *)

Fixpoint syms_loop (fuel : nat) (lens : list Z) (max_code : Z)
    (n prevlen nextlen count max_count min_count : Z) : list (Z * Z) :=
  match fuel with
  | O => []
  | S f =>
    if n <=? max_code then
      let curlen := nextlen in
      let nextlen := Znth (n + 1) lens in
      let count := count + 1 in
      if (count <? max_count) && (curlen =? nextlen) then
        syms_loop f lens max_code (n + 1) prevlen nextlen count max_count min_count
      else
        let out :=
          if count <? min_count then repeat (curlen, 0) (Z.to_nat count)
          else if negb (curlen =? 0) then
            (if negb (curlen =? prevlen) then [(curlen, 0)] else []) ++ [(REP_3_6, 2)]
          else if count <=? 10 then [(REPZ_3_10, 3)]
          else [(REPZ_11_138, 7)] in
        let '(max_count, min_count) :=
          if nextlen =? 0 then (138, 3)
          else if curlen =? nextlen then (6, 3)
          else (7, 4) in
        out ++ syms_loop f lens max_code (n + 1) curlen nextlen 0 max_count min_count
    else []
  end.

Definition init_counts (nextlen : Z) : Z * Z := if nextlen =? 0 then (138, 3) else (7, 4).

(** The stream of send_tree for [lens] (the [Len] fields, guard included) and [max_code]. *)
Definition tree_syms (lens : list Z) (max_code : Z) : list (Z * Z) :=
  let nextlen := Znth 0 lens in
  let '(max_count, min_count) := init_counts nextlen in
  syms_loop (Z.to_nat (max_code + 1)) lens max_code 0 (-1) nextlen 0 max_count min_count.

Fixpoint sumZ (l : list Z) : Z := match l with [] => 0 | x :: r => x + sumZ r end.

Lemma sumZ_app : forall l1 l2, sumZ (l1 ++ l2) = sumZ l1 + sumZ l2.
Proof. induction l1; simpl; intros; [lia | rewrite IHl1; lia]. Qed.

(** Cost of a stream under a bit-length code [tau]: code bits plus extra bits. *)
Definition cost_tau (tau : Z -> Z) (l : list (Z * Z)) : Z := sumZ (map (fun p => tau (fst p) + snd p) l).

Lemma cost_tau_app : forall tau l1 l2, cost_tau tau (l1 ++ l2) = cost_tau tau l1 + cost_tau tau l2.
Proof. intros; unfold cost_tau; rewrite map_app, sumZ_app; lia. Qed.

Lemma cost_tau_repeat : forall tau x e m, cost_tau tau (repeat (x, e) m) = Z.of_nat m * (tau x + e).
Proof.
  intros tau x e m; induction m as [|m IH]; [reflexivity|].
  unfold cost_tau in *; simpl repeat; cbn [map sumZ fst snd]. rewrite IH. lia.
Qed.

(** The bits of the stream with the actual bit-length code lengths [bll]. *)
Definition stream_bits (bll : list Z) (l : list (Z * Z)) : Z := cost_tau (fun s => Znth s bll) l.

(** ** send_tree adds the stream's bits *)

Lemma send_tree_loop_bits : forall fuel t mc blc bll o n p nl c mx mn,
  bitpos (send_tree_loop fuel t mc blc bll o n p nl c mx mn) =
  bitpos o + stream_bits bll (syms_loop fuel (dl t) mc n p nl c mx mn).
Proof.
  unfold stream_bits.
  induction fuel as [|fuel IH]; intros; simpl; [unfold cost_tau; simpl; lia|].
  destruct (n <=? mc); [|unfold cost_tau; simpl; lia].
  destruct ((c + 1 <? mx) && (nl =? Znth (n + 1) (dl t))); [apply IH|].
  set (o' := if c + 1 <? mn then _ else _).
  set (out := if c + 1 <? mn then _ else _).
  assert (Ho : bitpos o' = bitpos o + cost_tau (fun s => Znth s bll) out).
  { subst o' out. destruct (c + 1 <? mn).
    - rewrite iter_send_code_bitpos, cost_tau_repeat. lia.
    - destruct (negb (nl =? 0)).
      + destruct (negb (nl =? p)); cbn [app];
          rewrite send_bits_bitpos, !send_code_bitpos; unfold cost_tau; simpl; lia.
      + destruct (c + 1 <=? 10); rewrite send_bits_bitpos, send_code_bitpos; unfold cost_tau; simpl; lia. }
  destruct (if Znth (n + 1) (dl t) =? 0 then _ else _) as [mx' mn'].
  rewrite IH, cost_tau_app, Ho. lia.
Qed.

Lemma send_tree_bits : forall o t mc bl,
  bitpos (send_tree o t mc bl) = bitpos o + stream_bits (dl bl) (tree_syms (dl t) mc).
Proof.
  intros. unfold send_tree, tree_syms, init_counts.
  destruct (Znth 0 (dl t) =? 0); apply send_tree_loop_bits.
Qed.

Lemma send_bl_lens_bits : forall m bl o rank blcodes,
  0 <= rank -> blcodes - rank <= Z.of_nat m ->
  bitpos (send_bl_lens m bl o rank blcodes) = bitpos o + 3 * Z.max 0 (blcodes - rank).
Proof.
  induction m as [|m IH]; intros bl o rank blcodes Hr Hm; cbn [send_bl_lens].
  - lia.
  - destruct (Z.ltb_spec rank blcodes).
    + rewrite IH by lia. rewrite send_bits_bitpos. lia.
    + lia.
Qed.

Theorem send_all_trees_bits : forall o lt dt bl lcodes dcodes blcodes,
  0 <= blcodes <= 19 ->
  bitpos (send_all_trees o lt dt bl lcodes dcodes blcodes) =
  bitpos o + 14 + 3 * blcodes + stream_bits (dl bl) (tree_syms (dl lt) (lcodes - 1))
  + stream_bits (dl bl) (tree_syms (dl dt) (dcodes - 1)).
Proof.
  intros. unfold send_all_trees.
  rewrite !send_tree_bits, send_bl_lens_bits by (simpl; lia). rewrite !send_bits_bitpos. lia.
Qed.

(** ** scan_tree adds the symbol counts of the stream *)

Definition cnt (s : Z) (l : list (Z * Z)) : Z := Z.of_nat (length (filter (fun q => fst q =? s) l)).

Lemma cnt_app : forall s l1 l2, cnt s (l1 ++ l2) = cnt s l1 + cnt s l2.
Proof. intros; unfold cnt; rewrite filter_app, length_app; lia. Qed.

Lemma cnt_nonneg : forall s l, 0 <= cnt s l.
Proof. intros; unfold cnt; lia. Qed.

Lemma cnt_cons : forall s x e l, cnt s ((x, e) :: l) = (if x =? s then 1 else 0) + cnt s l.
Proof. intros; unfold cnt; cbn [filter fst]; destruct (x =? s); cbn [length]; rewrite ?Nat2Z.inj_succ; lia. Qed.

Lemma cnt_nil : forall s, cnt s [] = 0.
Proof. reflexivity. Qed.

Lemma cnt_repeat : forall s x e m, cnt s (repeat (x, e) m) = if x =? s then Z.of_nat m else 0.
Proof.
  intros s x e m; induction m as [|m IH]; [simpl; destruct (x =? s); reflexivity|].
  simpl repeat. rewrite cnt_cons, IH. destruct (x =? s); lia.
Qed.

Lemma Znth_upd_other : forall (l : list Z) i j u, i <> j -> Znth i (upd_Znth j l u) = Znth i l.
Proof.
  intros. destruct (Z_le_gt_dec 0 j); [destruct (Z_lt_ge_dec j (Zlength l))|].
  - apply upd_Znth_diff'; auto; lia.
  - rewrite upd_Znth_out_of_range by lia. reflexivity.
  - rewrite upd_Znth_out_of_range by lia. reflexivity.
Qed.

Lemma upd_add : forall blf x k s,
  0 <= x < Zlength blf -> 0 <= Znth x blf -> 0 <= k -> Znth x blf + k < 65536 ->
  Znth s (upd_Znth x blf (u16 (Znth x blf + k))) = Znth s blf + (if x =? s then k else 0).
Proof.
  intros blf x k s Hx H0 Hk Hw. destruct (Z.eqb_spec x s) as [<-|Hne].
  - rewrite upd_Znth_same by lia. unfold u16. rewrite Z.mod_small by lia. lia.
  - rewrite Znth_upd_other by auto. lia.
Qed.

Definition no_wrap (blf : list Z) (l : list (Z * Z)) : Prop :=
  (forall q, In q l -> 0 <= fst q < Zlength blf) /\
  (forall s, 0 <= s < Zlength blf -> 0 <= Znth s blf /\ Znth s blf + cnt s l < 65536).

Definition adds (blf blf' : list Z) (l : list (Z * Z)) : Prop :=
  Zlength blf' = Zlength blf /\ forall s, 0 <= s < Zlength blf -> Znth s blf' = Znth s blf + cnt s l.

Lemma adds_trans : forall blf blf1 blf2 l1 l2, adds blf blf1 l1 -> adds blf1 blf2 l2 -> adds blf blf2 (l1 ++ l2).
Proof.
  intros blf blf1 blf2 l1 l2 [L1 H1] [L2 H2]. split; [lia|].
  intros s Hs. rewrite H2, H1, cnt_app by lia. lia.
Qed.

Lemma no_wrap_after : forall blf blf1 l1 l2, no_wrap blf (l1 ++ l2) -> adds blf blf1 l1 -> no_wrap blf1 l2.
Proof.
  intros blf blf1 l1 l2 [R W] [L1 H1]. split.
  - intros q Hq. rewrite L1. apply R, in_or_app; auto.
  - intros s Hs. rewrite L1 in Hs. rewrite H1 by lia. specialize (W s Hs). rewrite cnt_app in W.
    pose proof (cnt_nonneg s l1). pose proof (cnt_nonneg s l2). lia.
Qed.

Lemma adds_one : forall blf x e k, no_wrap blf (repeat (x, e) (Z.to_nat k)) -> 1 <= k ->
  adds blf (upd_Znth x blf (u16 (Znth x blf + k))) (repeat (x, e) (Z.to_nat k)).
Proof.
  intros blf x e k [R W] Hk.
  assert (Hx : 0 <= x < Zlength blf).
  { apply (R (x, e)). destruct (Z.to_nat k) eqn:E; [lia|]. left; reflexivity. }
  specialize (W x Hx). rewrite cnt_repeat, Z.eqb_refl, Z2Nat.id in W by lia.
  split; [rewrite upd_Znth_Zlength; lia|].
  intros s Hs. rewrite upd_add by lia. rewrite cnt_repeat, Z2Nat.id by lia. reflexivity.
Qed.

Lemma scan_tree_loop_counts : forall fuel t mc blf n p nl c mx mn,
  0 <= c -> mn <= 4 ->
  no_wrap blf (syms_loop fuel (dl t) mc n p nl c mx mn) ->
  adds blf (scan_tree_loop fuel t mc blf n p nl c mx mn) (syms_loop fuel (dl t) mc n p nl c mx mn).
Proof.
  induction fuel as [|fuel IH]; intros t mc blf n p nl c mx mn Hc Hmn Hnw.
  - split; [reflexivity|]. intros; simpl; rewrite cnt_nil; lia.
  - cbn [scan_tree_loop syms_loop] in *.
    destruct (n <=? mc); [|split; [reflexivity|intros; rewrite cnt_nil; lia]].
    destruct ((c + 1 <? mx) && (nl =? Znth (n + 1) (dl t))); [apply IH; auto; lia|].
    set (mm := if Znth (n + 1) (dl t) =? 0 then (138, 3)
               else if nl =? Znth (n + 1) (dl t) then (6, 3) else (7, 4)) in *.
    assert (Hmn' : snd mm <= 4)
      by (unfold mm; destruct (Znth (n + 1) (dl t) =? 0); [|destruct (nl =? Znth (n + 1) (dl t))];
          simpl; lia).
    clearbody mm. destruct mm as [mx' mn']. cbn beta iota in *. cbn [snd] in Hmn'.
    set (rest := syms_loop fuel (dl t) mc (n + 1) nl (Znth (n + 1) (dl t)) 0 mx' mn') in *.
    match goal with |- adds _ (scan_tree_loop _ _ _ ?b1 _ _ _ _ _ _) (?out ++ _) =>
      assert (Hb1 : adds blf b1 out); [|
      apply (adds_trans blf b1); [exact Hb1|]; apply IH; [lia|lia|];
      exact (no_wrap_after blf b1 out _ Hnw Hb1)] end.
    destruct (Z.ltb_spec (c + 1) mn) as [Hlt|Hge].
    + replace (u16 (c + 1)) with (c + 1) by (unfold u16; rewrite Z.mod_small; lia).
      apply adds_one; [|lia]. split.
      * intros q Hq. apply (proj1 Hnw). apply in_or_app; left; auto.
      * intros s Hs. destruct (proj2 Hnw s Hs) as [W1 W2]. rewrite cnt_app in W2.
        pose proof (cnt_nonneg s rest). lia.
    + assert (Hnw1 : forall l, no_wrap blf (l ++ rest) -> no_wrap blf l).
      { intros l [R W]. split; [intros q Hq; apply R, in_or_app; auto|].
        intros s Hs. destruct (W s Hs) as [W1 W2]. rewrite cnt_app in W2.
        pose proof (cnt_nonneg s rest). lia. }
      destruct (negb (nl =? 0)).
      * destruct (negb (nl =? p)).
        -- apply Hnw1 in Hnw. cbn [app] in Hnw.
           set (b1 := upd_Znth nl blf (u16 (Znth nl blf + 1))).
           assert (A1 : adds blf b1 (repeat (nl, 0) (Z.to_nat 1))).
           { apply adds_one; [|lia]. destruct Hnw as [R W]. split.
             - intros q [<-|[]]. apply R; left; auto.
             - intros s Hs. destruct (W s Hs) as [W1 W2]. split; auto.
               rewrite cnt_repeat. change (Z.of_nat (Z.to_nat 1)) with 1.
               rewrite !cnt_cons, cnt_nil in W2. destruct (nl =? s), (REP_3_6 =? s); lia. }
           assert (A2 : adds b1 (upd_Znth REP_3_6 b1 (u16 (Znth REP_3_6 b1 + 1))) (repeat (REP_3_6, 2) (Z.to_nat 1))).
           { apply adds_one; [|lia]. apply (no_wrap_after blf b1 [(nl, 0)]); [exact Hnw|exact A1]. }
           exact (adds_trans _ _ _ _ _ A1 A2).
        -- apply Hnw1 in Hnw. cbn [app] in Hnw.
           apply (adds_one blf REP_3_6 2 1); [exact Hnw|lia].
      * apply Hnw1 in Hnw.
        destruct (c + 1 <=? 10); apply (adds_one blf _ _ 1); auto; lia.
Qed.

(** The bit-length tree after scan_tree. *)
Theorem scan_tree_counts : forall t mc bl,
  0 <= mc ->
  let t' := set_dl t (mc + 1) 65535 in
  no_wrap (fc bl) (tree_syms (dl t') mc) ->
  fst (scan_tree t mc bl) = t' /\ dl (snd (scan_tree t mc bl)) = dl bl /\
  adds (fc bl) (fc (snd (scan_tree t mc bl))) (tree_syms (dl t') mc).
Proof.
  intros t mc bl Hmc t' Hnw. unfold scan_tree.
  assert (E0 : Znth 0 (dl t) = Znth 0 (dl t')) by (unfold t', set_dl; simpl; rewrite Znth_upd_other; lia).
  unfold tree_syms, init_counts in *. rewrite <- E0 in Hnw |- *.
  destruct (Znth 0 (dl t) =? 0); cbn [fst snd dl fc];
    (split; [reflexivity|split; [reflexivity|]]); apply scan_tree_loop_counts; auto; lia.
Qed.

(** ** The stream's symbols and extra bits; its cost by symbol counts *)

Lemma syms_loop_past : forall fuel lens mc n p nl c mx mn, mc < n -> syms_loop fuel lens mc n p nl c mx mn = [].
Proof. intros [|f]; intros; simpl; [reflexivity|]. destruct (Z.leb_spec n mc); [lia|reflexivity]. Qed.

Definition syms_ok (l : list (Z * Z)) : Prop :=
  forall q, In q l -> 0 <= fst q < 19 /\ snd q = Znth (fst q) extra_blbits.

Lemma syms_ok_app : forall l1 l2, syms_ok l1 -> syms_ok l2 -> syms_ok (l1 ++ l2).
Proof. intros l1 l2 H1 H2 q Hq. apply in_app_or in Hq. destruct Hq; auto. Qed.

Lemma extra_blbits_small : forall s, 0 <= s <= 15 -> Znth s extra_blbits = 0.
Proof.
  intros s Hs. unfold Znth. destruct (Z_lt_dec s 0); [lia|].
  assert (Hn : (Z.to_nat s < 16)%nat) by lia. remember (Z.to_nat s) as m. clear -Hn.
  do 16 (destruct m as [|m]; [reflexivity|]). lia.
Qed.

Lemma syms_loop_ok : forall fuel lens mc n p nl c mx mn,
  (forall i, 0 <= i <= mc -> 0 <= Znth i lens <= 15) -> 0 <= n -> (n <= mc -> 0 <= nl <= 15) ->
  syms_ok (syms_loop fuel lens mc n p nl c mx mn).
Proof.
  induction fuel as [|f IH]; intros lens mc n p nl c mx mn Hl Hn Hnl; [intros q []|].
  cbn [syms_loop]. destruct (Z.leb_spec n mc) as [Hle|Hgt]; [|intros q []].
  assert (Hnl' : n + 1 <= mc -> 0 <= Znth (n + 1) lens <= 15) by (intros; apply Hl; lia).
  destruct ((c + 1 <? mx) && (nl =? Znth (n + 1) lens)); [apply IH; auto; lia|].
  destruct (if Znth (n + 1) lens =? 0 then _ else _) as [mx' mn'].
  apply syms_ok_app; [|apply IH; auto; lia].
  specialize (Hnl Hle).
  destruct (c + 1 <? mn).
  - intros q Hq. apply repeat_spec in Hq. subst q. simpl. split; [lia|]. rewrite extra_blbits_small; lia.
  - destruct (negb (nl =? 0)); [destruct (negb (nl =? p))|destruct (c + 1 <=? 10)];
      intros q Hq; unfold REP_3_6, REPZ_3_10, REPZ_11_138 in Hq; simpl in Hq;
      repeat (destruct Hq as [<-|Hq];
              [cbn [fst snd]; split; [lia| first [reflexivity | (rewrite extra_blbits_small by lia; reflexivity)]]|]);
      destruct Hq.
Qed.

Lemma tree_syms_ok : forall lens mc,
  0 <= mc -> (forall i, 0 <= i <= mc -> 0 <= Znth i lens <= 15) -> syms_ok (tree_syms lens mc).
Proof.
  intros lens mc Hmc Hl. unfold tree_syms. destruct (init_counts (Znth 0 lens)).
  apply syms_loop_ok; auto; [lia|]. intros; apply Hl; lia.
Qed.

Fixpoint sum_syms (f : Z -> Z) (m : nat) : Z :=
  match m with O => 0 | S m' => sum_syms f m' + f (Z.of_nat m') end.

Lemma sum_syms_ext : forall f g m, (forall s, 0 <= s < Z.of_nat m -> f s = g s) -> sum_syms f m = sum_syms g m.
Proof.
  induction m as [|m IH]; intros H; cbn [sum_syms]; [reflexivity|].
  rewrite IH by (intros; apply H; lia). rewrite H by lia. reflexivity.
Qed.

Lemma sum_syms_add : forall f g m, sum_syms (fun s => f s + g s) m = sum_syms f m + sum_syms g m.
Proof. induction m as [|m IH]; cbn [sum_syms]; [reflexivity|]. rewrite IH; lia. Qed.

Lemma sum_syms_indicator : forall x v m, 0 <= x < Z.of_nat m ->
  sum_syms (fun s => (if x =? s then 1 else 0) * v s) m = v x.
Proof.
  induction m as [|m IH]; intros Hx; cbn [sum_syms]; [lia|].
  destruct (Z.eqb_spec x (Z.of_nat m)) as [Ex|Hne].
  - rewrite (sum_syms_ext _ (fun _ => 0)).
    + assert (Z0 : sum_syms (fun _ => 0) m = 0) by (clear; induction m as [|m IH]; cbn [sum_syms]; lia).
      rewrite Z0, <- Ex. lia.
    + intros s Hs. destruct (Z.eqb_spec x s); lia.
  - rewrite IH by lia. lia.
Qed.

(** The stream's cost from the symbol counts: what gen_bitlen adds to opt_len for the bit-length tree. *)
Theorem cost_by_counts : forall tau l, syms_ok l ->
  cost_tau tau l = sum_syms (fun s => cnt s l * (tau s + Znth s extra_blbits)) 19.
Proof.
  intros tau l. induction l as [|[x e] l IH]; intros Hok.
  - unfold cost_tau; cbn [map sumZ]. rewrite (sum_syms_ext _ (fun _ => 0)); [|intros; rewrite cnt_nil; lia].
    clear. generalize 19%nat. induction n; cbn [sum_syms]; lia.
  - assert (Hx := Hok (x, e) (in_eq _ _)). simpl in Hx.
    unfold cost_tau in *; cbn [map sumZ fst snd]. rewrite IH by (intros q Hq; apply Hok; right; auto).
    rewrite (sum_syms_ext (fun s => cnt s ((x, e) :: l) * (tau s + Znth s extra_blbits))
                          (fun s => (if x =? s then 1 else 0) * (tau s + Znth s extra_blbits) +
                                    cnt s l * (tau s + Znth s extra_blbits))).
    + rewrite sum_syms_add, sum_syms_indicator by (simpl; lia). destruct Hx as [_ ->]. lia.
    + intros s Hs. rewrite cnt_cons. lia.
Qed.

(** ** The per-code bound under a bit-length code [tau] *)

(** The cost of one piece of [g] zeros ([1 <= g <= 138]): single zeros, REPZ_3_10 or REPZ_11_138. *)
Definition zpiece (tau : Z -> Z) (g : Z) : Z :=
  if g <=? 0 then 0 else if g <? 3 then g * tau 0 else if g <=? 10 then tau 17 + 3 else tau 18 + 7.

(** The cost of a run of [g] zeros: pieces of 138 (REPZ_11_138) and a last piece of 1..138 zeros.  Equal to the
    recursive definition 0 (g = 0), zpiece g (1 <= g <= 138), tau 18 + 7 + gapcost (g - 138) (g > 138). *)
Definition gapcost (tau : Z -> Z) (g : Z) : Z :=
  if g <=? 0 then 0 else ((g - 1) / 138) * (tau 18 + 7) + zpiece tau (g - 138 * ((g - 1) / 138)).

(** The cost charged to a used code of length [l]: its own symbol, or its share of a REP_3_6 (at least 3 codes
    per REP_3_6 of tau 16 + 2 bits; the ceiling of (tau 16 + 2) / 3). *)
Definition entry_tau (tau : Z -> Z) (l : Z) : Z := Z.max (tau l) ((tau 16 + 4) / 3).

(** [zrun lens n]: the number of zero lengths immediately before index [n]. *)
Fixpoint zrun_nat (lens : list Z) (m : nat) : Z :=
  match m with O => 0 | S m' => if Znth (Z.of_nat m') lens =? 0 then zrun_nat lens m' + 1 else 0 end.
Definition zrun (lens : list Z) (n : Z) : Z := zrun_nat lens (Z.to_nat n).

(** The charge of index [i]: nothing for a zero length, else the entry cost and the zero run before it. *)
Definition ch (tau : Z -> Z) (lens : list Z) (i : Z) : Z :=
  if Znth i lens =? 0 then 0 else entry_tau tau (Znth i lens) + gapcost tau (zrun lens i).
Fixpoint chs_nat (tau : Z -> Z) (lens : list Z) (m : nat) : Z :=
  match m with O => 0 | S m' => chs_nat tau lens m' + ch tau lens (Z.of_nat m') end.
(** [charge tau lens n] = sum of the charges of the indices [0 .. n-1]. *)
Definition charge (tau : Z -> Z) (lens : list Z) (n : Z) : Z := chs_nat tau lens (Z.to_nat n).

Lemma zrun_0 : forall lens, zrun lens 0 = 0.
Proof. reflexivity. Qed.

Lemma zrun_succ : forall lens n, 0 <= n ->
  zrun lens (n + 1) = if Znth n lens =? 0 then zrun lens n + 1 else 0.
Proof. intros. unfold zrun. rewrite Z2Nat.inj_add, Nat.add_1_r by lia. simpl. rewrite Z2Nat.id by lia. reflexivity. Qed.

Lemma charge_0 : forall tau lens, charge tau lens 0 = 0.
Proof. reflexivity. Qed.

Lemma charge_succ : forall tau lens n, 0 <= n -> charge tau lens (n + 1) = charge tau lens n + ch tau lens n.
Proof. intros. unfold charge. rewrite Z2Nat.inj_add, Nat.add_1_r by lia. simpl. rewrite Z2Nat.id by lia. reflexivity. Qed.

Lemma gapcost_0 : forall tau, gapcost tau 0 = 0.
Proof. reflexivity. Qed.

Lemma gapcost_shift : forall tau k c, 0 <= k -> 1 <= c <= 138 ->
  gapcost tau (138 * k + c) = k * (tau 18 + 7) + zpiece tau c.
Proof.
  intros tau k c Hk Hc. unfold gapcost.
  destruct (Z.leb_spec (138 * k + c) 0); [lia|].
  replace ((138 * k + c - 1) / 138) with k.
  - replace (138 * k + c - 138 * k) with c by lia. reflexivity.
  - replace (138 * k + c - 1) with (k * 138 + (c - 1)) by lia.
    rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
Qed.

Lemma zrun_nonneg : forall lens n, 0 <= zrun lens n.
Proof.
  intros lens n. unfold zrun. induction (Z.to_nat n) as [|m IH]; simpl; [lia|].
  destruct (Znth (Z.of_nat m) lens =? 0); lia.
Qed.

Section PerCode.
Variable tau : Z -> Z.
Variable lens : list Z.
Variable mc : Z.
Hypothesis Htau : forall s, 0 <= tau s.
Hypothesis Hmc : 0 <= mc.
Hypothesis Hlens : forall i, 0 <= i <= mc -> 0 <= Znth i lens <= 15.
Hypothesis Hlast : Znth mc lens <> 0.
Hypothesis Hguard : Znth (mc + 1) lens = 65535.

Lemma entry_ge : forall l, tau l <= entry_tau tau l /\ tau 16 + 2 <= 3 * entry_tau tau l /\ 0 <= entry_tau tau l.
Proof.
  intros l. unfold entry_tau. pose proof (Htau l). pose proof (Htau 16).
  pose proof (Z.mul_div_le (tau 16 + 4) 3 ltac:(lia)). pose proof (Z.mod_pos_bound (tau 16 + 4) 3 ltac:(lia)).
  pose proof (Z.div_mod (tau 16 + 4) 3 ltac:(lia)). lia.
Qed.

(** The loop invariant: [C] is the cost emitted so far. *)
Definition pinv (n p nl c mx mn C : Z) : Prop :=
  0 <= n <= mc /\ nl = Znth n lens /\ 0 <= c <= n /\ c < mx /\
  (forall i, n - c <= i < n -> Znth i lens = nl) /\
  (nl <> 0 -> ((nl <> p /\ mx = 7 /\ mn = 4) \/ (nl = p /\ mx = 6 /\ mn = 3)) /\
     C + c * entry_tau tau nl <= charge tau lens n + (if c =? 0 then gapcost tau (zrun lens n) else 0)) /\
  (nl = 0 -> mx = 138 /\ mn = 3 /\
     exists k, 0 <= k /\ zrun lens n = 138 * k + c /\ C <= charge tau lens n + k * (tau 18 + 7)).

Lemma pinv_step : forall fuel n p nl c mx mn C,
  pinv n p nl c mx mn C -> mc + 1 - n <= Z.of_nat fuel ->
  C + cost_tau tau (syms_loop fuel lens mc n p nl c mx mn) <= charge tau lens (mc + 1).
Proof.
  induction fuel as [|fuel IH]; intros n p nl c mx mn C Hinv Hf.
  { destruct Hinv as [Hn _]. simpl in Hf. lia. }
  destruct Hinv as [Hn [Hnl [Hc [Hcm [Hrun [Hnz Hz]]]]]].
  cbn [syms_loop]. destruct (Z.leb_spec n mc) as [_|]; [|lia].
  assert (Hln := Hlens n ltac:(lia)).
  assert (Hch : charge tau lens (n + 1) = charge tau lens n + ch tau lens n) by (apply charge_succ; lia).
  assert (Hzr : zrun lens (n + 1) = if Znth n lens =? 0 then zrun lens n + 1 else 0) by (apply zrun_succ; lia).
  set (nx := Znth (n + 1) lens) in *.
  (* the next length: a real length when n < mc, the guard when n = mc *)
  assert (Hnx : n < mc -> 0 <= nx <= 15) by (intros; unfold nx; apply Hlens; lia).
  assert (Hnx' : n = mc -> nx = 65535) by (intros ->; exact Hguard).
  destruct ((c + 1 <? mx) && (nl =? nx)) eqn:Econt.
  - (* continue *)
    apply andb_true_iff in Econt. destruct Econt as [E1 E2]. apply Z.ltb_lt in E1. apply Z.eqb_eq in E2.
    assert (Hlt : n < mc) by (destruct (Z.eq_dec n mc) as [->|]; [rewrite Hnx' in E2 by auto; lia|lia]).
    apply IH; [|lia]. rewrite <- E2.
    split; [lia|]. split; [exact E2|]. split; [lia|]. split; [lia|].
    split; [intros i Hi; destruct (Z.eq_dec i n) as [->|]; [auto|apply Hrun; lia]|].
    split.
    + intros Hnz0. destruct (Hnz Hnz0) as [Hm HC]. split; [exact Hm|].
      replace (c + 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      rewrite Hch. unfold ch. rewrite <- Hnl. destruct (Z.eqb_spec nl 0) as [|_]; [lia|].
      destruct (Z.eqb_spec c 0) as [->|Hc0].
      * lia.
      * (* inside a run of nonzero lengths: no zero run before n *)
        assert (Zn : zrun lens n = 0).
        { replace n with ((n - 1) + 1) by lia. rewrite zrun_succ by lia.
          rewrite (Hrun (n - 1)) by lia. destruct (Z.eqb_spec nl 0); [lia|reflexivity]. }
        rewrite Zn, gapcost_0 in *. lia.
    + intros Hz0. destruct (Hz Hz0) as [Hm1 [Hm2 [k [Hk [Hzk HC]]]]]. split; [auto|]. split; [auto|].
      exists k. split; [auto|]. split.
      * rewrite Hzr, <- Hnl. destruct (Z.eqb_spec nl 0); lia.
      * rewrite Hch. unfold ch. rewrite <- Hnl. rewrite Hz0, Z.eqb_refl. lia.
  - (* emit a piece of c + 1 equal lengths nl *)
    set (out := if c + 1 <? mn then _ else _).
    set (mm := if nx =? 0 then (138, 3) else if nl =? nx then (6, 3) else (7, 4)).
    assert (Hmm : mm = (fst mm, snd mm)) by (destruct mm; reflexivity).
    rewrite Hmm. cbn beta iota.
    rewrite cost_tau_app.
    assert (Hent := entry_ge nl).
    (* cost of the piece *)
    assert (Hout : (nl <> 0 -> cost_tau tau out <= (c + 1) * entry_tau tau nl) /\
                   (nl = 0 -> cost_tau tau out = zpiece tau (c + 1))).
    { split.
      - intros Hnz0. destruct (Hnz Hnz0) as [Hm _]. subst out.
        destruct (Z.ltb_spec (c + 1) mn).
        + rewrite cost_tau_repeat, Z2Nat.id by lia. nia.
        + destruct (Z.eqb_spec nl 0); [lia|]. cbn [negb].
          destruct Hm as [[Hp [-> ->]]|[Hp [-> ->]]].
          * destruct (Z.eqb_spec nl p); [lia|]. cbn [negb app].
            unfold cost_tau; cbn [map sumZ fst snd]. unfold REP_3_6. nia.
          * destruct (Z.eqb_spec nl p); [|lia]. cbn [negb app].
            unfold cost_tau; cbn [map sumZ fst snd]. unfold REP_3_6. nia.
      - intros Hz0. destruct (Hz Hz0) as [-> [-> _]]. subst out. unfold zpiece.
        destruct (Z.leb_spec (c + 1) 0); [lia|].
        destruct (Z.ltb_spec (c + 1) 3).
        + rewrite cost_tau_repeat, Z2Nat.id, Hz0 by lia. lia.
        + rewrite Hz0, Z.eqb_refl. cbn [negb].
          destruct (c + 1 <=? 10); unfold cost_tau; cbn [map sumZ fst snd]; unfold REPZ_3_10, REPZ_11_138; lia. }
    destruct (Z.eq_dec n mc) as [Heq|Hlt].
    + (* the last index: the rest of the stream is empty *)
      rewrite syms_loop_past by lia. unfold cost_tau at 2; cbn [map sumZ].
      assert (Hnz0 : nl <> 0) by (rewrite Hnl, Heq; auto).
      destruct (Hnz Hnz0) as [_ HC]. rewrite <- Heq, Hch. unfold ch. rewrite <- Hnl.
      destruct (Z.eqb_spec nl 0); [lia|].
      destruct (Z.eqb_spec c 0) as [->|Hc0].
      * pose proof (proj1 Hout Hnz0). lia.
      * assert (Zn : zrun lens n = 0).
        { replace n with ((n - 1) + 1) by lia. rewrite zrun_succ by lia.
          rewrite (Hrun (n - 1)) by lia. destruct (Z.eqb_spec nl 0); [lia|reflexivity]. }
        rewrite Zn, gapcost_0. pose proof (proj1 Hout Hnz0). lia.
    + assert (Hlt' : n < mc) by lia. specialize (Hnx Hlt').
      (* the cost after this piece, charged up to n + 1 *)
      assert (Hafter : (nx <> 0 -> C + cost_tau tau out <= charge tau lens (n + 1) + gapcost tau (zrun lens (n + 1)))
                       /\ (nx = 0 -> exists k, 0 <= k /\ zrun lens (n + 1) = 138 * k /\
                             C + cost_tau tau out <= charge tau lens (n + 1) + k * (tau 18 + 7))).
      { destruct (Z.eqb_spec nl 0) as [Hz0|Hnz0].
        - (* a zero piece *)
          destruct (Hz Hz0) as [Hm1 [Hm2 [k [Hk [Hzk HC]]]]].
          rewrite (proj2 Hout Hz0). rewrite Hch. unfold ch. rewrite <- Hnl, Hz0, Z.eqb_refl.
          rewrite Hzr, <- Hnl, Hz0, Z.eqb_refl.
          assert (Hc1 : c + 1 <= 138) by lia.
          split.
          + intros Hnx0.
            replace (zrun lens n + 1) with (138 * k + (c + 1)) by lia.
            rewrite gapcost_shift by lia. lia.
          + intros Hnx0.
            (* the zero run goes on: the piece is full *)
            assert (Hfull : c + 1 = 138).
            { apply andb_false_iff in Econt. destruct Econt as [E|E].
              - apply Z.ltb_ge in E. lia.
              - apply Z.eqb_neq in E. lia. }
            exists (k + 1). split; [lia|]. split; [lia|].
            assert (zpiece tau (c + 1) = tau 18 + 7) by (rewrite Hfull; reflexivity). nia.
        - (* a nonzero piece *)
          destruct (Hnz Hnz0) as [_ HC]. pose proof (proj1 Hout Hnz0).
          rewrite Hch. unfold ch. rewrite <- Hnl. destruct (Z.eqb_spec nl 0); [lia|].
          rewrite Hzr, <- Hnl. destruct (Z.eqb_spec nl 0); [lia|]. rewrite gapcost_0.
          destruct (Z.eqb_spec c 0) as [->|Hc0].
          + split; [intros; lia|]. intros _. exists 0. split; [lia|]. split; [lia|]. lia.
          + assert (Zn : zrun lens n = 0).
            { replace n with ((n - 1) + 1) by lia. rewrite zrun_succ by lia.
              rewrite (Hrun (n - 1)) by lia. destruct (Z.eqb_spec nl 0); [lia|reflexivity]. }
            rewrite Zn, gapcost_0 in *.
            split; [intros; lia|]. intros _. exists 0. split; [lia|]. split; [lia|]. lia. }
      assert (HIH := IH (n + 1) nl nx 0 (fst mm) (snd mm) (C + cost_tau tau out)).
      enough (HP : pinv (n + 1) nl nx 0 (fst mm) (snd mm) (C + cost_tau tau out))
        by (specialize (HIH HP ltac:(lia)); lia).
      { (* the invariant at n + 1 *)
        split; [lia|]. split; [reflexivity|]. split; [lia|].
        split; [unfold mm; destruct (nx =? 0); [|destruct (nl =? nx)]; simpl; lia|].
        split; [intros; lia|]. split.
        -- intros Hnx0. split.
           ++ unfold mm. destruct (Z.eqb_spec nx 0); [lia|].
              destruct (Z.eqb_spec nl nx); simpl; [right|left]; auto.
           ++ destruct Hafter as [Ha _]. replace (0 =? 0) with true by reflexivity.
              specialize (Ha Hnx0). lia.
        -- intros Hnx0. split; [unfold mm; rewrite Hnx0; reflexivity|].
           split; [unfold mm; rewrite Hnx0; reflexivity|].
           destruct Hafter as [_ Hb]. destruct (Hb Hnx0) as [k [Hk [Hzk HC]]].
           exists k. split; [auto|]. split; [lia|]. lia. }
Qed.

End PerCode.

(** The per-code bound: the stream's cost under [tau] is at most the sum, over the used codes [c <= max_code],
    of [entry_tau tau (lens[c]) + gapcost tau (zero run before c)]. *)
Theorem tree_syms_cost : forall tau lens mc,
  (forall s, 0 <= tau s) -> 0 <= mc ->
  (forall i, 0 <= i <= mc -> 0 <= Znth i lens <= 15) -> Znth mc lens <> 0 -> Znth (mc + 1) lens = 65535 ->
  cost_tau tau (tree_syms lens mc) <= charge tau lens (mc + 1).
Proof.
  intros tau lens mc Htau Hmc Hlens Hlast Hguard. unfold tree_syms, init_counts.
  replace (cost_tau tau _) with (0 + cost_tau tau (syms_loop (Z.to_nat (mc + 1)) lens mc 0 (-1) (Znth 0 lens) 0
      (fst (if Znth 0 lens =? 0 then (138, 3) else (7, 4))) (snd (if Znth 0 lens =? 0 then (138, 3) else (7, 4)))))
    by (destruct (Znth 0 lens =? 0); reflexivity).
  apply pinv_step; auto; [|lia].
  assert (H0 := Hlens 0 ltac:(lia)).
  split; [lia|]. split; [reflexivity|]. split; [lia|].
  split; [destruct (Znth 0 lens =? 0); simpl; lia|].
  split; [intros; lia|]. split.
  - intros Hnz. split.
    + destruct (Z.eqb_spec (Znth 0 lens) 0); [lia|]. left; simpl; repeat split; lia.
    + rewrite Z.eqb_refl, zrun_0, gapcost_0, charge_0. lia.
  - intros Hz. rewrite Hz. simpl. split; [reflexivity|]. split; [reflexivity|].
    exists 0. rewrite ?zrun_0, ?charge_0. unfold zrun, charge; simpl; lia.
Qed.

(** ** The crude bound: bit-length codes of at most 7 bits give at most 7 bits per entry *)

Lemma crude_step : forall bll lens mc, (forall s, Znth s bll <= 7) ->
  forall fuel n p nl c mx mn C, 0 <= c <= n -> 3 <= mn -> n <= mc + 1 -> C <= 7 * (n - c) ->
  C + stream_bits bll (syms_loop fuel lens mc n p nl c mx mn) <= 7 * (mc + 1).
Proof.
  intros bll lens mc Hb. unfold stream_bits.
  induction fuel as [|fuel IH]; intros n p nl c mx mn C Hc Hmn Hn HC.
  { cbn [syms_loop]; unfold cost_tau; cbn [map sumZ]; lia. }
  cbn [syms_loop]. destruct (Z.leb_spec n mc) as [Hle|Hgt]; [|unfold cost_tau; cbn [map sumZ]; lia].
  destruct ((c + 1 <? mx) && (nl =? Znth (n + 1) lens)); [apply IH; lia|].
  set (mm := if Znth (n + 1) lens =? 0 then (138, 3) else if nl =? Znth (n + 1) lens then (6, 3) else (7, 4)).
  assert (Hmm : mm = (fst mm, snd mm)) by (destruct mm; reflexivity).
  assert (Hmn' : 3 <= snd mm) by (unfold mm; destruct (_ =? 0); [|destruct (_ =? _)]; simpl; lia).
  rewrite Hmm. cbn beta iota. rewrite cost_tau_app.
  set (out := if c + 1 <? mn then _ else _).
  assert (Hout : cost_tau (fun s => Znth s bll) out <= 7 * (c + 1)).
  { subst out. pose proof (Hb nl). pose proof (Hb REP_3_6). pose proof (Hb REPZ_3_10). pose proof (Hb REPZ_11_138).
    destruct (Z.ltb_spec (c + 1) mn).
    - rewrite cost_tau_repeat, Z2Nat.id by lia. nia.
    - destruct (negb (nl =? 0)); [destruct (negb (nl =? p))|destruct (Z.leb_spec (c + 1) 10)];
        unfold cost_tau; cbn [app map sumZ fst snd]; lia. }
  pose proof (IH (n + 1) nl (Znth (n + 1) lens) 0 (fst mm) (snd mm) (C + cost_tau (fun s => Znth s bll) out)).
  lia.
Qed.

Theorem tree_syms_crude : forall bll lens mc, (forall s, Znth s bll <= 7) -> 0 <= mc ->
  stream_bits bll (tree_syms lens mc) <= 7 * (mc + 1).
Proof.
  intros bll lens mc Hb Hmc. unfold tree_syms, init_counts.
  replace (stream_bits bll _) with (0 + stream_bits bll (syms_loop (Z.to_nat (mc + 1)) lens mc 0 (-1) (Znth 0 lens) 0
      (fst (if Znth 0 lens =? 0 then (138, 3) else (7, 4))) (snd (if Znth 0 lens =? 0 then (138, 3) else (7, 4)))))
    by (destruct (Znth 0 lens =? 0); reflexivity).
  apply crude_step; auto; try lia. destruct (Znth 0 lens =? 0); simpl; lia.
Qed.
