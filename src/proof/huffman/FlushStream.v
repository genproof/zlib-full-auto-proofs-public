(** * Lemma (i): facts about send_tree's run-length stream, symbol counting, small table facts *)

From Coq Require Import ZArith List Lia Bool Permutation.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.huffman.Model Zlib.proof.huffman.HuffAbs Zlib.proof.huffman.Heap
               Zlib.proof.huffman.Bits Zlib.proof.huffman.Overlay Zlib.proof.huffman.BuildTree Zlib.proof.huffman.FlushTree.
Require Zlib.proof.huffman.Header.
Import ListNotations.
Local Open Scope Z_scope.

Module H := Zlib.proof.huffman.Header.

(** ** A nonzero length is sent as itself the first time *)

Lemma stream_has_value : forall fuel lens mc n p nl c mx mn,
  n <= mc -> (Z.to_nat (mc + 1 - n) <= fuel)%nat -> nl <> 0 -> p <> nl -> 0 <= nl <= 15 -> 0 <= c ->
  Znth (mc + 1) lens = 65535 ->
  In (nl, 0) (H.syms_loop fuel lens mc n p nl c mx mn).
Proof.
  induction fuel as [|fuel IH]; intros lens mc n p nl c mx mn Hn Hf Hnl Hp Hr Hc0 Hg; [lia|].
  cbn [H.syms_loop]. replace (n <=? mc) with true by (symmetry; apply Z.leb_le; auto).
  destruct ((c + 1 <? mx) && (nl =? Znth (n + 1) lens)) eqn:Ec.
  - apply andb_true_iff in Ec. destruct Ec as [_ E]. apply Z.eqb_eq in E.
    assert (n + 1 <= mc) by (destruct (Z.eq_dec n mc) as [->|]; [rewrite Hg in E; lia|lia]).
    rewrite E in Hnl, Hp, Hr |- *. apply IH; auto; lia.
  - destruct (if Znth (n + 1) lens =? 0 then _ else _) as [mx' mn'].
    apply in_or_app. left. destruct (c + 1 <? mn).
    + destruct (Z.to_nat (c + 1)) as [|k] eqn:Ek; [lia|]. left; reflexivity.
    + replace (negb (nl =? 0)) with true by (symmetry; apply negb_true_iff, Z.eqb_neq; auto).
      replace (negb (nl =? p)) with true by (symmetry; apply negb_true_iff, Z.eqb_neq; auto).
      left; reflexivity.
Qed.

Lemma stream_first_nonzero : forall fuel lens mc n p nl c mx mn i0,
  n <= i0 <= mc -> (Z.to_nat (mc + 1 - n) <= fuel)%nat -> nl = Znth n lens ->
  Znth i0 lens <> 0 -> 0 <= Znth i0 lens <= 15 -> (forall j, n <= j < i0 -> Znth j lens = 0) ->
  (n = i0 -> p <> nl) -> 0 <= c -> Znth (mc + 1) lens = 65535 ->
  In (Znth i0 lens, 0) (H.syms_loop fuel lens mc n p nl c mx mn).
Proof.
  induction fuel as [|fuel IH]; intros lens mc n p nl c mx mn i0 Hn Hf Hnl Hz Hr Hj Hp Hc0 Hg; [lia|].
  destruct (Z.eq_dec n i0) as [->|Hne].
  - rewrite Hnl in *. apply stream_has_value; auto; lia.
  - assert (Hnl0 : nl = 0) by (rewrite Hnl; apply Hj; lia).
    cbn [H.syms_loop]. replace (n <=? mc) with true by (symmetry; apply Z.leb_le; lia).
    destruct ((c + 1 <? mx) && (nl =? Znth (n + 1) lens)) eqn:Ec.
    + apply andb_true_iff in Ec. destruct Ec as [_ E]. apply Z.eqb_eq in E.
      assert (n + 1 <> i0) by (intros Hc; rewrite <- Hc in Hz; lia).
      apply IH; auto; try lia. intros j Hj'; apply Hj; lia.
    + destruct (if Znth (n + 1) lens =? 0 then _ else _) as [mx' mn'].
      apply in_or_app. right. apply IH; auto; try lia.
      * intros j Hj'; apply Hj; lia.
      * intros Hc. rewrite Hc. lia.
Qed.

Lemma first_nonzero : forall (lens : list Z) i, 0 <= i -> Znth i lens <> 0 ->
  exists i0, 0 <= i0 <= i /\ Znth i0 lens <> 0 /\ forall j, 0 <= j < i0 -> Znth j lens = 0.
Proof.
  intros lens i. remember (Z.to_nat i) as k eqn:Ek. revert i Ek.
  induction k as [k IH] using lt_wf_ind. intros i Ek Hi Hnz.
  destruct (existsb (fun j => negb (Znth j lens =? 0)) (zseq 0 (Z.to_nat i))) eqn:E.
  - apply existsb_exists in E. destruct E as [j [Hj Hjn]]. apply in_zseq in Hj.
    apply negb_true_iff, Z.eqb_neq in Hjn.
    destruct (IH (Z.to_nat j) ltac:(lia) j eq_refl ltac:(lia) Hjn) as [i0 [H1 [H2 H3]]].
    exists i0. split; [lia|]. auto.
  - exists i. split; [lia|]. split; [auto|]. intros j Hj.
    destruct (Z.eq_dec (Znth j lens) 0) as [|Hne]; [auto|]. exfalso.
    assert (Ht : existsb (fun j => negb (Znth j lens =? 0)) (zseq 0 (Z.to_nat i)) = true).
    { apply existsb_exists. exists j. split; [apply in_zseq; lia|]. apply negb_true_iff, Z.eqb_neq; auto. }
    congruence.
Qed.

(** The stream contains the first nonzero length of the table. *)
Theorem tree_syms_has_length : forall lens mc, 0 <= mc ->
  (forall i, 0 <= i <= mc -> 0 <= Znth i lens <= 15) -> Znth mc lens <> 0 -> Znth (mc + 1) lens = 65535 ->
  exists v, 1 <= v <= 15 /\ In (v, 0) (H.tree_syms lens mc).
Proof.
  intros lens mc Hmc Hl Hnz Hg.
  destruct (first_nonzero lens mc Hmc Hnz) as [i0 [Hi0 [Hz Hj]]].
  exists (Znth i0 lens). split; [specialize (Hl i0 Hi0); lia|].
  unfold H.tree_syms, H.init_counts.
  assert (H0 := Hl 0 ltac:(lia)).
  destruct (Znth 0 lens =? 0); apply stream_first_nonzero; auto; lia.
Qed.

(** The symbols of the stream: lengths of the table or 16, 17, 18. *)
Lemma syms_loop_range : forall fuel lens mc n p nl c mx mn B,
  (forall i, 0 <= i <= mc -> 0 <= Znth i lens <= B) -> 0 <= n -> (n <= mc -> 0 <= nl <= B) ->
  forall q, In q (H.syms_loop fuel lens mc n p nl c mx mn) -> (0 <= fst q <= B \/ 16 <= fst q <= 18).
Proof.
  induction fuel as [|f IH]; intros lens mc n p nl c mx mn B Hl Hn Hnl q Hq; [destruct Hq|].
  cbn [H.syms_loop] in Hq. destruct (Z.leb_spec n mc) as [Hle|Hgt]; [|destruct Hq].
  assert (Hnl' : n + 1 <= mc -> 0 <= Znth (n + 1) lens <= B) by (intros; apply Hl; lia).
  destruct ((c + 1 <? mx) && (nl =? Znth (n + 1) lens));
    [exact (IH lens mc (n + 1) p (Znth (n + 1) lens) (c + 1) mx mn B Hl ltac:(lia) Hnl' q Hq)|].
  destruct (if Znth (n + 1) lens =? 0 then _ else _) as [mx' mn'].
  apply in_app_or in Hq. destruct Hq as [Hq|Hq];
    [|exact (IH lens mc (n + 1) nl (Znth (n + 1) lens) 0 mx' mn' B Hl ltac:(lia) Hnl' q Hq)].
  specialize (Hnl Hle).
  destruct (c + 1 <? mn).
  - apply repeat_spec in Hq. subst q. simpl. left; lia.
  - destruct (negb (nl =? 0)); [destruct (negb (nl =? p))|destruct (c + 1 <=? 10)];
      unfold REP_3_6, REPZ_3_10, REPZ_11_138 in Hq; simpl in Hq;
      repeat (destruct Hq as [<-|Hq]; [simpl; lia|]); destruct Hq.
Qed.

Lemma tree_syms_range : forall lens mc B, 0 <= mc -> (forall i, 0 <= i <= mc -> 0 <= Znth i lens <= B) ->
  forall q, In q (H.tree_syms lens mc) -> (0 <= fst q <= B \/ 16 <= fst q <= 18).
Proof.
  intros lens mc B Hmc Hl q Hq. unfold H.tree_syms in Hq. destruct (H.init_counts (Znth 0 lens)) as [mx mn].
  exact (syms_loop_range _ lens mc 0 (-1) (Znth 0 lens) 0 mx mn B Hl ltac:(lia) ltac:(intros; apply Hl; lia) q Hq).
Qed.

(** ** Sums over symbols indices *)

Lemma sum_syms_zseq : forall f m, H.sum_syms f m = sumZ (map f (zseq 0 m)).
Proof.
  intros f m. induction m as [|m IH]; [reflexivity|].
  cbn [H.sum_syms]. rewrite IH, zseq_succ_r, map_app, sumZ_app. simpl. lia.
Qed.

Lemma cnt_pos : forall s l, (exists e, In (s, e) l) -> 1 <= H.cnt s l.
Proof.
  intros s l [e He]. unfold H.cnt. induction l as [|q l IH]; [destruct He|].
  destruct He as [Eq|He].
  - subst q. simpl. rewrite Z.eqb_refl. simpl. lia.
  - specialize (IH He). simpl. destruct (fst q =? s); simpl; lia.
Qed.

Lemma cnt_in : forall s l, 1 <= H.cnt s l -> exists e, In (s, e) l.
Proof.
  intros s l. unfold H.cnt. induction l as [|[x e] l IH]; [simpl; lia|].
  simpl. destruct (Z.eqb_spec x s) as [<-|Hne]; [intros _; exists e; left; reflexivity|].
  intros H1. destruct (IH H1) as [e' He']. exists e'. right; auto.
Qed.

Lemma sumZ_indicator_zseq : forall x n c, 0 <= x < Z.of_nat n ->
  sumZ (map (fun s => if x =? s then c else 0) (zseq 0 n)) = c.
Proof.
  intros x n c Hx. rewrite (sumZ_map_ext' _ (fun s => if s =? x then c else 0)).
  - apply sumZ_indicator2; [apply zseq_nodup|apply in_zseq; lia].
  - intros s _. destruct (Z.eqb_spec x s), (Z.eqb_spec s x); congruence.
Qed.

Lemma sum_cnt_length : forall l, (forall q, In q l -> 0 <= fst q < 19) ->
  sumZ (map (fun s => H.cnt s l) (zseq 0 19)) = Z.of_nat (length l).
Proof.
  induction l as [|[x e] l IH]; intros Hl.
  - reflexivity.
  - rewrite (sumZ_map_ext' (fun s => H.cnt s ((x, e) :: l)) (fun s => (if x =? s then 1 else 0) + H.cnt s l))
      by (intros; apply H.cnt_cons).
    rewrite sumZ_map_add'. rewrite IH by (intros; apply Hl; right; auto).
    rewrite sumZ_indicator_zseq by (specialize (Hl (x, e) (in_eq _ _)); simpl in Hl; simpl; lia).
    cbn [length]. lia.
Qed.

(** ** find_max_blindex *)

Lemma fmb_spec : forall fuel bl i, 3 <= i -> (Z.to_nat (i - 2) <= fuel)%nat ->
  (exists r, 3 <= r <= i /\ Znth (Znth r bl_order) (dl bl) <> 0) ->
  3 <= find_max_blindex fuel bl i <= i.
Proof.
  induction fuel as [|fuel IH]; intros bl i Hi Hf [r [Hr Hnz]]; [lia|].
  cbn [find_max_blindex]. replace (i >=? 3) with true by (symmetry; apply Z.geb_le; lia).
  destruct (Z.eqb_spec (Znth (Znth i bl_order) (dl bl)) 0) as [E|E]; cbn [negb]; [|lia].
  assert (Hri : r <> i) by (intros ->; contradiction).
  assert (H1 := IH bl (i - 1) ltac:(lia) ltac:(lia) ltac:(exists r; split; [lia|auto])). lia.
Qed.

Definition blo_ok (v : Z) : bool := existsb (fun r => Znth r bl_order =? v) (zseq 3 16).

Lemma blo_all : forallb blo_ok (zseq 0 16) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma bl_order_small : forall v, 0 <= v <= 15 -> exists r, 3 <= r <= 18 /\ Znth r bl_order = v.
Proof.
  intros v Hv. assert (H1 := proj1 (forallb_forall _ _) blo_all v ltac:(apply in_zseq; simpl; lia)).
  unfold blo_ok in H1. apply existsb_exists in H1. destruct H1 as [r [Hr E]]. apply in_zseq in Hr.
  apply Z.eqb_eq in E. exists r. split; [simpl in Hr; lia|auto].
Qed.

Lemma bl_order_range : forall r, 0 <= r < 19 -> 0 <= Znth r bl_order < 19.
Proof.
  intros r Hr. assert (G : forallb (fun r => (0 <=? Znth r bl_order) && (Znth r bl_order <? 19)) (zseq 0 19) = true)
    by (vm_compute; reflexivity).
  assert (H1 := proj1 (forallb_forall _ _) G r ltac:(apply in_zseq; simpl; lia)).
  apply andb_true_iff in H1. destruct H1 as [A B]. apply Z.leb_le in A. apply Z.ltb_lt in B. lia.
Qed.

(** ** Depth at most the number of leaves minus one *)

Lemma huff_depth_count : forall P R, huff P R -> forall k,
  (forall I, In I P -> forall x, In x I -> ld x <= k) -> forall x, In x R -> ld x <= k + Z.of_nat (length P) - 1.
Proof.
  intros P R H. induction H as [I|P a b rest R Hp Ha Hb Hh IH]; intros k Hk x Hx.
  - simpl. specialize (Hk I (in_eq _ _) x Hx). lia.
  - assert (HL : length P = S (S (length rest))) by (rewrite (Permutation_length Hp); reflexivity).
    assert (Hk' : forall J, In J (merge a b :: rest) -> forall y, In y J -> ld y <= k + 1).
    { intros J [<-|HJ] y Hy.
      - apply in_merge in Hy. destruct Hy as [z [-> [Hz|Hz]]]; unfold deeper, ld; simpl.
        + assert (In a P) by (apply (Permutation_in _ (Permutation_sym Hp)); left; auto).
          specialize (Hk a H z Hz). unfold ld in Hk. lia.
        + assert (In b P) by (apply (Permutation_in _ (Permutation_sym Hp)); right; left; auto).
          specialize (Hk b H z Hz). unfold ld in Hk. lia.
      - assert (In J P) by (apply (Permutation_in _ (Permutation_sym Hp)); right; right; auto).
        specialize (Hk J H y Hy). lia. }
    specialize (IH (k + 1) Hk' x Hx). cbn [length] in IH. rewrite HL. lia.
Qed.

(** ** charge reads tau only on 0..18 *)

Lemma charge_tau_ext : forall tau1 tau2 lens n, 0 <= n -> (forall s, 0 <= s < 19 -> tau1 s = tau2 s) ->
  (forall i, 0 <= i < n -> 0 <= Znth i lens <= 15) -> H.charge tau1 lens n = H.charge tau2 lens n.
Proof.
  intros tau1 tau2 lens n Hn Ht Hl. unfold H.charge.
  assert (G : forall m, Z.of_nat m <= n -> H.chs_nat tau1 lens m = H.chs_nat tau2 lens m).
  { induction m as [|m IH]; intros Hm; cbn [H.chs_nat]; [reflexivity|].
    rewrite IH by lia. f_equal. unfold H.ch.
    destruct (Znth (Z.of_nat m) lens =? 0); [reflexivity|].
    unfold H.entry_tau, H.gapcost, H.zpiece. rewrite !Ht by (try specialize (Hl (Z.of_nat m) ltac:(lia)); lia).
    reflexivity. }
  apply G. lia.
Qed.

(** ** The symbol codes of a block *)

Lemma lcode_range : forall s, valid_sym (fst s) (snd s) -> 0 <= lcode_of s < L_CODES /\ lcode_of s <> END_BLOCK.
Proof.
  intros [d lc] [Hl Hd]. unfold lcode_of; simpl in *. destruct (Z.eqb_spec d 0).
  - unfold L_CODES, END_BLOCK. lia.
  - destruct (length_code_facts lc Hl) as [A _]. unfold L_CODES, END_BLOCK, LITERALS. lia.
Qed.

Definition dcode_of (s : Z * Z) : Z := d_code (fst s - 1).

Lemma dcode_range : forall s, valid_sym (fst s) (snd s) -> fst s <> 0 -> 0 <= dcode_of s < D_CODES.
Proof.
  intros [d lc] [Hl Hd] Hne. unfold dcode_of; simpl in *. destruct (dist_code_facts (d - 1) ltac:(lia)) as [A _].
  unfold D_CODES. lia.
Qed.

(** Counting: a sum over the symbols grouped by code. *)
Lemma sum_by_code : forall (code : Z * Z -> Z) (P : Z * Z -> bool) (phi : Z -> Z) n (syms : list (Z * Z)),
  (forall s, In s syms -> P s = true -> 0 <= code s < n) ->
  sumZ (map (fun s => if P s then phi (code s) else 0) syms) =
  sumZ (map (fun c => Zlength (filter (fun s => P s && (code s =? c)) syms) * phi c) (zseq 0 (Z.to_nat n))).
Proof.
  intros code P phi n syms. induction syms as [|s syms IH]; intros Hs.
  - cbn [map sumZ]. symmetry. clear.
    induction (zseq 0 (Z.to_nat n)) as [|a l IHl]; [reflexivity|]. cbn [map sumZ filter] in IHl |- *.
    rewrite Zlength_nil in *. lia.
  - cbn [map sumZ]. rewrite IH by (intros; apply Hs; auto; right; auto).
    rewrite (sumZ_map_ext' (fun c => Zlength (filter (fun s0 => P s0 && (code s0 =? c)) (s :: syms)) * phi c)
               (fun c => (if P s && (code s =? c) then phi c else 0) +
                         Zlength (filter (fun s0 => P s0 && (code s0 =? c)) syms) * phi c)).
    + rewrite sumZ_map_add'. f_equal.
      destruct (P s) eqn:EP; simpl.
      * rewrite (sumZ_map_ext' _ (fun c => if code s =? c then phi (code s) else 0)).
        -- symmetry. apply sumZ_indicator_zseq. specialize (Hs s (in_eq _ _) EP). lia.
        -- intros c _. destruct (Z.eqb_spec (code s) c); [subst; reflexivity|reflexivity].
      * clear. induction (zseq 0 (Z.to_nat n)); simpl; lia.
    + intros c _. simpl. destruct (P s && (code s =? c)); [rewrite Zlength_cons|]; lia.
Qed.
