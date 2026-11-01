(** * Lemma (i) for dynamic blocks: the bound of BlockFacts from a per-code certificate

    A certificate [C] gives integer multipliers (all scaled by [ce_D C]) for the facts of [block_facts]:
    [ce_lam] for (A), [ce_ml]/[ce_md] for the Kraft sums, [ce_eta] for the number of symbols, [ce_kap] for
    "as many length codes as distance codes", the tables [ce_P]/[ce_R] that split the excess cost of a match
    (u + v - 24)^+ into a length part and a distance part, [ce_th0] for H <= 2283, a menu of bit-length codes
    [ce_menu] with weights for the header bound under a bit-length code (with overhead [ce_dbl]), and the gap
    multipliers [ce_sgl]/[ce_sgd].  After the combination the bound is a sum of per-code terms; each is linear in
    the code's frequency for a fixed length, so it is checked (by computation, [cert_ok]) at the two ends of the
    frequency range the Fibonacci caps allow, for every length 1..15.  [cert_sound] turns a checked certificate
    into the overlay bound. *)

From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.huffman.Model Zlib.proof.huffman.HuffAbs Zlib.proof.huffman.Heap
               Zlib.proof.huffman.Bits Zlib.proof.huffman.Header Zlib.proof.huffman.Overlay
               Zlib.proof.huffman.BlockFacts.
Import ListNotations.
Local Open Scope Z_scope.

Notation hsum := HuffAbs.sumZ.

(** ** Sums over ranges *)

Definition rs (a : Z) (n : nat) (g : Z -> Z) : Z := hsum (map g (zseq a n)).

Lemma rs_S : forall a n g, rs a (S n) g = g a + rs (a + 1) n g.
Proof. reflexivity. Qed.

Lemma rs_O : forall a g, rs a O g = 0.
Proof. reflexivity. Qed.

Lemma rs_ext : forall n a g h, (forall i, a <= i < a + Z.of_nat n -> g i = h i) -> rs a n g = rs a n h.
Proof.
  induction n as [|n IH]; intros a g h H; [reflexivity|].
  rewrite !rs_S. rewrite H by lia. rewrite (IH (a + 1) g h) by (intros; apply H; lia). reflexivity.
Qed.

Lemma rs_le : forall n a g h, (forall i, a <= i < a + Z.of_nat n -> g i <= h i) -> rs a n g <= rs a n h.
Proof.
  induction n as [|n IH]; intros a g h H; [rewrite !rs_O; lia|].
  rewrite !rs_S. assert (H1 := H a ltac:(lia)). assert (H2 := IH (a + 1) g h ltac:(intros; apply H; lia)). lia.
Qed.

Lemma rs_add : forall n a g h, rs a n (fun i => g i + h i) = rs a n g + rs a n h.
Proof. induction n as [|n IH]; intros a g h; [reflexivity|]. rewrite !rs_S, IH. lia. Qed.

Lemma rs_scal : forall n a k g, rs a n (fun i => k * g i) = k * rs a n g.
Proof. induction n as [|n IH]; intros a k g; [rewrite !rs_O; lia|]. rewrite !rs_S, IH. lia. Qed.

Lemma rs_nonneg : forall n a g, (forall i, a <= i < a + Z.of_nat n -> 0 <= g i) -> 0 <= rs a n g.
Proof.
  intros n a g H. assert (E := rs_le n a (fun _ => 0) g H).
  assert (Z0 : rs a n (fun _ => 0) = 0).
  { clear. revert a. induction n as [|n IH]; intros a; [reflexivity|]. rewrite rs_S, IH. lia. }
  lia.
Qed.

Lemma rs_zero : forall n a g, (forall i, a <= i < a + Z.of_nat n -> g i = 0) -> rs a n g = 0.
Proof.
  intros n a g H. rewrite (rs_ext n a g (fun i => 0 * g i)) by (intros; rewrite H; lia).
  rewrite rs_scal. lia.
Qed.

Lemma rs_ind : forall n a b v, a <= b < a + Z.of_nat n -> rs a n (fun i => if i =? b then v else 0) = v.
Proof.
  induction n as [|n IH]; intros a b v H; [lia|]. rewrite rs_S.
  destruct (Z.eqb_spec a b) as [->|Hne].
  - rewrite rs_zero; [lia|]. intros i Hi. destruct (Z.eqb_spec i b); [lia|reflexivity].
  - rewrite IH by lia. lia.
Qed.

Lemma rs_snoc : forall n a g, rs a (S n) g = rs a n g + g (a + Z.of_nat n).
Proof.
  induction n as [|n IH]; intros a g.
  - rewrite rs_S, !rs_O. simpl. replace (a + 0) with a by lia. lia.
  - rewrite rs_S, IH, rs_S. replace (a + 1 + Z.of_nat n) with (a + Z.of_nat (S n)) by lia. lia.
Qed.

Lemma rs_split : forall m n a g, rs a (n + m) g = rs a n g + rs (a + Z.of_nat n) m g.
Proof.
  induction n as [|n IH]; intros a g.
  - simpl. replace (a + 0) with a by lia. reflexivity.
  - simpl (S n + m)%nat. rewrite !rs_S, IH. replace (a + 1 + Z.of_nat n) with (a + Z.of_nat (S n)) by lia. lia.
Qed.

Lemma rs_single : forall n a g b, (forall i, a <= i < a + Z.of_nat n -> 0 <= g i) -> a <= b < a + Z.of_nat n ->
  g b <= rs a n g.
Proof.
  intros n a g b H Hb.
  assert (E : rs a n g = rs a n (fun i => if i =? b then g b else 0) + rs a n (fun i => if i =? b then 0 else g i)).
  { rewrite <- rs_add. apply rs_ext. intros i Hi. destruct (Z.eqb_spec i b); subst; lia. }
  rewrite E, rs_ind by lia. assert (0 <= rs a n (fun i => if i =? b then 0 else g i)); [|lia].
  apply rs_nonneg. intros i Hi. destruct (i =? b); [lia|]. apply H; auto.
Qed.

Lemma rs_two : forall n a g b1 b2, (forall i, a <= i < a + Z.of_nat n -> 0 <= g i) ->
  a <= b1 < a + Z.of_nat n -> a <= b2 < a + Z.of_nat n -> b1 <> b2 -> g b1 + g b2 <= rs a n g.
Proof.
  intros n a g b1 b2 H H1 H2 Hne.
  assert (E : rs a n g = rs a n (fun i => if i =? b1 then g b1 else 0) + rs a n (fun i => if i =? b1 then 0 else g i)).
  { rewrite <- rs_add. apply rs_ext. intros i Hi. destruct (Z.eqb_spec i b1); subst; lia. }
  rewrite E, rs_ind by lia.
  assert (g b2 <= rs a n (fun i => if i =? b1 then 0 else g i)); [|lia].
  assert (Hs := rs_single n a (fun i => if i =? b1 then 0 else g i) b2
                  ltac:(intros i Hi; cbv beta; destruct (i =? b1); [lia|]; apply H; auto) H2).
  cbv beta in Hs. destruct (Z.eqb_spec b2 b1); [lia|]. exact Hs.
Qed.

Lemma zsum_rs : forall n g, zsum n g = rs 0 (Z.to_nat n) g.
Proof. reflexivity. Qed.

Lemma rs_menu : forall {T} (M : list (T * Z)) n a (h : T -> Z -> Z),
  rs a n (fun c => hsum (map (fun p => snd p * h (fst p) c) M)) = hsum (map (fun p => snd p * rs a n (h (fst p))) M).
Proof.
  intros T M; induction M as [|p M IH]; intros n a h.
  - simpl. apply rs_zero. intros; reflexivity.
  - simpl. rewrite rs_add, rs_scal, IH. reflexivity.
Qed.

(** ** Counting by a key *)

Lemma Zlength_filter_cons : forall {A} (f : A -> bool) x l,
  Zlength (filter f (x :: l)) = (if f x then 1 else 0) + Zlength (filter f l).
Proof. intros. simpl. destruct (f x); [rewrite Zlength_cons|]; lia. Qed.

Lemma sum_by_key : forall {A} (key : A -> Z) (h : Z -> Z) (N : Z) (xs : list A),
  (forall x, In x xs -> 0 <= key x < N) ->
  hsum (map (fun x => h (key x)) xs) = zsum N (fun j => h j * Zlength (filter (fun x => key x =? j) xs)).
Proof.
  intros A key h N xs Hk. induction xs as [|x xs IH].
  - rewrite zsum_rs. symmetry. apply rs_zero. intros. simpl. rewrite Zlength_nil. lia.
  - simpl map. simpl hsum. rewrite IH by (intros; apply Hk; right; auto). rewrite !zsum_rs.
    rewrite (rs_ext _ 0 (fun j => h j * Zlength (filter (fun x0 => key x0 =? j) (x :: xs)))
               (fun j => (if j =? key x then h (key x) else 0) + h j * Zlength (filter (fun x0 => key x0 =? j) xs))).
    2:{ intros j Hj. rewrite Zlength_filter_cons. destruct (Z.eqb_spec (key x) j), (Z.eqb_spec j (key x)); subst; lia. }
    rewrite rs_add, rs_ind; [reflexivity|]. specialize (Hk x (or_introl eq_refl)). rewrite Z2Nat.id; lia.
Qed.

Lemma hsum_ones : forall {A} (xs : list A), hsum (map (fun _ => 1) xs) = Zlength xs.
Proof. intros A xs; induction xs as [|x xs IH]; [reflexivity|]. cbn [map HuffAbs.sumZ]. rewrite IH, Zlength_cons. lia. Qed.

Lemma hsum_map_le : forall {A} (f g : A -> Z) l, (forall x, In x l -> f x <= g x) -> hsum (map f l) <= hsum (map g l).
Proof. intros. apply sumZ_le. auto. Qed.

Lemma hsum_map_add : forall {A} (f g : A -> Z) l, hsum (map (fun x => f x + g x) l) = hsum (map f l) + hsum (map g l).
Proof. intros A f g l; induction l as [|x l IH]; [reflexivity|]. cbn [map HuffAbs.sumZ]. rewrite IH. lia. Qed.

(** ** Fibonacci monotonicity *)

Lemma fibn_le_S : forall n, fibn n <= fibn (S n).
Proof.
  intros n. destruct n as [|n]; [simpl; lia|]. change (fibn (S (S n))) with (fibn (S n) + fibn n).
  assert (H := fibn_nonneg n). lia.
Qed.

Lemma fib_mono : forall a b, 0 <= a <= b -> fib a <= fib b.
Proof.
  intros a b H. unfold fib. replace (Z.to_nat b) with (Z.to_nat a + (Z.to_nat b - Z.to_nat a))%nat by lia.
  generalize (Z.to_nat b - Z.to_nat a)%nat. intros k. induction k as [|k IH].
  - rewrite Nat.add_0_r. lia.
  - rewrite Nat.add_succ_r. eapply Z.le_trans; [exact IH|apply fibn_le_S].
Qed.

(** ** zrun facts *)

Lemma zrun_le : forall lens n, 0 <= n -> zrun lens n <= n.
Proof.
  intros lens n Hn. unfold zrun. rewrite <- (Z2Nat.id n) at 2 by lia. generalize (Z.to_nat n). intros m.
  induction m as [|m IH]; simpl; [lia|]. destruct (Znth (Z.of_nat m) lens =? 0); lia.
Qed.

Lemma gap_sum : forall lens n,
  rs 0 n (fun c => if Znth c lens =? 0 then 0 else zrun lens c + 1) + zrun lens (Z.of_nat n) = Z.of_nat n.
Proof.
  intros lens n. induction n as [|n IH]; [reflexivity|].
  rewrite rs_snoc. replace (0 + Z.of_nat n) with (Z.of_nat n) by lia.
  replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia. rewrite zrun_succ by lia.
  destruct (Znth (Z.of_nat n) lens =? 0); lia.
Qed.

Lemma gap_sum_le : forall lens n, 0 <= n ->
  zsum n (fun c => if Znth c lens =? 0 then 0 else zrun lens c + 1) <= n.
Proof.
  intros lens n Hn. rewrite zsum_rs. assert (H := gap_sum lens (Z.to_nat n)).
  assert (H0 := zrun_nonneg lens n). rewrite Z2Nat.id in H by lia. lia.
Qed.

Lemma chs_rs : forall tau lens m, chs_nat tau lens m = rs 0 m (ch tau lens).
Proof.
  intros tau lens m. induction m as [|m IH]; [reflexivity|]. simpl chs_nat. rewrite IH, rs_snoc.
  replace (0 + Z.of_nat m) with (Z.of_nat m) by lia. reflexivity.
Qed.

Lemma charge_zsum : forall tau lens mx N, 0 <= mx < N ->
  (forall i, mx < i < N -> Znth i lens = 0) -> charge tau lens (mx + 1) = zsum N (ch tau lens).
Proof.
  intros tau lens mx N Hm Hz. unfold charge. rewrite chs_rs, zsum_rs.
  replace (Z.to_nat N) with (Z.to_nat (mx + 1) + Z.to_nat (N - (mx + 1)))%nat by lia.
  rewrite rs_split. rewrite (rs_zero _ (0 + Z.of_nat (Z.to_nat (mx + 1)))); [lia|].
  intros i Hi. unfold ch. rewrite Hz by lia. reflexivity.
Qed.

(** ** Certificates *)

Record cert := mkCert {
  ce_L : Z;            (* lit_bufsize *)
  ce_s : Z;            (* the shift of the Fibonacci caps the certificate assumes (0 or 2) *)
  ce_D : Z;            (* common denominator *)
  ce_lam : Z; ce_ml : Z; ce_md : Z; ce_eta : Z; ce_kap : Z;
  ce_P : list Z;       (* u = 0..20 *)
  ce_R : list Z;       (* v = 0..28 *)
  ce_nul : list Z;     (* per literal/length code allowance, 286 *)
  ce_nud : list Z;     (* per distance code allowance, 30 *)
  ce_nuF : Z;          (* per forced distance code *)
  ce_th0 : Z;          (* weight of H <= 2283 *)
  ce_menu : list (list Z * Z);  (* bit-length codes and their weights *)
  ce_dbl : Z;          (* overhead of the bit-length tree in the header bound *)
  ce_sgl : Z; ce_sgd : Z;       (* gap rows *)
  ce_bgl : Z; ce_bgd : Z        (* maxima of the gap terms *)
}.

Section Checks.
Variable C : cert.

Definition tauf (t : list Z) : Z -> Z := fun s => Znth s t.
Definition stl (c : Z) : Z := Znth c static_ltree_len.
Definition xlb (c : Z) : Z := Znth (c - 257) extra_lbits.
Definition xdb (d : Z) : Z := Znth d extra_dbits.

Definition capz (l : Z) : Z :=
  let fb := fib (l + 1 - ce_s C) in
  if fb =? 0 then ce_L C - 1 else Z.min (ce_L C - 1) ((ce_L C + 1) / fb).

Definition menu_entry (l : Z) : Z := hsum (map (fun p => snd p * entry_tau (tauf (fst p)) l) (ce_menu C)).
Definition menu_gap (g : Z) : Z := hsum (map (fun p => snd p * gapcost (tauf (fst p)) g) (ce_menu C)).

Definition al (c l : Z) : Z :=
  (if 257 <=? c then Znth (l + xlb c) (ce_P C) else 0) - ce_lam C * (l - stl c) - ce_eta C +
  (if 257 <=? c then ce_kap C else 0).
Definition bl (l : Z) : Z := - ce_ml C * 2 ^ (15 - l) + menu_entry l.
Definition ad (d l : Z) : Z := Znth (l + xdb d) (ce_R C) - ce_lam C * (l - 5) - ce_kap C.
Definition bd (l : Z) : Z := - ce_md C * 2 ^ (15 - l) + menu_entry l.

Definition chk_pr : bool :=
  forallb (fun u => forallb (fun v => ce_D C * Z.max 0 (u + v - 24) <=? Znth u (ce_P C) + Znth v (ce_R C))
                            (zseq 0 29)) (zseq 0 21).

Definition chk_l1 (c : Z) : bool :=
  forallb (fun l => (capz l <? 1) ||
     ((al c l + bl l + ce_bgl C <=? Znth c (ce_nul C)) && (al c l * capz l + bl l + ce_bgl C <=? Znth c (ce_nul C))))
    (zseq 1 15).

Definition chk_lit : bool :=
  forallb (fun c => (c =? 256) || (0 <=? Znth c (ce_nul C))) (zseq 0 286) && forallb chk_l1 (zseq 0 286).

Definition chk_gl : bool := forallb (fun g => menu_gap g - ce_sgl C * (g + 1) <=? ce_bgl C) (zseq 0 286).

Definition chk_d1 (d : Z) : bool :=
  forallb (fun l => ((capz l <? 1) ||
     ((ad d l + bd l + ce_bgd C <=? Znth d (ce_nud C)) && (ad d l * capz l + bd l + ce_bgd C <=? Znth d (ce_nud C)))) &&
     (bd l + ce_bgd C <=? Znth d (ce_nud C) + ce_nuF C))
    (zseq 1 15).

Definition chk_dist : bool :=
  forallb (fun d => 0 <=? Znth d (ce_nud C)) (zseq 0 30) && forallb chk_d1 (zseq 0 30).

Definition chk_gd : bool := forallb (fun g => menu_gap g - ce_sgd C * (g + 1) <=? ce_bgd C) (zseq 0 30).

Definition tau_okb (t : list Z) : bool :=
  forallb (fun s => (1 <=? Znth s t) && (Znth s t <=? 15)) (zseq 0 19) &&
  (zsum 19 (fun s => 2 ^ (15 - Znth s t)) <=? 2 ^ 15).

Definition chk_menu : bool :=
  forallb (fun p => (0 <=? snd p) && tau_okb (fst p)) (ce_menu C) &&
  match ce_menu C with [] => true | _ => ce_L C <=? 256 end.

Definition thsum : Z := hsum (map snd (ce_menu C)).

Definition chk_signs : bool :=
  (0 <? ce_D C) && (0 <=? ce_lam C) && (0 <=? ce_md C) && (0 <=? ce_eta C) && (0 <=? ce_th0 C) &&
  (0 <=? ce_sgl C) && (0 <=? ce_sgd C) && (0 <=? ce_nuF C) && (0 <=? ce_s C) && (ce_s C <=? 2) &&
  (ce_lam C + ce_th0 C + thsum =? ce_D C) && (128 <=? ce_L C).

Definition final_val : Z :=
  ce_th0 C * 2283 + thsum * (71 + ce_dbl C) - ce_lam C + 2 ^ 15 * (ce_ml C + ce_md C) + ce_eta C * ce_L C +
  zsum 286 (fun c => Znth c (ce_nul C)) + zsum 30 (fun d => Znth d (ce_nud C)) + 2 * ce_nuF C +
  286 * ce_sgl C + 30 * ce_sgd C.

Definition chk_final : bool := final_val <=? ce_D C * (8 * ce_L C - 10).

Definition cert_ok : bool :=
  chk_signs && chk_pr && chk_lit && chk_gl && chk_dist && chk_gd && chk_menu && chk_final.

End Checks.

(** ** Soundness *)

Lemma forallb_zseq : forall f a n, forallb f (zseq a n) = true -> forall i, a <= i < a + Z.of_nat n -> f i = true.
Proof. intros f a n H i Hi. rewrite forallb_forall in H. apply H, in_zseq. exact Hi. Qed.

(** Linear in the frequency between 1 and the cap. *)
Lemma lin_bound : forall a b f cap nu, 1 <= f <= cap -> a + b <= nu -> a * cap + b <= nu -> f * a + b <= nu.
Proof.
  intros a b f cap nu Hf H1 H2. destruct (Z_le_gt_dec 0 a) as [Ha|Ha].
  - assert (f * a <= cap * a) by (apply Z.mul_le_mono_nonneg_r; lia). lia.
  - assert (f * a <= 1 * a) by (apply Z.mul_le_mono_nonpos_r; lia). lia.
Qed.

(** The cap from the Fibonacci bound. *)
Lemma cap_ok : forall C f l s L, ce_L C = L -> 0 <= s <= ce_s C -> ce_s C <= 2 -> 1 <= l ->
  1 <= f -> f <= L - 1 -> f * fib (l + 1 - s) <= L + 1 -> f <= capz C l.
Proof.
  intros C f l s L EL Hs Hs2 Hl Hf1 Hf2 Hcap. unfold capz. rewrite EL.
  assert (Hm : fib (l + 1 - ce_s C) <= fib (l + 1 - s)) by (apply fib_mono; lia).
  assert (Hn := fib_nonneg (l + 1 - ce_s C)).
  destruct (Z.eqb_spec (fib (l + 1 - ce_s C)) 0) as [E|E]; [lia|].
  apply Z.min_glb; [lia|]. apply Z.div_le_lower_bound; [lia|].
  assert (f * fib (l + 1 - ce_s C) <= f * fib (l + 1 - s)) by (apply Z.mul_le_mono_nonneg_l; lia). lia.
Qed.

Lemma menu_split : forall C lens c, Znth c lens <> 0 ->
  hsum (map (fun p => snd p * ch (tauf (fst p)) lens c) (ce_menu C)) =
  menu_entry C (Znth c lens) + menu_gap C (zrun lens c).
Proof.
  intros C lens c Hc. unfold menu_entry, menu_gap. rewrite <- hsum_map_add. f_equal. apply map_ext. intros p.
  unfold ch. rewrite (proj2 (Z.eqb_neq _ _) Hc). lia.
Qed.

Lemma menu_zero : forall C lens c, Znth c lens = 0 ->
  hsum (map (fun p => snd p * ch (tauf (fst p)) lens c) (ce_menu C)) = 0.
Proof.
  intros C lens c Hc. induction (ce_menu C) as [|p M IH]; [reflexivity|]. simpl. rewrite IH. unfold ch.
  rewrite Hc. simpl. lia.
Qed.

Lemma menu_H : forall (M : list (list Z * Z)) X Y (ql qd : list Z -> Z),
  (forall p, In p M -> 0 <= snd p /\ X <= Y + ql (fst p) + qd (fst p)) ->
  hsum (map snd M) * X <= hsum (map snd M) * Y + hsum (map (fun p => snd p * ql (fst p)) M) +
                          hsum (map (fun p => snd p * qd (fst p)) M).
Proof.
  intros M X Y ql qd H. induction M as [|p M IH]; simpl; [lia|].
  destruct (H p (or_introl eq_refl)) as [H0 H1]. assert (IH' := IH ltac:(intros; apply H; right; auto)).
  assert (snd p * X <= snd p * (Y + ql (fst p) + qd (fst p))) by (apply Z.mul_le_mono_nonneg_l; lia). nia.
Qed.

Lemma tau_okb_ok : forall t, tau_okb t = true -> tau_ok (tauf t).
Proof.
  intros t H. unfold tau_okb in H. apply andb_true_iff in H. destruct H as [H1 H2]. split.
  - intros s Hs. assert (E := forallb_zseq _ _ _ H1 s ltac:(unfold BL_CODES in Hs; simpl; lia)).
    unfold tauf. apply andb_true_iff in E. rewrite !Z.leb_le in E. lia.
  - apply Z.leb_le in H2. exact H2.
Qed.

Section Sound.
Variable C : cert.
Hypothesis HC : cert_ok C = true.
Variables (L b0 : Z) (syms : list (Z * Z)) (ll dl0 : list Z) (lmax dmax hdr sl sd : Z).
Hypothesis HB : block_facts L b0 syms ll dl0 lmax dmax hdr sl sd.
Hypothesis HL : L = ce_L C.
Hypothesis Hsl : sl <= ce_s C.
Hypothesis Hsd : sd <= ce_s C.

Let F c := lfreq syms c.
Let G d := dfreq syms d.
Let D := ce_D C.

Lemma HCsplit : chk_signs C = true /\ chk_pr C = true /\ chk_lit C = true /\ chk_gl C = true /\
                chk_dist C = true /\ chk_gd C = true /\ chk_menu C = true /\ chk_final C = true.
Proof. unfold cert_ok in HC. repeat rewrite andb_true_iff in HC. tauto. Qed.

Lemma signs : 0 < ce_D C /\ 0 <= ce_lam C /\ 0 <= ce_md C /\ 0 <= ce_eta C /\ 0 <= ce_th0 C /\
  0 <= ce_sgl C /\ 0 <= ce_sgd C /\ 0 <= ce_nuF C /\ 0 <= ce_s C /\ ce_s C <= 2 /\
  ce_lam C + ce_th0 C + thsum C = ce_D C /\ 128 <= ce_L C.
Proof.
  destruct HCsplit as [H1 _]. unfold chk_signs in H1. repeat rewrite andb_true_iff in H1.
  rewrite !Z.leb_le, Z.ltb_lt, Z.eqb_eq in H1. tauto.
Qed.

(** *** Symbols *)

Definition dkey (x : Z * Z) : Z := if fst x =? 0 then 30 else d_code (fst x - 1).

Lemma lcode_range : forall x, valid_sym (fst x) (snd x) ->
  (fst x = 0 /\ lcode_of x = snd x /\ 0 <= snd x <= 255) \/
  (fst x <> 0 /\ lcode_of x = Znth (snd x) length_code_tab + 257 /\ 0 <= Znth (snd x) length_code_tab <= 28 /\
   0 <= Znth (Znth (snd x) length_code_tab) extra_lbits <= 5).
Proof.
  intros x [Hl Hd]. unfold lcode_of. destruct (Z.eqb_spec (fst x) 0) as [E|E]; [left; auto|right].
  destruct (length_code_facts (snd x) Hl) as [A [B _]]. unfold LITERALS. split; auto. split; [lia|]. auto.
Qed.

Lemma dkey_range : forall x, valid_sym (fst x) (snd x) ->
  (fst x = 0 /\ dkey x = 30) \/
  (fst x <> 0 /\ dkey x = d_code (fst x - 1) /\ 0 <= d_code (fst x - 1) <= 29 /\
   0 <= Znth (d_code (fst x - 1)) extra_dbits <= 13).
Proof.
  intros x [Hl Hd]. unfold dkey. destruct (Z.eqb_spec (fst x) 0) as [E|E]; [left; auto|right].
  destruct (dist_code_facts (fst x - 1) ltac:(lia)) as [A [B _]]. auto.
Qed.

Lemma valid_all : forall x, In x syms -> valid_sym (fst x) (snd x).
Proof. exact (bf_valid _ _ _ _ _ _ _ _ _ _ HB). Qed.

Lemma lkey_bound : forall x, In x syms -> 0 <= lcode_of x < 286.
Proof. intros x Hx. destruct (lcode_range x (valid_all x Hx)) as [[_ [-> ?]]|[_ [-> [? _]]]]; lia. Qed.

Lemma dkey_bound : forall x, In x syms -> 0 <= dkey x < 31.
Proof. intros x Hx. destruct (dkey_range x (valid_all x Hx)) as [[_ ->]|[_ [-> [? _]]]]; lia. Qed.

Definition cnt_l (j : Z) : Z := Zlength (filter (fun x => lcode_of x =? j) syms).
Definition cnt_d (d : Z) : Z := Zlength (filter (fun x => dkey x =? d) syms).

Lemma F_cnt : forall j, F j = cnt_l j + (if j =? END_BLOCK then 1 else 0).
Proof. reflexivity. Qed.

Lemma filter_false : forall {A} (f : A -> bool) l, (forall x, In x l -> f x = false) -> filter f l = [].
Proof. intros A f l H. induction l as [|x l IH]; simpl; [reflexivity|]. rewrite H by (left; auto). apply IH. intros; apply H; right; auto. Qed.

Lemma cnt_l_256 : cnt_l 256 = 0.
Proof.
  unfold cnt_l. rewrite filter_false; [reflexivity|]. intros x Hx.
  destruct (lcode_range x (valid_all x Hx)) as [[_ [-> ?]]|[_ [-> [? _]]]]; apply Z.eqb_neq; lia.
Qed.

Lemma cnt_d_G : forall d, 0 <= d < 30 -> cnt_d d = G d.
Proof.
  intros d Hd. unfold cnt_d, G, dfreq. f_equal. apply filter_ext_in. intros x Hx. unfold dkey.
  destruct (Z.eqb_spec (fst x) 0).
  - rewrite (proj2 (Z.eqb_neq 30 d)) by lia. reflexivity.
  - reflexivity.
Qed.

Lemma F_nonneg : forall c, 0 <= F c.
Proof. intros c. rewrite F_cnt. unfold cnt_l. assert (H := Zlength_nonneg (filter (fun x => lcode_of x =? c) syms)). destruct (c =? END_BLOCK); lia. Qed.

Lemma G_nonneg : forall d, 0 <= G d.
Proof. intros d. apply Zlength_nonneg. Qed.

Lemma F_256 : F 256 = 1.
Proof. rewrite F_cnt, cnt_l_256. reflexivity. Qed.

(** The number of symbols and of matches. *)
Definition nm : Z := hsum (map (fun x => if fst x =? 0 then 0 else 1) syms).

Lemma sumF : zsum 286 F = Zlength syms + 1.
Proof.
  assert (Hk := sum_by_key lcode_of (fun _ => 1) 286 syms lkey_bound). rewrite hsum_ones in Hk.
  rewrite zsum_rs in Hk |- *. change (Z.to_nat 286) with 286%nat in *.
  rewrite (rs_ext _ 0 F (fun j => 1 * Zlength (filter (fun x => lcode_of x =? j) syms) + (if j =? 256 then 1 else 0)))
    by (intros j Hj; rewrite F_cnt; unfold cnt_l, END_BLOCK; lia).
  rewrite rs_add, rs_ind by (simpl; lia). lia.
Qed.

Definition Mt (j : Z) : Z := if 257 <=? j then F j else 0.

Lemma nm_l : nm = zsum 286 Mt.
Proof.
  unfold nm. transitivity (hsum (map (fun x => (fun j => if 257 <=? j then 1 else 0) (lcode_of x)) syms)).
  - f_equal. apply map_ext_in. intros x Hx.
    destruct (lcode_range x (valid_all x Hx)) as [[E [-> ?]]|[E [-> [? _]]]].
    + rewrite E. simpl. destruct (Z.leb_spec 257 (snd x)); lia.
    + rewrite (proj2 (Z.eqb_neq _ _) E). destruct (Z.leb_spec 257 (Znth (snd x) length_code_tab + 257)); lia.
  - assert (Hk := sum_by_key lcode_of (fun j => if 257 <=? j then 1 else 0) 286 syms lkey_bound). cbv beta in Hk.
    rewrite Hk. rewrite !zsum_rs. apply rs_ext. intros j Hj.
    unfold Mt. destruct (Z.leb_spec 257 j); [|lia]. rewrite F_cnt. replace (j =? END_BLOCK) with false
      by (symmetry; apply Z.eqb_neq; unfold END_BLOCK; lia). fold (cnt_l j). lia.
Qed.

Lemma nm_d : nm = zsum 30 G.
Proof.
  unfold nm. transitivity (hsum (map (fun x => (fun d => if d =? 30 then 0 else 1) (dkey x)) syms)).
  - f_equal. apply map_ext_in. intros x Hx.
    destruct (dkey_range x (valid_all x Hx)) as [[E ->]|[E [-> [? _]]]].
    + rewrite E. reflexivity.
    + rewrite (proj2 (Z.eqb_neq _ _) E). destruct (Z.eqb_spec (d_code (fst x - 1)) 30); lia.
  - assert (Hk := sum_by_key dkey (fun d => if d =? 30 then 0 else 1) 31 syms dkey_bound). cbv beta in Hk.
    rewrite Hk. rewrite !zsum_rs.
    change (Z.to_nat 31) with (S 30). rewrite rs_snoc. simpl (0 + Z.of_nat 30). rewrite Z.eqb_refl.
    change (Z.to_nat 30) with 30%nat. rewrite Z.mul_0_l, Z.add_0_r. apply rs_ext. intros d Hd.
    replace (d =? 30) with false by (symmetry; apply Z.eqb_neq; lia). fold (cnt_d d). rewrite cnt_d_G by lia. lia.
Qed.

Lemma nm_le : nm <= Zlength syms.
Proof.
  unfold nm. rewrite <- hsum_ones. apply hsum_map_le. intros x _. destruct (fst x =? 0); lia.
Qed.

(** *** Code facts *)

Lemma n_bounds : 1 <= Zlength syms <= L - 1.
Proof. exact (bf_n _ _ _ _ _ _ _ _ _ _ HB). Qed.

Lemma F_le : forall c, 0 <= c < 286 -> c <> 256 -> F c <= L - 1.
Proof.
  intros c Hc Hne. assert (H2 := rs_two 286 0 F c 256 (fun i _ => F_nonneg i) ltac:(simpl; lia) ltac:(simpl; lia) Hne).
  change (rs 0 286 F) with (zsum 286 F) in H2. rewrite sumF, F_256 in H2.
  assert (H3 := n_bounds). lia.
Qed.

Lemma G_le : forall d, 0 <= d < 30 -> G d <= L - 1.
Proof.
  intros d Hd. assert (H1 := rs_single 30 0 G d (fun i _ => G_nonneg i) ltac:(simpl; lia)).
  change (rs 0 30 G) with (zsum 30 G) in H1. rewrite <- nm_d in H1. assert (H2 := nm_le). assert (H3 := n_bounds). lia.
Qed.


(** *** Extracting the checks *)

Lemma chk_pr_spec : forall u v, 0 <= u <= 20 -> 0 <= v <= 28 ->
  ce_D C * Z.max 0 (u + v - 24) <= Znth u (ce_P C) + Znth v (ce_R C).
Proof.
  intros u v Hu Hv. destruct HCsplit as [_ [H2 _]]. unfold chk_pr in H2.
  assert (E := forallb_zseq _ _ _ H2 u ltac:(simpl; lia)). cbv beta in E.
  assert (E2 := forallb_zseq _ _ _ E v ltac:(simpl; lia)). cbv beta in E2. apply Z.leb_le in E2. exact E2.
Qed.

Lemma nul_nonneg : forall c, 0 <= c < 286 -> c <> 256 -> 0 <= Znth c (ce_nul C).
Proof.
  intros c Hc Hne. destruct HCsplit as [_ [_ [H3 _]]]. unfold chk_lit in H3. apply andb_true_iff in H3.
  destruct H3 as [H3 _]. assert (E := forallb_zseq _ _ _ H3 c ltac:(simpl; lia)). cbv beta in E.
  apply orb_true_iff in E. destruct E as [E|E]; [apply Z.eqb_eq in E; lia|apply Z.leb_le in E; exact E].
Qed.

Lemma chk_l1_spec : forall c l, 0 <= c < 286 -> 1 <= l <= 15 -> 1 <= capz C l ->
  al C c l + bl C l + ce_bgl C <= Znth c (ce_nul C) /\ al C c l * capz C l + bl C l + ce_bgl C <= Znth c (ce_nul C).
Proof.
  intros c l Hc Hl Hcap. destruct HCsplit as [_ [_ [H3 _]]]. unfold chk_lit in H3. apply andb_true_iff in H3.
  destruct H3 as [_ H3]. assert (E := forallb_zseq _ _ _ H3 c ltac:(simpl; lia)). unfold chk_l1 in E.
  assert (E2 := forallb_zseq _ _ _ E l ltac:(simpl; lia)). cbv beta in E2.
  apply orb_true_iff in E2. destruct E2 as [E2|E2]; [apply Z.ltb_lt in E2; lia|].
  apply andb_true_iff in E2. rewrite !Z.leb_le in E2. exact E2.
Qed.

Lemma chk_gl_spec : forall g, 0 <= g <= 285 -> menu_gap C g - ce_sgl C * (g + 1) <= ce_bgl C.
Proof.
  intros g Hg. destruct HCsplit as [_ [_ [_ [H4 _]]]]. unfold chk_gl in H4.
  assert (E := forallb_zseq _ _ _ H4 g ltac:(simpl; lia)). cbv beta in E. apply Z.leb_le in E. exact E.
Qed.

Lemma nud_nonneg : forall d, 0 <= d < 30 -> 0 <= Znth d (ce_nud C).
Proof.
  intros d Hd. destruct HCsplit as [_ [_ [_ [_ [H5 _]]]]]. unfold chk_dist in H5. apply andb_true_iff in H5.
  destruct H5 as [H5 _]. assert (E := forallb_zseq _ _ _ H5 d ltac:(simpl; lia)). cbv beta in E.
  apply Z.leb_le in E. exact E.
Qed.

Lemma chk_d1_spec : forall d l, 0 <= d < 30 -> 1 <= l <= 15 ->
  (1 <= capz C l ->
   ad C d l + bd C l + ce_bgd C <= Znth d (ce_nud C) /\ ad C d l * capz C l + bd C l + ce_bgd C <= Znth d (ce_nud C)) /\
  bd C l + ce_bgd C <= Znth d (ce_nud C) + ce_nuF C.
Proof.
  intros d l Hd Hl. destruct HCsplit as [_ [_ [_ [_ [H5 _]]]]]. unfold chk_dist in H5. apply andb_true_iff in H5.
  destruct H5 as [_ H5]. assert (E := forallb_zseq _ _ _ H5 d ltac:(simpl; lia)). unfold chk_d1 in E.
  assert (E2 := forallb_zseq _ _ _ E l ltac:(simpl; lia)). cbv beta in E2.
  apply andb_true_iff in E2. destruct E2 as [E2 E3]. apply Z.leb_le in E3. split; [|exact E3].
  intros Hcap. apply orb_true_iff in E2. destruct E2 as [E2|E2]; [apply Z.ltb_lt in E2; lia|].
  apply andb_true_iff in E2. rewrite !Z.leb_le in E2. exact E2.
Qed.

Lemma chk_gd_spec : forall g, 0 <= g <= 29 -> menu_gap C g - ce_sgd C * (g + 1) <= ce_bgd C.
Proof.
  intros g Hg. destruct HCsplit as [_ [_ [_ [_ [_ [H6 _]]]]]]. unfold chk_gd in H6.
  assert (E := forallb_zseq _ _ _ H6 g ltac:(simpl; lia)). cbv beta in E. apply Z.leb_le in E. exact E.
Qed.

Lemma menu_ok : forall p, In p (ce_menu C) -> 0 <= snd p /\ tau_ok (tauf (fst p)) /\ ce_L C <= 256.
Proof.
  intros p Hp. destruct HCsplit as [_ [_ [_ [_ [_ [_ [H7 _]]]]]]]. unfold chk_menu in H7.
  apply andb_true_iff in H7. destruct H7 as [H7 H8]. rewrite forallb_forall in H7. specialize (H7 p Hp).
  apply andb_true_iff in H7. destruct H7 as [H7a H7b]. apply Z.leb_le in H7a.
  split; [exact H7a|]. split; [apply tau_okb_ok; exact H7b|].
  destruct (ce_menu C) as [|q M]; [destruct Hp|]. apply Z.leb_le in H8. exact H8.
Qed.

Lemma final_spec : final_val C <= ce_D C * (8 * ce_L C - 10).
Proof. destruct HCsplit as [_ [_ [_ [_ [_ [_ [_ H8]]]]]]]. apply Z.leb_le in H8. exact H8. Qed.

(** *** The excess cost of the symbols *)

Definition PiC (c : Z) : Z := if 257 <=? c then Znth (Znth c ll + xlb c) (ce_P C) else 0.
Definition RhoC (d : Z) : Z := Znth (Znth d dl0 + xdb d) (ce_R C).
Definition Rk (d : Z) : Z := if d =? 30 then 0 else RhoC d.
Definition wsym (x : Z * Z) : Z := PiC (lcode_of x) + Rk (dkey x).

Lemma llen_all : forall c, 0 <= c < 286 -> 0 <= Znth c ll <= 15.
Proof. intros c Hc. apply (bf_llen _ _ _ _ _ _ _ _ _ _ HB c). unfold L_CODES; lia. Qed.
Lemma dlen_all : forall d, 0 <= d < 30 -> 0 <= Znth d dl0 <= 15.
Proof. intros d Hd. apply (bf_dlen _ _ _ _ _ _ _ _ _ _ HB d). unfold D_CODES; lia. Qed.

Lemma sym_w : forall x, In x syms ->
  ce_D C * (sym_cost ll dl0 (fst x) (snd x) - 24) <= wsym x /\ 0 <= wsym x.
Proof.
  intros x Hx. assert (HD := proj1 signs). unfold wsym.
  destruct (lcode_range x (valid_all x Hx)) as [[E0 [El Hr]]|[E0 [El [Hj Hxl]]]];
  destruct (dkey_range x (valid_all x Hx)) as [[E1 Ed]|[E1 [Ed [Hd Hxd]]]]; try congruence.
  - rewrite El, Ed. unfold PiC, Rk. replace (257 <=? snd x) with false by (symmetry; apply Z.leb_gt; lia).
    rewrite Z.eqb_refl. unfold sym_cost. rewrite E0, Z.eqb_refl.
    assert (H15 := llen_all (snd x) ltac:(lia)). nia.
  - rewrite El, Ed. set (j := Znth (snd x) length_code_tab) in *. set (d := d_code (fst x - 1)) in *.
    unfold PiC, Rk, RhoC, xlb, xdb. replace (257 <=? j + 257) with true by (symmetry; apply Z.leb_le; lia).
    replace (d =? 30) with false by (symmetry; apply Z.eqb_neq; lia). replace (j + 257 - 257) with j by lia.
    unfold sym_cost. rewrite (proj2 (Z.eqb_neq _ _) E0). fold j d.
    assert (H1 := llen_all (j + 257) ltac:(lia)). assert (H2 := dlen_all d ltac:(lia)).
    assert (Hu : 0 <= Znth (j + 257) ll + Znth j extra_lbits <= 20) by lia.
    assert (Hv : 0 <= Znth d dl0 + Znth d extra_dbits <= 28) by lia.
    assert (Hpr := chk_pr_spec (Znth (j + 257) ll + Znth j extra_lbits) (Znth d dl0 + Znth d extra_dbits) Hu Hv).
    assert (0 <= ce_D C * Z.max 0 (Znth (j + 257) ll + Znth j extra_lbits + (Znth d dl0 + Znth d extra_dbits) - 24))
      by (apply Z.mul_nonneg_nonneg; lia).
    assert (ce_D C * (Znth (j + 257) ll + Znth j extra_lbits + Znth d dl0 + Znth d extra_dbits - 24) <=
            ce_D C * Z.max 0 (Znth (j + 257) ll + Znth j extra_lbits + (Znth d dl0 + Znth d extra_dbits) - 24))
      by (apply Z.mul_le_mono_nonneg_l; lia).
    lia.
Qed.

Lemma cost_sum_hsum : forall l, cost_sum ll dl0 l = hsum (map (fun x => sym_cost ll dl0 (fst x) (snd x)) l).
Proof. intros l; induction l as [|[d c] l IH]; [reflexivity|]. simpl. rewrite IH. reflexivity. Qed.

Lemma prefix_gen : forall (cf w : Z * Z -> Z) Dd l, 0 < Dd ->
  (forall x, In x l -> Dd * (cf x - 24) <= w x /\ 0 <= w x) ->
  forall k, Dd * (hsum (map cf (firstn k l)) - 24 * Z.of_nat (length (firstn k l))) <= hsum (map w l).
Proof.
  intros cf w Dd l HD H. induction l as [|x l IH]; intros k.
  - destruct k; simpl; lia.
  - destruct k as [|k].
    + assert (Hn : 0 <= hsum (map w (x :: l))) by (apply sumZ_nonneg; intros y Hy; apply H; auto).
      cbn [firstn length map HuffAbs.sumZ] in *. lia.
    + cbn [firstn map length HuffAbs.sumZ]. assert (IH' := IH ltac:(intros; apply H; right; auto) k).
      destruct (H x (or_introl eq_refl)) as [H1 H2]. nia.
Qed.

Lemma wsum : hsum (map wsym syms) = zsum 286 (fun c => F c * PiC c) + zsum 30 (fun d => G d * RhoC d).
Proof.
  unfold wsym. rewrite hsum_map_add. f_equal.
  - rewrite (sum_by_key lcode_of PiC 286 syms lkey_bound). rewrite !zsum_rs. apply rs_ext. intros j Hj.
    rewrite F_cnt. fold (cnt_l j). unfold END_BLOCK. destruct (Z.eqb_spec j 256) as [->|Hne].
    + rewrite cnt_l_256. unfold PiC. simpl. lia.
    + lia.
  - rewrite (sum_by_key dkey Rk 31 syms dkey_bound). rewrite !zsum_rs.
    change (Z.to_nat 31) with (S 30). rewrite rs_snoc. simpl (0 + Z.of_nat 30). unfold Rk at 2. rewrite Z.eqb_refl.
    change (Z.to_nat 30) with 30%nat. rewrite Z.mul_0_l, Z.add_0_r. apply rs_ext. intros d Hd.
    unfold Rk. replace (d =? 30) with false by (symmetry; apply Z.eqb_neq; lia). fold (cnt_d d).
    rewrite cnt_d_G by lia. lia.
Qed.

Lemma prefix_bound : forall k, (k <= length syms)%nat ->
  ce_D C * (cost_sum ll dl0 (firstn k syms) - 24 * Z.of_nat k) <=
  zsum 286 (fun c => F c * PiC c) + zsum 30 (fun d => G d * RhoC d).
Proof.
  intros k Hk. rewrite <- wsum, cost_sum_hsum.
  assert (H := prefix_gen (fun x => sym_cost ll dl0 (fst x) (snd x)) wsym (ce_D C) syms (proj1 signs) sym_w k).
  rewrite firstn_length_le in H by exact Hk. exact H.
Qed.

(** *** Per-code bounds: literal/length codes *)

Definition Kl (c : Z) : Z := if Znth c ll =? 0 then 0 else 2 ^ (15 - Znth c ll).
Definition Gp (c : Z) : Z := if Znth c ll =? 0 then 0 else zrun ll c + 1.
Definition MCh (lens : list Z) (c : Z) : Z := hsum (map (fun p => snd p * ch (tauf (fst p)) lens c) (ce_menu C)).

Lemma rs_MCh : forall lens n a, rs a n (fun c => MCh lens c) =
  hsum (map (fun p => snd p * rs a n (ch (tauf (fst p)) lens)) (ce_menu C)).
Proof. intros. exact (rs_menu (ce_menu C) n a (fun t c => ch (tauf t) lens c)). Qed.

Definition TL (c : Z) : Z :=
  F c * PiC c + (- ce_lam C) * (F c * (Znth c ll - stl c)) + (- ce_eta C) * F c + ce_kap C * Mt c +
  (- ce_ml C) * Kl c + MCh ll c + (- ce_sgl C) * Gp c.

Lemma lused : forall c, 0 <= c < 286 -> (0 < F c <-> Znth c ll <> 0).
Proof. intros c Hc. apply (bf_lused _ _ _ _ _ _ _ _ _ _ HB c). unfold L_CODES; lia. Qed.

Lemma Lge : 128 <= L.
Proof. destruct signs as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ H]]]]]]]]]]]. lia. Qed.

Lemma shifts : 0 <= sl /\ 0 <= sd.
Proof. destruct (bf_shift _ _ _ _ _ _ _ _ _ _ HB) as [A [B _]]. lia. Qed.

Lemma TL_le : forall c, 0 <= c < 286 -> TL c <= Znth c (ce_nul C).
Proof.
  intros c Hc. assert (HF := F_nonneg c). destruct (Z.eq_dec (F c) 0) as [E0|E0].
  - assert (El : Znth c ll = 0).
    { destruct (Z.eq_dec (Znth c ll) 0) as [|Hne]; auto. apply (lused c Hc) in Hne. lia. }
    assert (Hc256 : c <> 256) by (intros ->; rewrite F_256 in E0; lia).
    unfold TL, Kl, Gp, MCh, Mt. rewrite menu_zero by exact El. rewrite El, E0. simpl.
    destruct (257 <=? c); assert (H := nul_nonneg c Hc Hc256); lia.
  - assert (Hl : Znth c ll <> 0) by (apply (lused c Hc); lia).
    set (l := Znth c ll) in *. assert (Hl15 := llen_all c Hc). fold l in Hl15.
    set (g := zrun ll c).
    assert (Hg : 0 <= g <= 285) by (split; [apply zrun_nonneg|]; assert (zrun ll c <= c) by (apply zrun_le; lia); unfold g; lia).
    assert (E : TL c = F c * al C c l + bl C l + (menu_gap C g - ce_sgl C * (g + 1))).
    { unfold TL, Kl, Gp, MCh, Mt, PiC, al, bl. fold l. rewrite menu_split by exact Hl. fold l g.
      rewrite (proj2 (Z.eqb_neq l 0) Hl). destruct (257 <=? c); ring. }
    assert (Hs2 : ce_s C <= 2) by (destruct signs as [_ [_ [_ [_ [_ [_ [_ [_ [_ [H2 _]]]]]]]]]]; exact H2).
    assert (Hsh := shifts). assert (Hlg := Lge).
    assert (Hcap : F c <= capz C l).
    { destruct (Z.eq_dec c 256) as [->|Hne].
      - assert (Hc1 : F 256 * fib (l + 1 - sl) <= L + 1).
        { apply (bf_cap_l _ _ _ _ _ _ _ _ _ _ HB 256); [unfold L_CODES; lia|]. change (0 < F 256). rewrite F_256; lia. }
        rewrite F_256 in *. apply (cap_ok C 1 l sl L); try lia.
      - apply (cap_ok C (F c) l sl L); try lia.
        + apply F_le; auto.
        + apply (bf_cap_l _ _ _ _ _ _ _ _ _ _ HB c); [unfold L_CODES; lia|change (0 < F c); lia]. }
    assert (Hl1 : 1 <= l <= 15) by lia. assert (Hcp : 1 <= capz C l) by lia.
    destruct (chk_l1_spec c l Hc Hl1 Hcp) as [K1 K2].
    assert (Hgl := chk_gl_spec g Hg).
    assert (H : F c * al C c l + (bl C l + ce_bgl C) <= Znth c (ce_nul C)) by (apply lin_bound with (capz C l); lia).
    lia.
Qed.

(** *** Per-code bounds: distance codes *)

Definition Kd (d : Z) : Z := if Znth d dl0 =? 0 then 0 else 2 ^ (15 - Znth d dl0).
Definition Gpd (d : Z) : Z := if Znth d dl0 =? 0 then 0 else zrun dl0 d + 1.
Definition forced (d : Z) : Z := if (0 <? Znth d dl0) && (dfreq syms d =? 0) then 1 else 0.

Definition TD (d : Z) : Z :=
  G d * RhoC d + (- ce_lam C) * (G d * (Znth d dl0 - 5)) + (- ce_kap C) * G d +
  (- ce_md C) * Kd d + MCh dl0 d + (- ce_sgd C) * Gpd d.

Lemma TD_le : forall d, 0 <= d < 30 -> TD d <= Znth d (ce_nud C) + ce_nuF C * forced d.
Proof.
  intros d Hd. assert (HG := G_nonneg d). assert (Hl15 := dlen_all d Hd).
  assert (HnuF := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 signs)))))))).
  set (l := Znth d dl0) in *. set (g := zrun dl0 d).
  assert (Hg : 0 <= g <= 29) by (split; [apply zrun_nonneg|]; assert (zrun dl0 d <= d) by (apply zrun_le; lia); unfold g; lia).
  destruct (Z.eq_dec l 0) as [El|Hl].
  - assert (Gz : G d = 0).
    { destruct (Z.eq_dec (G d) 0) as [|Hne]; auto. exfalso.
      apply (bf_dused _ _ _ _ _ _ _ _ _ _ HB d); [unfold D_CODES; lia|change (0 < G d); lia|exact El]. }
    unfold TD, Kd, Gpd, MCh, forced. fold l. rewrite menu_zero by exact El. rewrite El, Gz. simpl.
    assert (H := nud_nonneg d Hd). lia.
  - destruct (chk_d1_spec d l Hd ltac:(lia)) as [K1 K2].
    assert (Hgd := chk_gd_spec g Hg).
    assert (E : TD d = G d * ad C d l + bd C l + (menu_gap C g - ce_sgd C * (g + 1))).
    { unfold TD, Kd, Gpd, MCh, RhoC, ad, bd, xdb. fold l. rewrite menu_split by exact Hl. fold l g.
      rewrite (proj2 (Z.eqb_neq l 0) Hl). ring. }
    destruct (Z.eq_dec (G d) 0) as [Gz|Gnz].
    + unfold forced. replace (0 <? Znth d dl0) with true by (symmetry; apply Z.ltb_lt; fold l; lia).
      replace (dfreq syms d =? 0) with true by (symmetry; apply Z.eqb_eq; exact Gz).
      rewrite E, Gz. simpl. lia.
    + unfold forced. replace (dfreq syms d =? 0) with false by (symmetry; apply Z.eqb_neq; exact Gnz).
      rewrite andb_false_r.
      assert (Hs2 : ce_s C <= 2) by (destruct signs as [_ [_ [_ [_ [_ [_ [_ [_ [_ [H2 _]]]]]]]]]]; exact H2).
      assert (Hsh := shifts). assert (Hlg := Lge).
      assert (Hcap : G d <= capz C l).
      { apply (cap_ok C (G d) l sd L); try lia.
        + apply G_le; auto.
        + apply (bf_cap_d _ _ _ _ _ _ _ _ _ _ HB d); [unfold D_CODES; lia|change (0 < G d); lia]. }
      destruct (K1 ltac:(lia)) as [K1a K1b].
      assert (H : G d * ad C d l + (bd C l + ce_bgd C) <= Znth d (ce_nud C)) by (apply lin_bound with (capz C l); lia).
      lia.
Qed.

(** *** Sums *)

Lemma TL_sum : zsum 286 TL =
  zsum 286 (fun c => F c * PiC c) - ce_lam C * zsum 286 (fun c => F c * (Znth c ll - stl c)) -
  ce_eta C * zsum 286 F + ce_kap C * zsum 286 Mt - ce_ml C * zsum 286 Kl +
  hsum (map (fun p => snd p * zsum 286 (ch (tauf (fst p)) ll)) (ce_menu C)) - ce_sgl C * zsum 286 Gp.
Proof.
  unfold TL. rewrite !zsum_rs. rewrite !rs_add, !rs_scal. rewrite rs_MCh.
  repeat match goal with |- context [rs ?a ?n (fun i => ?g i)] => change (rs a n (fun i => g i)) with (rs a n g) end.
  assert (Em : hsum (map (fun p => snd p * zsum 286 (ch (tauf (fst p)) ll)) (ce_menu C)) =
               hsum (map (fun p => snd p * rs 0 (Z.to_nat 286) (ch (tauf (fst p)) ll)) (ce_menu C))) by reflexivity.
  rewrite Em. lia.
Qed.

Lemma TD_sum : zsum 30 TD =
  zsum 30 (fun d => G d * RhoC d) - ce_lam C * zsum 30 (fun d => G d * (Znth d dl0 - 5)) -
  ce_kap C * zsum 30 G - ce_md C * zsum 30 Kd +
  hsum (map (fun p => snd p * zsum 30 (ch (tauf (fst p)) dl0)) (ce_menu C)) - ce_sgd C * zsum 30 Gpd.
Proof.
  unfold TD. rewrite !zsum_rs. rewrite !rs_add, !rs_scal. rewrite rs_MCh.
  repeat match goal with |- context [rs ?a ?n (fun i => ?g i)] => change (rs a n (fun i => g i)) with (rs a n g) end.
  assert (Em : hsum (map (fun p => snd p * zsum 30 (ch (tauf (fst p)) dl0)) (ce_menu C)) =
               hsum (map (fun p => snd p * rs 0 (Z.to_nat 30) (ch (tauf (fst p)) dl0)) (ce_menu C))) by reflexivity.
  rewrite Em. lia.
Qed.

Lemma TL_sum_le : zsum 286 TL <= zsum 286 (fun c => Znth c (ce_nul C)).
Proof. rewrite !zsum_rs. apply rs_le. intros c Hc. apply TL_le. simpl in Hc. lia. Qed.

Lemma TD_sum_le : zsum 30 TD <= zsum 30 (fun d => Znth d (ce_nud C)) + 2 * ce_nuF C.
Proof.
  assert (HnuF := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 signs)))))))).
  assert (Hf := proj1 (bf_forced _ _ _ _ _ _ _ _ _ _ HB)). cbv zeta in Hf.
  change (zsum D_CODES (fun d => if (0 <? Znth d dl0) && (dfreq syms d =? 0) then 1 else 0)) with (rs 0 30 forced) in Hf.
  assert (Hle : rs 0 30 TD <= rs 0 30 (fun d => Znth d (ce_nud C)) + ce_nuF C * rs 0 30 forced).
  { rewrite <- rs_scal, <- rs_add. apply rs_le. intros d Hd. apply TD_le. simpl in Hd. lia. }
  change (zsum 30 TD) with (rs 0 30 TD). change (zsum 30 (fun d => Znth d (ce_nud C))) with (rs 0 30 (fun d => Znth d (ce_nud C))).
  assert (ce_nuF C * rs 0 30 forced <= ce_nuF C * 2) by (apply Z.mul_le_mono_nonneg_l; lia). lia.
Qed.

(** *** The theorem *)

Hypothesis Htau : ce_menu C <> [] -> forall tau, tau_ok tau ->
  hdr <= 71 + charge tau ll (lmax + 1) + charge tau dl0 (dmax + 1) + ce_dbl C.

Theorem cert_bound : forall k, (k <= length syms)%nat ->
  b0 + 3 + hdr + cost_sum ll dl0 (firstn k syms) <= 8 * (L + 3 * Z.of_nat k).
Proof.
  intros k Hk.
  destruct signs as [HD [Hlam [Hmd [Heta [Hth0 [Hsgl [Hsgd [HnuF [_ [_ [Hsum HL128]]]]]]]]]]].
  assert (Hpre := prefix_bound k Hk).
  assert (HTL := TL_sum_le). rewrite TL_sum in HTL.
  assert (HTD := TD_sum_le). rewrite TD_sum in HTD.
  assert (HA := bf_A _ _ _ _ _ _ _ _ _ _ HB).
  assert (HKl := bf_kraft_l _ _ _ _ _ _ _ _ _ _ HB).
  assert (HKd := bf_kraft_d _ _ _ _ _ _ _ _ _ _ HB).
  assert (HH := bf_H _ _ _ _ _ _ _ _ _ _ HB).
  assert (Hb0 := bf_b0 _ _ _ _ _ _ _ _ _ _ HB).
  assert (HSF := sumF). assert (Hn := n_bounds).
  assert (HSM : zsum 286 Mt = zsum 30 G) by (rewrite <- nm_l, nm_d; reflexivity).
  assert (HGL := gap_sum_le ll 286 ltac:(lia)). assert (HGD := gap_sum_le dl0 30 ltac:(lia)).
  fold (Gp) in HGL. fold (Gpd) in HGD.
  change (zsum L_CODES (fun c => lfreq syms c * (Znth c ll - Znth c static_ltree_len)))
    with (zsum 286 (fun c => F c * (Znth c ll - stl c))) in HA.
  change (zsum D_CODES (fun d => dfreq syms d * (Znth d dl0 - 5))) with (zsum 30 (fun d => G d * (Znth d dl0 - 5))) in HA.
  change (zsum L_CODES (fun c => if Znth c ll =? 0 then 0 else 2 ^ (15 - Znth c ll))) with (zsum 286 Kl) in HKl.
  change (zsum D_CODES (fun d => if Znth d dl0 =? 0 then 0 else 2 ^ (15 - Znth d dl0))) with (zsum 30 Kd) in HKd.
  (* the header against the menu *)
  assert (Hmenu : thsum C * hdr <= thsum C * (71 + ce_dbl C) +
            hsum (map (fun p => snd p * zsum 286 (ch (tauf (fst p)) ll)) (ce_menu C)) +
            hsum (map (fun p => snd p * zsum 30 (ch (tauf (fst p)) dl0)) (ce_menu C))).
  { unfold thsum. apply (menu_H (ce_menu C) hdr (71 + ce_dbl C) (fun t => zsum 286 (ch (tauf t) ll))
                          (fun t => zsum 30 (ch (tauf t) dl0))).
    intros p Hp. destruct (menu_ok p Hp) as [Hth [Htk _]]. split; [exact Hth|].
    assert (Hne : ce_menu C <> []) by (intros E; rewrite E in Hp; destruct Hp).
    assert (H1 := Htau Hne (tauf (fst p)) Htk).
    destruct (bf_lmax _ _ _ _ _ _ _ _ _ _ HB) as [Hlm _]. destruct (bf_dmax _ _ _ _ _ _ _ _ _ _ HB) as [Hdm _].
    unfold END_BLOCK, L_CODES, D_CODES in Hlm, Hdm.
    rewrite (charge_zsum _ ll lmax 286) in H1 by (try lia;
      intros i Hi; assert (Hr : 0 <= i < L_CODES) by (unfold L_CODES; lia);
      apply (proj2 (bf_llen _ _ _ _ _ _ _ _ _ _ HB i Hr)); lia).
    rewrite (charge_zsum _ dl0 dmax 30) in H1 by (try lia;
      intros i Hi; assert (Hr : 0 <= i < D_CODES) by (unfold D_CODES; lia);
      apply (proj2 (bf_dlen _ _ _ _ _ _ _ _ _ _ HB i Hr)); lia).
    lia. }
  assert (Hfin := final_spec). unfold final_val in Hfin. rewrite <- HL in Hfin.
  (* products with the (nonnegative) multipliers *)
  assert (P1 : ce_lam C * (hdr + zsum 286 (fun c => F c * (Znth c ll - stl c)) + zsum 30 (fun d => G d * (Znth d dl0 - 5)))
               <= ce_lam C * (-1)) by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (P2 : ce_eta C * zsum 286 F <= ce_eta C * L) by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (P3 : ce_md C * zsum 30 Kd <= ce_md C * 2 ^ 15) by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (P4 : ce_sgl C * zsum 286 Gp <= ce_sgl C * 286) by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (P5 : ce_sgd C * zsum 30 Gpd <= ce_sgd C * 30) by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (P6 : ce_th0 C * hdr <= ce_th0 C * 2283) by (apply Z.mul_le_mono_nonneg_l; lia).
  rewrite HSM, HKl in HTL.
  set (X := cost_sum ll dl0 (firstn k syms) - 24 * Z.of_nat k) in *.
  assert (Hmain : ce_D C * (hdr + X - (8 * L - 10)) <= 0).
  { rewrite <- Hsum. nia. }
  assert (Hx : hdr + X - (8 * L - 10) <= 0).
  { destruct (Z_le_gt_dec (hdr + X - (8 * L - 10)) 0) as [|Hgt]; auto.
    assert (0 < ce_D C * (hdr + X - (8 * L - 10))) by (apply Z.mul_pos_pos; lia). lia. }
  unfold X in Hx. lia.
Qed.
End Sound.
