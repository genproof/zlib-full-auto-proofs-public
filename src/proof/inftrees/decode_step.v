(* Part of fact_decode: one iteration keeps the table contents (decode_defs.v dcontent); the last one breaks with every fill done. Use fact_result.v (Section Loop: inv, step_inv, ...) by Require. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.inftrees.facts.
Require Import Zlib.proof.inftrees.fact_result.
Require Import Zlib.proof.inftrees.model_inv.
Require Import Zlib.proof.inftrees.decode_defs.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* Arithmetic and list helpers.                                                                   *)

Lemma ds_land_mod : forall x m, 0 <= m -> Z.land x (2 ^ m - 1) = x mod 2 ^ m.
Proof. intros. rewrite <- Z.land_ones by lia. f_equal. rewrite Z.ones_equiv. lia. Qed.

Lemma ds_pow_pos : forall a, 0 <= a -> 0 < 2 ^ a.
Proof. intros; apply Z.pow_pos_nonneg; lia. Qed.

Lemma ds_pow_split : forall a b, 0 <= a <= b -> 2 ^ b = 2 ^ (b - a) * 2 ^ a.
Proof. intros. rewrite <- Z.pow_add_r by lia. f_equal; lia. Qed.

Lemma ds_mod_add : forall x k a b, 0 <= a <= b -> (x + k * 2 ^ b) mod 2 ^ a = x mod 2 ^ a.
Proof.
  intros. rewrite (ds_pow_split a b) by lia. rewrite Z.mul_assoc. apply Z.mod_add.
  pose proof (ds_pow_pos a); lia.
Qed.

Lemma ds_mod_mod : forall x a b, 0 <= a <= b -> (x mod 2 ^ b) mod 2 ^ a = x mod 2 ^ a.
Proof.
  intros. pose proof (Z.div_mod x (2 ^ b)) as E.
  assert (2 ^ b <> 0) by (pose proof (ds_pow_pos b); lia).
  specialize (E H0).
  rewrite E at 2. rewrite Z.add_comm, Z.mul_comm. rewrite ds_mod_add by lia. reflexivity.
Qed.

Lemma ds_upd_len : forall {A} {d: Inhabitant A} i (l: list A) x, Zlength (upd_Znth i l x) = Zlength l.
Proof.
  intros. destruct (Z_le_gt_dec 0 i); [destruct (Z_lt_dec i (Zlength l))|].
  - apply upd_Znth_Zlength. lia.
  - rewrite upd_Znth_out_of_range by lia. auto.
  - rewrite upd_Znth_out_of_range by lia. auto.
Qed.

Lemma ds_upd_other : forall {A} {d: Inhabitant A} (t: list A) P Q x, P <> Q ->
  Znth P (upd_Znth Q t x) = Znth P t.
Proof.
  intros. destruct (Z_le_gt_dec 0 Q); [destruct (Z_lt_dec Q (Zlength t))|].
  - apply upd_Znth_diff'; lia.
  - rewrite upd_Znth_out_of_range by lia. auto.
  - rewrite upd_Znth_out_of_range by lia. auto.
Qed.

Lemma ds_upd_keep : forall {A} {d: Inhabitant A} (t: list A) P Q x, Znth P t = x ->
  Znth P (upd_Znth Q t x) = x.
Proof.
  intros. destruct (Z.eq_dec P Q).
  - subst. destruct (Z_le_gt_dec 0 Q); [destruct (Z_lt_dec Q (Zlength t))|].
    + apply upd_Znth_same; lia.
    + rewrite upd_Znth_out_of_range by lia; auto.
    + rewrite upd_Znth_out_of_range by lia; auto.
  - rewrite ds_upd_other; auto.
Qed.

Lemma ds_rep_fill_len : forall n t base incr e, Zlength (rep_fill t base incr n e) = Zlength t.
Proof. induction n; intros; cbn [rep_fill]; auto. rewrite IHn. apply ds_upd_len. Qed.

Lemma ds_rep_fill_miss : forall n t base incr e P,
  (forall k, 0 <= k < Z.of_nat n -> base + k * incr <> P) ->
  Znth P (rep_fill t base incr n e) = Znth P t.
Proof.
  induction n; intros; cbn [rep_fill]; auto.
  rewrite IHn by (intros; apply H; lia). apply ds_upd_other.
  intro E. apply (H (Z.of_nat n)); [lia|]. congruence.
Qed.

Lemma ds_rep_fill_keep : forall n t base incr e P, Znth P t = e ->
  Znth P (rep_fill t base incr n e) = e.
Proof. induction n; intros; cbn [rep_fill]; auto. apply IHn. apply ds_upd_keep; auto. Qed.

Lemma ds_rep_fill_hit : forall n t base incr e k, 0 <= k < Z.of_nat n ->
  0 <= base + k * incr < Zlength t ->
  Znth (base + k * incr) (rep_fill t base incr n e) = e.
Proof.
  induction n; intros; cbn [rep_fill]; [lia|].
  destruct (Z.eq_dec k (Z.of_nat n)).
  - subst. apply ds_rep_fill_keep. apply upd_Znth_same. lia.
  - apply IHn; [lia|]. rewrite ds_upd_len. lia.
Qed.

(* The table after the do/while fill of one iteration. *)
Definition fill_tab (type: Z) (W: list Z) (s: state) : list entry :=
  rep_fill (s_tab s) (s_next s + Z.shiftr (s_huff s) (s_drop s)) (Z.shiftl 1 (s_len s - s_drop s))
    (Z.to_nat (Z.shiftl 1 (s_curr s) / Z.shiftl 1 (s_len s - s_drop s)))
    (sym_entry type (Znth (s_sym s) W) (s_len s - s_drop s)).

(* The positions the fill of sorted position j writes. *)
Definition fpos (ls: list Z) (root j P: Z) : Prop :=
  (Znth j ls <= root /\ exists k, 0 <= k < 2 ^ (root - Znth j ls) /\ P = dhuff ls j + k * 2 ^ Znth j ls) \/
  (root < Znth j ls /\ exists k, 0 <= k < 2 ^ (gmax ls root (pfx ls root j) - Znth j ls) /\
     P = dnxt ls root (pfx ls root j) + Z.shiftr (dhuff ls j) root + k * 2 ^ (Znth j ls - root)).

Section D.
Variables (type: Z) (lens W ls: list Z) (root: Z) (old: list entry).
Variable Hrange : Forall (fun l => 1 <= l <= MAXBITS) ls.
Variable Hsorted : forall a b, 0 <= a -> a <= b < Zlength ls -> Znth a ls <= Znth b ls.
Variable HN : 0 < Zlength ls.
Variable HWls : forall i, 0 <= i < Zlength ls -> Znth (Znth i W) lens = Znth i ls.
Variable HWr : Forall (fun s => 0 <= s <= 65535) W.
Variable Hroot : Znth 0 ls <= root <= Znth (Zlength ls - 1) ls.
Variable Hk : ksum ls <= 2 ^ MAXBITS.
Variable Hinc : ksum ls < 2 ^ MAXBITS -> Znth (Zlength ls - 1) ls <= root.
Variable Htype : 0 <= type <= 2.
Variable Hcodes : type = CODES -> Znth (Zlength ls - 1) ls <= root.
Variable Hcap : (type = LENS -> ENOUGH_LENS <= Zlength old) /\ (type = DISTS -> ENOUGH_DISTS <= Zlength old).
Variable Hcap0 : 2 ^ root <= Zlength old.
Variable Hold : Forall entry_ok old.
Variable Hbits : bits_stmt.
Variable Hsub : subbits_stmt.

Lemma ds_lr : forall i, 0 <= i < Zlength ls -> 1 <= Znth i ls <= MAXBITS.
Proof. apply ls_range; auto. Qed.

Lemma ds_rr : 1 <= root <= MAXBITS.
Proof. pose proof (ds_lr 0 ltac:(lia)). pose proof (ds_lr (Zlength ls - 1) ltac:(lia)). lia. Qed.

Lemma ds_kpre : forall i, 0 <= i < Zlength ls ->
  0 <= kpre ls i /\ kpre ls i + 2 ^ (MAXBITS - Znth i ls) <= 2 ^ MAXBITS.
Proof. intros. split; [unfold kpre; apply ksum_nonneg|]. pose proof (kpre_next_le ls i H). lia. Qed.

Lemma ds_C : forall i, 0 <= i < Zlength ls ->
  0 <= dcode ls i /\ kpre ls i = dcode ls i * 2 ^ (MAXBITS - Znth i ls) /\ dcode ls i < 2 ^ Znth i ls.
Proof.
  intros. pose proof (C_facts type ls root Hrange Hsorted HN Hk Htype i H) as HC.
  cbv zeta in HC. destruct HC as (A & B & C & D & E). unfold dcode. lia.
Qed.

Lemma ds_huff_range : forall i, 0 <= i < Zlength ls -> 0 <= dhuff ls i < 2 ^ Znth i ls.
Proof.
  intros. destruct Hbits as (B1 & _). pose proof (ds_lr i H). unfold dhuff. apply B1. lia.
Qed.

Lemma ds_huff_mod : forall i m, 0 <= i < Zlength ls -> 0 <= m <= Znth i ls ->
  dhuff ls i mod 2 ^ m = reverse_bits (kpre ls i / 2 ^ (MAXBITS - m)) m.
Proof.
  intros. destruct Hbits as (B1 & B2 & _). pose proof (ds_lr i H). pose proof (ds_C i H) as (C0 & _).
  rewrite <- ds_land_mod by lia. unfold dhuff. rewrite B2 by lia. f_equal. unfold dcode.
  rewrite Z.div_div by (try apply Z.pow_nonzero; try apply ds_pow_pos; lia).
  rewrite <- Z.pow_add_r by lia. f_equal. f_equal. lia.
Qed.

Lemma ds_hm : forall i, 0 <= i < Zlength ls -> root <= Znth i ls ->
  dhuff ls i mod 2 ^ root = reverse_bits (pfx ls root i) root.
Proof. intros. pose proof ds_rr. rewrite ds_huff_mod by lia. reflexivity. Qed.

(* Prefix-freeness: no earlier code is a prefix of a later one. *)
Lemma ds_pf : forall j i, 0 <= j < i -> i < Zlength ls -> dhuff ls i mod 2 ^ Znth j ls <> dhuff ls j.
Proof.
  intros j i Hj Hi E.
  assert (Hl: Znth j ls <= Znth i ls) by (apply Hsorted; lia).
  pose proof (ds_lr j ltac:(lia)). pose proof (ds_lr i ltac:(lia)).
  rewrite ds_huff_mod in E by lia.
  destruct (ds_C j ltac:(lia)) as (Cj0 & CjK & Cjl).
  destruct (ds_kpre i ltac:(lia)) as (Ki0 & Ki1).
  assert (Hq: 0 <= kpre ls i / 2 ^ (MAXBITS - Znth j ls) < 2 ^ Znth j ls).
  { split. apply Z.div_pos; [lia| apply ds_pow_pos; lia].
    apply Z.div_lt_upper_bound; [apply ds_pow_pos; lia|]. rewrite <- Z.pow_add_r by lia.
    replace (MAXBITS - Znth j ls + Znth j ls) with MAXBITS by lia.
    pose proof (ds_pow_pos (MAXBITS - Znth i ls)); lia. }
  assert (EC: kpre ls i / 2 ^ (MAXBITS - Znth j ls) = dcode ls j).
  { apply (rev_inj root Hbits _ _ (Znth j ls)); auto; lia. }
  assert (H3: kpre ls (j + 1) <= kpre ls i) by (apply kpre_mono; lia).
  rewrite kpre_S in H3 by lia.
  assert (dcode ls j + 1 <= kpre ls i / 2 ^ (MAXBITS - Znth j ls)).
  { apply Z.div_le_lower_bound; [apply ds_pow_pos; lia|]. nia. }
  lia.
Qed.

Lemma ds_pfx_range : forall i, 0 <= i < Zlength ls -> 0 <= pfx ls root i < 2 ^ root.
Proof. apply pfx_range; auto. Qed.

Lemma ds_g : forall i, 0 <= i < Zlength ls -> root < Znth i ls ->
  Znth i ls <= gmax ls root (pfx ls root i) <= MAXBITS.
Proof. apply gmax_long; auto. Qed.

Lemma ds_fpos_short : forall j P, 0 <= j < Zlength ls -> Znth j ls <= root -> fpos ls root j P ->
  0 <= P < 2 ^ root /\ P mod 2 ^ Znth j ls = dhuff ls j.
Proof.
  intros j P Hj Hs [[_ (k & Hk0 & ->)]|[? _]]; [|lia].
  pose proof (ds_lr j Hj). pose proof (ds_huff_range j Hj).
  rewrite ds_mod_add by lia. rewrite Z.mod_small by lia. split; [|auto].
  rewrite (ds_pow_split (Znth j ls) root) by lia. nia.
Qed.

Lemma ds_fpos_long : forall j P, 0 <= j < Zlength ls -> root < Znth j ls -> fpos ls root j P ->
  dnxt ls root (pfx ls root j) <= P < dnxt ls root (pfx ls root j) + 2 ^ (gmax ls root (pfx ls root j) - root) /\
  2 ^ root <= dnxt ls root (pfx ls root j).
Proof.
  intros j P Hj Hs [[? _]|[_ (k & Hk0 & ->)]]; [lia|].
  pose proof (ds_lr j Hj). pose proof (ds_huff_range j Hj). pose proof ds_rr.
  pose proof (ds_g j Hj Hs). pose proof (ds_pfx_range j Hj).
  pose proof (sumq_nonneg ls root (pfx ls root j) ltac:(lia)).
  unfold dnxt. rewrite Z.shiftr_div_pow2 by lia.
  assert (A: 0 <= dhuff ls j / 2 ^ root < 2 ^ (Znth j ls - root)).
  { split; [apply Z.div_pos; [lia | apply ds_pow_pos; lia]|].
    apply Z.div_lt_upper_bound; [apply ds_pow_pos; lia|].
    rewrite <- Z.pow_add_r by lia. replace (root + (Znth j ls - root)) with (Znth j ls) by lia. lia. }
  rewrite (ds_pow_split (Znth j ls - root) (gmax ls root (pfx ls root j) - root)) by lia.
  replace (gmax ls root (pfx ls root j) - root - (Znth j ls - root))
    with (gmax ls root (pfx ls root j) - Znth j ls) by lia.
  nia.
Qed.

Lemma ds_regions : forall j i, 0 <= j < Zlength ls -> 0 <= i < Zlength ls ->
  root < Znth j ls -> root < Znth i ls -> pfx ls root j < pfx ls root i ->
  dnxt ls root (pfx ls root j) + 2 ^ (gmax ls root (pfx ls root j) - root) <= dnxt ls root (pfx ls root i).
Proof.
  intros. pose proof (ds_pfx_range j H). pose proof (ds_pfx_range i H0).
  pose proof (sumq_mono ls root (pfx ls root j + 1) (pfx ls root i) ltac:(lia)).
  rewrite sumq_succ in H6 by lia. rewrite (fq_long ls root Hrange HN Hroot j H H1) in H6.
  unfold dnxt. lia.
Qed.

(* Two fills hit disjoint positions. *)
Lemma ds_D1 : forall j i P, 0 <= j < i -> i < Zlength ls -> fpos ls root j P -> fpos ls root i P -> False.
Proof.
  intros j i P Hji HiN Fj Fi.
  assert (Hl: Znth j ls <= Znth i ls) by (apply Hsorted; lia).
  pose proof (ds_lr j ltac:(lia)). pose proof (ds_lr i ltac:(lia)). pose proof ds_rr.
  destruct (Z_le_gt_dec (Znth i ls) root) as [Si|Li']; [|assert (Li: root < Znth i ls) by lia].
  - destruct (ds_fpos_short j P ltac:(lia) ltac:(lia) Fj) as [_ Ej].
    destruct Fi as [[_ (k & Hk0 & ->)]|[? _]]; [|lia].
    rewrite ds_mod_add in Ej by lia. apply (ds_pf j i); auto; lia.
  - destruct (Z_le_gt_dec (Znth j ls) root) as [Sj|Lj']; [|assert (Lj: root < Znth j ls) by lia].
    + destruct (ds_fpos_short j P ltac:(lia) Sj Fj). destruct (ds_fpos_long i P ltac:(lia) Li Fi). lia.
    + assert (pfx ls root j <= pfx ls root i) by (apply pfx_mono; auto; lia).
      destruct (Z.eq_dec (pfx ls root j) (pfx ls root i)) as [Ep|Ep].
      * destruct Fj as [[? _]|[_ (kj & Hkj & Pj)]]; [lia|].
        destruct Fi as [[? _]|[_ (ki & Hki & Pi)]]; [lia|].
        rewrite Ep in Pj. rewrite Pj in Pi.
        assert (EA: Z.shiftr (dhuff ls j) root + kj * 2 ^ (Znth j ls - root) =
                    Z.shiftr (dhuff ls i) root + ki * 2 ^ (Znth i ls - root)) by lia.
        rewrite !Z.shiftr_div_pow2 in EA by lia.
        pose proof (ds_huff_range j ltac:(lia)). pose proof (ds_huff_range i ltac:(lia)).
        assert (E1: (dhuff ls i / 2 ^ root) mod 2 ^ (Znth j ls - root) = dhuff ls j / 2 ^ root).
        { rewrite <- (ds_mod_add (dhuff ls i / 2 ^ root) ki (Znth j ls - root) (Znth i ls - root)) by lia.
          rewrite <- EA. rewrite ds_mod_add by lia. apply Z.mod_small.
          split; [apply Z.div_pos; [lia | apply ds_pow_pos; lia]|].
          apply Z.div_lt_upper_bound; [apply ds_pow_pos; lia|].
          rewrite <- Z.pow_add_r by lia. replace (root + (Znth j ls - root)) with (Znth j ls) by lia. lia. }
        assert (E2: dhuff ls i mod 2 ^ root = dhuff ls j mod 2 ^ root).
        { rewrite !ds_hm by lia. rewrite Ep. reflexivity. }
        apply (ds_pf j i); [lia|lia|].
        replace (2 ^ Znth j ls) with (2 ^ root * 2 ^ (Znth j ls - root))
          by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
        rewrite Z.rem_mul_r by (try apply Z.pow_nonzero; try apply ds_pow_pos; lia).
        rewrite E1, E2.
        pose proof (Z.div_mod (dhuff ls j) (2 ^ root) ltac:(apply Z.pow_nonzero; lia)). lia.
      * pose proof (ds_regions j i ltac:(lia) ltac:(lia) Lj Li ltac:(lia)).
        destruct (ds_fpos_long j P ltac:(lia) Lj Fj). destruct (ds_fpos_long i P ltac:(lia) Li Fi). lia.
Qed.

(* A root-table link of a later long position hits no earlier fill. *)
Lemma ds_D2 : forall j i P, 0 <= j < i -> i < Zlength ls -> root < Znth i ls ->
  fpos ls root j P -> P <> reverse_bits (pfx ls root i) root.
Proof.
  intros j i P Hji HiN Li Fj E. pose proof ds_rr.
  assert (Hl: Znth j ls <= Znth i ls) by (apply Hsorted; lia).
  pose proof (ds_lr j ltac:(lia)).
  destruct (Z_le_gt_dec (Znth j ls) root) as [Sj|Lj']; [|assert (Lj: root < Znth j ls) by lia].
  - destruct (ds_fpos_short j P ltac:(lia) Sj Fj) as [_ Ej]. rewrite E in Ej.
    rewrite <- ds_hm in Ej by lia. rewrite ds_mod_mod in Ej by lia. apply (ds_pf j i); auto; lia.
  - destruct (ds_fpos_long j P ltac:(lia) Lj Fj). destruct Hbits as (B1 & _).
    pose proof (B1 (pfx ls root i) root ltac:(lia)). lia.
Qed.

(* A fill hits no root-table link of an earlier or the same group. *)
Lemma ds_D2' : forall j i P, 0 <= j <= i -> i < Zlength ls -> root < Znth j ls ->
  fpos ls root i P -> P <> reverse_bits (pfx ls root j) root.
Proof.
  intros j i P Hji HiN Lj Fi E. pose proof ds_rr.
  assert (Hl: Znth j ls <= Znth i ls) by (apply Hsorted; lia).
  destruct (ds_fpos_long i P ltac:(lia) ltac:(lia) Fi). destruct Hbits as (B1 & _).
  pose proof (B1 (pfx ls root j) root ltac:(lia)). lia.
Qed.

Lemma ds_D3 : forall a b, 0 <= a < Zlength ls -> 0 <= b < Zlength ls ->
  reverse_bits (pfx ls root a) root = reverse_bits (pfx ls root b) root -> dlink ls root a = dlink ls root b.
Proof.
  intros. pose proof ds_rr.
  assert (pfx ls root a = pfx ls root b).
  { apply (rev_inj root Hbits _ _ root); auto; try lia; apply ds_pfx_range; auto. }
  unfold dlink. rewrite H3. reflexivity.
Qed.

Lemma ds_fills_transfer : forall j t t', (forall P, fpos ls root j P -> Znth P t' = Znth P t) ->
  fills_done type W ls root j t -> fills_done type W ls root j t'.
Proof.
  intros j t t' H [F1 F2]. split.
  - intros Hs k Hk0. rewrite H; [apply F1; auto|]. left. split; [auto|]. exists k; auto.
  - intros Hs k Hk0. rewrite H; [apply F2; auto|]. right. split; [auto|]. exists k; auto.
Qed.

Lemma ds_fill_params : forall i s, inv ls root old i s ->
  (Znth i ls <= root ->
     s_next s + Z.shiftr (s_huff s) (s_drop s) = dhuff ls i /\
     Z.shiftl 1 (s_len s - s_drop s) = 2 ^ Znth i ls /\
     Z.shiftl 1 (s_curr s) / Z.shiftl 1 (s_len s - s_drop s) = 2 ^ (root - Znth i ls) /\
     sym_entry type (Znth (s_sym s) W) (s_len s - s_drop s) = sym_entry type (Znth i W) (Znth i ls)) /\
  (root < Znth i ls ->
     s_next s + Z.shiftr (s_huff s) (s_drop s) = dnxt ls root (pfx ls root i) + Z.shiftr (dhuff ls i) root /\
     Z.shiftl 1 (s_len s - s_drop s) = 2 ^ (Znth i ls - root) /\
     Z.shiftl 1 (s_curr s) / Z.shiftl 1 (s_len s - s_drop s) = 2 ^ (gmax ls root (pfx ls root i) - Znth i ls) /\
     sym_entry type (Znth (s_sym s) W) (s_len s - s_drop s) = sym_entry type (Znth i W) (Znth i ls - root)) /\
  0 <= Z.shiftl 1 (s_curr s) / Z.shiftl 1 (s_len s - s_drop s).
Proof.
  intros i s Hinv.
  destruct Hinv as (Hi & Hsym & Hlen & Hhuff & Hcl & Hcnt & Hlow & Hhigh & Htl & Htok & Htfr & Hucap).
  pose proof (ds_lr i Hi). pose proof ds_rr.
  assert (Hh: s_huff s = dhuff ls i) by (rewrite Hhuff; reflexivity).
  rewrite Hsym, Hlen, Hh.
  destruct (Z_le_gt_dec (Znth i ls) root) as [S|L'].
  - destruct (Hlow S) as (Ed & Ec & En & Eu & Elo). rewrite Ed, Ec, En.
    rewrite Z.shiftr_0_r, Z.sub_0_r, !pow2_shiftl by lia.
    rewrite (ds_pow_split (Znth i ls) root) by lia. rewrite Z.div_mul by (apply Z.pow_nonzero; lia).
    split; [intros; repeat split; first [lia | reflexivity]|]. split; [intros; lia|].
    apply Z.pow_nonneg; lia.
  - destruct (Hhigh ltac:(lia)) as (Ed & Elo & Ec & En & Eu).
    pose proof (ds_g i Hi ltac:(lia)).
    rewrite Ed, Ec, En.
    rewrite !pow2_shiftl by lia.
    rewrite (ds_pow_split (Znth i ls - root) (gmax ls root (pfx ls root i) - root)) by lia.
    rewrite Z.div_mul by (apply Z.pow_nonzero; lia).
    replace (gmax ls root (pfx ls root i) - root - (Znth i ls - root))
      with (gmax ls root (pfx ls root i) - Znth i ls) by lia.
    split; [intros; lia|]. split; [intros; repeat split; first [lia | reflexivity]|].
    apply Z.pow_nonneg; lia.
Qed.

Lemma ds_fill_ok : forall i s, inv ls root old i s -> dcontent type W ls root i (s_tab s) ->
  (forall j, 0 <= j <= i -> fills_done type W ls root j (fill_tab type W s)) /\
  (forall j, 0 <= j <= i -> link_done ls root j (fill_tab type W s)) /\
  Zlength (fill_tab type W s) = Zlength old.
Proof.
  intros i s Hinv [Cf Cl].
  pose proof (ds_fill_params i s Hinv) as (PS & PL & Pn).
  pose proof Hinv as (Hi & Hsym & Hlen & Hhuff & Hcl & Hcnt & Hlow & Hhigh & Htl & Htok & Htfr & Hucap).
  pose proof (ds_lr i Hi). pose proof ds_rr.
  assert (HW: forall k, 0 <= k < Z.of_nat (Z.to_nat (Z.shiftl 1 (s_curr s) / Z.shiftl 1 (s_len s - s_drop s))) ->
     fpos ls root i (s_next s + Z.shiftr (s_huff s) (s_drop s) + k * Z.shiftl 1 (s_len s - s_drop s))).
  { intros k Hkk. rewrite Z2Nat.id in Hkk by lia.
    destruct (Z_le_gt_dec (Znth i ls) root) as [S|L'].
    - destruct (PS S) as (E1 & E2 & E3 & _). rewrite E3 in Hkk. rewrite E1, E2.
      left. split; [auto|]. exists k. auto.
    - destruct (PL ltac:(lia)) as (E1 & E2 & E3 & _). rewrite E3 in Hkk. rewrite E1, E2.
      right. split; [lia|]. exists k. auto. }
  assert (Hin: forall P, fpos ls root i P -> 0 <= P < Zlength (s_tab s)).
  { intros P F. rewrite Htl. destruct (Z_le_gt_dec (Znth i ls) root) as [S|L'].
    - destruct (ds_fpos_short i P Hi S F). lia.
    - destruct (ds_fpos_long i P Hi ltac:(lia) F) as [A B].
      destruct (Hhigh ltac:(lia)) as (Ed & Elo & Ec & En & Eu).
      assert (dnxt ls root (pfx ls root i) + 2 ^ (gmax ls root (pfx ls root i) - root) = s_used s)
        by (unfold dnxt; rewrite Eu, En, Ec; reflexivity).
      lia. }
  split; [|split].
  - intros j Hj. destruct (Z.eq_dec j i) as [->|Hne].
    + split.
      * intros S k Hkk. destruct (PS S) as (E1 & E2 & E3 & E4). unfold fill_tab. rewrite E4.
        rewrite <- E1, <- E2. apply ds_rep_fill_hit.
        -- rewrite Z2Nat.id by lia. rewrite E3. lia.
        -- apply Hin. rewrite E1, E2. left. split; [auto|]. exists k. auto.
      * intros L k Hkk. destruct (PL L) as (E1 & E2 & E3 & E4). unfold fill_tab. rewrite E4.
        rewrite <- E1, <- E2. apply ds_rep_fill_hit.
        -- rewrite Z2Nat.id by lia. rewrite E3. lia.
        -- apply Hin. rewrite E1, E2. right. split; [auto|]. exists k. auto.
    + apply (ds_fills_transfer j (s_tab s)); [|apply Cf; lia].
      intros P F. unfold fill_tab. apply ds_rep_fill_miss. intros k Hkk E.
      apply (ds_D1 j i P); [lia|lia|auto|]. rewrite <- E. apply HW; auto.
  - intros j Hj Hr. unfold fill_tab. rewrite ds_rep_fill_miss.
    + apply (Cl j); auto; lia.
    + intros k Hkk E. apply (ds_D2' j i _ ltac:(lia) ltac:(lia) Hr (HW k Hkk) E).
  - unfold fill_tab. rewrite ds_rep_fill_len. auto.
Qed.

Lemma ds_step_cases : forall i s s', inv ls root old i s -> i + 1 < Zlength ls ->
  step type lens W root (Znth (Zlength ls - 1) ls) s = Continue s' ->
  (s_tab s' = fill_tab type W s /\
     (root < Znth (i + 1) ls -> root < Znth i ls /\ pfx ls root (i + 1) = pfx ls root i)) \/
  (root < Znth (i + 1) ls /\
     s_tab s' = upd_Znth (reverse_bits (pfx ls root (i + 1)) root) (fill_tab type W s) (dlink ls root (i + 1))).
Proof.
  intros i s s' Hinv Hi1 Hst.
  assert (Hinv' : inv ls root old (i + 1) s').
  { destruct (step_inv type lens W ls root old Hrange Hsorted HN HWls HWr Hroot Hk Hinc Htype Hcodes Hcap
                Hbits Hsub i s Hinv Hi1) as [(s'' & E & H)|(s'' & E & _)];
      rewrite Hst in E; inversion E; subst; auto. }
  pose proof Hinv as Hinv0.
  destruct s as [huff sym len curr drop low used next cnt tab].
  unfold step, fill_tab in *. cbv beta zeta in Hst.
  cbn [s_huff s_sym s_len s_curr s_drop s_low s_used s_next s_cnt s_tab] in *.
  pose proof ds_rr as Hr.
  match type of Hst with (if ?c then _ else _) = _ => destruct c end; [discriminate|].
  match type of Hst with (if ?c then _ else _) = _ => destruct c eqn:Ec end.
  - match type of Hst with (if ?c then _ else _) = _ => destruct c end; [discriminate|].
    injection Hst as <-. right.
    destruct Hinv' as (Hi' & Hsym' & Hlen' & Hhuff' & Hcl' & Hcnt' & Hlow' & Hhigh' & _).
    cbn [s_huff s_sym s_len s_curr s_drop s_low s_used s_next s_cnt s_tab] in *.
    apply andb_true_iff in Ec as [Ec _]. apply Z.ltb_lt in Ec. rewrite Hlen' in Ec.
    destruct (Hhigh' Ec) as (Ed' & Elo' & Ec' & En' & Eu').
    split; auto. rewrite Elo'. unfold dlink, dnxt. rewrite <- Ec', <- En'. reflexivity.
  - injection Hst as <-. left. cbn [s_tab]. split; auto. intro Hl1.
    destruct Hinv' as (Hi' & Hsym' & Hlen' & Hhuff' & Hcl' & Hcnt' & Hlow' & Hhigh' & _).
    destruct Hinv0 as (Hi & Hsym & Hlen & Hhuff & Hcl & Hcnt & Hlow & Hhigh & _).
    cbn [s_huff s_sym s_len s_curr s_drop s_low s_used s_next s_cnt s_tab] in *.
    destruct (Hhigh' Hl1) as (Ed' & Elo' & _).
    pose proof Hbits as (B1 & _).
    pose proof (B1 (pfx ls root (i + 1)) root ltac:(lia)).
    destruct (Z_le_gt_dec (Znth i ls) root) as [S|L'].
    + destruct (Hlow S) as (_ & _ & _ & _ & Elo). rewrite Elo, ones32 in Elo'.
      assert (2 ^ root <= 2 ^ 15) by (apply Z.pow_le_mono_r; unfold MAXBITS in *; lia). lia.
    + destruct (Hhigh ltac:(lia)) as (_ & Elo & _). rewrite Elo in Elo'.
      split; [lia|]. symmetry. apply (rev_inj root Hbits _ _ root); auto; try lia.
      apply ds_pfx_range; lia. apply ds_pfx_range; lia.
Qed.

Lemma ds_step_last : forall s, inv ls root old (Zlength ls - 1) s ->
  exists s', step type lens W root (Znth (Zlength ls - 1) ls) s = Break s' /\
    s_used s' = s_used s /\ s_next s' = s_next s /\ s_len s' = s_len s /\ s_drop s' = s_drop s /\
    s_huff s' = next_huff (s_huff s) (s_len s) /\ s_tab s' = fill_tab type W s.
Proof.
  intros s Hinv.
  destruct Hinv as (Hi & Hsym & Hlen & Hhuff & Hcl & Hcnt & _).
  destruct s as [huff sym len curr drop low used next cnt tab].
  cbn [s_huff s_sym s_len s_curr s_drop s_low s_used s_next s_cnt s_tab] in *.
  assert (Hc: Znth len cnt - 1 = 0).
  { rewrite Hlen, Hcnt by (apply ds_lr; lia).
    replace (sublist (Zlength ls - 1) (Zlength ls) ls) with [Znth (Zlength ls - 1) ls].
    - rewrite count_len_cons, Z.eqb_refl. reflexivity.
    - rewrite <- sublist_len_1 by lia. f_equal. lia. }
  unfold step, fill_tab. cbv beta zeta.
  cbn [s_huff s_sym s_len s_curr s_drop s_low s_used s_next s_cnt s_tab].
  rewrite Hc, Hlen, !Z.eqb_refl. cbn [andb].
  eexists. split; [reflexivity|]. cbn. repeat split; reflexivity.
Qed.

Lemma ds_step_main : forall i s s', inv ls root old i s -> dcontent type W ls root i (s_tab s) ->
  i + 1 < Zlength ls ->
  step type lens W root (Znth (Zlength ls - 1) ls) s = Continue s' ->
  dcontent type W ls root (i + 1) (s_tab s').
Proof.
  intros i s s' Hinv Hc Hi1 Hst.
  destruct (ds_fill_ok i s Hinv Hc) as (F1 & F2 & F3).
  pose proof Hinv as (Hi & _).
  pose proof ds_rr as Hr.
  destruct (ds_step_cases i s s' Hinv Hi1 Hst) as [(Et & Hl)|(Hl & Et)]; rewrite Et; split.
  - intros j Hj. apply F1. lia.
  - intros j Hj HjN. destruct (Z.eq_dec j (i + 1)) as [->|Hne].
    + intro Hr1. destruct (Hl Hr1) as (Hli & Ep).
      pose proof (F2 i ltac:(lia) Hli) as X. unfold dlink. rewrite Ep. exact X.
    + apply F2. lia.
  - intros j Hj. apply (ds_fills_transfer j (fill_tab type W s)); [|apply F1; lia].
    intros P F. apply ds_upd_other. apply (ds_D2 j (i + 1)); auto; lia.
  - assert (HL: 0 <= reverse_bits (pfx ls root (i + 1)) root < Zlength (fill_tab type W s)).
    { pose proof Hbits as (B1 & _). pose proof (B1 (pfx ls root (i + 1)) root ltac:(lia)). lia. }
    intros j Hj HjN. destruct (Z.eq_dec j (i + 1)) as [->|Hne].
    + intros _. apply upd_Znth_same. auto.
    + intro Hrj.
      destruct (Z.eq_dec (reverse_bits (pfx ls root j) root) (reverse_bits (pfx ls root (i + 1)) root)) as [EL|NL].
      * rewrite EL, upd_Znth_same by auto. apply ds_D3; auto; lia.
      * rewrite ds_upd_other by auto. apply F2; [lia|auto].
Qed.

Lemma ds_last_main : forall s, inv ls root old (Zlength ls - 1) s ->
  dcontent type W ls root (Zlength ls - 1) (s_tab s) ->
  exists s', step type lens W root (Znth (Zlength ls - 1) ls) s = Break s' /\
    s_used s' = s_used s /\ s_next s' = s_next s /\ s_len s' = s_len s /\ s_drop s' = s_drop s /\
    s_huff s' = next_huff (s_huff s) (s_len s) /\
    (forall j, 0 <= j < Zlength ls -> fills_done type W ls root j (s_tab s') /\ link_done ls root j (s_tab s')).
Proof.
  intros s Hinv Hc.
  destruct (ds_fill_ok (Zlength ls - 1) s Hinv Hc) as (F1 & F2 & F3).
  destruct (ds_step_last s Hinv) as (s' & E & E1 & E2 & E3 & E4 & E5 & Et).
  exists s'. repeat (split; [assumption|]).
  intros j Hj. rewrite Et. split; [apply F1 | apply F2]; lia.
Qed.

End D.

Lemma dstep_last_ok : dstep_stmt /\ dlast_stmt.
Proof.
  split.
  - intros type lens W ls root old i s s' Hd Hb Hs Hinv Hc Hi1 Hst.
    destruct Hd as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14).
    eapply ds_step_main; eauto.
  - intros type lens W ls root old s Hd Hb Hs Hinv Hc.
    destruct Hd as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14).
    eapply ds_last_main; eauto.
Qed.
