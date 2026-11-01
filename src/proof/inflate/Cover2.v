(* THE covering fact, corrected: Tables.v's cover_stmt is false (a CODES table built from
   20 code lengths gives symbol 19 the end-of-block entry); inflate always builds the code length code
   from 19 lengths, so the hypothesis (type = CODES -> Zlength lens <= 19) is added (as fact_decode has). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.inflate.Inv.
Require Import Zlib.proof.inftrees.facts.
Require Import Zlib.proof.inftrees.fact_result.
Require Import Zlib.proof.inftrees.decode_defs.
Require Import Zlib.proof.inftrees.decode_step.
Require Import Zlib.proof.inftrees.decode_run.
Require Import Zlib.proof.inftrees.part_decode.
Require Import Zlib.proof.inftrees.part_result.
Require Zlib.proof.inftrees.part_sorted.
Require Zlib.proof.inftrees.part_rfc.
Require Zlib.proof.inftrees.part_bits.
Require Zlib.proof.inftrees.part_subbits.
Require Zlib.proof.inftrees.part_size.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The entry of a symbol is final, with a meaning of its kind (a check over all symbols).          *)

Definition final_okb (kind: Z) (e: entry) : bool :=
  if kind =? CODES then ((e_op e =? 0) && (0 <=? e_val e) && (e_val e <=? 18)) || (e_op e =? 64)
  else if kind =? LENS then
    ((e_op e =? 0) && (0 <=? e_val e) && (e_val e <=? 255)) ||
    ((16 <=? e_op e) && (e_op e <=? 21) && (3 <=? e_val e) && (e_val e <=? 258)) || (e_op e =? 96) ||
    (negb (Z.land (e_op e) 64 =? 0) && (Z.land (e_op e) 48 =? 0))
  else
    ((16 <=? e_op e) && (e_op e <=? 29) && (1 <=? e_val e) && (e_val e <=? 32768)) ||
    (negb (Z.land (e_op e) 64 =? 0) && (Z.land (e_op e) 48 =? 0)).

Lemma final_okb_ok : forall kind e, final_okb kind e = true -> final_ok kind e.
Proof.
  intros kind e H. unfold final_okb, final_ok in *.
  destruct (kind =? CODES); [|destruct (kind =? LENS)];
    repeat (rewrite ?orb_true_iff, ?andb_true_iff, ?negb_true_iff, ?Z.eqb_eq, ?Z.eqb_neq, ?Z.leb_le in H);
    lia.
Qed.

Definition sym_okb (type: Z) (n: nat) : bool :=
  forallb (fun s => negb (islink type (e_op (sym_entry type s 0))) && final_okb type (sym_entry type s 0))
          (zseq 0 n).

Lemma sym_okb_0 : sym_okb 0 19 = true. Proof. vm_compute. reflexivity. Qed.
Lemma sym_okb_1 : sym_okb 1 288 = true. Proof. vm_compute. reflexivity. Qed.
Lemma sym_okb_2 : sym_okb 2 32 = true. Proof. vm_compute. reflexivity. Qed.

Lemma sym_ok : forall type s b, 0 <= type <= 2 -> 0 <= s < max_codes type -> (type = CODES -> s < 19) ->
  islink type (e_op (sym_entry type s b)) = false /\ final_ok type (sym_entry type s b) /\
  e_bits (sym_entry type s b) = b.
Proof.
  intros type s b Ht Hs H19.
  assert (E: sym_entry type s b = mkE (e_op (sym_entry type s 0)) b (e_val (sym_entry type s 0))).
  { unfold sym_entry. destruct (s + 1 <? match_of type); [|destruct (match_of type <=? s)]; reflexivity. }
  assert (K: forall n, sym_okb type n = true -> 0 <= s < Z.of_nat n ->
             islink type (e_op (sym_entry type s 0)) = false /\ final_okb type (sym_entry type s 0) = true).
  { intros n Hn Hsn. unfold sym_okb in Hn. rewrite forallb_forall in Hn.
    specialize (Hn s ltac:(apply In_zseq; lia)). apply andb_prop in Hn. destruct Hn as [H1 H2].
    apply negb_true_iff in H1. auto. }
  assert (K2: islink type (e_op (sym_entry type s 0)) = false /\ final_okb type (sym_entry type s 0) = true).
  { unfold max_codes, CODES in *.
    assert (type = 0 \/ type = 1 \/ type = 2) as [-> | [-> | ->]] by lia; cbn in Hs.
    - apply (K 19%nat); [apply sym_okb_0 | cbn; specialize (H19 eq_refl); lia].
    - apply (K 288%nat); [apply sym_okb_1 | cbn; lia].
    - apply (K 32%nat); [apply sym_okb_2 | cbn; lia]. }
  destruct K2 as [K1 K2]. apply final_okb_ok in K2.
  rewrite E. cbn [e_op e_bits]. split; [auto|]. split; [|reflexivity].
  unfold final_ok in *. cbn [e_op e_val]. exact K2.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Covering: every pattern of a complete code starts with exactly one code (Kraft intervals).       *)

Lemma pow2_pos : forall n, 0 <= n -> 0 < 2 ^ n.
Proof. intros. apply Z.pow_pos_nonneg; lia. Qed.

Lemma pow2_split : forall a b, 0 <= a -> 0 <= b -> 2 ^ (a + b) = 2 ^ a * 2 ^ b.
Proof. intros. apply Z.pow_add_r; lia. Qed.

(* the top m of the d reversed bits of P are the reversed low m bits of P *)
Lemma rev_top : bits_stmt -> forall P d m, 0 <= m <= d -> 0 <= P < 2 ^ d ->
  reverse_bits P d / 2 ^ (d - m) = reverse_bits (P mod 2 ^ m) m.
Proof.
  intros Hbits P d m Hm HP. destruct Hbits as (B1 & B2 & B3 & B4 & B5).
  pose proof (B1 P d ltac:(lia)) as HR.
  assert (Hq: 0 <= reverse_bits P d / 2 ^ (d - m) < 2 ^ m).
  { pose proof (pow2_pos (d - m) ltac:(lia)). split; [apply Z.div_pos; lia|].
    apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia.
    replace (d - m + m) with d by lia. lia. }
  pose proof (B2 (reverse_bits P d) d m ltac:(lia) ltac:(lia)) as E.
  rewrite B3 in E by lia.
  transitivity (reverse_bits (reverse_bits (reverse_bits P d / 2 ^ (d - m)) m) m).
  - symmetry. apply B3; lia.
  - f_equal. rewrite <- E. rewrite <- Z.land_ones by lia. rewrite Z.ones_equiv. f_equal; try lia.
Qed.

Lemma find_interval : forall (f: Z -> Z) v n, f 0 <= v < f (Z.of_nat n) ->
  exists j, 0 <= j < Z.of_nat n /\ f j <= v < f (j + 1).
Proof.
  intros f v n. induction n as [|n IH]; intros [H1 H2].
  - cbn in *. lia.
  - destruct (Z_lt_le_dec v (f (Z.of_nat n))).
    + destruct IH as (j & Hj & Hf); [lia|]. exists j. lia.
    + exists (Z.of_nat n). rewrite Nat2Z.inj_succ in H2.
      replace (Z.succ (Z.of_nat n)) with (Z.of_nat n + 1) in H2 by lia. lia.
Qed.

Lemma kpre_interval_unique : forall ls j j', Forall (fun l => 1 <= l <= MAXBITS) ls ->
  0 <= j < Zlength ls -> 0 <= j' < Zlength ls ->
  kpre ls j' <= kpre ls j < kpre ls (j' + 1) -> j = j'.
Proof.
  intros ls j j' Hr Hj Hj' H.
  destruct (Z.lt_trichotomy j j') as [Hl|[Hl|Hl]]; auto; exfalso.
  - pose proof (kpre_mono ls (j + 1) j' ltac:(lia) ltac:(lia)).
    pose proof (kpre_S ls j ltac:(lia)). pose proof (pow2_pos (MAXBITS - Znth j ls)).
    pose proof (ls_range ls Hr j Hj). unfold MAXBITS in *. specialize (H2 ltac:(lia)). lia.
  - pose proof (kpre_mono ls (j' + 1) j ltac:(lia) ltac:(lia)). lia.
Qed.

Section Cover.
Variable ls : list Z.
Context (Hrange : Forall (fun l => 1 <= l <= MAXBITS) ls).
Context (Hsorted : forall a b, 0 <= a -> a <= b < Zlength ls -> Znth a ls <= Znth b ls).
Context (Hfull : ksum ls = 2 ^ MAXBITS).
Context (Hbits : bits_stmt).

(* P, a pattern of d bits (first bit = bit 0), starts with the code of exactly one sorted position j:
   the top m <= l_j bits of its Kraft prefix are the first m bits of P. *)
Lemma locate : forall d P, 0 <= d <= MAXBITS -> 0 <= P < 2 ^ d ->
  exists j, 0 <= j < Zlength ls /\
    forall m, 0 <= m <= d -> m <= Znth j ls ->
      kpre ls j / 2 ^ (MAXBITS - m) = reverse_bits (P mod 2 ^ m) m.
Proof.
  intros d P Hd HP. pose proof Hbits as (B1 & B2 & B3 & B4 & B5).
  set (R := reverse_bits P d). pose proof (B1 P d ltac:(lia)) as HR. fold R in HR.
  set (v := R * 2 ^ (MAXBITS - d)).
  assert (E15: 2 ^ MAXBITS = 2 ^ d * 2 ^ (MAXBITS - d)) by (rewrite <- pow2_split by lia; f_equal; lia).
  pose proof (pow2_pos (MAXBITS - d) ltac:(lia)). pose proof (Zlength_nonneg ls).
  destruct (find_interval (kpre ls) v (Z.to_nat (Zlength ls))) as (j & Hj & Hv).
  { rewrite kpre_0, Z2Nat.id by lia. rewrite kpre_full, Hfull. unfold v. nia. }
  rewrite Z2Nat.id in Hj by lia. exists j. split; [lia|]. intros m Hm Hml.
  set (l := Znth j ls) in *. pose proof (ls_range ls Hrange j Hj) as Hl. fold l in Hl.
  assert (Hdv: kpre ls j mod 2 ^ (MAXBITS - l) = 0) by (apply kpre_div_self; auto).
  pose proof (pow2_pos (MAXBITS - l) ltac:(lia)).
  set (C := kpre ls j / 2 ^ (MAXBITS - l)).
  assert (HK: kpre ls j = C * 2 ^ (MAXBITS - l)).
  { pose proof (Z.div_mod (kpre ls j) (2 ^ (MAXBITS - l)) ltac:(lia)). unfold C. lia. }
  assert (HS: kpre ls (j + 1) = (C + 1) * 2 ^ (MAXBITS - l)) by (rewrite kpre_S by lia; fold l; lia).
  assert (Hvc: v / 2 ^ (MAXBITS - l) = C).
  { symmetry. apply Z.div_unique_pos with (v - C * 2 ^ (MAXBITS - l)); lia. }
  rewrite <- (rev_top Hbits P d m) by lia. fold R.
  assert (E1: 2 ^ (MAXBITS - m) = 2 ^ (MAXBITS - l) * 2 ^ (l - m))
    by (rewrite <- pow2_split by lia; f_equal; lia).
  assert (E2: 2 ^ (MAXBITS - m) = 2 ^ (MAXBITS - d) * 2 ^ (d - m))
    by (rewrite <- pow2_split by lia; f_equal; lia).
  pose proof (pow2_pos (l - m) ltac:(lia)). pose proof (pow2_pos (d - m) ltac:(lia)).
  transitivity (v / 2 ^ (MAXBITS - m)).
  - rewrite E1, <- !Z.div_div by lia. fold C. rewrite Hvc. reflexivity.
  - unfold v. rewrite E2, <- Z.div_div by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.

End Cover.

Lemma islink_small : forall kind o, 1 <= o <= 15 -> islink kind o = true.
Proof.
  intros kind o Ho. unfold islink.
  assert (Z.land o 240 = 0).
  { assert (o = 1 \/ o = 2 \/ o = 3 \/ o = 4 \/ o = 5 \/ o = 6 \/ o = 7 \/ o = 8 \/
            o = 9 \/ o = 10 \/ o = 11 \/ o = 12 \/ o = 13 \/ o = 14 \/ o = 15) by lia.
    repeat destruct H as [H|H]; subst; reflexivity. }
  rewrite H. replace (o =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  destruct (kind =? DISTS); reflexivity.
Qed.

Lemma split_idx : forall i k root l, 0 <= root < l -> 0 <= i < 2 ^ root -> 0 <= k ->
  Z.shiftr ((i + k * 2 ^ root) mod 2 ^ l) root + ((i + k * 2 ^ root) / 2 ^ l) * 2 ^ (l - root) = k.
Proof.
  intros i k root l Hr Hi Hk. rewrite Z.shiftr_div_pow2 by lia.
  set (x := i + k * 2 ^ root).
  pose proof (pow2_pos root ltac:(lia)). pose proof (pow2_pos (l - root) ltac:(lia)).
  assert (Hx: x / 2 ^ root = k).
  { unfold x. rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
  assert (E: 2 ^ l = 2 ^ (l - root) * 2 ^ root) by (rewrite <- pow2_split by lia; f_equal; lia).
  assert (Ex: x = x mod 2 ^ l + ((x / 2 ^ l) * 2 ^ (l - root)) * 2 ^ root).
  { pose proof (Z.div_mod x (2 ^ l) ltac:(lia)). rewrite E in H1 at 1. lia. }
  rewrite <- Hx. rewrite <- Z.div_add by lia. f_equal. symmetry. exact Ex.
Qed.

(* The final table of the model's loop (decode_defs.v dfinal) is a valid table within `used`. *)
Lemma cover_final : forall type W ls root used t,
  Forall (fun l => 1 <= l <= MAXBITS) ls ->
  (forall a b, 0 <= a -> a <= b < Zlength ls -> Znth a ls <= Znth b ls) ->
  0 < Zlength ls -> 1 <= root <= MAXBITS -> ksum ls <= 2 ^ MAXBITS -> bits_stmt ->
  (forall j b, 0 <= j < Zlength ls ->
     islink type (e_op (sym_entry type (Znth j W) b)) = false /\
     final_ok type (sym_entry type (Znth j W) b) /\ e_bits (sym_entry type (Znth j W) b) = b) ->
  dfinal type W ls root used t -> used <= Zlength t -> Forall entry_ok t ->
  tab_ok type t root used.
Proof.
  intros type W ls root used t Hr Hs HN Hroot Hk Hbits Hsym Hf Hut Hok.
  destruct Hf as (Hfl & Hu1 & Hu2 & Hinc).
  assert (Hent: forall i, 0 <= i < used -> entry_ok (Znth i t)).
  { intros. rewrite Forall_forall in Hok. apply Hok. apply Znth_In. lia. }
  pose proof Hbits as (B1 & B2 & B3 & B4 & B5).
  unfold tab_ok. constructor; [unfold MAXBITS in *; lia | lia |].
  intros i Hi. cbv beta zeta.
  pose proof (pow2_pos root ltac:(lia)).
  split; [apply Hent; lia|].
  destruct (Z_lt_le_dec (ksum ls) (2 ^ MAXBITS)) as [Hlt|Hge].
  - (* incomplete: one code of length 1 *)
    destruct (Hinc Hlt) as (HN1 & H01 & Er & Eu & Ht1). subst root used.
    change (2 ^ 1) with 2 in Hi.
    assert (i = 0 \/ i = 1) as [-> | ->] by lia.
    + destruct (Hfl 0 ltac:(lia)) as [[F _] _].
      specialize (F ltac:(lia) 0 ltac:(rewrite H01; simpl; lia)).
      assert (Hdh: dhuff ls 0 = 0) by (unfold dhuff, dcode; rewrite kpre_0, Zdiv_0_l; apply reverse_bits_0).
      rewrite Hdh, H01 in F. change (0 + 0 * 2 ^ 1) with 0 in F. rewrite F.
      destruct (Hsym 0 1 ltac:(lia)) as (S1 & S2 & S3). rewrite S1. split; [lia|auto].
    + rewrite Ht1. unfold invalid_entry. cbn [e_op e_bits e_val].
      replace (islink type 64) with false by (unfold islink; cbn; destruct (type =? DISTS); reflexivity).
      split; [lia|]. unfold final_ok; cbn [e_op e_val].
      destruct (type =? CODES); [right; reflexivity|].
      destruct (type =? LENS); [right; right; right|right]; split; cbn; (discriminate || reflexivity).
  - assert (Hfull: ksum ls = 2 ^ MAXBITS) by lia.
    destruct (locate ls Hr Hs Hfull Hbits root i ltac:(lia) Hi) as (j & Hj & Hm).
    set (l := Znth j ls) in *. pose proof (ls_range ls Hr j Hj) as Hl. fold l in Hl.
    destruct (Hfl j Hj) as [[Fs Fl] Lk]. fold l in Fs, Fl, Lk.
    destruct (Z_le_gt_dec l root) as [Hshort|Hlong].
    + (* a short code: its entry, replicated *)
      pose proof (pow2_pos l ltac:(lia)).
      assert (Hdh: dhuff ls j = i mod 2 ^ l).
      { unfold dhuff, dcode. fold l. rewrite (Hm l) by lia. apply B3; [lia|]. apply Z.mod_pos_bound; lia. }
      assert (Hk': 0 <= i / 2 ^ l < 2 ^ (root - l)).
      { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
        rewrite <- Z.pow_add_r by lia. replace (l + (root - l)) with root by lia. lia. }
      specialize (Fs Hshort (i / 2 ^ l) Hk'). rewrite Hdh in Fs.
      replace (i mod 2 ^ l + i / 2 ^ l * 2 ^ l) with i in Fs
        by (pose proof (Z.div_mod i (2 ^ l) ltac:(lia)); lia).
      rewrite Fs. destruct (Hsym j l Hj) as (S1 & S2 & S3). rewrite S1. split; [lia|auto].
    + (* a long code: the link to its sub-table *)
      set (q := pfx ls root j) in *.
      assert (Hq: q = reverse_bits i root).
      { unfold q, pfx. rewrite (Hm root) by lia. rewrite Z.mod_small by lia. reflexivity. }
      assert (Hrq: reverse_bits q root = i) by (rewrite Hq; apply B3; lia).
      unfold link_done in Lk. fold l q in Lk. specialize (Lk ltac:(lia)). rewrite Hrq in Lk. rewrite Lk.
      destruct (gmax_props ls root q) as (G1 & G2 & G3).
      set (g := gmax ls root q) in *.
      assert (Hlg: l <= g) by (apply G2; auto; lia).
      assert (Hg: g <= MAXBITS).
      { destruct G3 as [G3|(j0 & Hj0 & _ & _ & G3)]; [lia|].
        rewrite G3. apply (ls_range ls Hr j0 Hj0). }
      unfold dlink. fold q g. cbn [e_op e_bits e_val].
      rewrite islink_small by (unfold MAXBITS in *; lia).
      unfold sub_ok. cbn [e_op e_bits e_val].
      split; [reflexivity|]. split; [lia|]. split; [unfold MAXBITS in *; lia|].
      intros k Hkk. cbv beta zeta.
      pose proof (pow2_pos (g - root) ltac:(lia)).
      set (P := i + k * 2 ^ root).
      assert (HP: 0 <= P < 2 ^ g).
      { unfold P. replace g with ((g - root) + root) by lia. rewrite pow2_split by lia. nia. }
      destruct (locate ls Hr Hs Hfull Hbits g P ltac:(lia) HP) as (j' & Hj' & Hm').
      set (l' := Znth j' ls) in *. pose proof (ls_range ls Hr j' Hj') as Hl'. fold l' in Hl'.
      assert (HPm: forall m, 0 <= m <= root -> P mod 2 ^ m = i mod 2 ^ m).
      { intros m Hm0. unfold P. replace (2 ^ root) with (2 ^ (root - m) * 2 ^ m)
          by (rewrite <- pow2_split by lia; f_equal; lia).
        rewrite Z.mul_assoc, Z.mod_add by (pose proof (pow2_pos m ltac:(lia)); lia). reflexivity. }
      assert (Hlong': root < l').
      { destruct (Z_lt_le_dec root l') as [|Hle]; [auto|exfalso].
        assert (E: kpre ls j' / 2 ^ (MAXBITS - l') = kpre ls j / 2 ^ (MAXBITS - l')).
        { rewrite (Hm' l') by lia. rewrite (Hm l') by lia. rewrite HPm by lia. reflexivity. }
        assert (Ejj: j = j').
        { apply (kpre_interval_unique ls j j' Hr Hj Hj').
          pose proof (kpre_div_self ls Hr Hs j' Hj') as K1. fold l' in K1.
          pose proof (kpre_S ls j' Hj') as K2. fold l' in K2.
          pose proof (pow2_pos (MAXBITS - l') ltac:(lia)).
          pose proof (Z.div_mod (kpre ls j') (2 ^ (MAXBITS - l')) ltac:(lia)).
          pose proof (Z.div_mod (kpre ls j) (2 ^ (MAXBITS - l')) ltac:(lia)).
          pose proof (Z.mod_pos_bound (kpre ls j) (2 ^ (MAXBITS - l')) ltac:(lia)).
          rewrite E in *. lia. }
        subst j'. unfold l' in Hle. fold l in Hle. lia. }
      assert (Hpq: pfx ls root j' = q).
      { unfold pfx. rewrite (Hm' root) by lia. rewrite HPm by lia. rewrite Z.mod_small by lia.
        symmetry; exact Hq. }
      assert (Hl'g: l' <= g) by (apply G2; auto).
      pose proof (pow2_pos l' ltac:(lia)).
      assert (Hdh': dhuff ls j' = P mod 2 ^ l').
      { unfold dhuff, dcode. fold l'. rewrite (Hm' l') by lia. apply B3; [lia|]. apply Z.mod_pos_bound; lia. }
      destruct (Hfl j' Hj') as [[_ Fl'] _]. fold l' in Fl'. rewrite Hpq in Fl'. fold g in Fl'.
      assert (Hx: 0 <= P / 2 ^ l' < 2 ^ (g - l')).
      { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
        rewrite <- Z.pow_add_r by lia. replace (l' + (g - l')) with g by lia. lia. }
      specialize (Fl' Hlong' (P / 2 ^ l') Hx). rewrite Hdh' in Fl'.
      assert (Hidx: Z.shiftr (P mod 2 ^ l') root + P / 2 ^ l' * 2 ^ (l' - root) = k)
        by (unfold P; apply split_idx; lia).
      rewrite <- Z.add_assoc, Hidx in Fl'. rewrite Fl'.
      destruct (Hsym j' (l' - root) Hj') as (S1 & S2 & S3).
      assert (Hdn: 0 <= dnxt ls root q).
      { unfold dnxt. pose proof (sumq_nonneg ls root q ltac:(rewrite Hq; apply B1; lia)). lia. }
      pose proof (Hu2 j Hj ltac:(fold l; lia)) as Hu. fold q g in Hu.
      split; [lia|]. split; [rewrite <- Fl'; apply Hent; lia|]. split; [auto|]. split; [rewrite S3; unfold MAXBITS in *; lia|auto].
Qed.

Definition cover2_stmt : Prop :=
  forall type lens req old root used t,
    inputs_ok type lens req -> (type = CODES -> Zlength lens <= 19) ->
    cap_ok type lens req (Zlength old) -> Forall entry_ok old ->
    inflate_table_model type lens req old = ROk root used t ->
    tab_ok type t root used /\ used <= Zlength old.

Lemma invalid_final : forall type b,
  islink type (e_op (invalid_entry b)) = false /\ final_ok type (invalid_entry b).
Proof.
  intros. unfold invalid_entry. cbn [e_op e_val].
  split; [unfold islink; cbn; destruct (type =? DISTS); reflexivity|].
  unfold final_ok; cbn [e_op e_val].
  destruct (type =? CODES); [right; reflexivity|].
  destruct (type =? LENS); [right; right; right|right]; split; cbn; (discriminate || reflexivity).
Qed.

Lemma cover2_proof : cover2_stmt.
Proof.
  intros type lens req old root used t Hin H19 Hcap Hold Hmodel.
  pose proof part_sorted.sorted_ok2 as Hsorted.
  pose proof part_rfc.rfc_ok2 as Hrfc.
  pose proof part_bits.bits_ok2 as Hbits.
  pose proof part_subbits.subbits_ok2 as Hsub.
  pose proof (part_size.size_ok2 Hsorted Hrfc Hbits) as Hsize.
  pose proof (fact_result_ok Hsorted Hrfc Hbits Hsub Hsize type lens req old Hin Hcap Hold) as FR.
  destruct (expected_call type lens req) as [[want r] sz].
  rewrite Hmodel in FR.
  destruct FR as (_ & _ & _ & Hu & _ & Htl & Htok & _).
  split; [|lia].
  pose proof Hin as (Ht & Hcodes & Hl & Hreq).
  unfold inflate_table_model in Hmodel.
  destruct (maxlen lens =? 0) eqn:Emx.
  - (* no symbol: two invalid entries *)
    inversion Hmodel; subst root used t; clear Hmodel.
    unfold tab_ok. constructor; [lia | cbn; lia |].
    intros i Hi. cbv beta zeta. change (2 ^ 1) with 2 in Hi.
    assert (Hfin: Znth i (upd_Znth 1 (upd_Znth 0 old (invalid_entry 1)) (invalid_entry 1)) = invalid_entry 1).
    { assert (i = 0 \/ i = 1) as [-> | ->] by lia.
      - rewrite upd_Znth_diff by (rewrite ?upd_Znth_Zlength; lia). rewrite upd_Znth_same by lia. reflexivity.
      - rewrite upd_Znth_same by (rewrite ?upd_Znth_Zlength; lia). reflexivity. }
    rewrite Hfin. destruct (invalid_final type 1) as [I1 I2]. rewrite I1.
    split; [unfold invalid_entry, entry_ok; cbn; lia|]. split; [cbn; lia|auto].
  - apply Z.eqb_neq in Emx.
    destruct (left_final (counts lens)) as [lft|] eqn:Eleft; [|discriminate].
    destruct ((0 <? lft) && ((type =? CODES) || negb (maxlen lens =? 1))) eqn:Etest; [discriminate|].
    destruct (over type (Z.shiftl 1 (root_of req lens))) eqn:Eover; [discriminate|].
    assert (Hd: dhyps type lens (sorted_syms lens) (sl lens) (root_of req lens) old)
      by (eapply dsetup_ok; eauto).
    assert (Hfin: exists s, used = s_used s /\ t = finish s /\ root = root_of req lens /\
      (run type lens (sorted_syms lens) (root_of req lens) (maxlen lens) (length (sorted_syms lens))
         (init_state lens (root_of req lens) old) = Break s \/
       run type lens (sorted_syms lens) (root_of req lens) (maxlen lens) (length (sorted_syms lens))
         (init_state lens (root_of req lens) old) = Continue s)).
    { destruct (run type lens (sorted_syms lens) (root_of req lens) (maxlen lens) (length (sorted_syms lens))
                  (init_state lens (root_of req lens) old)) eqn:Er;
        inversion Hmodel; subst; eexists; eauto. }
    destruct Hfin as (s & -> & -> & -> & Hrun).
    destruct dstep_last_ok as [Hstep Hlast].
    pose proof (drun_ok type lens req old s Hsorted Hbits Hsub Hstep Hlast Hl Emx Hd Hrun) as Hf.
    destruct Hd as (Hrange & Hsl & HN & HWls & HWr & Hroot & Hk & _).
    destruct (Hsorted lens Hl) as (SW & _).
    assert (HWl: Zlength (sl lens) = Zlength (sorted_syms lens)) by (unfold sl; apply Zlength_map).
    apply (cover_final type (sorted_syms lens) (sl lens) (root_of req lens) (s_used s) (finish s)); auto.
    + pose proof (ls_range _ Hrange 0 ltac:(lia)). pose proof (ls_range _ Hrange (Zlength (sl lens) - 1) ltac:(lia)).
      lia.
    + intros j b Hj. rewrite Forall_forall in SW.
      pose proof (SW _ (Znth_In j (sorted_syms lens) ltac:(lia))) as Hs.
      apply sym_ok; auto; lia.
    + lia.
Qed.
