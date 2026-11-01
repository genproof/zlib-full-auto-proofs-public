(* Part: fact_result (facts.v) from the parts of fact_result.v; reuse its Qed lemmas (classify_ok, Section Loop: inv, step_inv, new_table, ...) by Require. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.inftrees.facts.
Require Import Zlib.proof.inftrees.fact_result.
Import ListNotations.
Local Open Scope Z_scope.

(* A step that continues either keeps `used` or has just checked it against ENOUGH. *)
Lemma step_used : forall type lens W root mx s s',
  step type lens W root mx s = Continue s' -> s_used s' = s_used s \/ over type (s_used s') = false.
Proof.
  intros. unfold step in H. cbv zeta in H.
  repeat match type of H with context [if ?b then _ else _] =>
    let E := fresh "E" in destruct b eqn:E end;
  inversion H; subst; cbn [s_used]; auto.
Qed.

Section Final.
Context (type: Z) (lens W ls: list Z) (root: Z) (old: list entry).
Context (Hrange : Forall (fun l => 1 <= l <= MAXBITS) ls).
Context (Hsorted : forall a b, 0 <= a -> a <= b < Zlength ls -> Znth a ls <= Znth b ls).
Context (HN : 0 < Zlength ls).
Context (HWls : forall i, 0 <= i < Zlength ls -> Znth (Znth i W) lens = Znth i ls).
Context (HWr : Forall (fun s => 0 <= s <= 65535) W).
Context (Hroot : Znth 0 ls <= root <= Znth (Zlength ls - 1) ls).
Context (Hk : ksum ls <= 2 ^ MAXBITS).
Context (Hinc : ksum ls < 2 ^ MAXBITS -> Znth (Zlength ls - 1) ls <= root).
Context (Htype : 0 <= type <= 2).
Context (Hcodes : type = CODES -> Znth (Zlength ls - 1) ls <= root).
Context (Hcap : (type = LENS -> ENOUGH_LENS <= Zlength old) /\ (type = DISTS -> ENOUGH_DISTS <= Zlength old)).
Context (Hcap0 : 2 ^ root <= Zlength old).
Context (Hold : Forall entry_ok old).
Context (Hbits : bits_stmt).
Context (Hsub : subbits_stmt).

Definition fin_ok (s': state) : Prop :=
  s_used s' = total ls root /\
  Zlength (finish s') = Zlength old /\ Forall entry_ok (finish s') /\
  (forall j, s_used s' <= j -> Znth j (finish s') = Znth j old) /\ s_used s' <= Zlength old.

Lemma last_step : forall s, inv ls root old (Zlength ls - 1) s ->
  exists s', step type lens W root (Znth (Zlength ls - 1) ls) s = Break s' /\ fin_ok s'.
Proof.
  intros s Hinv.
  destruct s as [huff sym len curr drop low used next cnt tab].
  destruct Hinv as (Hi & Hsym & Hlen & Hhuff & Hcl & Hcnt & Hlow & Hhigh & Htl & Htok & Htfr & Hucap).
  cbn [s_huff s_sym s_len s_curr s_drop s_low s_used s_next s_cnt s_tab] in *.
  subst sym len huff.
  assert (HM: MAXBITS = 15) by reflexivity.
  set (i := Zlength ls - 1) in *.
  pose proof (l_range ls Hrange i Hi) as Hl.
  pose proof (root_range ls root Hrange HN Hroot) as Hr.
  destruct (C_facts type ls root Hrange Hsorted HN Hk Htype i Hi) as (HC0 & HK & HS & HC1 & _).
  pose proof Hbits as Hbits'. destruct Hbits' as (B1 & B2 & B3 & B4 & B5).
  set (l := Znth i ls) in *. set (C := kpre ls i / 2 ^ (MAXBITS - l)) in *.
  assert (Hc: Znth l cnt - 1 = 0).
  { rewrite Hcnt by lia. rewrite count_len_sublist_cons by lia. fold l. rewrite Z.eqb_refl.
    rewrite sublist_nil' by lia. reflexivity. }
  assert (Hdc : 0 <= drop <= l /\ l - drop <= curr /\ 0 <= next /\ used = next + 2 ^ curr /\ 0 <= curr).
  { destruct (Z_le_gt_dec l root) as [L|L].
    - destruct (Hlow L) as (-> & -> & -> & -> & _). lia.
    - destruct (Hhigh ltac:(lia)) as (-> & _ & -> & -> & ->).
      pose proof (gmax_long ls root Hrange i Hi ltac:(lia)).
      pose proof (pfx_range ls root Hrange HN Hroot Hk i Hi).
      pose proof (sumq_nonneg ls root (pfx ls root i)).
      assert (0 < 2 ^ root) by (apply Z.pow_pos_nonneg; lia). fold l in H. lia. }
  destruct Hdc as (Hd & Hdc & Hnx & Hu & Hcu).
  assert (Hhere: entry_ok (sym_entry type (Znth i W) (l - drop))).
  { apply sym_entry_ok; [|lia]. apply (@Znth_Forall_def Z 0 (fun s => 0 <= s <= 65535)); auto. lia. }
  assert (Hcnt0: 0 <= Z.shiftl 1 curr / Z.shiftl 1 (l - drop)).
  { rewrite !pow2_shiftl by lia. apply Z.div_pos; [apply Z.pow_nonneg | apply Z.pow_pos_nonneg]; lia. }
  destruct (rep_fill_props (Z.to_nat (Z.shiftl 1 curr / Z.shiftl 1 (l - drop))) tab
             (next + Z.shiftr (reverse_bits C l) drop) (Z.shiftl 1 (l - drop))
             (sym_entry type (Znth i W) (l - drop)) used) as (T1 & T2 & T3); auto.
  { intros k Hkk. rewrite Z2Nat.id in Hkk by lia. rewrite Hu.
    apply fill_bounds; auto; try lia. apply B1. lia. }
  set (t1 := rep_fill tab (next + Z.shiftr (reverse_bits C l) drop) (Z.shiftl 1 (l - drop))
               (Z.to_nat (Z.shiftl 1 curr / Z.shiftl 1 (l - drop))) (sym_entry type (Znth i W) (l - drop))) in *.
  unfold step. cbn [s_huff s_sym s_len s_curr s_drop s_low s_used s_next s_cnt s_tab].
  fold t1. rewrite Hc, !Z.eqb_refl. cbn [andb].
  eexists. split; [reflexivity|].
  unfold fin_ok, finish. cbn [s_huff s_sym s_len s_curr s_drop s_low s_used s_next s_cnt s_tab].
  (* the next code after the last one *)
  assert (Hh: next_huff (reverse_bits C l) l = reverse_bits ((C + 1) mod 2 ^ l) l) by (apply B5; lia).
  rewrite Hh. set (h := reverse_bits ((C + 1) mod 2 ^ l) l).
  assert (Hh2: h = 0 \/ (drop = 0 /\ next = 0 /\ used = 2 ^ root /\ 0 <= h < 2 ^ root)).
  { destruct (Z_le_gt_dec l root) as [L|L].
    - right. destruct (Hlow L) as (-> & -> & -> & -> & _). split; [auto|]. split; [auto|]. split; [auto|].
      pose proof (B1 ((C + 1) mod 2 ^ l) l ltac:(lia)). fold h in H.
      assert (2 ^ l <= 2 ^ root) by (apply Z.pow_le_mono_r; lia). lia.
    - left. pose proof (complete_of_long ls root Hsorted Hk Hinc i Hi ltac:(lia)) as Hcomp.
      rewrite <- kpre_full in Hcomp. replace (Zlength ls) with (i + 1) in Hcomp by lia.
      rewrite HS in Hcomp.
      assert (H2: 2 ^ MAXBITS = 2 ^ l * 2 ^ (MAXBITS - l)) by (rewrite <- (pow_split 0) by lia; f_equal; lia).
      assert (0 < 2 ^ (MAXBITS - l)) by (apply Z.pow_pos_nonneg; lia).
      assert (C + 1 = 2 ^ l) by nia.
      subst h. rewrite H0, Z.mod_same by (apply Z.pow_nonzero; lia). apply reverse_bits_0. }
  split.
  - (* used = total *)
    unfold total. destruct (Z_le_gt_dec l root) as [L|L].
    + destruct (Hlow L) as (_ & _ & _ & -> & _).
      rewrite (sumq_zero ls root 0 (2 ^ root)); [change (sumq ls root 0) with 0; lia| |].
      * pose proof (Z.pow_pos_nonneg 2 root ltac:(lia) ltac:(lia)). lia.
      * intros. apply (fq_after ls root Hrange Hsorted HN Hroot i q); auto; lia.
    + destruct (Hhigh ltac:(lia)) as (_ & _ & Ec & En & Eu). rewrite Eu, En, Ec.
      pose proof (pfx_range ls root Hrange HN Hroot Hk i Hi).
      rewrite (sumq_zero ls root (pfx ls root i + 1) (2 ^ root)); [|lia|].
      * rewrite sumq_succ by lia. rewrite (fq_long ls root Hrange HN Hroot i Hi ltac:(lia)). lia.
      * intros. apply (fq_after ls root Hrange Hsorted HN Hroot i q); auto; lia.
  - destruct (h =? 0) eqn:E0.
    + split; [lia|]. split; [auto|]. split; [|lia]. intros. rewrite T3 by lia. apply Htfr. lia.
    + apply Z.eqb_neq in E0. destruct Hh2 as [Hh2|(-> & -> & -> & Hh2)]; [congruence|].
      split; [rewrite (upd_len 0); lia|]. split.
      * apply Forall_upd_Znth; auto. unfold entry_ok, invalid_entry; cbn [e_op e_bits e_val]. lia.
      * split; [|lia]. intros. rewrite (upd_frame 0) by lia. rewrite T3 by lia. apply Htfr. lia.
Qed.

Lemma run_final : forall k i s, inv ls root old i s -> i + Z.of_nat k = Zlength ls ->
  over type (s_used s) = false ->
  (exists s', run type lens W root (Znth (Zlength ls - 1) ls) k s = Break s' /\ fin_ok s' /\
              over type (s_used s') = false) \/
  (exists s', run type lens W root (Znth (Zlength ls - 1) ls) k s = Full s' /\
     over type (s_used s') = true /\ s_used s' <= total ls root /\
     Zlength (s_tab s') = Zlength old /\ Forall entry_ok (s_tab s')).
Proof.
  induction k as [|k IH]; intros i s Hinv Hik Hov.
  - exfalso. destruct Hinv as (Hi & _). lia.
  - cbn [run]. destruct (Z.eq_dec (i + 1) (Zlength ls)) as [Ei|Ei].
    + replace i with (Zlength ls - 1) in Hinv by lia.
      destruct (last_step s Hinv) as (s' & Hs & Hf). rewrite Hs. left. exists s'.
      split; [auto|]. split; [auto|].
      unfold step in Hs. cbv zeta in Hs.
      destruct (_ && _) in Hs; [inversion Hs; subst; cbn [s_used]; auto|].
      repeat match type of Hs with context [if ?b then _ else _] =>
        let E := fresh "E" in destruct b eqn:E end; discriminate.
    + destruct Hinv as (Hi & Hrest).
      destruct (step_inv type lens W ls root old Hrange Hsorted HN HWls HWr Hroot Hk Hinc Htype Hcodes
                  Hcap Hbits Hsub i s (conj Hi Hrest) ltac:(lia))
        as [(s' & Hs & Hinv')|(s' & Hs & H1 & H2 & H3 & H4)].
      * rewrite Hs. apply (IH (i + 1)); auto; [lia|].
        destruct (step_used _ _ _ _ _ _ _ Hs) as [->|]; auto.
      * rewrite Hs. right. exists s'. auto.
Qed.

End Final.

Lemma left_loop_nonneg : forall k len left cnt x, 0 <= left -> left_loop k len left cnt = Some x -> 0 <= x.
Proof.
  induction k; intros len left cnt x H H0; cbn [left_loop] in H0.
  - inversion H0; lia.
  - destruct (2 * left - Znth len cnt <? 0) eqn:E; [discriminate|]. apply Z.ltb_ge in E.
    eapply IHk; [|exact H0]. lia.
Qed.

Lemma over_mono : forall type a b, a <= b -> over type a = true -> over type b = true.
Proof.
  intros. unfold over in *. rewrite orb_true_iff, !andb_true_iff, !Z.ltb_lt in *.
  destruct H0 as [[? ?]|[? ?]]; [left|right]; split; auto; lia.
Qed.

Lemma want_over : forall type size,
  (if (type =? LENS) && (ENOUGH_LENS <? size) then 1
   else if (type =? DISTS) && (ENOUGH_DISTS <? size) then 1 else 0)
  = if over type size then 1 else 0.
Proof.
  intros. unfold over. destruct ((type =? LENS) && _); destruct ((type =? DISTS) && _); reflexivity.
Qed.

Lemma fact_result_ok : sorted_stmt -> rfc_stmt -> bits_stmt -> subbits_stmt -> size_stmt -> fact_result.
Proof.
  intros Hso Hrfc Hbits Hsub Hsize type lens req old Hin Hcap Hold.
  destruct Hin as (Ht & Hn & Hlr & Hreq).
  destruct (classify_ok lens Hlr) as (Cmax & Cmin & Cleft).
  destruct (Hso lens Hlr) as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9).
  destruct Hcap as (HcC & HcL & HcD).
  assert (Hcap2: 2 <= Zlength old).
  { assert (type = 0 \/ type = 1 \/ type = 2) as [E|[E|E]] by lia;
     [destruct (HcC E) as (_ & ? & _) | specialize (HcL E) | specialize (HcD E)];
     unfold ENOUGH_LENS, ENOUGH_DISTS in *; lia. }
  assert (HK15: 2 ^ MAXBITS = 32768) by reflexivity.
  assert (HGP: GP_KRAFT_ONE = 32768) by reflexivity.
  unfold expected_call. cbv beta zeta iota.
  rewrite want_over.
  unfold inflate_table_model. cbv beta zeta.
  destruct (maxlen lens =? 0) eqn:Emx.
  - (* no symbol *)
    apply Z.eqb_eq in Emx.
    assert (HV: expected_valid type lens = 0) by (unfold expected_valid; rewrite <- Cmax, Emx; reflexivity).
    assert (HR: expected_root req lens = 1) by (unfold expected_root; rewrite <- Cmax, Emx; reflexivity).
    rewrite HV, HR.
    assert (Hsl: sl lens = []) by (apply S8; auto).
    assert (Hkr: kraft lens = 0) by (rewrite <- S7, Hsl; reflexivity).
    rewrite Hsize by (auto; try lia; unfold MAXBITS; lia).
    rewrite Hsl. change (2 ^ 1 + sumf [] 1 (Z.to_nat (2 ^ 1))) with 2.
    replace (over type 2) with false
      by (unfold over; destruct (type =? LENS), (type =? DISTS); reflexivity).
    cbn [negb Z.eqb].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
    split; [intros; reflexivity|].
    split; [rewrite !(upd_len 0); reflexivity|]. split.
    + repeat apply Forall_upd_Znth; auto; unfold entry_ok, invalid_entry; cbn [e_op e_bits e_val]; lia.
    + intros. rewrite !(upd_frame 0) by lia. reflexivity.
  - apply Z.eqb_neq in Emx.
    set (root := root_of req lens).
    assert (HR: expected_root req lens = root).
    { unfold expected_root, root, root_of. rewrite <- Cmax, <- (Cmin Emx).
      replace (maxlen lens =? 0) with false by (symmetry; apply Z.eqb_neq; auto).
      destruct (maxlen lens <? req) eqn:E1; [apply Z.ltb_lt in E1 | apply Z.ltb_ge in E1]; bdestr; lia. }
    set (ls := sl lens) in *. set (W := sorted_syms lens) in *.
    assert (HN: 0 < Zlength ls).
    { destruct ls eqn:E; [exfalso; apply Emx; apply S8; auto|]. rewrite Zlength_cons. pose proof (Zlength_nonneg l). lia. }
    destruct (S9 ltac:(intro E; rewrite E in HN; cbn in HN; lia)) as (Hmin & Hmax).
    assert (Hmm: Znth 0 ls <= Znth (Zlength ls - 1) ls) by (apply S3; lia).
    assert (H1l: 1 <= Znth 0 ls).
    { eapply Forall_forall in S2; [exact (proj1 S2)|]. apply Znth_In. lia. }
    assert (Hroot: Znth 0 ls <= root <= Znth (Zlength ls - 1) ls).
    { unfold root, root_of. rewrite Hmin, Hmax. rewrite Hmin, Hmax in Hmm. lia. }
    assert (Hrr: 1 <= root <= MAXBITS).
    { split; [lia|]. eapply Z.le_trans; [apply Hroot|].
      eapply Forall_forall in S2; [exact (proj2 S2)|]. apply Znth_In. lia. }
    assert (HmxW: maxlen lens = Znth (Zlength ls - 1) ls) by auto.
    destruct (left_final (counts lens)) as [lft|] eqn:Elf.
    2: { (* over-subscribed *)
      assert (HV: expected_valid type lens = -1).
      { unfold expected_valid. rewrite <- Cmax, HGP. rewrite HK15 in Cleft.
        replace (maxlen lens =? 0) with false by (symmetry; apply Z.eqb_neq; auto).
        replace (32768 <? kraft lens) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
      rewrite HV. reflexivity. }
    assert (Hlft0: 0 <= lft) by (unfold left_final in Elf; eapply left_loop_nonneg; [|exact Elf]; lia).
    rewrite HK15 in Cleft.
    assert (Hk: ksum ls <= 2 ^ MAXBITS) by (rewrite S7, HK15; lia).
    destruct ((0 <? lft) && ((type =? CODES) || negb (maxlen lens =? 1))) eqn:Ebad.
    { (* incomplete and not allowed *)
      assert (HV: expected_valid type lens = -1).
      { unfold expected_valid. rewrite <- Cmax, HGP.
        apply andb_true_iff in Ebad. destruct Ebad as [Eb1 Eb2]. apply Z.ltb_lt in Eb1.
        replace (maxlen lens =? 0) with false by (symmetry; apply Z.eqb_neq; auto).
        replace (32768 <? kraft lens) with false by (symmetry; apply Z.ltb_ge; lia).
        replace (kraft lens <? 32768) with true by (symmetry; apply Z.ltb_lt; lia).
        rewrite Eb2. reflexivity. }
      rewrite HV. reflexivity. }
    assert (HV: expected_valid type lens = 0).
    { unfold expected_valid. rewrite <- Cmax, HGP.
      replace (maxlen lens =? 0) with false by (symmetry; apply Z.eqb_neq; auto).
      replace (32768 <? kraft lens) with false by (symmetry; apply Z.ltb_ge; lia).
      destruct (Z.eq_dec lft 0).
      - replace (kraft lens <? 32768) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
      - replace (0 <? lft) with true in Ebad by (symmetry; apply Z.ltb_lt; lia). cbn [andb] in Ebad.
        rewrite Ebad, andb_false_r. reflexivity. }
    assert (Hinc: ksum ls < 2 ^ MAXBITS -> Znth (Zlength ls - 1) ls <= root).
    { intros Hlt. rewrite <- HmxW.
      replace (0 <? lft) with true in Ebad by (symmetry; apply Z.ltb_lt; lia). cbn [andb] in Ebad.
      apply orb_false_iff in Ebad. destruct Ebad as [_ Eb]. apply negb_false_iff, Z.eqb_eq in Eb. lia. }
    rewrite HV, HR. cbn [negb Z.eqb].
    assert (HT: two_level_size lens root = total ls root).
    { rewrite Hsize by (auto; try (rewrite HK15; lia); lia). reflexivity. }
    rewrite HT.
    assert (Htot: 2 ^ root <= total ls root).
    { unfold total. pose proof (sumq_nonneg ls root (2 ^ root)). lia. }
    assert (Hcodes: type = CODES -> Znth (Zlength ls - 1) ls <= root).
    { intros E. destruct (HcC E) as (H1 & _). unfold root, root_of. lia. }
    rewrite (pow2_shiftl root) by lia.
    destruct (over type (2 ^ root)) eqn:Eo.
    { (* the root table alone is too big *)
      rewrite (over_mono type (2 ^ root) (total ls root)) by auto. auto. }
    assert (Hcap0: 2 ^ root <= Zlength old).
    { assert (type = 0 \/ type = 1 \/ type = 2) as [E|[E|E]] by lia.
      - destruct (HcC E) as (H1 & _ & H3). rewrite pow2_shiftl in H3 by lia.
        assert (root = maxlen lens) by (unfold root, root_of; lia). congruence.
      - specialize (HcL E). unfold over in Eo. rewrite E in Eo. cbn [Z.eqb andb orb LENS DISTS Pos.eqb] in Eo. rewrite ?orb_false_r in Eo.
        apply Z.ltb_ge in Eo. unfold ENOUGH_LENS in *. lia.
      - specialize (HcD E). unfold over in Eo. rewrite E in Eo. cbn [Z.eqb andb orb LENS DISTS Pos.eqb] in Eo. rewrite ?orb_false_r in Eo.
        apply Z.ltb_ge in Eo. unfold ENOUGH_DISTS in *. lia. }
    assert (HWls: forall i, 0 <= i < Zlength ls -> Znth (Znth i W) lens = Znth i ls).
    { intros. unfold ls, sl. fold W. rewrite Znth_map; auto. unfold ls, sl in H. rewrite Zlength_map in H. auto. }
    assert (HWr: Forall (fun s => 0 <= s <= 65535) W).
    { eapply Forall_impl; [|exact S1]. intros a Ha. cbn beta in Ha.
      unfold max_codes in Hn. destruct (type =? CODES), (type =? LENS); lia. }
    assert (Hinit: inv ls root old 0 (init_state lens root old)).
    { unfold inv, init_state. cbn [s_huff s_sym s_len s_curr s_drop s_low s_used s_next s_cnt s_tab].
      rewrite kpre_0, Z.div_0_l, reverse_bits_0 by (apply Z.pow_nonzero; lia).
      rewrite sublist_same by lia. rewrite (pow2_shiftl root) by lia.
      split; [lia|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|].
      split; [intros; apply S5; auto|].
      split; [intros; auto|]. split; [intros; lia|].
      split; [auto|]. split; [auto|]. split; [auto|]. auto. }
    assert (HLW: 0 + Z.of_nat (length W) = Zlength ls).
    { unfold ls, sl. fold W. rewrite Zlength_map, Zlength_correct. lia. }
    rewrite HmxW.
    destruct (run_final type lens W ls root old S2 S3 HN HWls HWr Hroot Hk Hinc Ht Hcodes
                (conj HcL HcD) Hcap0 Hbits Hsub (length W) 0 _ Hinit HLW ltac:(cbn [init_state s_used]; rewrite (pow2_shiftl root) by lia; exact Eo))
      as [(s' & Hrun & Hfin & Hov)|(s' & Hrun & H1 & H2 & H3 & H4)]; rewrite Hrun.
    + destruct Hfin as (F1 & F2 & F3 & F4 & F5). rewrite F1 in *. rewrite Hov.
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [pose proof (Z.pow_pos_nonneg 2 root ltac:(lia) ltac:(lia)); lia|].
      split; [|split; [auto|split; [auto|intros; apply F4; lia]]].
      intros E. specialize (Hcodes E). unfold total.
      rewrite (sumq_zero ls root 0 (2 ^ root)); [change (sumq ls root 0) with 0; rewrite (pow2_shiftl root) by lia; lia| |].
      * pose proof (Z.pow_pos_nonneg 2 root ltac:(lia) ltac:(lia)). lia.
      * intros. apply (fq_after ls root S2 S3 HN Hroot (Zlength ls - 1) q); try lia.
    + rewrite (over_mono type (s_used s') (total ls root)) by auto. auto.
Qed.