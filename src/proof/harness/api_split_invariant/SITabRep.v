(* inflate_table's tables (and the fixed tables) decide an entry by its code bits: every entry is replicated over the indices that agree with it on its bits (SIDefs.trep); the distance tables' distances are at most 32768. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_split_invariant.SIDefs.
Require Zlib.proof.inflate.Cover2 Zlib.proof.inflate.Cover3Len.
Require Import Zlib.proof.inftrees.facts Zlib.proof.inftrees.fact_result Zlib.proof.inftrees.decode_defs
  Zlib.proof.inftrees.decode_step Zlib.proof.inftrees.decode_run Zlib.proof.inftrees.part_decode
  Zlib.proof.inftrees.part_result.
Require Zlib.proof.inftrees.part_sorted Zlib.proof.inftrees.part_rfc Zlib.proof.inftrees.part_bits
  Zlib.proof.inftrees.part_subbits Zlib.proof.inftrees.part_size.
Import Zlib.proof.inftrees.model.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* Arithmetic                                                                                     *)

(* the low l bits of i + k 2^root, i < 2^root <= 2^l: i, then the low l - root bits of k *)
Lemma tr_mod_split : forall i k root l, 0 <= root <= l -> 0 <= i < 2 ^ root -> 0 <= k ->
  (i + k * 2 ^ root) mod 2 ^ l = i + (k mod 2 ^ (l - root)) * 2 ^ root.
Proof.
  intros i k root l Hl Hi Hk.
  assert (E: 2 ^ l = 2 ^ (l - root) * 2 ^ root) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  pose proof (Cover2.pow2_pos (l - root) ltac:(lia)). pose proof (Cover2.pow2_pos root ltac:(lia)).
  rewrite (Z.div_mod k (2 ^ (l - root))) at 1 by lia.
  replace (i + (2 ^ (l - root) * (k / 2 ^ (l - root)) + k mod 2 ^ (l - root)) * 2 ^ root)
    with ((i + k mod 2 ^ (l - root) * 2 ^ root) + (k / 2 ^ (l - root)) * 2 ^ l) by (rewrite E; ring).
  rewrite Z.mod_add by lia. apply Z.mod_small.
  pose proof (Z.mod_pos_bound k (2 ^ (l - root)) ltac:(lia)). split; nia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The final table of inflate_table's loop (decode_defs.dfinal) replicates its entries: a root     *)
(* entry of a short code fills every index that agrees with the code on its bits; a sub-table entry *)
(* likewise within its sub-table.                                                                  *)

Section Rep.
Context (type: Z) (W ls: list Z) (root used: Z) (t: list entry) (lk: Z -> bool).
Context (Hr : Forall (fun l => 1 <= l <= MAXBITS) ls).
Context (Hs : forall a b, 0 <= a -> a <= b < Zlength ls -> Znth a ls <= Znth b ls).
Context (HN : 0 < Zlength ls).
Context (Hroot : 1 <= root <= MAXBITS).
Context (Hbits : bits_stmt).
(* the link test lk: false on the symbols' entries and on the invalid entry, true on the links *)
Context (Hsym : forall j b, 0 <= j < Zlength ls ->
  lk (e_op (sym_entry type (Znth j W) b)) = false /\ e_bits (sym_entry type (Znth j W) b) = b).
Context (Hlk : forall j, 0 <= j < Zlength ls -> root < Znth j ls -> lk (e_op (dlink ls root j)) = true).
Context (Hinv : lk 64 = false).
Context (Hf : dfinal type W ls root used t).

(* a short code's fill: every root index that ends with the code *)
Lemma tr_fill_short : forall j i, 0 <= j < Zlength ls -> Znth j ls <= root -> 0 <= i < 2 ^ root ->
  i mod 2 ^ Znth j ls = dhuff ls j -> Znth i t = sym_entry type (Znth j W) (Znth j ls).
Proof.
  intros j i Hj Hs' Hi Hd. destruct Hf as (Hfl & _).
  destruct (Hfl j Hj) as [[Fs _] _].
  set (l := Znth j ls) in *. pose proof (ls_range ls Hr j Hj) as Hl. fold l in Hl.
  pose proof (Cover2.pow2_pos l ltac:(lia)).
  assert (Hk': 0 <= i / 2 ^ l < 2 ^ (root - l)).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
    rewrite <- Z.pow_add_r by lia. replace (l + (root - l)) with root by lia. lia. }
  specialize (Fs Hs' (i / 2 ^ l) Hk'). rewrite <- Hd in Fs.
  replace (i mod 2 ^ l + i / 2 ^ l * 2 ^ l) with i in Fs
    by (pose proof (Z.div_mod i (2 ^ l) ltac:(lia)); lia).
  exact Fs.
Qed.

(* a long code's fill in the sub-table of its root prefix: every sub-table index kk whose pattern
   i + kk 2^root ends with the code *)
Lemma tr_fill_long : forall j i kk, 0 <= j < Zlength ls -> root < Znth j ls -> 0 <= i < 2 ^ root ->
  0 <= kk < 2 ^ (gmax ls root (pfx ls root j) - root) ->
  (i + kk * 2 ^ root) mod 2 ^ Znth j ls = dhuff ls j ->
  Znth (dnxt ls root (pfx ls root j) + kk) t = sym_entry type (Znth j W) (Znth j ls - root).
Proof.
  intros j i kk Hj Hlong Hi Hkk Hd. destruct Hf as (Hfl & _).
  destruct (Hfl j Hj) as [[_ Fl] _].
  set (l := Znth j ls) in *. pose proof (ls_range ls Hr j Hj) as Hl. fold l in Hl.
  destruct (gmax_props ls root (pfx ls root j)) as (G1 & G2 & _).
  set (g := gmax ls root (pfx ls root j)) in *.
  assert (Hlg: l <= g) by (apply G2; auto; lia).
  pose proof (Cover2.pow2_pos l ltac:(lia)). pose proof (Cover2.pow2_pos root ltac:(lia)).
  pose proof (Cover2.pow2_pos (g - root) ltac:(lia)).
  set (P := i + kk * 2 ^ root).
  assert (HP: 0 <= P < 2 ^ g).
  { unfold P. replace g with ((g - root) + root) by lia. rewrite Cover2.pow2_split by lia. nia. }
  assert (Hx: 0 <= P / 2 ^ l < 2 ^ (g - l)).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
    rewrite <- Z.pow_add_r by lia. replace (l + (g - l)) with g by lia. lia. }
  specialize (Fl Hlong (P / 2 ^ l) Hx). fold P in Hd. rewrite <- Hd in Fl.
  assert (Hidx: Z.shiftr (P mod 2 ^ l) root + P / 2 ^ l * 2 ^ (l - root) = kk)
    by (unfold P; apply Cover2.split_idx; lia).
  rewrite <- Z.add_assoc, Hidx in Fl. exact Fl.
Qed.

(* a root index of a complete code: the fill of a short code, or the link of a long code's group
   whose sub-table indices are each the fill of a long code of the group *)
Lemma tr_root : ksum ls = 2 ^ MAXBITS -> forall i, 0 <= i < 2 ^ root ->
  exists j, 0 <= j < Zlength ls /\
   ((Znth j ls <= root /\ dhuff ls j = i mod 2 ^ Znth j ls) \/
    (root < Znth j ls /\ Znth i t = dlink ls root j /\
     forall kk, 0 <= kk < 2 ^ (gmax ls root (pfx ls root j) - root) ->
       exists j', 0 <= j' < Zlength ls /\ root < Znth j' ls /\ pfx ls root j' = pfx ls root j /\
         (i + kk * 2 ^ root) mod 2 ^ Znth j' ls = dhuff ls j')).
Proof.
  intros Hfull i Hi. pose proof Hbits as (B1 & B2 & B3 & B4 & B5).
  destruct Hf as (Hfl & Hu1 & Hu2 & Hinc).
  destruct (Cover2.locate ls Hr Hs Hfull Hbits root i ltac:(lia) Hi) as (j & Hj & Hm).
  exists j. split; [exact Hj|].
  set (l := Znth j ls) in *. pose proof (ls_range ls Hr j Hj) as Hl. fold l in Hl.
  destruct (Z_le_gt_dec l root) as [Hshort|Hlong].
  - left. split; [exact Hshort|].
    pose proof (Cover2.pow2_pos l ltac:(lia)).
    unfold dhuff, dcode. fold l. rewrite (Hm l) by lia. apply B3; [lia|]. apply Z.mod_pos_bound; lia.
  - right. split; [lia|].
    destruct (Hfl j Hj) as [_ Lk].
    set (q := pfx ls root j) in *.
    assert (Hq: q = reverse_bits i root).
    { unfold q, pfx. rewrite (Hm root) by lia. rewrite Z.mod_small by lia. reflexivity. }
    assert (Hrq: reverse_bits q root = i) by (rewrite Hq; apply B3; lia).
    unfold link_done in Lk. fold l q in Lk. specialize (Lk ltac:(lia)). rewrite Hrq in Lk.
    split; [exact Lk|].
    destruct (gmax_props ls root q) as (G1 & G2 & G3).
    set (g := gmax ls root q) in *.
    assert (Hlg: l <= g) by (apply G2; auto; lia).
    assert (Hg: g <= MAXBITS).
    { destruct G3 as [G3|(j0 & Hj0 & _ & _ & G3)]; [lia|].
      rewrite G3. apply (ls_range ls Hr j0 Hj0). }
    intros k Hkk.
    pose proof (Cover2.pow2_pos (g - root) ltac:(lia)).
    set (P := i + k * 2 ^ root).
    assert (HP: 0 <= P < 2 ^ g).
    { unfold P. replace g with ((g - root) + root) by lia. rewrite Cover2.pow2_split by lia. nia. }
    destruct (Cover2.locate ls Hr Hs Hfull Hbits g P ltac:(lia) HP) as (j' & Hj' & Hm').
    set (l' := Znth j' ls) in *. pose proof (ls_range ls Hr j' Hj') as Hl'. fold l' in Hl'.
    assert (HPm: forall m, 0 <= m <= root -> P mod 2 ^ m = i mod 2 ^ m).
    { intros m Hm0. unfold P. replace (2 ^ root) with (2 ^ (root - m) * 2 ^ m)
        by (rewrite <- Cover2.pow2_split by lia; f_equal; lia).
      rewrite Z.mul_assoc, Z.mod_add by (pose proof (Cover2.pow2_pos m ltac:(lia)); lia). reflexivity. }
    assert (Hlong': root < l').
    { destruct (Z_lt_le_dec root l') as [|Hle]; [auto|exfalso].
      assert (E: kpre ls j' / 2 ^ (MAXBITS - l') = kpre ls j / 2 ^ (MAXBITS - l')).
      { rewrite (Hm' l') by lia. rewrite (Hm l') by lia. rewrite HPm by lia. reflexivity. }
      assert (Ejj: j = j').
      { apply (Cover2.kpre_interval_unique ls j j' Hr Hj Hj').
        pose proof (kpre_div_self ls Hr Hs j' Hj') as K1. fold l' in K1.
        pose proof (kpre_S ls j' Hj') as K2. fold l' in K2.
        pose proof (Cover2.pow2_pos (MAXBITS - l') ltac:(lia)).
        pose proof (Z.div_mod (kpre ls j') (2 ^ (MAXBITS - l')) ltac:(lia)).
        pose proof (Z.div_mod (kpre ls j) (2 ^ (MAXBITS - l')) ltac:(lia)).
        pose proof (Z.mod_pos_bound (kpre ls j) (2 ^ (MAXBITS - l')) ltac:(lia)).
        rewrite E in *. lia. }
      subst j'. unfold l' in Hle. fold l in Hle. lia. }
    assert (Hpq: pfx ls root j' = q).
    { unfold pfx. rewrite (Hm' root) by lia. rewrite HPm by lia. rewrite Z.mod_small by lia.
      symmetry; exact Hq. }
    exists j'. split; [exact Hj'|]. split; [exact Hlong'|]. split; [exact Hpq|].
    assert (Hl'g: l' <= g) by (apply G2; auto).
    pose proof (Cover2.pow2_pos l' ltac:(lia)).
    fold P. unfold dhuff, dcode. fold l'. rewrite (Hm' l') by lia. symmetry. apply B3; [lia|].
    apply Z.mod_pos_bound; lia.
Qed.

Lemma tr_rep : ksum ls <= 2 ^ MAXBITS -> trep (fun i => Znth i t) root lk.
Proof.
  intros Hk. pose proof Hf as (Hfl & Hu1 & Hu2 & Hinc).
  pose proof (Cover2.pow2_pos root ltac:(lia)) as Hr0.
  destruct (Z_lt_le_dec (ksum ls) (2 ^ MAXBITS)) as [Hlt|Hge].
  - (* incomplete: one code of length 1, root 1: entry 0 is its symbol, entry 1 invalid *)
    destruct (Hinc Hlt) as (HN1 & H01 & Er & Eu & Ht1).
    assert (Hdh: dhuff ls 0 = 0) by (unfold dhuff, dcode; rewrite kpre_0, Zdiv_0_l; apply reverse_bits_0).
    assert (E0: Znth 0 t = sym_entry type (Znth 0 W) 1).
    { rewrite <- H01. apply tr_fill_short; try lia. rewrite H01, Hdh. reflexivity. }
    rewrite Er. change (2 ^ 1) with 2 in *.
    split.
    + intros i i2 Hi Hi2 _ Hm.
      assert (Hb: e_bits (Znth i t) = 1).
      { assert (i = 0 \/ i = 1) as [-> | ->] by lia.
        - rewrite E0. apply (Hsym 0 1). lia.
        - rewrite Ht1. reflexivity. }
      rewrite Hb in Hm. change (2 ^ 1) with 2 in Hm.
      rewrite !Z.mod_small in Hm by lia. subst i2. reflexivity.
    + intros i Hi Hl. exfalso.
      assert (i = 0 \/ i = 1) as [-> | ->] by lia.
      * rewrite E0, (proj1 (Hsym 0 1 ltac:(lia))) in Hl. discriminate.
      * rewrite Ht1 in Hl. cbn in Hl. rewrite Hinv in Hl. discriminate.
  - assert (Hfull: ksum ls = 2 ^ MAXBITS) by lia.
    split.
    + intros i i2 Hi Hi2 Hl Hm.
      destruct (tr_root Hfull i Hi) as (j & Hj & [(Hshort & Hd) | (Hlong & Ei & _)]).
      * assert (Ei: Znth i t = sym_entry type (Znth j W) (Znth j ls)) by (apply tr_fill_short; auto).
        rewrite Ei in Hm |- *. rewrite (proj2 (Hsym j _ Hj)) in Hm.
        apply tr_fill_short; auto. rewrite <- Hm. symmetry; exact Hd.
      * rewrite Ei, (Hlk j Hj Hlong) in Hl. discriminate.
    + intros i Hi Hl jj kk Hjj Hkk Hm.
      destruct (tr_root Hfull i Hi) as (j & Hj & [(Hshort & Hd) | (Hlong & Ei & Hsub)]).
      * exfalso. assert (Ei: Znth i t = sym_entry type (Znth j W) (Znth j ls)) by (apply tr_fill_short; auto).
        rewrite Ei, (proj1 (Hsym j _ Hj)) in Hl. discriminate.
      * rewrite Ei in Hjj, Hkk, Hm |- *. unfold dlink in Hjj, Hkk, Hm |- *. cbn [e_op e_val] in Hjj, Hkk, Hm |- *.
        set (q := pfx ls root j) in *.
        destruct (Hsub jj Hjj) as (j1 & Hj1 & Hl1 & Hq1 & Hd1).
        assert (E1: Znth (dnxt ls root q + jj) t = sym_entry type (Znth j1 W) (Znth j1 ls - root)).
        { rewrite <- Hq1. apply (tr_fill_long j1 i jj); auto; rewrite Hq1; auto. }
        rewrite E1 in Hm |- *. rewrite (proj2 (Hsym j1 _ Hj1)) in Hm.
        rewrite <- Hq1. apply (tr_fill_long j1 i kk); auto; [rewrite Hq1; auto|].
        pose proof (ls_range ls Hr j1 Hj1).
        rewrite tr_mod_split by lia. rewrite <- Hm. rewrite <- tr_mod_split by lia. exact Hd1.
Qed.

End Rep.

(* The tables inflate_table builds replicate their entries. *)
Lemma si_tabrep_model : forall type lens req old root used t,
  inputs_ok type lens req -> (type = CODES -> Zlength lens <= 19) ->
  cap_ok type lens req (Zlength old) -> Forall entry_ok old ->
  inflate_table_model type lens req old = ROk root used t ->
  trep (fun i => Znth i t) root
    (if type =? CODES then no_link else if type =? LENS then len_islink else dist_islink).
Proof.
  intros type lens req old root used t Hin H19 Hcap Hold Hmodel.
  set (lk := if type =? CODES then no_link else if type =? LENS then len_islink else dist_islink).
  pose proof part_sorted.sorted_ok2 as Hsorted. pose proof part_rfc.rfc_ok2 as Hrfc.
  pose proof part_bits.bits_ok2 as Hbits. pose proof part_subbits.subbits_ok2 as Hsub.
  pose proof Hin as (Ht & Hcodes & Hl & Hreq).
  (* the link test is inflate_table's (Tables.islink), but for the code length code (no links) *)
  assert (Hlk: type <> CODES -> forall op, lk op = Tables.islink type op).
  { intros Hc op. unfold lk, Tables.islink, CODES, LENS, DISTS in *.
    assert (type = 1 \/ type = 2) as [-> | ->] by lia; reflexivity. }
  assert (Hinv: lk 64 = false).
  { unfold lk. destruct (type =? CODES); [reflexivity|]. destruct (type =? LENS); reflexivity. }
  unfold inflate_table_model in Hmodel.
  destruct (maxlen lens =? 0) eqn:Emx.
  - (* no symbol: two invalid entries of 1 bit *)
    inversion Hmodel; subst root used t; clear Hmodel.
    assert (H2: 2 <= Zlength old).
    { destruct Hcap as (C1 & C2 & C3). unfold CODES, LENS, DISTS, ENOUGH_LENS, ENOUGH_DISTS in *.
      assert (type = 0 \/ type = 1 \/ type = 2) as [E | [E | E]] by lia.
      - apply C1; auto. - specialize (C2 E); lia. - specialize (C3 E); lia. }
    assert (Hfin: forall i, 0 <= i < 2 ->
      Znth i (upd_Znth 1 (upd_Znth 0 old (invalid_entry 1)) (invalid_entry 1)) = invalid_entry 1).
    { intros i Hi. assert (i = 0 \/ i = 1) as [-> | ->] by lia.
      - rewrite upd_Znth_diff by (rewrite ?upd_Znth_Zlength; lia). rewrite upd_Znth_same by lia. reflexivity.
      - rewrite upd_Znth_same by (rewrite ?upd_Znth_Zlength; lia). reflexivity. }
    change (2 ^ 1) with 2. split.
    + intros i i2 Hi Hi2 _ _. rewrite !Hfin by lia. reflexivity.
    + intros i Hi Hli. rewrite Hfin in Hli by lia. cbn in Hli. fold lk in Hli. rewrite Hinv in Hli. discriminate.
  - apply Z.eqb_neq in Emx.
    destruct (left_final (counts lens)) as [lft|] eqn:Eleft; [|discriminate].
    destruct (((0 <? lft) && ((type =? CODES) || negb (maxlen lens =? 1)))%bool) eqn:Etest; [discriminate|].
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
    destruct Hd as (Hrange & Hsl & HN & HWls & HWr & Hroot & Hk & _ & _ & Hcodes' & _).
    destruct (Hsorted lens Hl) as (SW & _).
    assert (HWl: Zlength (sl lens) = Zlength (sorted_syms lens)) by (unfold sl; apply Zlength_map).
    apply (tr_rep type (sorted_syms lens) (sl lens) (root_of req lens) (s_used s) (finish s) lk); auto.
    + pose proof (ls_range _ Hrange 0 ltac:(lia)).
      pose proof (ls_range _ Hrange (Zlength (sl lens) - 1) ltac:(lia)). lia.
    + intros j b Hj. rewrite Forall_forall in SW.
      pose proof (SW _ (Znth_In j (sorted_syms lens) ltac:(lia))) as Hs.
      destruct (Cover2.sym_ok type (Znth j (sorted_syms lens)) b) as (S1 & _ & S3); auto; try lia.
      split; [|exact S3].
      destruct (Z.eq_dec type CODES) as [Ec|Ec]; [unfold lk; rewrite Ec; reflexivity|].
      rewrite Hlk by exact Ec. exact S1.
    + intros j Hj Hlong.
      destruct (Z.eq_dec type CODES) as [Ec|Ec].
      { exfalso. specialize (Hcodes' Ec). pose proof (Hsl j (Zlength (sl lens) - 1) ltac:(lia) ltac:(lia)). lia. }
      rewrite Hlk by exact Ec. unfold dlink. cbn [e_op].
      destruct (gmax_props (sl lens) (root_of req lens) (pfx (sl lens) (root_of req lens) j)) as (G1 & G2 & G3).
      assert (Hlg: Znth j (sl lens) <= gmax (sl lens) (root_of req lens) (pfx (sl lens) (root_of req lens) j))
        by (apply G2; auto).
      pose proof (ls_range _ Hrange j Hj).
      assert (Hg: gmax (sl lens) (root_of req lens) (pfx (sl lens) (root_of req lens) j) <= MAXBITS).
      { destruct G3 as [G3|(j0 & Hj0 & _ & _ & G3)]; [lia|].
        rewrite G3. apply (ls_range _ Hrange j0 Hj0). }
      pose proof (ls_range _ Hrange 0 ltac:(lia)).
      apply Cover2.islink_small. unfold MAXBITS in *. lia.
Qed.


(* ---------------------------------------------------------------------------------------------- *)
(* The fixed tables, by computation: a boolean form of trep over a concrete table.                *)

Definition ent_eqb (a b: entry) : bool :=
  ((e_op a =? e_op b) && (e_bits a =? e_bits b) && (e_val a =? e_val b))%bool.

Lemma ent_eqb_ok : forall a b, ent_eqb a b = true -> a = b.
Proof.
  intros [o1 b1 v1] [o2 b2 v2] H. unfold ent_eqb in H. cbn in H.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1, H2, H3. subst. reflexivity.
Qed.

Definition trep_chk (tbl: list entry) (rb: Z) (lk: Z -> bool) : bool :=
  forallb (fun a => let i := Z.of_nat a in let e := Znth i tbl in
    if lk (e_op e) then
      forallb (fun b => let j := Z.of_nat b in let ej := Znth (e_val e + j) tbl in
        forallb (fun c => let k := Z.of_nat c in
          (negb (j mod 2 ^ e_bits ej =? k mod 2 ^ e_bits ej) || ent_eqb (Znth (e_val e + k) tbl) ej)%bool)
          (List.seq 0 (Z.to_nat (2 ^ e_op e))))
        (List.seq 0 (Z.to_nat (2 ^ e_op e)))
    else
      forallb (fun b => let j := Z.of_nat b in
        (negb (i mod 2 ^ e_bits e =? j mod 2 ^ e_bits e) || ent_eqb (Znth j tbl) e)%bool)
        (List.seq 0 (Z.to_nat (2 ^ rb))))
    (List.seq 0 (Z.to_nat (2 ^ rb))).

Lemma trep_chk_ok : forall tbl rb lk, trep_chk tbl rb lk = true -> trep (fun i => Znth i tbl) rb lk.
Proof.
  intros tbl rb lk H. unfold trep_chk in H. rewrite forallb_forall in H. split.
  - intros i j Hi Hj Hl Hm.
    specialize (H (Z.to_nat i) ltac:(apply List.in_seq; lia)). rewrite Z2Nat.id in H by lia.
    cbv zeta in H. rewrite Hl, forallb_forall in H.
    specialize (H (Z.to_nat j) ltac:(apply List.in_seq; lia)). rewrite Z2Nat.id in H by lia.
    rewrite Hm, Z.eqb_refl in H. apply ent_eqb_ok. exact H.
  - intros i Hi Hl j k Hj Hk Hm.
    specialize (H (Z.to_nat i) ltac:(apply List.in_seq; lia)). rewrite Z2Nat.id in H by lia.
    cbv zeta in H. rewrite Hl, forallb_forall in H.
    specialize (H (Z.to_nat j) ltac:(apply List.in_seq; lia)). rewrite forallb_forall in H.
    specialize (H (Z.to_nat k) ltac:(apply List.in_seq; lia)). rewrite !Z2Nat.id in H by lia.
    rewrite Hm, Z.eqb_refl in H. apply ent_eqb_ok. exact H.
Qed.

Lemma trep_chk_lenfix : trep_chk lenfix_list 9 len_islink = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma trep_chk_distfix : trep_chk distfix_list 5 dist_islink = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma dist_ok_distfix : Forall dist_ok distfix_list.
Proof.
  assert (H: forallb (fun e => ((Z.land (e_op e) 16 =? 0) ||
                              (e_val e + 2 ^ Z.land (e_op e) 15 - 1 <=? 32768))%bool) distfix_list = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in H. apply Forall_forall. intros e He Hop.
  specialize (H e He). apply orb_prop in H as [H|H].
  - apply Z.eqb_eq in H. contradiction.
  - apply Z.leb_le in H. exact H.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Coverage, for any table type: every entry of [0, 2^root + sumq ls root (2^root)) of a complete
   code's table is a fill (a sym_entry) or a link (a dlink), so a property Pr of all the possible
   fills and links holds of every entry there.  This is the argument of Cover3Len.v's Section Cov,
   which is stated for length tables and len_ok only. *)

Section CovG.
Context (type: Z) (Pr: entry -> Prop).
Context (W ls: list Z) (root: Z) (t: list entry).
Context (Hrange : Forall (fun l => 1 <= l <= MAXBITS) ls).
Context (Hsorted : forall a b, 0 <= a -> a <= b < Zlength ls -> Znth a ls <= Znth b ls).
Context (HN : 0 < Zlength ls).
Context (Hroot : Znth 0 ls <= root <= Znth (Zlength ls - 1) ls).
Context (Hk : ksum ls = 2 ^ MAXBITS).
Context (Hbits : bits_stmt).
Context (Hfill : forall j, 0 <= j < Zlength ls -> fills_done type W ls root j t).
Context (Hlink : forall j, 0 <= j < Zlength ls -> link_done ls root j t).
Context (Hsym : forall s b, Pr (sym_entry type s b)).
Context (Hlnk : forall j, 0 <= j < Zlength ls -> root < Znth j ls -> Pr (dlink ls root j)).

Lemma si_cov_root : forall P, 0 <= P < 2 ^ root -> Pr (Znth P t).
Proof.
  intros P HP. pose proof Hbits as (B1 & B2 & B3 & B4 & B5). pose proof (Cover3Len.c3_root ls root Hrange HN Hroot) as Hr.
  assert (HM: MAXBITS = 15) by reflexivity.
  set (r := reverse_bits P root).
  assert (Hr0: 0 <= r < 2 ^ root) by (apply B1; lia).
  assert (Hrr: reverse_bits r root = P) by (apply B3; lia).
  set (E := 2 ^ (MAXBITS - root)).
  assert (HE: 0 < E) by (apply Cover3Len.c3_pow_pos; lia).
  assert (H15: 2 ^ MAXBITS = 2 ^ root * E) by (unfold E; rewrite <- Z.pow_add_r by lia; f_equal; lia).
  destruct (Cover3Len.c3_find_j ls HN Hk (r * E) ltac:(nia)) as (j & Hj & Hlo & Hhi).
  destruct (Cover3Len.c3_C ls root Hrange Hsorted HN Hk j Hj) as (HC0 & HK & HS & HCl).
  pose proof (ls_range ls Hrange j Hj) as Hl.
  set (l := Znth j ls) in *. set (C := kpre ls j / 2 ^ (MAXBITS - l)) in *.
  set (D := 2 ^ (MAXBITS - l)) in *.
  assert (HD: 0 < D) by (apply Cover3Len.c3_pow_pos; lia).
  destruct (Z_le_gt_dec l root) as [S|L].
  - (* a short code: P is one of its fills *)
    set (A := 2 ^ (root - l)).
    assert (HA: 0 < A) by (apply Cover3Len.c3_pow_pos; lia).
    assert (EDA: D = A * E) by (unfold D, A, E; rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (Hra: r / A = C).
    { apply Cover3Len.c3_div_pin; auto. split.
      - apply (Cover3Len.c3_cancel_le _ _ E); auto. rewrite <- Z.mul_assoc, <- EDA. lia.
      - apply (Cover3Len.c3_cancel_lt _ _ E); auto. rewrite <- Z.mul_assoc, <- EDA. lia. }
    assert (Hmod: P mod 2 ^ l = dhuff ls j).
    { rewrite <- ds_land_mod by lia. rewrite <- Hrr. rewrite B2 by lia. fold A. rewrite Hra. reflexivity. }
    destruct (Hfill j Hj) as (F & _). fold l in F.
    assert (H2l: 0 < 2 ^ l) by (apply Cover3Len.c3_pow_pos; lia).
    assert (Hk0: 0 <= P / 2 ^ l < 2 ^ (root - l)).
    { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; auto.
      rewrite <- Z.pow_add_r by lia. replace (l + (root - l)) with root by lia. lia. }
    specialize (F S (P / 2 ^ l) Hk0).
    rewrite <- Hmod in F. rewrite (Z.mul_comm (P / 2 ^ l)), Z.add_comm, <- Z.div_mod in F by lia.
    rewrite F. apply Hsym.
  - (* a long code: P is the link of its group *)
    set (A := 2 ^ (l - root)).
    assert (HA: 0 < A) by (apply Cover3Len.c3_pow_pos; lia).
    assert (EDA: E = A * D) by (unfold D, A, E; rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (HCr: C = r * A).
    { assert (C <= r * A) by (apply (Cover3Len.c3_cancel_le _ _ D); auto; rewrite <- Z.mul_assoc, <- EDA; lia).
      assert (r * A < C + 1) by (apply (Cover3Len.c3_cancel_lt _ _ D); auto; rewrite <- Z.mul_assoc, <- EDA; lia).
      lia. }
    assert (Hp: pfx ls root j = r).
    { unfold pfx. fold E. rewrite HK, HCr, EDA. rewrite <- Z.mul_assoc. apply Z.div_mul. lia. }
    assert (L': root < Znth j ls) by (fold l; lia).
    pose proof (Hlink j Hj L') as Lk. rewrite Hp, Hrr in Lk. rewrite Lk. apply Hlnk; [exact Hj | exact L'].
Qed.

Lemma si_cov_sub : forall P, 2 ^ root <= P < 2 ^ root + sumq ls root (2 ^ root) -> Pr (Znth P t).
Proof.
  intros P HP. pose proof Hbits as (B1 & B2 & B3 & B4 & B5). pose proof (Cover3Len.c3_root ls root Hrange HN Hroot) as Hr.
  assert (HM: MAXBITS = 15) by reflexivity.
  set (E := 2 ^ (MAXBITS - root)).
  assert (HE: 0 < E) by (apply Cover3Len.c3_pow_pos; lia).
  assert (H15: 2 ^ MAXBITS = 2 ^ root * E) by (unfold E; rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (H2r: 0 < 2 ^ root) by (apply Cover3Len.c3_pow_pos; lia).
  (* the group q of P *)
  destruct (Cover3Len.c3_find (sumq ls root) (P - 2 ^ root) (Z.to_nat (2 ^ root))) as (q & Hq & Hqlo & Hqhi).
  { change (sumq ls root 0) with 0. lia. }
  { rewrite Z2Nat.id by lia. lia. }
  rewrite Z2Nat.id in Hq by lia. rewrite sumq_succ in Hqhi by lia.
  assert (Hfq: fq ls root q <> 0) by lia.
  destruct (fq_nonzero ls root q Hfq) as (j0 & Hj0 & Hl0 & Hp0).
  destruct (gmax_props ls root q) as (G1 & G2 & _).
  set (g := gmax ls root q) in *.
  assert (Hg0: Znth j0 ls <= g) by (apply G2; auto).
  pose proof (Cover3Len.c3_gmax_le ls root Hrange q) as Hg15. fold g in Hg15.
  assert (Efq: fq ls root q = 2 ^ (g - root)) by (unfold fq; fold g; destruct (g =? 0) eqn:Eg; [apply Z.eqb_eq in Eg; lia|auto]).
  rewrite Efq in Hqhi.
  set (p' := P - 2 ^ root - sumq ls root q).
  assert (Hp': 0 <= p' < 2 ^ (g - root)) by (unfold p'; lia).
  set (r' := reverse_bits p' (g - root)).
  assert (Hr': 0 <= r' < 2 ^ (g - root)) by (apply B1; lia).
  assert (Hrr': reverse_bits r' (g - root) = p') by (apply B3; lia).
  set (G := 2 ^ (MAXBITS - g)).
  assert (HG: 0 < G) by (apply Cover3Len.c3_pow_pos; lia).
  assert (EEG: E = 2 ^ (g - root) * G) by (unfold E, G; rewrite <- Z.pow_add_r by lia; f_equal; lia).
  set (Q := q * E).
  set (X := Q + r' * G).
  assert (HX: Q <= X < Q + E) by (unfold X; nia).
  assert (HXm: X < 2 ^ MAXBITS) by (unfold Q in HX; nia).
  (* the group start j0 lies in [Q, Q + E) *)
  assert (Hk0: Q <= kpre ls j0 < Q + E).
  { pose proof (Z.div_mod (kpre ls j0) E ltac:(lia)). pose proof (Z.mod_pos_bound (kpre ls j0) E HE).
    fold E in Hp0. rewrite Hp0 in H. unfold Q. lia. }
  destruct (Cover3Len.c3_find_j ls HN Hk X ltac:(unfold Q in *; nia)) as (j & Hj & Hlo & Hhi).
  destruct (Cover3Len.c3_C ls root Hrange Hsorted HN Hk j Hj) as (HC0 & HK & HS & HCl).
  pose proof (ls_range ls Hrange j Hj) as Hl.
  set (l := Znth j ls) in *. set (C := kpre ls j / 2 ^ (MAXBITS - l)) in *.
  set (D := 2 ^ (MAXBITS - l)) in *.
  assert (HD: 0 < D) by (apply Cover3Len.c3_pow_pos; lia).
  assert (L: root < l).
  { destruct (Z_le_gt_dec l root) as [S|L]; [exfalso|lia].
    set (A := 2 ^ (root - l)).
    assert (HA: 0 < A) by (apply Cover3Len.c3_pow_pos; lia).
    assert (EDA: D = A * E) by (unfold D, A, E; rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (C * A < q + 1).
    { apply (Cover3Len.c3_cancel_lt _ _ E); auto. rewrite <- Z.mul_assoc, <- EDA. unfold Q in HX. lia. }
    assert (q < (C + 1) * A).
    { apply (Cover3Len.c3_cancel_lt _ _ E); auto. rewrite <- Z.mul_assoc, <- EDA. unfold Q in HX. lia. }
    assert (A1: kpre ls j <= kpre ls j0).
    { rewrite HK, EDA. replace (C * (A * E)) with (C * A * E) by ring.
      apply Z.le_trans with (q * E); [apply Z.mul_le_mono_nonneg_r; lia | unfold Q in Hk0; lia]. }
    assert (A2: kpre ls j0 < kpre ls (j + 1)).
    { rewrite HS, EDA. replace ((C + 1) * (A * E)) with ((C + 1) * A * E) by ring.
      apply Z.lt_le_trans with ((q + 1) * E); [unfold Q in Hk0; lia | apply Z.mul_le_mono_nonneg_r; lia]. }
    destruct (Z_lt_ge_dec j0 j) as [J|J].
    - pose proof (kpre_mono ls (j0 + 1) j ltac:(lia) ltac:(lia)). rewrite kpre_S in H1 by lia.
      pose proof (Cover3Len.c3_pow_pos (MAXBITS - Znth j0 ls)). lia.
    - destruct (Z_lt_ge_dec j j0) as [J'|J'].
      + pose proof (kpre_mono ls (j + 1) j0 ltac:(lia) ltac:(lia)). lia.
      + assert (j = j0) by lia. subst j0. fold l in Hl0. lia. }
  set (A := 2 ^ (l - root)).
  assert (HA: 0 < A) by (apply Cover3Len.c3_pow_pos; lia).
  assert (EDA: E = A * D) by (unfold D, A, E; rewrite <- Z.pow_add_r by lia; f_equal; lia).
  set (d := C - q * A).
  assert (Hd: 0 <= d < A).
  { unfold d. split.
    - assert (q * A < C + 1); [|lia]. apply (Cover3Len.c3_cancel_lt _ _ D); auto. rewrite <- Z.mul_assoc, <- EDA.
      unfold Q in HX. lia.
    - assert (C < q * A + A); [|lia]. apply (Cover3Len.c3_cancel_lt _ _ D); auto.
      replace ((q * A + A) * D) with (q * E + E) by (rewrite EDA; ring). unfold Q in HX. lia. }
  assert (Hpj: pfx ls root j = q).
  { unfold pfx. fold E. apply Cover3Len.c3_div_pin; auto. rewrite HK, EDA. replace C with (q * A + d) by (unfold d; lia).
    assert (0 <= d * D < A * D) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_lt_mono_pos_r; lia]).
    replace ((q * A + d) * D) with (q * (A * D) + d * D) by ring.
    replace ((q + 1) * (A * D)) with (q * (A * D) + A * D) by ring. lia. }
  assert (Hlg: l <= g) by (apply G2; auto; fold E; rewrite <- Hpj; reflexivity).
  set (B := 2 ^ (g - l)).
  assert (HB: 0 < B) by (apply Cover3Len.c3_pow_pos; lia).
  assert (EDB: D = B * G) by (unfold D, B, G; rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (Hrd: r' / B = d).
  { apply Cover3Len.c3_div_pin; auto. split.
    - apply (Cover3Len.c3_cancel_le _ _ G); auto. rewrite <- Z.mul_assoc, <- EDB.
      assert (kpre ls j = Q + d * D) by (rewrite HK; unfold Q, d; rewrite EDA; ring). unfold X in Hlo. lia.
    - apply (Cover3Len.c3_cancel_lt _ _ G); auto. rewrite <- Z.mul_assoc, <- EDB.
      assert (kpre ls (j + 1) = Q + (d + 1) * D) by (rewrite HS; unfold Q, d; rewrite EDA; ring).
      unfold X in Hhi. lia. }
  (* the fill of j that hits P *)
  set (h := dhuff ls j).
  assert (Hh: 0 <= h < 2 ^ l) by (apply B1; lia).
  assert (HhC: reverse_bits h l = C) by (apply B3; lia).
  assert (Hhr: 0 <= h / 2 ^ root < A).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; auto.
    unfold A. rewrite <- Z.pow_add_r by lia. replace (root + (l - root)) with l by lia. lia. }
  assert (HCd: C mod A = d).
  { unfold d. rewrite <- (Z.mod_unique C A q (C - q * A)); auto; lia. }
  assert (Hd': reverse_bits (h / 2 ^ root) (l - root) = d).
  { rewrite <- HCd. unfold A. rewrite <- ds_land_mod by lia. rewrite <- HhC. rewrite B2 by lia.
    f_equal. f_equal. f_equal. lia. }
  assert (Hpm: p' mod A = h / 2 ^ root).
  { unfold A. rewrite <- ds_land_mod by lia. rewrite <- Hrr'. rewrite B2 by lia.
    replace (g - root - (l - root)) with (g - l) by lia. fold B. rewrite Hrd. rewrite <- Hd'.
    apply B3; [lia|exact Hhr]. }
  destruct (Hfill j Hj) as (_ & F). fold l in F. rewrite Hpj in F. fold g in F.
  assert (Hkk: 0 <= p' / A < 2 ^ (g - l)).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; auto. unfold A.
    rewrite <- Z.pow_add_r by lia. replace (l - root + (g - l)) with (g - root) by lia. lia. }
  specialize (F L (p' / A) Hkk). fold A in F. fold h in F.
  rewrite Z.shiftr_div_pow2 in F by lia. rewrite <- Hpm in F.
  assert (Ep: p' mod A + p' / A * A = p') by (pose proof (Z.div_mod p' A ltac:(lia)); lia).
  rewrite <- Z.add_assoc, Ep in F.
  unfold dnxt, p' in F. replace (2 ^ root + sumq ls root q + (P - 2 ^ root - sumq ls root q)) with P in F by lia.
  rewrite F. apply Hsym.
Qed.

End CovG.

(* The entries a distance table can hold have distances up to 32768: a symbol's entry (base dbase[s]
   plus at most 2^dext[s]-1 extra, checked on the tables), a link and the invalid entry (no distance
   flag 16 in their op). *)
Definition si_dchk : bool :=
  forallb (fun i => let o := Znth i dext in
                    orb (Z.land o 16 =? 0) (Znth i dbase + 2 ^ Z.land o 15 - 1 <=? 32768))
          (zseq 0 32).

Lemma si_dchk_ok : si_dchk = true.
Proof. vm_compute. reflexivity. Qed.

Lemma si_sym_dist_ok : forall s b, dist_ok (sym_entry DISTS s b).
Proof.
  intros. unfold dist_ok, sym_entry. cbv zeta.
  change (match_of DISTS) with 0. change (extra_of DISTS) with dext. change (base_of DISTS) with dbase.
  destruct (s + 1 <? 0); [cbn [e_op]; intros H; exfalso; apply H; reflexivity|].
  destruct (0 <=? s) eqn:Es; [|cbn [e_op]; intros H; exfalso; apply H; reflexivity].
  apply Z.leb_le in Es. cbn [e_op e_val]. rewrite Z.sub_0_r.
  destruct (Z_lt_dec s 32);
    [|intros Ho; rewrite (Znth_overflow s dext) in Ho by (cbn; lia); exfalso; apply Ho; reflexivity].
  pose proof si_dchk_ok as H. unfold si_dchk in H. rewrite forallb_forall in H.
  specialize (H s (proj2 (In_zseq 32 0 s) ltac:(lia))). cbv zeta in H.
  intros Ho. rewrite orb_true_iff, Z.eqb_eq, Z.leb_le in H. destruct H; [contradiction|lia].
Qed.

Lemma si_invalid_dist_ok : forall b, dist_ok (invalid_entry b).
Proof. intros. unfold dist_ok, invalid_entry. cbn [e_op]. intros H; exfalso; apply H; reflexivity. Qed.

Lemma si_land16_small : forall x, 0 <= x < 16 -> Z.land x 16 = 0.
Proof.
  intros x Hx. assert (E: x = x mod 2 ^ 4) by (rewrite Z.mod_small; cbn; lia).
  rewrite E, <- Z.land_ones by lia. rewrite <- Z.land_assoc. change (Z.land (Z.ones 4) 16) with 0. apply Z.land_0_r.
Qed.

Lemma si_link_dist_ok : forall ls root j, Forall (fun l => 1 <= l <= MAXBITS) ls -> 0 <= root ->
  0 <= j < Zlength ls -> root < Znth j ls -> dist_ok (dlink ls root j).
Proof.
  intros ls root j Hr H0 Hj L. unfold dist_ok, dlink. cbn [e_op].
  pose proof (Cover3Len.c3_gmax_le ls root Hr (pfx ls root j)).
  pose proof (proj1 (proj2 (gmax_props ls root (pfx ls root j))) j Hj L eq_refl).
  pose proof (ls_range ls Hr j Hj). unfold MAXBITS in *.
  intros Ho. exfalso. apply Ho. apply si_land16_small. lia.
Qed.

(* The entries of a distance table inflate_table builds, in the region it uses, have distances up to
   32768. *)
Lemma si_tabrep_dist : forall lens req old root used t,
  inputs_ok DISTS lens req -> cap_ok DISTS lens req (Zlength old) -> Forall entry_ok old ->
  inflate_table_model DISTS lens req old = ROk root used t ->
  forall i, 0 <= i < used -> dist_ok (Znth i t).
Proof.
  intros lens req old root used t Hin Hcap Hold Hmodel i Hi.
  pose proof Hin as Hin'. destruct Hin' as (Ht & Hcodes & Hl & Hreq).
  pose proof part_sorted.sorted_ok2 as Hso. pose proof part_rfc.rfc_ok2 as Hrfc.
  pose proof part_bits.bits_ok2 as Hbits. pose proof part_subbits.subbits_ok2 as Hsub.
  pose proof (part_size.size_ok2 Hso Hrfc Hbits) as Hsize.
  pose proof (fact_result_ok Hso Hrfc Hbits Hsub Hsize DISTS lens req old Hin Hcap Hold) as FR.
  destruct (expected_call DISTS lens req) as [[want r0] size] eqn:Eec.
  rewrite Hmodel in FR. destruct FR as (_ & Er & Eu & Hu & _ & Hlen & _).
  unfold expected_call in Eec. injection Eec as Ew Er0 Es.
  assert (HM: MAXBITS = 15) by reflexivity.
  unfold inflate_table_model in Hmodel.
  destruct (maxlen lens =? 0) eqn:Emx.
  - (* no symbol: two invalid entries *)
    inversion Hmodel; subst root used t; clear Hmodel.
    destruct Hcap as (_ & _ & HcL). specialize (HcL eq_refl). unfold ENOUGH_DISTS in HcL.
    assert (i = 0 \/ i = 1) as [-> | ->] by lia.
    + rewrite upd_Znth_diff by (rewrite ?upd_Znth_Zlength; lia). rewrite upd_Znth_same by lia.
      apply si_invalid_dist_ok.
    + rewrite upd_Znth_same by (rewrite ?upd_Znth_Zlength; lia). apply si_invalid_dist_ok.
  - apply Z.eqb_neq in Emx.
    destruct (left_final (counts lens)) as [lft|] eqn:Eleft; [|discriminate].
    destruct (andb (0 <? lft) (orb (DISTS =? CODES) (negb (maxlen lens =? 1)))) eqn:Etest; [discriminate|].
    destruct (over DISTS (Z.shiftl 1 (root_of req lens))) eqn:Eover; [discriminate|].
    assert (Hd: dhyps DISTS lens (sorted_syms lens) (sl lens) (root_of req lens) old)
      by (eapply dsetup_ok; eauto).
    assert (Hfin: exists s, used = s_used s /\ t = finish s /\ root = root_of req lens /\
      (run DISTS lens (sorted_syms lens) (root_of req lens) (maxlen lens) (length (sorted_syms lens))
         (init_state lens (root_of req lens) old) = Break s \/
       run DISTS lens (sorted_syms lens) (root_of req lens) (maxlen lens) (length (sorted_syms lens))
         (init_state lens (root_of req lens) old) = Continue s)).
    { destruct (run DISTS lens (sorted_syms lens) (root_of req lens) (maxlen lens) (length (sorted_syms lens))
                  (init_state lens (root_of req lens) old)) eqn:Er';
        inversion Hmodel; subst; eexists; eauto. }
    destruct Hfin as (s & Eus & Ets & Ers & Hrun).
    destruct dstep_last_ok as [Hstep Hlast].
    pose proof (drun_ok DISTS lens req old s Hso Hbits Hsub Hstep Hlast Hl Emx Hd Hrun) as Hf.
    rewrite <- Eus, <- Ets, <- Ers in Hf. rewrite <- Ers in Hd.
    destruct Hd as (Hrange & Hsorted & HN & HWls & HWr & Hroot & Hk & Hinc & _ & _ & _ & Hcap0 & _ & _).
    destruct Hf as (Hfl & H2r & _ & Hincf).
    destruct (Z.eq_dec (ksum (sl lens)) (2 ^ MAXBITS)) as [Hc|Hc].
    + (* a complete code *)
      destruct (Hso lens Hl) as (_ & _ & _ & _ & _ & _ & Sk & _ & _).
      pose proof (Cover3Len.c3_root (sl lens) root Hrange HN Hroot) as Hr.
      assert (Hus: used <= 2 ^ root + sumq (sl lens) root (2 ^ root)).
      { rewrite Eu, <- Es, Er0, <- Er, Hsize by (auto; lia). unfold sumq. lia. }
      destruct (Z_lt_dec i (2 ^ root)).
      * apply (si_cov_root DISTS dist_ok (sorted_syms lens) (sl lens) root t Hrange Hsorted HN Hroot Hc Hbits);
          [intros j Hj; apply (proj1 (Hfl j Hj)) | intros j Hj; apply (proj2 (Hfl j Hj)) | apply si_sym_dist_ok
          | intros j Hj Lj; apply si_link_dist_ok; auto; lia | lia].
      * apply (si_cov_sub DISTS dist_ok (sorted_syms lens) (sl lens) root t Hrange Hsorted HN Hroot Hc Hbits);
          [intros j Hj; apply (proj1 (Hfl j Hj)) | apply si_sym_dist_ok | lia].
    + (* an incomplete code: one code of length 1, root 1 *)
      destruct (Hincf ltac:(lia)) as (EN & E0 & -> & -> & Hent).
      assert (i = 0 \/ i = 1) as [-> | ->] by lia.
      * destruct (Hfl 0 ltac:(lia)) as ((F & _) & _).
        rewrite E0 in F. specialize (F ltac:(lia) 0 ltac:(cbn; lia)).
        replace (dhuff (sl lens) 0 + 0 * 2 ^ 1) with 0 in F.
        { rewrite F. apply si_sym_dist_ok. }
        unfold dhuff, dcode. rewrite E0, kpre_0, Z.div_0_l, reverse_bits_0 by (cbn; lia). lia.
      * rewrite Hent. apply si_invalid_dist_ok.
Qed.

Lemma si_tabrep : tabrep_stmt.
Proof.
  split; [exact si_tabrep_model|].
  split; [exact (trep_chk_ok _ _ _ trep_chk_lenfix)|].
  split; [exact (trep_chk_ok _ _ _ trep_chk_distfix)|].
  split; [exact si_tabrep_dist | exact dist_ok_distfix].
Qed.
