(* Part of the decode theory: the tables inflate builds decode the codes.  Definitions: DecodeDefs.v / Decode.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.rfc1951.Decode.
Import ListNotations.
Local Open Scope Z_scope.
Require Import Zlib.proof.inftrees.ref Zlib.proof.inftrees.facts.
Require Zlib.proof.inftrees.fact_result Zlib.proof.inftrees.part_result Zlib.proof.inftrees.part_sorted
  Zlib.proof.inftrees.part_rfc Zlib.proof.inftrees.part_bits Zlib.proof.inftrees.part_subbits
  Zlib.proof.inftrees.part_size Zlib.proof.inftrees.part_enough.
Require Zlib.proof.inflate.Cover2 Zlib.proof.inftrees.part_decode Zlib.proof.inftrees.part_loop_facts.


(* the four clauses of tdec (DecodeDefs.v), named *)
Definition td_full (s: istate) (t: tref) (root type: Z) (lens: list Z) : Prop :=
  forall sy, 0 <= sy < Zlength lens -> Znth sy lens <> 0 -> forall x, 0 <= x ->
   exists op val,
     twalk s t root (Z.lor (ref.reverse_bits (code lens sy) (Znth sy lens)) (Z.shiftl x (Znth sy lens)))
       = Some (op, val, Znth sy lens) /\
     ref.means_symbol type sy op val = true.
Definition td_part (s: istate) (t: tref) (root: Z) (lens: list Z) : Prop :=
  forall sy, 0 <= sy < Zlength lens -> Znth sy lens <> 0 -> forall b pat, 0 <= b < Znth sy lens -> 0 <= pat ->
   pat mod 2 ^ b = ref.reverse_bits (code lens sy) (Znth sy lens) mod 2 ^ b ->
   let e := tab_entry lenfix_list distfix_list s t (pat mod 2 ^ root) in
   b < e_bits e \/
   (ref.is_link (e_op e) = true /\
    b < e_bits e + e_bits (tab_entry lenfix_list distfix_list s t (e_val e + Z.shiftr pat (e_bits e) mod 2 ^ e_op e))).
Definition td_nl (s: istate) (t: tref) (root type: Z) : Prop :=
  type = CODES -> forall i, 0 <= i < 2 ^ root ->
   ref.is_link (e_op (tab_entry lenfix_list distfix_list s t i)) = false.

Lemma tdec_intro : forall s t root type lens, 1 <= root <= 15 -> td_full s t root type lens ->
  td_part s t root lens -> td_nl s t root type -> tdec s t root type lens.
Proof. intros. unfold tdec. auto. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* (1) the fixed tables decode the fixed codes                                                    *)

(* the low root bits of a code reversed (rev < 2^len) followed by any bits x *)
Lemma tabdec_pat_mod : forall r len x root, 0 <= len <= root -> 0 <= r < 2 ^ len -> 0 <= x ->
  Z.lor r (Z.shiftl x len) mod 2 ^ root = r + (x mod 2 ^ (root - len)) * 2 ^ len.
Proof.
  intros r len x root Hl Hr Hx.
  assert (Hland : Z.land r (Z.shiftl x len) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i len) as [H|H].
    - rewrite Z.shiftl_spec_low by lia. apply andb_false_r.
    - rewrite <- (Z.mod_small r (2 ^ len)) by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
  rewrite <- Z.lxor_lor by exact Hland. rewrite <- Z.add_nocarry_lxor by exact Hland.
  rewrite Z.shiftl_mul_pow2 by lia.
  assert (Hp : 2 ^ root = 2 ^ (root - len) * 2 ^ len) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (H1 : 0 < 2 ^ (root - len)) by (apply Z.pow_pos_nonneg; lia).
  rewrite (Z.div_mod x (2 ^ (root - len))) at 1 by lia.
  pose proof (Z.mod_pos_bound x (2 ^ (root - len)) H1).
  rewrite Hp.
  replace (r + (2 ^ (root - len) * (x / 2 ^ (root - len)) + x mod 2 ^ (root - len)) * 2 ^ len)
    with ((r + x mod 2 ^ (root - len) * 2 ^ len) + (x / 2 ^ (root - len)) * (2 ^ (root - len) * 2 ^ len)) by ring.
  rewrite Z.mod_add by lia. apply Z.mod_small. split; nia.
Qed.

Definition tabdec_chk (tbl: list entry) (root type: Z) (lens: list Z) : bool :=
  forallb (fun n =>
    let sy := Z.of_nat n in let len := Znth sy lens in let rev := ref.reverse_bits (code lens sy) len in
    (len =? 0) ||
    ((0 <? len) && (len <=? root) && (0 <=? rev) && (rev <? 2 ^ len) &&
     forallb (fun m =>
       let e := Znth (rev + Z.of_nat m * 2 ^ len) tbl in
       negb (ref.is_link (e_op e)) && (e_bits e =? len) && ref.means_symbol type sy (e_op e) (e_val e))
       (seq 0 (Z.to_nat (2 ^ (root - len))))))
    (seq 0 (length lens)).

Lemma tabdec_chk_ok : forall tbl root type lens s t,
  1 <= root <= 15 -> (forall i, tab_entry lenfix_list distfix_list s t i = Znth i tbl) ->
  tabdec_chk tbl root type lens = true -> 1 <= root <= 15 /\ td_full s t root type lens.
Proof.
  intros tbl root type lens s t Hroot Htab Hc. split; [exact Hroot|]. unfold td_full.
  intros sy Hsy Hnz x Hx. unfold tabdec_chk in Hc. rewrite forallb_forall in Hc.
  specialize (Hc (Z.to_nat sy)). rewrite Z2Nat.id in Hc by lia.
  assert (Hin : In (Z.to_nat sy) (seq 0 (length lens))).
  { apply in_seq. rewrite Zlength_correct in Hsy. lia. }
  specialize (Hc Hin). cbv zeta in Hc.
  apply Z.eqb_neq in Hnz. rewrite Hnz in Hc. simpl orb in Hc.
  repeat rewrite andb_true_iff in Hc. destruct Hc as [[[[H0 H1] H2] H3] Hall].
  apply Z.ltb_lt in H0. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3.
  rewrite forallb_forall in Hall.
  set (len := Znth sy lens) in *. set (rev := ref.reverse_bits (code lens sy) len) in *.
  assert (H1' : 0 < 2 ^ (root - len)) by (apply Z.pow_pos_nonneg; lia).
  pose proof (Z.mod_pos_bound x (2 ^ (root - len)) H1') as Hm.
  specialize (Hall (Z.to_nat (x mod 2 ^ (root - len)))).
  rewrite Z2Nat.id in Hall by lia.
  assert (Hin2 : In (Z.to_nat (x mod 2 ^ (root - len))) (seq 0 (Z.to_nat (2 ^ (root - len))))).
  { apply in_seq. lia. }
  specialize (Hall Hin2).
  repeat rewrite andb_true_iff in Hall. destruct Hall as [[Hl Hb] Hs].
  apply Z.eqb_eq in Hb. apply negb_true_iff in Hl.
  unfold twalk. rewrite tabdec_pat_mod by lia. rewrite Htab, Hl.
  eexists _, _. split; [rewrite Hb; reflexivity | exact Hs].
Qed.

Lemma tabdec_chk_lenfix : tabdec_chk lenfix_list 9 LENS fixed_ll = true.
Proof. vm_compute. reflexivity. Qed.

Lemma tabdec_chk_distfix : tabdec_chk distfix_list 5 DISTS fixed_dl = true.
Proof. vm_compute. reflexivity. Qed.

(* partial reads on a table without links: a pattern agreeing with code sy on b < len bits reaches an entry
   of more than b bits *)
Definition tabdec_revs (lens: list Z) : list (Z * Z) :=
  map (fun n => let sy := Z.of_nat n in let len := Znth sy lens in (len, ref.reverse_bits (code lens sy) len))
      (seq 0 (length lens)).

Definition tabdec_pchk (tbl: list entry) (root: Z) (lens: list Z) : bool :=
  let rv := tabdec_revs lens in
  forallb (fun n => let i := Z.of_nat n in let e := Znth i tbl in
    negb (ref.is_link (e_op e)) &&
    forallb (fun lr => let '(len, rev) := lr in
      forallb (fun bn => let b := Z.of_nat bn in negb (i mod 2 ^ b =? rev mod 2 ^ b) || (b <? e_bits e))
        (seq 0 (Z.to_nat len))) rv)
    (seq 0 (Z.to_nat (2 ^ root))).

Lemma tdc_mod_mod : forall x r b, 0 <= b <= r -> x mod 2 ^ r mod 2 ^ b = x mod 2 ^ b.
Proof.
  intros. rewrite <- !Z.land_ones by lia. rewrite <- Z.land_assoc. f_equal.
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, !Z.testbit_ones_nonneg by lia.
  destruct (Z.ltb_spec n r), (Z.ltb_spec n b); try lia; reflexivity.
Qed.

Lemma tabdec_pchk_ok : forall tbl root lens s t,
  1 <= root <= 15 -> (forall i, tab_entry lenfix_list distfix_list s t i = Znth i tbl) ->
  (forall sy, 0 <= sy < Zlength lens -> Znth sy lens <= root) ->
  tabdec_pchk tbl root lens = true -> td_part s t root lens.
Proof.
  intros tbl root lens s t Hroot Htab Hle Hc. intros sy Hsy Hnz b pat Hb Hp Hpm. cbv zeta.
  unfold tabdec_pchk in Hc. cbv zeta in Hc. rewrite forallb_forall in Hc.
  assert (Hpos: 0 < 2 ^ root) by (apply Z.pow_pos_nonneg; lia).
  pose proof (Z.mod_pos_bound pat (2 ^ root) Hpos) as Hm.
  specialize (Hc (Z.to_nat (pat mod 2 ^ root)) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in Hc by lia. rewrite Htab. left.
  apply andb_prop in Hc. destruct Hc as [_ Hc]. rewrite forallb_forall in Hc.
  specialize (Hc (Znth sy lens, ref.reverse_bits (code lens sy) (Znth sy lens))).
  assert (Hin: In (Znth sy lens, ref.reverse_bits (code lens sy) (Znth sy lens)) (tabdec_revs lens)).
  { unfold tabdec_revs. apply in_map_iff. exists (Z.to_nat sy). split.
    - cbv zeta. rewrite Z2Nat.id by lia. reflexivity.
    - apply in_seq. rewrite Zlength_correct in Hsy. lia. }
  specialize (Hc Hin). rewrite forallb_forall in Hc.
  specialize (Hc (Z.to_nat b) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in Hc by lia.
  assert (Eb: pat mod 2 ^ root mod 2 ^ b = pat mod 2 ^ b).
  { pose proof (Hle sy Hsy). apply tdc_mod_mod. lia. }
  rewrite Eb, Hpm, Z.eqb_refl in Hc. cbn [negb orb] in Hc. apply Z.ltb_lt. exact Hc.
Qed.

Lemma tabdec_nl_fix : forall tbl root s t type,
  (forall i, tab_entry lenfix_list distfix_list s t i = Znth i tbl) -> type <> CODES -> td_nl s t root type.
Proof. intros. intro. contradiction. Qed.

Lemma tabdec_pchk_lenfix : tabdec_pchk lenfix_list 9 fixed_ll = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma tabdec_pchk_distfix : tabdec_pchk distfix_list 5 fixed_dl = true.
Proof. vm_compute. reflexivity. Qed.

Lemma tabdec_fixed : forall s, tdec s TLenfix 9 LENS fixed_ll /\ tdec s TDistfix 5 DISTS fixed_dl.
Proof.
  intro s. split.
  - destruct (tabdec_chk_ok lenfix_list 9 LENS fixed_ll s TLenfix ltac:(lia) ltac:(reflexivity) tabdec_chk_lenfix)
      as [R F].
    apply tdec_intro; auto.
    + apply (tabdec_pchk_ok lenfix_list); [lia | reflexivity | | exact tabdec_pchk_lenfix].
      intros sy Hsy. assert (Hc: forallb (fun l => l <=? 9) fixed_ll = true) by (vm_compute; reflexivity).
      rewrite forallb_forall in Hc. apply Z.leb_le, Hc, Znth_In. exact Hsy.
    + apply (tabdec_nl_fix lenfix_list); [reflexivity | unfold LENS, CODES; lia].
  - destruct (tabdec_chk_ok distfix_list 5 DISTS fixed_dl s TDistfix ltac:(lia) ltac:(reflexivity) tabdec_chk_distfix)
      as [R F].
    apply tdec_intro; auto.
    + apply (tabdec_pchk_ok distfix_list); [lia | reflexivity | | exact tabdec_pchk_distfix].
      intros sy Hsy. assert (Hc: forallb (fun l => l <=? 5) fixed_dl = true) by (vm_compute; reflexivity).
      rewrite forallb_forall in Hc. apply Z.leb_le, Hc, Znth_In. exact Hsy.
    + apply (tabdec_nl_fix distfix_list); [reflexivity | unfold DISTS, CODES; lia].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* (2) fact_decode (inftrees facts.v) for ANY following bits x >= 0, not only x < 2^(longest - len) *)

Require Zlib.proof.inftrees.fact_result Zlib.proof.inftrees.model_inv Zlib.proof.inftrees.decode_defs
  Zlib.proof.inftrees.decode_step Zlib.proof.inftrees.decode_run Zlib.proof.inftrees.decode_walk
  Zlib.proof.inftrees.part_decode Zlib.proof.inftrees.part_sorted Zlib.proof.inftrees.part_rfc
  Zlib.proof.inftrees.part_bits Zlib.proof.inftrees.part_subbits.

Module TabDecWalk.
Import Zlib.proof.inftrees.facts Zlib.proof.inftrees.fact_result Zlib.proof.inftrees.model_inv
  Zlib.proof.inftrees.decode_defs Zlib.proof.inftrees.decode_step Zlib.proof.inftrees.decode_run
  Zlib.proof.inftrees.decode_walk Zlib.proof.inftrees.part_decode.

Lemma dwalk_any : forall type lens W ls root old used t,
  dhyps type lens W ls root old -> bits_stmt ->
  (forall j b, 0 <= j < Zlength ls -> is_link (e_op (sym_entry type (Znth j W) b)) = false) ->
  dfinal type W ls root used t ->
  forall j x, 0 <= j < Zlength ls -> 0 <= x ->
  walk t used root (Z.lor (dhuff ls j) (Z.shiftl x (Znth j ls)))
    = Some (e_op (sym_entry type (Znth j W) 0), e_val (sym_entry type (Znth j W) 0), Znth j ls).
Proof.
  intros type lens W ls root old used t Hd Hbits Hnl Hf j x Hj Hx.
  destruct Hd as (Hrange & Hsorted & HN & HWls & HWr & Hroot & Hk & Hinc & Htype & Hcodes & Hcap & Hcap0 & Hold & Hone).
  destruct Hf as (Hfl & Hused & Hsub & _).
  destruct (Hfl j Hj) as [[Fs Fl] Lk].
  pose proof (l_range ls Hrange j Hj) as Hl.
  pose proof (root_range ls root Hrange HN Hroot) as Hr.
  set (l := Znth j ls) in *.
  set (h := dhuff ls j) in *.
  destruct Hbits as (B1 & B2 & B3 & B4 & B5) eqn:EB.
  assert (Hh: 0 <= h < 2 ^ l) by (apply B1; lia).
  rewrite dw_lor_add by lia.
  unfold walk. rewrite dw_mask by lia.
  destruct (Z_le_gt_dec l root) as [Hs|Hlong].
  - (* short code *)
    rewrite dw_split_mod by lia.
    set (k := x mod 2 ^ (root - l)).
    assert (Hk0: 0 <= k < 2 ^ (root - l)) by (apply Z.mod_pos_bound, Z.pow_pos_nonneg; lia).
    assert (HP: 2 ^ root = 2 ^ l * 2 ^ (root - l)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (Hi: h + k * 2 ^ l < 2 ^ root) by (rewrite HP; pose proof (dw_mix_lt h k (2 ^ l) (2 ^ (root - l)) Hh Hk0); lia).
    destruct (used <=? h + k * 2 ^ l) eqn:E; [apply Z.leb_le in E; lia|].
    rewrite (Fs Hs k Hk0). rewrite (Hnl j l Hj).
    rewrite dw_sym_op, dw_sym_val, dw_sym_bits. reflexivity.
  - (* long code *)
    assert (Hlt: root < l) by lia. clear Hlong. rename Hlt into Hlong.
    assert (HPl: 2 ^ l = 2 ^ (l - root) * 2 ^ root) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (HPr: 0 < 2 ^ root) by (apply Z.pow_pos_nonneg; lia).
    assert (HPlr: 0 < 2 ^ (l - root)) by (apply Z.pow_pos_nonneg; lia).
    assert (Ei: (h + x * 2 ^ l) mod 2 ^ root = reverse_bits (pfx ls root j) root).
    { replace (h + x * 2 ^ l) with (h + (x * 2 ^ (l - root)) * 2 ^ root) by (rewrite HPl; ring).
      rewrite Z.mod_add by lia. rewrite <- dw_mask by lia.
      unfold h, dhuff, dcode. apply (huff_mask ls root Hrange HN Hroot Hbits j Hj). lia. }
    pose proof (pfx_range ls root Hrange HN Hroot Hk j Hj) as Hpr.
    assert (Hi: 0 <= reverse_bits (pfx ls root j) root < 2 ^ root) by (apply B1; lia).
    rewrite Ei.
    destruct (used <=? reverse_bits (pfx ls root j) root) eqn:E; [apply Z.leb_le in E; lia|].
    rewrite (Lk Hlong). unfold dlink. cbn [e_op e_bits e_val].
    pose proof (gmax_long ls root Hrange j Hj Hlong) as Hg.
    pose proof (Hsub j Hj Hlong) as Hsj.
    set (g := gmax ls root (pfx ls root j)) in *.
    set (nx := dnxt ls root (pfx ls root j)) in *.
    rewrite dw_is_link_small by (unfold MAXBITS in *; lia).
    replace (root + (g - root)) with g by lia.
    destruct (MAXBITS <? g) eqn:E2; [apply Z.ltb_lt in E2; lia|].
    rewrite dw_mask by lia. rewrite dw_split_mod by lia.
    set (k := x mod 2 ^ (g - l)).
    assert (Hk0: 0 <= k < 2 ^ (g - l)) by (apply Z.mod_pos_bound, Z.pow_pos_nonneg; lia).
    assert (Ej: Z.shiftr (h + k * 2 ^ l) root = Z.shiftr h root + k * 2 ^ (l - root)).
    { rewrite !Z.shiftr_div_pow2 by lia. rewrite HPl, Z.mul_assoc, Z.div_add by lia. reflexivity. }
    rewrite Ej.
    assert (Hhr: Z.shiftr h root < 2 ^ (l - root)).
    { rewrite Z.shiftr_div_pow2 by lia. apply Z.div_lt_upper_bound; lia. }
    assert (Hhr0: 0 <= Z.shiftr h root) by (apply Z.shiftr_nonneg; lia).
    assert (HPg: 2 ^ (g - root) = 2 ^ (g - l) * 2 ^ (l - root)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    destruct (used <=? nx + (Z.shiftr h root + k * 2 ^ (l - root))) eqn:E3; [apply Z.leb_le in E3;
      pose proof (dw_mix_lt _ _ _ _ (conj Hhr0 Hhr) Hk0); lia|].
    rewrite Z.add_assoc, (Fl Hlong k Hk0). rewrite (Hnl j (l - root) Hj).
    rewrite dw_sym_op, dw_sym_val, dw_sym_bits. f_equal. f_equal. lia.
Qed.

Lemma walk_any : forall type lens req old root used t,
  inputs_ok type lens req -> cap_ok type lens req (Zlength old) -> Forall entry_ok old ->
  (type = CODES -> Zlength lens <= 19) ->
  inflate_table_model type lens req old = ROk root used t ->
  forall s, 0 <= s < Zlength lens -> Znth s lens <> 0 -> forall x, 0 <= x ->
  exists op val,
    walk t used root (Z.lor (reverse_bits (rfc_code lens s) (Znth s lens)) (Z.shiftl x (Znth s lens)))
      = Some (op, val, Znth s lens) /\
    means_symbol type s op val = true.
Proof.
  pose proof part_sorted.sorted_ok2 as Hsorted. pose proof part_rfc.rfc_ok2 as Hrfc.
  pose proof part_bits.bits_ok2 as Hbits. pose proof part_subbits.subbits_ok2 as Hsub.
  intros type lens req old root used t Hin Hcap Hold H19 Hmodel.
  pose proof Hin as Hin'. destruct Hin' as (Ht & Hcodes & Hl & Hreq).
  unfold inflate_table_model in Hmodel.
  destruct (maxlen lens =? 0) eqn:Emx.
  - apply Z.eqb_eq in Emx. intros s Hs Hnz. exfalso. pose proof (Znth_le_maxlen lens s Hs).
    rewrite Forall_forall in Hl. pose proof (Hl (Znth s lens) (Znth_In _ _ Hs)). lia.
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
    destruct (Hsorted lens Hl) as (SW & Sr & Ss & Sin & Scnt & Scl & Sk & Snil & Sends).
    assert (Hne: sl lens <> []) by (intro E; apply Snil in E; contradiction).
    destruct (Sends Hne) as (E0 & EN).
    assert (HWl: Zlength (sl lens) = Zlength (sorted_syms lens)) by (unfold sl; apply Zlength_map).
    intros s0 Hs0 Hnz x Hx.
    destruct (In_Znth _ _ (Sin s0 Hs0 Hnz)) as (j & Hj & Ej).
    assert (Hlj: Znth j (sl lens) = Znth s0 lens) by (unfold sl; rewrite Znth_map by lia; congruence).
    assert (Hcode: rfc_code lens s0 = dcode (sl lens) j).
    { pose proof (Hrfc lens Hl j ltac:(lia)) as R. rewrite Ej, Hlj in R. unfold dcode. rewrite Hlj, <- R.
      rewrite Z.div_mul; auto. apply Z.pow_nonzero; [lia|].
      rewrite Forall_forall in Hl. pose proof (Hl _ (Znth_In _ _ Hs0)). unfold MAXBITS in *. lia. }
    assert (Hnl: forall j' b, 0 <= j' < Zlength (sl lens) ->
               is_link (e_op (sym_entry type (Znth j' (sorted_syms lens)) b)) = false).
    { intros. rewrite Forall_forall in SW. pose proof (SW _ (Znth_In j' (sorted_syms lens) ltac:(lia))).
      apply (sym_means type _ b); auto; lia. }
    pose proof (dwalk_any type lens (sorted_syms lens) (sl lens) (root_of req lens) old (s_used s) (finish s)
                  Hd Hbits Hnl Hf j x ltac:(lia) Hx) as Hw.
    rewrite Hlj in Hw.
    unfold dhuff in Hw. rewrite Hlj, <- Hcode, Ej in Hw.
    do 2 eexists. split; [exact Hw|].
    rewrite Forall_forall in SW. pose proof (SW _ (Znth_In j (sorted_syms lens) ltac:(lia))). try rewrite Ej in H.
    apply (sym_means type s0 0); auto; lia.
Qed.
End TabDecWalk.

Lemma tabdec_walk : forall type lens req old root used t,
  inputs_ok type lens req -> cap_ok type lens req (Zlength old) -> Forall entry_ok old ->
  (type = CODES -> Zlength lens <= 19) ->
  inflate_table_model type lens req old = ROk root used t ->
  forall s, 0 <= s < Zlength lens -> Znth s lens <> 0 -> forall x, 0 <= x ->
  exists op val,
    walk t used root (Z.lor (reverse_bits (rfc_code lens s) (Znth s lens)) (Z.shiftl x (Znth s lens)))
      = Some (op, val, Znth s lens) /\
    means_symbol type s op val = true.
Proof.
  exact TabDecWalk.walk_any.
Qed.


(* ---------------------------------------------------------------------------------------------- *)
(* (3) Format's canonical codes and Kraft sum are the reference's                                 *)

Lemma tdc_filter_eq : forall (xs: list Z) l,
  Zlength (filter (fun x => x =? l) xs) = count_len xs l.
Proof.
  intros. unfold count_len. f_equal. apply filter_ext. intros. apply Z.eqb_sym.
Qed.

Lemma tdc_next_code_loop : forall lens k j,
  next_code_loop k (Z.of_nat j + 1) (next_code_n lens j) lens = next_code_n lens (j + k).
Proof.
  induction k; intros j.
  - cbn. rewrite Nat.add_0_r. reflexivity.
  - cbn [next_code_loop]. replace (Z.of_nat j + 1 - 1) with (Z.of_nat j) by lia.
    replace (Z.shiftl (next_code_n lens j + bl_count lens (Z.of_nat j)) 1) with (next_code_n lens (S j)).
    + replace (Z.of_nat j + 1 + 1) with (Z.of_nat (S j) + 1) by lia. rewrite IHk.
      f_equal. lia.
    + cbn [next_code_n]. rewrite Z.shiftl_mul_pow2 by lia. f_equal. f_equal.
      unfold count_of, bl_count. destruct (Z.of_nat j =? 0); auto. apply tdc_filter_eq.
Qed.

Lemma tdc_code : forall lens s, 0 <= Znth s lens -> Znth s lens <> 0 -> code lens s = rfc_code lens s.
Proof.
  intros lens s H0 Hnz. unfold code, rfc_code.
  destruct (Znth s lens =? 0) eqn:E; [apply Z.eqb_eq in E; contradiction|].
  rewrite tdc_filter_eq. f_equal. unfold next_code.
  pose proof (tdc_next_code_loop lens (Z.to_nat (Znth s lens)) 0) as X. cbn in X. exact (eq_sym X).
Qed.

Lemma tdc_kraft_fold : forall lens a, Forall (fun l => 0 <= l <= MAXBITS) lens ->
  fold_left (fun k l => if l =? 0 then k else k + Z.shiftl 1 (MAXBITS - l)) lens a = a + kraft_sum lens.
Proof.
  induction lens as [|x xs IH]; intros a H; cbn [fold_left kraft_sum fold_right].
  - lia.
  - inversion H; subst. rewrite IH by auto. fold (kraft_sum xs).
    destruct (x =? 0); [lia|]. rewrite Z.shiftl_1_l. unfold MAXBITS, MAXLEN. lia.
Qed.

Lemma tdc_kraft : forall lens, Forall (fun l => 0 <= l <= MAXBITS) lens -> kraft lens = kraft_sum lens.
Proof. intros. unfold kraft. rewrite tdc_kraft_fold by auto. lia. Qed.

Lemma tdc_maxlen_nonneg : forall lens, 0 <= maxlen lens.
Proof. induction lens; unfold maxlen in *; cbn [fold_right]; lia. Qed.

Lemma tdc_nused0 : forall lens, nused lens = 0 -> kraft_sum lens = 0 /\ maxlen lens = 0.
Proof.
  induction lens as [|x xs IH]; intros Hn; [split; reflexivity|].
  unfold nused in Hn. cbn [filter] in Hn. unfold kraft_sum, maxlen; cbn [fold_right].
  fold (kraft_sum xs) (maxlen xs).
  destruct (x =? 0) eqn:E; cbn [negb] in Hn.
  - apply Z.eqb_eq in E; subst. destruct (IH Hn) as [A B]. rewrite A, B. lia.
  - rewrite Zlength_cons in Hn. pose proof (Zlength_nonneg (filter (fun l => negb (l =? 0)) xs)). lia.
Qed.

Lemma tdc_single : forall lens, Forall (fun l => 0 <= l <= MAXBITS) lens -> nused lens = 1 ->
  kraft_sum lens = 2 ^ (MAXLEN - maxlen lens) /\ 1 <= maxlen lens.
Proof.
  induction lens as [|x xs IH]; intros H Hn; [discriminate|].
  inversion H; subst.
  unfold nused in Hn. cbn [filter] in Hn. unfold kraft_sum, maxlen; cbn [fold_right].
  fold (kraft_sum xs) (maxlen xs).
  destruct (x =? 0) eqn:E; cbn [negb] in Hn.
  - apply Z.eqb_eq in E; subst. destruct (IH H3 Hn) as [A B]. rewrite A. split; [f_equal|]; lia.
  - apply Z.eqb_neq in E. rewrite Zlength_cons in Hn.
    destruct (tdc_nused0 xs ltac:(unfold nused; lia)) as [A B]. rewrite A, B.
    replace (Z.max x 0) with x by lia. split; [lia|]. lia.
Qed.

Lemma tdc_maxlen_le : forall lens m, 0 <= m -> Forall (fun l => l <= m) lens -> maxlen lens <= m.
Proof.
  induction lens as [|x xs IH]; intros m Hm H; unfold maxlen in *; cbn [fold_right]; [lia|].
  inversion H; subst. specialize (IH m Hm H3). lia.
Qed.

(* expected_valid = 0 for the codes inflate accepts *)
Lemma tdc_valid : forall type lens, Forall (fun l => 0 <= l <= MAXBITS) lens ->
  complete lens \/ (type <> CODES /\ single lens) \/ empty_code lens -> expected_valid type lens = 0.
Proof.
  intros type lens Hr Hc. unfold expected_valid.
  rewrite <- Zlib.proof.inftrees.fact_result.maxlen_longest, tdc_kraft by auto.
  unfold GP_KRAFT_ONE. destruct Hc as [Hc|[[Ht Hc]|Hc]].
  - unfold complete in Hc. rewrite Hc. destruct (maxlen lens =? 0); reflexivity.
  - destruct Hc as [Hn Hk]. destruct (tdc_single lens Hr Hn) as [A B].
    assert (Hm: maxlen lens <= MAXBITS) by (apply tdc_maxlen_le; [unfold MAXBITS; lia|];
      eapply Forall_impl; [|exact Hr]; cbv beta; lia).
    assert (E1: maxlen lens = 1).
    { destruct (Z.eq_dec (maxlen lens) 1); auto. exfalso.
      assert (2 ^ (MAXLEN - maxlen lens) <= 2 ^ 13) by (apply Z.pow_le_mono_r; unfold MAXLEN; lia).
      rewrite <- A, Hk in H. unfold MAXLEN in H. cbn in H. lia. }
    rewrite E1, Hk. unfold MAXLEN. cbn.
    destruct (type =? CODES) eqn:E; [apply Z.eqb_eq in E; contradiction|]. reflexivity.
  - destruct (tdc_nused0 lens Hc) as [_ B]. rewrite B. reflexivity.
Qed.

Lemma tdc_root : forall lens req, Forall (fun l => 0 <= l <= MAXBITS) lens -> 1 <= req <= 15 ->
  1 <= expected_root req lens <= 15.
Proof.
  intros lens req Hr Hq. unfold expected_root.
  rewrite <- Zlib.proof.inftrees.fact_result.maxlen_longest.
  destruct (maxlen lens =? 0) eqn:E; [lia|]. apply Z.eqb_neq in E.
  rewrite <- Zlib.proof.inftrees.fact_result.minlen_shortest by auto.
  destruct (Zlib.proof.inftrees.fact_result.minlen_range lens Hr) as [R1 R2].
  pose proof (tdc_maxlen_nonneg lens).
  assert (Hm: maxlen lens <= MAXBITS) by (apply tdc_maxlen_le; [unfold MAXBITS; lia|];
      eapply Forall_impl; [|exact Hr]; cbv beta; lia).
  unfold MAXBITS in *.
  destruct (maxlen lens <? req); destruct (_ <? minlen lens); lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* (4) inflate's walk (twalk) on a table in the state is the reference walk                       *)

Lemma tdc_mask : forall pat r, 0 <= r -> Z.land pat (Z.shiftl 1 r - 1) = pat mod 2 ^ r.
Proof.
  intros. rewrite Z.shiftl_1_l. replace (2 ^ r - 1) with (Z.ones r) by (rewrite Z.ones_equiv; lia).
  apply Z.land_ones. lia.
Qed.

Lemma tdc_shiftr_mod : forall pat b o, 0 <= b -> 0 <= o ->
  Z.shiftr (pat mod 2 ^ (b + o)) b = Z.shiftr pat b mod 2 ^ o.
Proof.
  intros. rewrite <- !Z.land_ones by lia. apply Z.bits_inj'. intros n Hn.
  rewrite Z.shiftr_spec, !Z.land_spec, Z.shiftr_spec by lia.
  rewrite (Z.testbit_ones_nonneg (b + o) (n + b)) by lia. rewrite (Z.testbit_ones_nonneg o n) by lia.
  destruct (Z.ltb_spec (n + b) (b + o)), (Z.ltb_spec n o); try lia; reflexivity.
Qed.

Lemma tdc_twalk : forall s' k t used root pat res, 0 <= root -> 0 <= pat -> Forall entry_ok t ->
  used <= Zlength t ->
  (forall i, 0 <= i < used -> Znth (k + i) (i_codes s') = Znth i t) ->
  walk t used root pat = Some res -> twalk s' (TCodes k) root pat = Some res.
Proof.
  intros s' k t used root pat res Hr Hp Hok Hu Ht W. unfold walk in W. unfold twalk, tab_entry.
  rewrite tdc_mask in W by lia.
  assert (Hm: 0 <= pat mod 2 ^ root) by (apply Z.mod_pos_bound, Z.pow_pos_nonneg; lia).
  destruct (used <=? pat mod 2 ^ root) eqn:E1; [discriminate|]. apply Z.leb_gt in E1.
  rewrite Ht by lia.
  pose proof (Forall_Znth _ t (pat mod 2 ^ root) ltac:(lia) Hok) as He.
  set (e := Znth (pat mod 2 ^ root) t) in *. cbv zeta in W.
  destruct (is_link (e_op e)) eqn:L; [|exact W].
  destruct (MAXBITS <? e_bits e + e_op e); [discriminate|].
  destruct He as (H1 & H2 & H3).
  rewrite tdc_mask, tdc_shiftr_mod in W by lia.
  assert (Hm2: 0 <= Z.shiftr pat (e_bits e) mod 2 ^ e_op e) by (apply Z.mod_pos_bound, Z.pow_pos_nonneg; lia).
  destruct (used <=? e_val e + Z.shiftr pat (e_bits e) mod 2 ^ e_op e) eqn:E2; [discriminate|].
  apply Z.leb_gt in E2. rewrite Ht by lia. exact W.
Qed.

Lemma tdc_rev_nonneg : forall c n, 0 <= n -> 0 <= reverse_bits c n.
Proof. intros. destruct Zlib.proof.inftrees.part_bits.bits_ok2 as [B _]. apply B; auto. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* (5) one call of inflate_table (call_table) on codes inflate accepts                            *)

Lemma tdc_fact_result : fact_result.
Proof.
  exact (Zlib.proof.inftrees.part_result.fact_result_ok Zlib.proof.inftrees.part_sorted.sorted_ok2
           Zlib.proof.inftrees.part_rfc.rfc_ok2 Zlib.proof.inftrees.part_bits.bits_ok2
           Zlib.proof.inftrees.part_subbits.subbits_ok2
           (Zlib.proof.inftrees.part_size.size_ok2 Zlib.proof.inftrees.part_sorted.sorted_ok2
              Zlib.proof.inftrees.part_rfc.rfc_ok2 Zlib.proof.inftrees.part_bits.bits_ok2)).
Qed.

Lemma tdc_fact_enough : fact_enough.
Proof.
  exact (Zlib.proof.inftrees.part_enough.fact_enough_ok Zlib.proof.inftrees.part_sorted.sorted_ok2
           Zlib.proof.inftrees.part_rfc.rfc_ok2 Zlib.proof.inftrees.part_bits.bits_ok2
           (Zlib.proof.inftrees.part_size.size_ok2 Zlib.proof.inftrees.part_sorted.sorted_ok2
              Zlib.proof.inftrees.part_rfc.rfc_ok2 Zlib.proof.inftrees.part_bits.bits_ok2)).
Qed.

Require Zlib.proof.inflate.Tables Zlib.proof.inflate.Cover2.

Module TabDecNoLink.
Import Zlib.proof.inftrees.facts Zlib.proof.inftrees.fact_result Zlib.proof.inftrees.model_inv
  Zlib.proof.inftrees.decode_defs Zlib.proof.inftrees.decode_step Zlib.proof.inftrees.decode_run
  Zlib.proof.inftrees.part_decode.

Lemma islink_codes : forall op, Zlib.proof.inflate.Tables.islink CODES op = is_link op.
Proof. intros. reflexivity. Qed.

Lemma nolink_final : forall W ls root used t,
  Forall (fun l => 1 <= l <= MAXBITS) ls ->
  (forall a b, 0 <= a -> a <= b < Zlength ls -> Znth a ls <= Znth b ls) ->
  0 < Zlength ls -> 1 <= root <= MAXBITS -> ksum ls <= 2 ^ MAXBITS -> bits_stmt ->
  Znth (Zlength ls - 1) ls <= root ->
  (forall j b, 0 <= j < Zlength ls -> is_link (e_op (sym_entry CODES (Znth j W) b)) = false) ->
  dfinal CODES W ls root used t ->
  forall i, 0 <= i < 2 ^ root -> is_link (e_op (Znth i t)) = false.
Proof.
  intros W ls root used t Hr Hs HN Hroot Hk Hbits Hmax Hsym Hf i Hi.
  destruct Hf as (Hfl & Hu1 & Hu2 & Hinc).
  pose proof Hbits as (B1 & B2 & B3 & B4 & B5).
  pose proof (Cover2.pow2_pos root ltac:(lia)).
  destruct (Z_lt_le_dec (ksum ls) (2 ^ MAXBITS)) as [Hlt|Hge].
  - destruct (Hinc Hlt) as (HN1 & H01 & Er & Eu & Ht1). subst root used.
    change (2 ^ 1) with 2 in Hi.
    assert (i = 0 \/ i = 1) as [-> | ->] by lia.
    + destruct (Hfl 0 ltac:(lia)) as [[F _] _].
      specialize (F ltac:(lia) 0 ltac:(rewrite H01; simpl; lia)).
      assert (Hdh: dhuff ls 0 = 0) by (unfold dhuff, dcode; rewrite kpre_0, Zdiv_0_l; apply reverse_bits_0).
      rewrite Hdh, H01 in F. change (0 + 0 * 2 ^ 1) with 0 in F. rewrite F.
      apply Hsym; lia.
    + rewrite Ht1. reflexivity.
  - assert (Hfull: ksum ls = 2 ^ MAXBITS) by lia.
    destruct (Cover2.locate ls Hr Hs Hfull Hbits root i ltac:(lia) Hi) as (j & Hj & Hm).
    set (l := Znth j ls) in *. pose proof (ls_range ls Hr j Hj) as Hl. fold l in Hl.
    destruct (Hfl j Hj) as [[Fs Fl] Lk]. fold l in Fs, Fl, Lk.
    assert (Hshort: l <= root) by (pose proof (Hs j (Zlength ls - 1) ltac:(lia) ltac:(lia)); unfold l; lia).
    pose proof (Cover2.pow2_pos l ltac:(lia)).
    assert (Hdh: dhuff ls j = i mod 2 ^ l).
    { unfold dhuff, dcode. fold l. rewrite (Hm l) by lia. apply B3; [lia|]. apply Z.mod_pos_bound; lia. }
    assert (Hk': 0 <= i / 2 ^ l < 2 ^ (root - l)).
    { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
      rewrite <- Z.pow_add_r by lia. replace (l + (root - l)) with root by lia. lia. }
    specialize (Fs Hshort (i / 2 ^ l) Hk'). rewrite Hdh in Fs.
    replace (i mod 2 ^ l + i / 2 ^ l * 2 ^ l) with i in Fs
      by (pose proof (Z.div_mod i (2 ^ l) ltac:(lia)); lia).
    rewrite Fs. apply Hsym; lia.
Qed.

Lemma nolink : forall lens req old root used t,
  inputs_ok CODES lens req -> Zlength lens <= 19 -> cap_ok CODES lens req (Zlength old) -> Forall entry_ok old ->
  inflate_table_model CODES lens req old = ROk root used t ->
  forall i, 0 <= i < 2 ^ root -> is_link (e_op (Znth i t)) = false.
Proof.
  intros lens req old root used t Hin H19 Hcap Hold Hmodel.
  pose proof part_sorted.sorted_ok2 as Hsorted.
  pose proof part_bits.bits_ok2 as Hbits.
  pose proof part_subbits.subbits_ok2 as Hsub.
  pose proof Hin as (Ht & Hcodes & Hl & Hreq).
  unfold inflate_table_model in Hmodel.
  destruct (maxlen lens =? 0) eqn:Emx.
  - inversion Hmodel; subst root used t; clear Hmodel.
    intros i Hi. change (2 ^ 1) with 2 in Hi.
    assert (Hfin: Znth i (upd_Znth 1 (upd_Znth 0 old (invalid_entry 1)) (invalid_entry 1)) = invalid_entry 1).
    { destruct Hcap as (Hc & _). destruct (Hc eq_refl) as (_ & Hc2 & _).
      assert (i = 0 \/ i = 1) as [-> | ->] by lia.
      - rewrite upd_Znth_diff by (rewrite ?upd_Znth_Zlength; lia). rewrite upd_Znth_same by lia. reflexivity.
      - rewrite upd_Znth_same by (rewrite ?upd_Znth_Zlength; lia). reflexivity. }
    rewrite Hfin. reflexivity.
  - apply Z.eqb_neq in Emx.
    destruct (left_final (counts lens)) as [lft|] eqn:Eleft; [|discriminate].
    destruct ((0 <? lft) && ((CODES =? CODES) || negb (maxlen lens =? 1))) eqn:Etest; [discriminate|].
    destruct (over CODES (Z.shiftl 1 (root_of req lens))) eqn:Eover; [discriminate|].
    assert (Hd: dhyps CODES lens (sorted_syms lens) (sl lens) (root_of req lens) old)
      by (eapply dsetup_ok; eauto; intros; lia).
    assert (Hfin: exists s, used = s_used s /\ t = finish s /\ root = root_of req lens /\
      (run CODES lens (sorted_syms lens) (root_of req lens) (maxlen lens) (length (sorted_syms lens))
         (init_state lens (root_of req lens) old) = Break s \/
       run CODES lens (sorted_syms lens) (root_of req lens) (maxlen lens) (length (sorted_syms lens))
         (init_state lens (root_of req lens) old) = Continue s)).
    { destruct (run CODES lens (sorted_syms lens) (root_of req lens) (maxlen lens) (length (sorted_syms lens))
                  (init_state lens (root_of req lens) old)) eqn:Er;
        inversion Hmodel; subst; eexists; eauto. }
    destruct Hfin as (s & -> & -> & -> & Hrun).
    destruct dstep_last_ok as [Hstep Hlast].
    pose proof (drun_ok CODES lens req old s Hsorted Hbits Hsub Hstep Hlast Hl Emx Hd Hrun) as Hf.
    destruct Hd as (Hrange & Hsl & HN & HWls & HWr & Hroot & Hk & _ & _ & Hcd & _).
    destruct (Hsorted lens Hl) as (SW & _).
    assert (HWl: Zlength (sl lens) = Zlength (sorted_syms lens)) by (unfold sl; apply Zlength_map).
    apply (nolink_final (sorted_syms lens) (sl lens) (root_of req lens) (s_used s) (finish s)); auto.
    + pose proof (ls_range _ Hrange 0 ltac:(lia)). pose proof (ls_range _ Hrange (Zlength (sl lens) - 1) ltac:(lia)).
      lia.
    + intros j b Hj. rewrite Forall_forall in SW.
      pose proof (SW _ (Znth_In j (sorted_syms lens) ltac:(lia))) as Hs.
      rewrite <- islink_codes. set (w := Znth j (sorted_syms lens)) in *. clearbody w.
      apply Cover2.sym_ok; unfold CODES, max_codes in *; cbn; try lia.
Qed.
End TabDecNoLink.

(* the code length code's table (all codes no longer than root = the longest length) has no links *)
Lemma tabdec_codes_nolink : forall lens req old root used t,
  inputs_ok CODES lens req -> Zlength lens <= 19 -> cap_ok CODES lens req (Zlength old) -> Forall entry_ok old ->
  inflate_table_model CODES lens req old = ROk root used t ->
  forall i, 0 <= i < 2 ^ root -> is_link (e_op (Znth i t)) = false.
Proof.
  exact TabDecNoLink.nolink.
Qed.

(* partial reads on a table inflate_table built *)
Lemma tdc_split : forall pat l, 0 <= pat -> 0 <= l -> pat = Z.lor (pat mod 2 ^ l) (Z.shiftl (Z.shiftr pat l) l).
Proof.
  intros pat l Hp Hl. apply Z.bits_inj'. intros n Hn. rewrite Z.lor_spec.
  destruct (Z.ltb_spec n l).
  - rewrite Z.mod_pow2_bits_low by lia. rewrite Z.shiftl_spec_low by lia. rewrite orb_false_r. reflexivity.
  - rewrite Z.mod_pow2_bits_high by lia. rewrite Z.shiftl_spec_high by lia. rewrite Z.shiftr_spec by lia.
    cbn [orb]. f_equal. lia.
Qed.

Lemma tdc_some_part : forall s' t root pat op val l' b, twalk s' t root pat = Some (op, val, l') -> b < l' ->
  let e := tab_entry lenfix_list distfix_list s' t (pat mod 2 ^ root) in
  b < e_bits e \/
  (ref.is_link (e_op e) = true /\
   b < e_bits e + e_bits (tab_entry lenfix_list distfix_list s' t (e_val e + Z.shiftr pat (e_bits e) mod 2 ^ e_op e))).
Proof.
  intros s' t root pat op val l' b H Hb. unfold twalk in H. cbv zeta in *.
  destruct (ref.is_link (e_op (tab_entry lenfix_list distfix_list s' t (pat mod 2 ^ root)))) eqn:L.
  - destruct (ref.is_link (e_op (tab_entry lenfix_list distfix_list s' t
      (e_val (tab_entry lenfix_list distfix_list s' t (pat mod 2 ^ root)) +
       Z.shiftr pat (e_bits (tab_entry lenfix_list distfix_list s' t (pat mod 2 ^ root))) mod
       2 ^ e_op (tab_entry lenfix_list distfix_list s' t (pat mod 2 ^ root)))))); [discriminate|].
    injection H; intros. right. split; [reflexivity|lia].
  - injection H; intros. left. lia.
Qed.

Lemma tdc_minlen_le : forall lens sy, 0 <= sy < Zlength lens -> Znth sy lens <> 0 -> minlen lens <= Znth sy lens.
Proof.
  induction lens as [|a r IH]; intros sy Hsy Hnz; [rewrite Zlength_nil in Hsy; lia|].
  rewrite Zlength_cons in Hsy. unfold minlen; cbn [fold_right]. fold (minlen r).
  destruct (Z.eq_dec sy 0) as [->|Hs].
  - rewrite Znth_0_cons in *. destruct (a =? 0) eqn:E; [apply Z.eqb_eq in E; contradiction|]. lia.
  - rewrite Znth_pos_cons in * by lia. specialize (IH (sy - 1) ltac:(lia) Hnz).
    destruct (a =? 0); lia.
Qed.

Lemma tdc_ms64 : forall type sy, (type = LENS /\ 0 <= sy < 286) \/ (type = DISTS /\ 0 <= sy < 30) ->
  means_symbol type sy 64 0 = false.
Proof.
  intros type sy H.
  assert (C1: forallb (fun n => negb (means_symbol LENS (Z.of_nat n) 64 0)) (seq 0 286) = true)
    by (vm_compute; reflexivity).
  assert (C2: forallb (fun n => negb (means_symbol DISTS (Z.of_nat n) 64 0)) (seq 0 30) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in C1, C2.
  destruct H as [[-> Hs]|[-> Hs]].
  - specialize (C1 (Z.to_nat sy) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in C1 by lia.
    apply negb_true_iff in C1. exact C1.
  - specialize (C2 (Z.to_nat sy) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in C2 by lia.
    apply negb_true_iff in C2. exact C2.
Qed.

Lemma tdc_islink : forall type op, 0 <= type <= 2 -> is_link op = true -> Zlib.proof.inflate.Tables.islink type op = true.
Proof.
  intros type op Ht H. unfold is_link in H. unfold Zlib.proof.inflate.Tables.islink.
  apply andb_prop in H. destruct H as [H1 H2]. rewrite H2, andb_true_r.
  destruct (type =? DISTS); auto.
Qed.

(* a complete code covers every pattern: some code is a prefix of it *)
Lemma tdc_cover : forall lens pat, Forall (fun l => 0 <= l <= MAXBITS) lens -> kraft lens = 2 ^ MAXBITS -> 0 <= pat ->
  exists sy, 0 <= sy < Zlength lens /\ Znth sy lens <> 0 /\
    pat mod 2 ^ Znth sy lens = reverse_bits (rfc_code lens sy) (Znth sy lens).
Proof.
  intros lens pat Hr Hk Hp.
  destruct (Zlib.proof.inftrees.part_sorted.sorted_ok2 lens Hr) as (SW & Sr & Ss & _ & _ & _ & Sk & _).
  pose proof Zlib.proof.inftrees.part_bits.bits_ok2 as Hbits.
  pose proof Hbits as (B1 & B2 & B3 & B4 & B5).
  set (ls := Zlib.proof.inftrees.fact_result.sl lens) in *.
  assert (Hfull: Zlib.proof.inftrees.fact_result.ksum ls = 2 ^ MAXBITS) by (rewrite Sk; exact Hk).
  set (P := pat mod 2 ^ MAXBITS).
  assert (HP: 0 <= P < 2 ^ MAXBITS) by (apply Z.mod_pos_bound; reflexivity).
  destruct (Zlib.proof.inflate.Cover2.locate ls Sr Ss Hfull Hbits MAXBITS P ltac:(unfold MAXBITS; lia) HP)
    as (j & Hj & Hm).
  assert (HWl: Zlength ls = Zlength (sorted_syms lens)) by (unfold ls, Zlib.proof.inftrees.fact_result.sl; apply Zlength_map).
  set (sy := Znth j (sorted_syms lens)).
  assert (Hj': 0 <= j < Zlength (sorted_syms lens)) by lia.
  assert (Hsy: 0 <= sy < Zlength lens) by (apply (Forall_Znth _ _ j Hj' SW)).
  assert (Hlj: Znth sy lens = Znth j ls)
    by (unfold ls, Zlib.proof.inftrees.fact_result.sl; rewrite Znth_map by lia; reflexivity).
  pose proof (Forall_Znth _ ls j Hj Sr) as Hl. cbv beta in Hl.
  exists sy. split; [exact Hsy|]. rewrite Hlj. split; [lia|].
  pose proof (Zlib.proof.inftrees.part_rfc.rfc_ok2 lens Hr j Hj) as R. fold ls sy in R.
  assert (Hc: rfc_code lens sy = Zlib.proof.inftrees.fact_result.kpre ls j / 2 ^ (MAXBITS - Znth j ls)).
  { rewrite <- R. rewrite Z.div_mul; auto. apply Z.pow_nonzero; unfold MAXBITS in *; lia. }
  rewrite Hc, (Hm (Znth j ls)) by (unfold MAXBITS in *; lia).
  assert (Hpm: P mod 2 ^ Znth j ls = pat mod 2 ^ Znth j ls) by (unfold P; apply tdc_mod_mod; unfold MAXBITS in *; lia).
  rewrite Hpm. symmetry. apply B3; [lia|]. apply Z.mod_pos_bound, Z.pow_pos_nonneg; lia.
Qed.

Lemma tdc_part : forall type lens req old root used t s' k,
  inputs_ok type lens req -> cap_ok type lens req (Zlength old) -> Forall entry_ok old ->
  (type = CODES -> Zlength lens <= 19) -> (type = LENS -> Zlength lens <= 286) -> (type = DISTS -> Zlength lens <= 30) ->
  inflate_table_model type lens req old = ROk root used t -> expected_valid type lens = 0 -> 1 <= req <= 15 ->
  (forall i, 0 <= i < used -> Znth (k + i) (i_codes s') = Znth i t) ->
  td_part s' (TCodes k) root lens.
Proof.
  intros type lens req old root used t s' k Hin Hcap Hold H19 H286 H30 EM Hv Hq Hk.
  pose proof (tdc_fact_result type lens req old Hin Hcap Hold) as FR.
  destruct (expected_call type lens req) as [[want r0] size] eqn:EC.
  assert (Er: r0 = expected_root req lens) by (unfold expected_call in EC; inversion EC; auto).
  rewrite EM in FR. destruct FR as (_ & Er0 & _ & Hu & _ & Lt & Ft & _).
  assert (Er1: root = expected_root req lens) by congruence. clear Er0 Er. rename Er1 into Er0.
  pose proof Hin as (Ht & _ & Hr & _).
  pose proof (tdc_root lens req Hr Hq) as Hroot. rewrite <- Er0 in Hroot.
  destruct (Zlib.proof.inflate.Cover2.cover2_proof type lens req old root used t Hin H19 Hcap Hold EM) as [TO _].
  assert (W: forall sy x, 0 <= sy < Zlength lens -> Znth sy lens <> 0 -> 0 <= x -> exists op val,
     twalk s' (TCodes k) root (Z.lor (reverse_bits (rfc_code lens sy) (Znth sy lens)) (Z.shiftl x (Znth sy lens)))
       = Some (op, val, Znth sy lens) /\ means_symbol type sy op val = true).
  { intros sy x Hsy Hnz Hx.
    destruct (tabdec_walk type lens req old root used t Hin Hcap Hold H19 EM sy Hsy Hnz x Hx) as (op & val & Wk & M).
    exists op, val. split; [|exact M].
    pose proof (Forall_Znth _ lens sy Hsy Hr) as Hl. cbv beta in Hl.
    apply (tdc_twalk s' k t used root); auto; try lia.
    apply Z.lor_nonneg. split; [apply tdc_rev_nonneg; lia|]. apply Z.shiftl_nonneg. lia. }
  assert (W2: forall sy pat, 0 <= sy < Zlength lens -> Znth sy lens <> 0 -> 0 <= pat ->
     pat mod 2 ^ Znth sy lens = reverse_bits (rfc_code lens sy) (Znth sy lens) ->
     exists op val, twalk s' (TCodes k) root pat = Some (op, val, Znth sy lens) /\ means_symbol type sy op val = true).
  { intros sy pat Hsy Hnz Hp Hm. pose proof (Forall_Znth _ lens sy Hsy Hr) as Hl. cbv beta in Hl.
    rewrite (tdc_split pat (Znth sy lens)) by lia. rewrite Hm. apply W; auto. apply Z.shiftr_nonneg; lia. }
  intros sy Hsy Hnz b pat Hb Hp Hpm.
  pose proof (Forall_Znth _ lens sy Hsy Hr) as Hl. cbv beta in Hl.
  rewrite tdc_code in Hpm by lia.
  pose proof (Zlib.proof.inftrees.part_decode.Znth_le_maxlen lens sy Hsy) as Hmx.
  unfold expected_valid in Hv. rewrite <- Zlib.proof.inftrees.fact_result.maxlen_longest, tdc_kraft in Hv by auto.
  unfold GP_KRAFT_ONE in Hv.
  destruct (maxlen lens =? 0) eqn:E0; [apply Z.eqb_eq in E0; lia|].
  destruct (32768 <? kraft_sum lens) eqn:E1; [discriminate|].
  destruct ((kraft_sum lens <? 32768) && ((type =? CODES) || negb (maxlen lens =? 1))) eqn:E2; [discriminate|].
  destruct (Z.ltb_spec (kraft_sum lens) 32768) as [Hinc|Hcomp].
  - (* a single code of length 1, root 1 *)
    rewrite andb_true_l, orb_false_iff in E2. destruct E2 as [E2a E2b].
    apply negb_false_iff, Z.eqb_eq in E2b. apply Z.eqb_neq in E2a.
    assert (Hl1: Znth sy lens = 1) by lia.
    assert (Hb0: b = 0) by lia. subst b.
    assert (Hr1: root = 1).
    { rewrite Er0. unfold expected_root. rewrite <- Zlib.proof.inftrees.fact_result.maxlen_longest, E2b.
      rewrite <- Zlib.proof.inftrees.fact_result.minlen_shortest by (auto; lia).
      pose proof (tdc_minlen_le lens sy Hsy Hnz).
      destruct (Zlib.proof.inftrees.fact_result.minlen_range lens Hr) as [M1 _].
      replace (1 =? 0) with false by reflexivity.
      destruct (Z.ltb_spec 1 req); [destruct (Z.ltb_spec 1 (minlen lens)) | destruct (Z.ltb_spec req (minlen lens))]; lia. }
    set (rv := reverse_bits (rfc_code lens sy) (Znth sy lens)) in *.
    assert (Hrv: 0 <= rv < 2).
    { destruct Zlib.proof.inftrees.part_bits.bits_ok2 as [B _]. unfold rv. rewrite Hl1.
      apply (B (rfc_code lens sy) 1); lia. }
    assert (Hp2: 0 <= pat mod 2 < 2) by (apply Z.mod_pos_bound; lia).
    destruct (Z.eq_dec (pat mod 2) rv) as [Eq|Ne].
    + assert (Eq': pat mod 2 ^ Znth sy lens = reverse_bits (rfc_code lens sy) (Znth sy lens)).
      { fold rv. rewrite Hl1. exact Eq. }
      destruct (W2 sy pat Hsy Hnz Hp Eq') as (op & val & T & _).
      apply (tdc_some_part _ _ _ _ _ _ _ _ T). lia.
    + pose proof (Zlib.proof.inftrees.part_decode.fact_decode_ok Zlib.proof.inftrees.part_loop_facts.loop_facts_ok
        Zlib.proof.inftrees.part_sorted.sorted_ok2 Zlib.proof.inftrees.part_rfc.rfc_ok2
        Zlib.proof.inftrees.part_bits.bits_ok2 Zlib.proof.inftrees.part_subbits.subbits_ok2
        (Zlib.proof.inftrees.part_size.size_ok2 Zlib.proof.inftrees.part_sorted.sorted_ok2
           Zlib.proof.inftrees.part_rfc.rfc_ok2 Zlib.proof.inftrees.part_bits.bits_ok2)
        type lens req old root used t Hin Hcap Hold H19 EM) as [_ FD2].
      assert (W1: walk t used root 1 = Some (64, 0, 1)).
      { apply FD2.
        - rewrite tdc_kraft by auto. unfold GP_KRAFT_ONE. lia.
        - rewrite <- Zlib.proof.inftrees.fact_result.maxlen_longest, E0. lia. }
      assert (T1: twalk s' (TCodes k) root 1 = Some (64, 0, 1)) by (apply (tdc_twalk s' k t used root); auto; lia).
      destruct (Z.eq_dec (pat mod 2) 1) as [P1|P0].
      * (* the invalid entry at index 1 *)
        cbv zeta. rewrite Hr1 in *. change (2 ^ 1) with 2. rewrite P1.
        destruct (ref.is_link (e_op (tab_entry lenfix_list distfix_list s' (TCodes k) 1))) eqn:L.
        -- left. unfold tab_entry. rewrite Hk by (destruct TO as [_ TS _]; change (2 ^ 1) with 2 in TS; lia).
           destruct TO as [_ TS TR]. specialize (TR 1 ltac:(change (2 ^ 1) with 2; lia)). cbv beta zeta in TR.
           destruct TR as [_ TR]. unfold tab_entry in L. rewrite Hk in L by (change (2 ^ 1) with 2 in TS; lia).
           rewrite (tdc_islink type _ ltac:(lia) L) in TR. destruct TR as (TR & _). lia.
        -- unfold twalk in T1. change (1 mod 2 ^ 1) with 1 in T1. rewrite L in T1. injection T1; intros. left. unfold tab_entry. lia.
      * (* index 0 = pattern rv = 1: the code of sy would mean the invalid entry *)
        exfalso. assert (Erv: rv = 1) by lia.
        destruct (W sy 0 Hsy Hnz ltac:(lia)) as (op & val & T0 & M0).
        rewrite Z.shiftl_0_l, Z.lor_0_r in T0. fold rv in T0. rewrite Erv, T1 in T0.
        injection T0; intros; subst op val.
        rewrite tdc_ms64 in M0; [discriminate|].
        unfold CODES, LENS, DISTS in *. assert (type = 1 \/ type = 2) as [-> | ->] by lia;
          [left|right]; split; auto; try lia.
  - (* a complete code: the code prefixing pat is longer than b (prefix-freeness) *)
    assert (Hk15: kraft lens = 2 ^ MAXBITS) by (rewrite tdc_kraft by auto; apply Z.ltb_ge in E1; unfold MAXBITS; cbn; lia).
    destruct (tdc_cover lens pat Hr Hk15 Hp) as (sy' & Hsy' & Hnz' & Hm').
    destruct (W2 sy' pat Hsy' Hnz' Hp Hm') as (op' & val' & T' & _).
    apply (tdc_some_part _ _ _ _ _ _ _ _ T').
    destruct (Z_lt_le_dec b (Znth sy' lens)) as [|Hle]; [auto|exfalso].
    pose proof (Forall_Znth _ lens sy' Hsy' Hr) as Hl'. cbv beta in Hl'.
    set (rv := reverse_bits (rfc_code lens sy) (Znth sy lens)) in *.
    assert (Hrv: 0 <= rv) by (apply tdc_rev_nonneg; lia).
    assert (Hrm: rv mod 2 ^ Znth sy' lens = reverse_bits (rfc_code lens sy') (Znth sy' lens)).
    { rewrite <- (tdc_mod_mod rv b (Znth sy' lens)) by lia. rewrite <- Hpm.
      rewrite tdc_mod_mod by lia. exact Hm'. }
    destruct (W sy 0 Hsy Hnz ltac:(lia)) as (o1 & v1 & T1 & _).
    rewrite Z.shiftl_0_l, Z.lor_0_r in T1. fold rv in T1.
    destruct (W2 sy' rv Hsy' Hnz' Hrv Hrm) as (o2 & v2 & T2 & _).
    rewrite T1 in T2. injection T2; intros. lia.
Qed.

Lemma tdc_call : forall type lo n req s lens,
  0 <= i_next s <= ENOUGH_CODES -> Zlength (i_codes s) = ENOUGH_CODES -> Forall entry_ok (i_codes s) ->
  lens = sublist lo (lo + n) (i_lens s) ->
  inputs_ok type lens req -> cap_ok type lens req (ENOUGH_CODES - i_next s) -> (type = CODES -> Zlength lens <= 19) ->
  1 <= req <= 15 -> (type = LENS -> Zlength lens <= 286) -> (type = DISTS -> Zlength lens <= 30) ->
  expected_valid type lens = 0 ->
  fst (fst (expected_call type lens req)) = 0 ->
  exists root used t,
    call_table type lo n req s = (0, sublist 0 (i_next s) (i_codes s) ++ t, i_next s + used, root) /\
    1 <= root <= 15 /\ used = snd (expected_call type lens req) /\ 0 <= used <= ENOUGH_CODES - i_next s /\
    Zlength t = ENOUGH_CODES - i_next s /\ Forall entry_ok t /\
    forall s' k, (forall i, 0 <= i < used -> Znth (k + i) (i_codes s') = Znth i t) -> tdec s' (TCodes k) root type lens.
Proof.
  intros type lo n req s lens Hn Hc Hok El Hin Hcap H19 Hq H286 H30 Hv Hw.
  set (old := sublist (i_next s) ENOUGH_CODES (i_codes s)).
  assert (Lo: Zlength old = ENOUGH_CODES - i_next s) by (unfold old; rewrite Zlength_sublist; lia).
  assert (Fo: Forall entry_ok old) by (unfold old; apply Forall_sublist; auto).
  rewrite <- Lo in Hcap.
  pose proof (tdc_fact_result type lens req old Hin Hcap Fo) as FR.
  pose proof Hin as (_ & _ & Hr & _).
  destruct (expected_call type lens req) as [[want root] size] eqn:EC. cbn [fst] in Hw. subst want.
  assert (Er: root = expected_root req lens) by (unfold expected_call in EC; inversion EC; auto).
  destruct (inflate_table_model type lens req old) as [|t0|r u t] eqn:EM; [lia|lia|].
  pose proof FR as FR'.
  destruct FR as (_ & -> & -> & Hu & _ & Lt & Ft & _).
  exists root, size, t.
  split; [unfold call_table; subst lens; fold old; rewrite EM; reflexivity|].
  split; [subst root; apply tdc_root; auto|].
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [auto|].
  intros s' k Hk. apply tdec_intro.
  { subst root; apply tdc_root; auto. }
  2: { apply (tdc_part type lens req old root size t s' k); auto. }
  2: { intros ET i Hi. subst type. unfold tab_entry.
       assert (Hsz: size = 2 ^ root) by (destruct FR' as (_ & _ & _ & _ & HC & _); rewrite HC by reflexivity;
         apply Z.shiftl_1_l).
       rewrite Hk by lia. apply (tabdec_codes_nolink lens req old root size t); auto. }
  intros sy Hsy Hnz x Hx.
  destruct (tabdec_walk type lens req old root size t Hin Hcap Fo H19 EM sy Hsy Hnz x Hx) as (op & val & W & M).
  exists op, val. split; [|exact M].
  pose proof (Forall_Znth _ lens sy Hsy Hr) as Hl. cbv beta in Hl.
  rewrite tdc_code by lia.
  apply (tdc_twalk s' k t size root); auto.
  - pose proof (tdc_root lens req Hr Hq). lia.
  - apply Z.lor_nonneg. split; [apply tdc_rev_nonneg; lia|]. apply Z.shiftl_nonneg. lia.
  - lia.
Qed.

Lemma tdc_range7 : forall lens, Forall (fun l => 0 <= l <= 7) lens -> Forall (fun l => 0 <= l <= MAXBITS) lens.
Proof. intros. eapply Forall_impl; [|exact H]. cbv beta. unfold MAXBITS. lia. Qed.

Lemma tdc_range15 : forall lens, lens_ok lens -> Forall (fun l => 0 <= l <= MAXBITS) lens.
Proof. intros. exact H. Qed.

Lemma tdc_want : forall type lens req,
  expected_valid type lens = 0 -> type = CODES \/ two_level_size lens (expected_root req lens) <=
    (if type =? LENS then ENOUGH_LENS else ENOUGH_DISTS) ->
  0 <= type <= 2 ->
  fst (fst (expected_call type lens req)) = 0.
Proof.
  intros type lens req Hv Hs Ht. unfold expected_call. cbn [fst]. rewrite Hv. cbn [Z.eqb negb].
  unfold CODES, LENS, DISTS in *.
  assert (type = 0 \/ type = 1 \/ type = 2) as [-> | [-> | ->]] by lia; cbn - [two_level_size expected_root];
    [reflexivity| |]; destruct Hs as [Hs|Hs]; try discriminate; cbn in Hs;
    match goal with |- context [?a <? ?b] => destruct (Z.ltb_spec a b); [lia|reflexivity] end.
Qed.

Lemma tabdec : tabdec_stmt.
Proof.
  constructor.
  - apply tabdec_fixed.
  - intros s Hn Hl Hc Hok Hcl.
    set (lens := sublist 0 19 (i_lens s)) in *.
    destruct Hcl as [Hr7 Hcomp].
    pose proof (tdc_range7 _ Hr7) as Hr.
    assert (Ll: Zlength lens = 19) by (unfold lens; rewrite Zlength_sublist; lia).
    assert (Hm: maxlen lens <= 7) by (apply tdc_maxlen_le; [lia|]; eapply Forall_impl; [|exact Hr7]; cbv beta; lia).
    pose proof (tdc_maxlen_nonneg lens).
    assert (A1: 0 <= i_next s <= ENOUGH_CODES) by (rewrite Hn; unfold ENOUGH_CODES; lia).
    assert (A2: inputs_ok CODES lens 7).
    { unfold inputs_ok. rewrite Ll. cbv [max_codes CODES LENS DISTS Z.eqb Pos.eqb]. split; [lia|]. split; [lia|]. split; [auto|lia]. }
    assert (A3: cap_ok CODES lens 7 (ENOUGH_CODES - i_next s)).
    { rewrite Hn. unfold cap_ok, CODES, LENS, DISTS. split; [|split; intro; discriminate].
      intros _. rewrite Z.shiftl_1_l. split; [lia|]. split; [unfold ENOUGH_CODES; lia|].
      assert (P7: 2 ^ maxlen lens <= 2 ^ 7) by (apply Z.pow_le_mono_r; lia). unfold ENOUGH_CODES. change (2 ^ 7) with 128 in P7. lia. }
    assert (A4: fst (fst (expected_call CODES lens 7)) = 0).
    { apply tdc_want; [apply tdc_valid; auto| left; reflexivity | unfold CODES; lia]. }
    destruct (tdc_call CODES 0 19 7 s lens A1 Hc Hok eq_refl A2 A3 ltac:(intros; lia) ltac:(lia)
                ltac:(unfold CODES, LENS; intro; discriminate) ltac:(unfold CODES, DISTS; intro; discriminate)
                ltac:(apply tdc_valid; auto) A4)
      as (root & used & t & Ecall & Hroot & Eu & Hu & Lt & Ft & Hdec).
    rewrite Ecall. rewrite Hn in *. split; [reflexivity|].
    intros s' Es. apply Hdec. intros i Hi. rewrite Es. rewrite sublist_nil. reflexivity.
  - intros s nlen ndist Hnl Hnd Hn Hl Hc Hok Hll Hdl.
    set (ll := sublist 0 nlen (i_lens s)) in *.
    set (dl := sublist nlen (nlen + ndist) (i_lens s)) in *.
    destruct Hll as (Hr1 & H256 & Hv1). destruct Hdl as (Hr2 & Hv2).
    assert (L1: Zlength ll = nlen) by (unfold ll; rewrite Zlength_sublist; lia).
    assert (L2: Zlength dl = ndist) by (unfold dl; rewrite Zlength_sublist; lia).
    assert (V1: expected_valid LENS ll = 0).
    { apply tdc_valid; auto. destruct Hv1; [left|right; left]; auto. split; [unfold LENS, CODES; lia|auto]. }
    assert (V2: expected_valid DISTS dl = 0).
    { apply tdc_valid; auto. destruct Hv2 as [?|[?|?]]; [left|right; left|right; right]; auto.
      split; [unfold DISTS, CODES; lia|auto]. }
    assert (S1: two_level_size ll (expected_root 9 ll) <= ENOUGH_LENS).
    { exact (tdc_fact_enough LENS ll ltac:(left; split; [reflexivity|lia]) Hr1 V1). }
    assert (S2: two_level_size dl (expected_root 6 dl) <= ENOUGH_DISTS).
    { exact (tdc_fact_enough DISTS dl ltac:(right; split; [reflexivity|lia]) Hr2 V2). }
    assert (A1: 0 <= i_next s <= ENOUGH_CODES) by (rewrite Hn; unfold ENOUGH_CODES; lia).
    assert (A2: inputs_ok LENS ll 9).
    { unfold inputs_ok. rewrite L1. cbv [max_codes CODES LENS DISTS Z.eqb Pos.eqb]. split; [lia|]. split; [lia|]. split; [auto|lia]. }
    assert (A3: cap_ok LENS ll 9 (ENOUGH_CODES - i_next s)).
    { rewrite Hn. unfold cap_ok, CODES, LENS, DISTS, ENOUGH_LENS, ENOUGH_CODES. split; [intro; discriminate|].
      split; intros; [lia|discriminate]. }
    assert (A4: fst (fst (expected_call LENS ll 9)) = 0) by (apply tdc_want; auto; unfold LENS; lia).
    destruct (tdc_call LENS 0 nlen 9 s ll A1 Hc Hok eq_refl A2 A3 ltac:(unfold LENS, CODES; intro; discriminate)
                ltac:(lia) ltac:(lia) ltac:(unfold LENS, DISTS; intro; discriminate) V1 A4)
      as (lb & u1 & t1 & Ecall1 & Hr1' & Eu1 & Hu1 & Lt1 & Ft1 & Hdec1).
    rewrite Ecall1. rewrite Hn in *.
    assert (Eu1': u1 <= ENOUGH_LENS).
    { rewrite Eu1. unfold expected_call. cbn [snd]. exact S1. }
    set (codes1 := sublist 0 0 (i_codes s) ++ t1).
    assert (Ec1: codes1 = t1) by (unfold codes1; rewrite sublist_nil; reflexivity).
    set (s1 := set_i_next (set_i_codes s codes1) (0 + u1)).
    assert (B0: i_next s1 = u1) by reflexivity.
    assert (B0': i_codes s1 = t1) by exact Ec1.
    assert (B0'': i_lens s1 = i_lens s) by reflexivity.
    assert (B1: 0 <= i_next s1 <= ENOUGH_CODES) by (rewrite B0; unfold ENOUGH_CODES, ENOUGH_LENS in *; lia).
    assert (B2: Zlength (i_codes s1) = ENOUGH_CODES) by (rewrite B0', Lt1; lia).
    assert (B3: Forall entry_ok (i_codes s1)) by (rewrite B0'; auto).
    assert (B4: inputs_ok DISTS dl 6).
    { unfold inputs_ok. rewrite L2. cbv [max_codes CODES LENS DISTS Z.eqb Pos.eqb]. split; [lia|]. split; [lia|]. split; [auto|lia]. }
    assert (B5: cap_ok DISTS dl 6 (ENOUGH_CODES - i_next s1)).
    { rewrite B0. unfold cap_ok, CODES, LENS, DISTS, ENOUGH_DISTS, ENOUGH_CODES, ENOUGH_LENS in *.
      split; [intro; discriminate|]. split; intros; [discriminate|lia]. }
    assert (B6: fst (fst (expected_call DISTS dl 6)) = 0) by (apply tdc_want; auto; unfold DISTS; lia).
    destruct (tdc_call DISTS nlen ndist 6 s1 dl B1 B2 B3 ltac:(rewrite B0''; reflexivity) B4 B5
                ltac:(unfold DISTS, CODES; intro; discriminate) ltac:(lia)
                ltac:(unfold DISTS, LENS; intro; discriminate) ltac:(lia) V2 B6)
      as (db & u2 & t2 & Ecall2 & Hr2' & Eu2 & Hu2 & Lt2 & Ft2 & Hdec2).
    split; [reflexivity|]. cbv zeta. rewrite Ecall2. rewrite B0, B0'. replace (0 + u1) with u1 by lia.
    split; [reflexivity|]. intros s' Es. split.
    + apply Hdec1. intros i Hi. rewrite Es. rewrite app_Znth1 by (rewrite Zlength_sublist; lia).
      rewrite Znth_sublist by lia. f_equal; lia.
    + apply Hdec2. intros i Hi. rewrite Es. rewrite app_Znth2 by (rewrite Zlength_sublist; lia).
      rewrite Zlength_sublist by lia. f_equal. lia.
Qed.
