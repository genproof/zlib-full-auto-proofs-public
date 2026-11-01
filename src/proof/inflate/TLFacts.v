(* Pure facts of the cases TABLE and LENLENS (CaseTABLE5.v, CaseLENLENS5.v): the model's steps (Model.v c_TABLE, c_LENLENS)
   cut into the pieces the C code executes, and mwf / mwf3 of the machines between them, as Step3Tables.v
   over mwf / mwf3 with cover3_stmt. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.inflate.Inv3.
Require Export Zlib.proof.inflate.MwfLemmas.
Require Export Zlib.proof.inflate.Cover3.
Require Zlib.proof.inftrees.ref Zlib.proof.inftrees.facts Zlib.proof.inftrees.part_result Zlib.proof.inftrees.part_sorted
  Zlib.proof.inftrees.part_rfc Zlib.proof.inftrees.part_bits Zlib.proof.inftrees.part_subbits
  Zlib.proof.inftrees.part_size.
Import ListNotations.
Local Open Scope Z_scope.

Lemma tl_fact_result : facts.fact_result.
Proof.
  exact (part_result.fact_result_ok part_sorted.sorted_ok2 part_rfc.rfc_ok2 part_bits.bits_ok2
           part_subbits.subbits_ok2
           (part_size.size_ok2 part_sorted.sorted_ok2 part_rfc.rfc_ok2 part_bits.bits_ok2)).
Qed.

Ltac md_neq := cbv [HEAD TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT LENGTH DONE BAD SYNC] in *;
  lia.

(* ---------------------------------------------------------------------------------------------- *)
(* NEEDBITS                                                                                       *)

Lemma tl_needbits_f_s: forall k n m, m_s (needbits_f k n m) = m_s m.
Proof.
  induction k; intros n m; simpl; auto.
  destruct (m_bits m <? n); auto. destruct (m_have m =? 0); auto. rewrite IHk. reflexivity.
Qed.

Lemma tl_needbits_s: forall n m, m_s (needbits n m) = m_s m.
Proof. intros. apply tl_needbits_f_s. Qed.

Lemma tl_needbits_f_ok: forall k n m,
  m_leave m = 0 -> 0 <= m_bits m -> n <= 32 -> n <= m_bits m + 8 * Z.of_nat k ->
  m_leave (needbits_f k n m) <> 1 -> n <= m_bits (needbits_f k n m) /\ m_leave (needbits_f k n m) = 0.
Proof.
  induction k; intros n m L B N F E; simpl in *.
  - split; [lia | auto].
  - destruct (Z.ltb_spec (m_bits m) n).
    + destruct (m_have m =? 0).
      * simpl in E. lia.
      * apply IHk; auto; unfold pull; simpl; unfold u32; rewrite ?Z.mod_small; lia.
    + split; [lia | auto].
Qed.

Lemma tl_needbits_ok: forall n m,
  mwf m -> m_leave m = 0 -> n <= 32 -> m_leave (needbits n m) <> 1 ->
  n <= m_bits (needbits n m) /\ m_leave (needbits n m) = 0.
Proof. intros n m W L N E. apply tl_needbits_f_ok; auto; try (destruct W; simpl; lia). Qed.

Lemma tl_leave01: forall m, mwf m -> m_leave m <> 1 -> m_leave m = 0.
Proof. intros m W H. pose proof (mw_leave _ W). lia. Qed.

Lemma tl_bitsn_range: forall m n, 0 <= n -> 0 <= bitsn m n < 2 ^ n.
Proof. intros m n H. unfold bitsn. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. Qed.

Lemma tl_drop_bits: forall n m, 0 <= n <= m_bits m -> m_bits m <= 39 -> m_bits (dropbits n m) = m_bits m - n.
Proof. intros n m H1 H2. unfold dropbits; simpl; unfold u32; rewrite Z.mod_small; lia. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* mwf under a new state                                                                         *)

Lemma tl_mwf_new_s: forall m s', mwf m -> swf s' -> modewf s' ->
  (m_out m = m_aout m \/ i_mode s' = LENGTH \/ i_mode s' = DONE \/ i_mode s' = BAD) ->
  mwf (set_m_s m s').
Proof. intros m s' W S M O. destruct W. constructor; simpl; auto. Qed.

Lemma tl_swf3_plain: forall s, i_mode s <> HEAD -> ~ decode_mode (i_mode s) ->
  i_mode s <> LENEXT -> i_mode s <> DISTEXT -> swf3 s.
Proof. intros s A B C D. constructor; intros; contradiction. Qed.

Lemma tl_out_eq: forall m, mwf m -> m_mode m = TABLE \/ m_mode m = LENLENS -> m_out m = m_aout m.
Proof. intros m W H. apply mwf_out_eq; auto; destruct H as [H|H]; rewrite H; md_neq. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* TABLE                                                                                          *)

Definition tl_nlen (m2: mst) : Z := bitsn m2 5 + 257.
Definition tl_ndist (m2: mst) : Z := bitsn (dropbits 5 m2) 5 + 1.
Definition tl_ncode (m2: mst) : Z := bitsn (dropbits 5 (dropbits 5 m2)) 4 + 4.

(* after the three fields and DROPBITS *)
Definition tl_m6 (m2: mst) : mst :=
  upd_s (dropbits 4 (dropbits 5 (dropbits 5 m2)))
    (fun s => set_i_ncode (set_i_ndist (set_i_nlen s (tl_nlen m2)) (tl_ndist m2)) (tl_ncode m2)).
(* entering LENLENS *)
Definition tl_m7 (m2: mst) : mst := set_mode (upd_s (tl_m6 m2) (fun s => set_i_have s 0)) LENLENS.

Lemma c_TABLE_eq: forall fl fx dx fa m, c_TABLE fl fx dx fa m =
  let m2 := needbits 14 m in
  if m_leave m2 =? 1 then IBrk m2 else
  if orb (286 <? tl_nlen m2) (30 <? tl_ndist m2) then IBrk (set_bad (tl_m6 m2) M_toomany) else
  c_LENLENS fl fx dx fa (tl_m7 m2).
Proof. intros. unfold c_TABLE at 1. exact eq_refl. Qed.

Lemma tl_ranges: forall m2,
  0 <= bitsn m2 5 < 32 /\ 0 <= bitsn (dropbits 5 m2) 5 < 32 /\ 0 <= bitsn (dropbits 5 (dropbits 5 m2)) 4 < 16.
Proof.
  intros m2. pose proof (tl_bitsn_range m2 5 ltac:(lia)). pose proof (tl_bitsn_range (dropbits 5 m2) 5 ltac:(lia)).
  pose proof (tl_bitsn_range (dropbits 5 (dropbits 5 m2)) 4 ltac:(lia)).
  change (2 ^ 5) with 32 in *. change (2 ^ 4) with 16 in *. lia.
Qed.

Lemma tl_mwf_m6: forall m2, mwf m2 -> 14 <= m_bits m2 -> mwf (dropbits 4 (dropbits 5 (dropbits 5 m2))).
Proof.
  intros m2 W B. pose proof (mw_bits _ W).
  assert (B3: m_bits (dropbits 5 m2) = m_bits m2 - 5) by (apply tl_drop_bits; lia).
  assert (B4: m_bits (dropbits 5 (dropbits 5 m2)) = m_bits m2 - 10) by (rewrite tl_drop_bits; lia).
  apply mwf_dropbits; [ | lia]. apply mwf_dropbits; [ | lia]. apply mwf_dropbits; auto; lia.
Qed.

Lemma tl_mwf3_m7: forall m2, mwf m2 -> 14 <= m_bits m2 -> m_mode m2 = TABLE ->
  tl_nlen m2 <= 286 -> tl_ndist m2 <= 30 -> mwf3 (tl_m7 m2).
Proof.
  intros m2 W B Md T1 T2.
  pose proof (tl_mwf_m6 m2 W B) as W5.
  set (m5 := dropbits 4 (dropbits 5 (dropbits 5 m2))) in *.
  assert (E5: m_s m5 = m_s m2) by reflexivity.
  assert (O5: m_out m5 = m_aout m5) by (apply mwf_out_eq; auto; unfold m_mode; rewrite E5; fold (m_mode m2);
    rewrite Md; md_neq).
  destruct (tl_ranges m2) as (R1 & R2 & R3). unfold tl_nlen, tl_ndist in *.
  pose proof (mw_s _ W5) as S5.
  split.
  - assert (EQ: tl_m7 m2 = set_m_s m5 (set_i_mode (set_i_have (set_i_ncode (set_i_ndist (set_i_nlen (m_s m5)
                  (tl_nlen m2)) (tl_ndist m2)) (tl_ncode m2)) 0) LENLENS)) by reflexivity.
    rewrite EQ. unfold tl_nlen, tl_ndist.
    apply tl_mwf_new_s; auto.
    + destruct S5; constructor; simpl; auto; try (unfold tl_ncode; lia); md_neq.
    + constructor; simpl; intros; try md_neq.
      * unfold tl_ncode. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. intros; lia.
      * unfold decode_mode in *; md_neq.
  - unfold tl_m7, set_mode, upd_s. cbn [m_s set_m_s set_i_mode i_mode].
    apply tl_swf3_plain; cbn [i_mode set_i_mode]; [md_neq | unfold decode_mode; md_neq | md_neq | md_neq].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* LENLENS: the order permutation                                                                *)

Lemma tl_order_nodup: NoDup order.
Proof. unfold order. repeat constructor; simpl; intuition lia. Qed.

Lemma tl_order_len: Zlength order = 19.
Proof. reflexivity. Qed.

Lemma tl_order_range: forall k, 0 <= k < 19 -> 0 <= Znth k order < 19.
Proof.
  intros k Hk. assert (F: Forall (fun x => 0 <= x < 19) order) by (unfold order; repeat constructor; lia).
  rewrite Forall_forall in F. apply F. apply Znth_In. rewrite tl_order_len. lia.
Qed.

Lemma tl_order_inj: forall i j, 0 <= i < 19 -> 0 <= j < 19 -> Znth i order = Znth j order -> i = j.
Proof. intros i j Hi Hj E. apply (NoDup_Znth_inj order i j tl_order_nodup); rewrite ?tl_order_len; auto. Qed.

Lemma tl_order_surj: forall x, 0 <= x < 19 -> exists k, 0 <= k < 19 /\ Znth k order = x.
Proof.
  intros x Hx. assert (IN: In x order) by (unfold order; simpl; lia).
  apply In_Znth in IN. destruct IN as (k & Hk & E). rewrite tl_order_len in Hk. eauto.
Qed.

Lemma tl_maxlen_le: forall l, Forall (fun x => 0 <= x <= 7) l -> 0 <= maxlen l <= 7.
Proof.
  induction l; intros F; simpl; [lia|]. inversion F; subst. specialize (IHl H2). unfold maxlen in *. simpl. lia.
Qed.

Lemma tl_forall_sublist: forall (P: Z -> Prop) lo hi l, 0 <= lo <= hi -> hi <= Zlength l ->
  (forall k, lo <= k < hi -> P (Znth k l)) -> Forall P (sublist lo hi l).
Proof.
  intros P lo hi l H1 H2 H. apply Forall_forall. intros x IN.
  apply In_Znth in IN. destruct IN as (i & Hi & <-). rewrite Zlength_sublist in Hi by lia.
  rewrite Znth_sublist by lia. apply H. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* LENLENS: the first loop                                                                       *)

(* lens[order[have++]] = BITS(3); DROPBITS(3); after NEEDBITS(3) gave m2 *)
Definition tl_ll_step (m2: mst) : mst :=
  let s := m_s m2 in
  dropbits 3 (upd_s m2 (fun _ => set_i_have (set_i_lens s (upd_Znth (Znth (i_have s) order) (i_lens s) (bitsn m2 3)))
                                             (i_have s + 1))).

Lemma lenlens_loop_S: forall k m, lenlens_loop (S k) m =
  if i_have (m_s m) <? i_ncode (m_s m) then
    let m2 := needbits 3 m in
    if m_leave m2 =? 1 then m2 else lenlens_loop k (tl_ll_step m2)
  else m.
Proof. reflexivity. Qed.

Lemma lenlens_loop_done: forall k m, i_ncode (m_s m) <= i_have (m_s m) -> lenlens_loop k m = m.
Proof.
  intros [|k] m H; [reflexivity|]. rewrite lenlens_loop_S.
  destruct (Z.ltb_spec (i_have (m_s m)) (i_ncode (m_s m))); [lia | reflexivity].
Qed.

(* the machine of the loop *)
Definition tl_llok (m: mst) : Prop := mwf m /\ m_mode m = LENLENS /\ m_leave m = 0.

Lemma tl_ll_step_ok: forall m, tl_llok m -> i_have (m_s m) < i_ncode (m_s m) ->
  m_leave (needbits 3 m) <> 1 ->
  tl_llok (tl_ll_step (needbits 3 m)) /\
  i_have (m_s (tl_ll_step (needbits 3 m))) = i_have (m_s m) + 1 /\
  i_ncode (m_s (tl_ll_step (needbits 3 m))) = i_ncode (m_s m) /\
  3 <= m_bits (needbits 3 m).
Proof.
  intros m (W & Md & L) Hh EL.
  pose proof (mw_md _ W) as MD. pose proof (mw_s _ W) as S.
  destruct (md_lenlens _ MD Md) as (Hc & H0 & Hnl & Hnd & LE).
  set (m2 := needbits 3 m).
  assert (W2: mwf m2) by (apply mwf_needbits; auto; lia).
  assert (E2: m_s m2 = m_s m) by (apply tl_needbits_s).
  destruct (tl_needbits_ok 3 m W L ltac:(lia) EL) as [NB NL]. fold m2 in NB, NL.
  destruct (sw_lens _ S) as [ZL FL].
  pose proof (tl_order_range (i_have (m_s m)) ltac:(lia)) as OR.
  pose proof (tl_bitsn_range m2 3 ltac:(lia)) as BR. change (2 ^ 3) with 8 in BR.
  unfold tl_ll_step. rewrite E2.
  set (L' := upd_Znth (Znth (i_have (m_s m)) order) (i_lens (m_s m)) (bitsn m2 3)).
  set (s' := set_i_have (set_i_lens (m_s m) L') (i_have (m_s m) + 1)).
  assert (W3: mwf (upd_s m2 (fun _ => s'))).
  { unfold upd_s. apply tl_mwf_new_s; auto.
    - destruct S; constructor; simpl; auto; try lia.
      split; [unfold L'; rewrite upd_Znth_Zlength; lia | ]. apply Forall_upd_Znth; auto. lia.
    - unfold m_mode in Md. constructor; simpl; intros; try md_neq.
      + split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
        intros k' Hk'. unfold L'. destruct (Z.eq_dec k' (i_have (m_s m))).
        * subst k'. rewrite upd_Znth_same by lia. lia.
        * pose proof (tl_order_range k' ltac:(lia)).
          rewrite upd_Znth_diff by (try lia; intros E; apply n; apply tl_order_inj; auto; lia).
          apply LE; lia.
      + unfold decode_mode in *; md_neq.
    - left. apply tl_out_eq; auto. unfold m_mode. rewrite E2. right; exact Md. }
  split; [ | split; [reflexivity | split; [reflexivity | exact NB]]].
  split; [apply mwf_dropbits; auto; simpl; lia | ].
  split; [exact Md | exact NL].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* LENLENS: the zero loop and the code length code                                               *)

Lemma lenlens_zero_S: forall k s, lenlens_zero (S k) s =
  if i_have s <? 19 then
    lenlens_zero k (set_i_have (set_i_lens s (upd_Znth (Znth (i_have s) order) (i_lens s) 0)) (i_have s + 1))
  else s.
Proof. reflexivity. Qed.

Lemma lenlens_zero_done: forall k s, 19 <= i_have s -> lenlens_zero k s = s.
Proof.
  intros [|k] s H; [reflexivity|]. rewrite lenlens_zero_S.
  destruct (Z.ltb_spec (i_have s) 19); [lia | reflexivity].
Qed.

(* the facts of the zero loop's states *)
Definition tl_zok (s: istate) : Prop :=
  0 <= i_have s <= 19 /\ Zlength (i_lens s) = 320 /\ Forall (fun x => 0 <= x <= 65535) (i_lens s) /\
  (forall k, 0 <= k < i_have s -> Znth (Znth k order) (i_lens s) <= 7).

Lemma tl_zero_step_ok: forall s, tl_zok s -> i_have s < 19 ->
  tl_zok (set_i_have (set_i_lens s (upd_Znth (Znth (i_have s) order) (i_lens s) 0)) (i_have s + 1)).
Proof.
  intros s (H0 & ZL & FL & LE) Hh.
  pose proof (tl_order_range (i_have s) ltac:(lia)) as OR.
  split; [simpl; lia|]. split; [simpl; rewrite upd_Znth_Zlength; lia|].
  split; [simpl; apply Forall_upd_Znth; auto; lia|].
  simpl. intros k Hk. destruct (Z.eq_dec k (i_have s)).
  - subst k. rewrite upd_Znth_same by lia. lia.
  - pose proof (tl_order_range k ltac:(lia)).
    rewrite upd_Znth_diff by (try lia; intros E; apply n; apply tl_order_inj; auto; lia).
    apply LE; lia.
Qed.

Lemma tl_zero_ok: forall n s, tl_zok s -> 19 <= i_have s + Z.of_nat n ->
  tl_zok (lenlens_zero n s) /\ i_have (lenlens_zero n s) = 19 /\
  exists L, lenlens_zero n s = set_i_have (set_i_lens s L) 19.
Proof.
  induction n; intros s HZ Hn.
  - pose proof (proj1 HZ) as H0. simpl in Hn. assert (i_have s = 19) by lia.
    split; [auto | split; [auto | exists (i_lens s); destruct s; simpl in *; subst; reflexivity]].
  - rewrite lenlens_zero_S. destruct (Z.ltb_spec (i_have s) 19).
    + destruct (IHn _ (tl_zero_step_ok s HZ ltac:(lia)) ltac:(simpl; lia)) as (Z1 & H1 & L & E).
      split; [auto | split; [auto | exists L; rewrite E; reflexivity]].
    + pose proof (proj1 HZ) as H0. assert (i_have s = 19) by lia.
      split; [auto | split; [auto | exists (i_lens s); destruct s; simpl in *; subst; reflexivity]].
Qed.

(* the state before inflate_table(CODES, ...) *)
Definition tl_s0 (sZ: istate) : istate :=
  set_i_lenbits (set_i_distcode (set_i_lencode (set_i_next sZ 0) (TCodes 0)) (TCodes 0)) 7.

(* the state after it *)
Definition tl_s1 (sZ: istate) : istate :=
  let s0 := tl_s0 sZ in
  let '(r, codes, nxt, lb) := call_table CODES 0 19 7 s0 in
  set_i_lenbits (set_i_next (set_i_codes s0 codes) nxt) lb.

Definition tl_r (sZ: istate) : Z :=
  let '(r, _, _, _) := call_table CODES 0 19 7 (tl_s0 sZ) in r.

Lemma c_LENLENS_eq: forall fl fx dx fa m, c_LENLENS fl fx dx fa m =
  let m1 := lenlens_loop 19 m in
  if m_leave m1 =? 1 then IBrk m1 else
  let sZ := lenlens_zero 19 (m_s m1) in
  let m := set_m_ret (set_m_s m1 (tl_s1 sZ)) (tl_r sZ) in
  if negb (tl_r sZ =? 0) then IBrk (set_bad m M_cl_set) else
  c_CODELENS fl fx dx fa (set_mode (upd_s m (fun s => set_i_have s 0)) CODELENS).
Proof.
  intros. cbv beta iota zeta delta [c_LENLENS tl_s1 tl_r tl_s0 call_table]. exact eq_refl.
Qed.

(* everything about the call, for a state of the zero loop's end *)
Lemma tl_table_ok: forall sZ, cover3_stmt -> swf sZ -> tl_zok sZ -> i_have sZ = 19 ->
  let s0 := tl_s0 sZ in
  let L := sublist 0 19 (i_lens sZ) in
  let old := sublist 0 ENOUGH_CODES (i_codes sZ) in
  let r := inflate_table_model CODES L 7 old in
  Zlength L = 19 /\ inputs_ok CODES L 7 /\ cap_ok CODES L 7 (Zlength old) /\ Forall entry_ok old /\
  Zlength old = ENOUGH_CODES /\ old = i_codes sZ /\
  Zlength (it_tab old r) = ENOUGH_CODES /\ Forall entry_ok (it_tab old r) /\
  0 <= it_adv r <= ENOUGH_CODES /\ 0 <= it_bits 7 r <= 15 /\ -1 <= it_ret r <= 1 /\
  tl_s1 sZ = set_i_lenbits (set_i_next (set_i_codes s0 (it_tab old r)) (it_adv r)) (it_bits 7 r) /\
  (it_ret r = 0 -> exists used t, r = ROk (it_bits 7 r) used t /\ used = it_adv r /\ t = it_tab old r /\
     tab_ok CODES t (it_bits 7 r) used /\ 1 <= used <= ENOUGH_CODES).
Proof.
  intros sZ C3S S (H0 & ZL & FL & LE) H19. cbv zeta.
  destruct (sw_codes _ S) as [ZC FC].
  set (L := sublist 0 19 (i_lens sZ)). set (old := sublist 0 ENOUGH_CODES (i_codes sZ)).
  assert (EO: old = i_codes sZ) by (unfold old; rewrite sublist_same; auto).
  assert (ZO: Zlength old = ENOUGH_CODES) by (rewrite EO; auto).
  assert (FO: Forall entry_ok old) by (rewrite EO; auto).
  assert (ZL19: Zlength L = 19) by (unfold L; rewrite Zlength_sublist; lia).
  assert (LE7: forall x, 0 <= x < 19 -> 0 <= Znth x (i_lens sZ) <= 7).
  { intros x Hx. destruct (tl_order_surj x Hx) as (k & Hk & <-). split; [|apply LE; lia].
    rewrite Forall_forall in FL. apply FL. apply Znth_In. pose proof (tl_order_range k Hk). lia. }
  assert (F07: Forall (fun x => 0 <= x <= 7) L).
  { apply tl_forall_sublist; try lia. intros k Hk. apply LE7; lia. }
  assert (IN0: inputs_ok CODES L 7).
  { unfold inputs_ok. rewrite ZL19. split; [unfold CODES; lia|].
    split; [unfold max_codes; simpl; lia|]. split; [|lia].
    eapply Forall_impl; [|exact F07]. unfold MAXBITS; simpl; intros; lia. }
  assert (CAP0: cap_ok CODES L 7 (Zlength old)).
  { pose proof (tl_maxlen_le _ F07) as ML. rewrite ZO.
    unfold cap_ok. unfold LENS, CODES, DISTS, ENOUGH_CODES. split; [|split; intros; lia].
    intros _. split; [lia|]. split; [lia|]. rewrite Z.shiftl_1_l.
    assert (2 ^ maxlen L <= 2 ^ 7) by (apply Z.pow_le_mono_r; lia).
    change (2 ^ 7) with 128 in *. lia. }
  assert (ES1: tl_s1 sZ = set_i_lenbits (set_i_next (set_i_codes (tl_s0 sZ)
                  (it_tab old (inflate_table_model CODES L 7 old))) (it_adv (inflate_table_model CODES L 7 old)))
                  (it_bits 7 (inflate_table_model CODES L 7 old))).
  { unfold tl_s1, call_table. cbn [tl_s0 i_next set_i_lenbits set_i_distcode set_i_lencode set_i_next i_codes i_lens].
    change (0 + 19) with 19. fold L. fold old. rewrite sublist_nil. reflexivity. }
  pose proof (tl_fact_result CODES L 7 old IN0 CAP0 FO) as FR.
  destruct (ref.expected_call CODES L 7) as [[want root] size].
  split; [exact ZL19 | ]. split; [exact IN0 | ]. split; [exact CAP0 | ]. split; [exact FO | ].
  split; [exact ZO | ]. split; [exact EO | ].
  rewrite ES1. clear ES1.
  destruct (inflate_table_model CODES L 7 old) as [ | t | root' used t] eqn:M; cbn [it_ret it_tab it_adv it_bits] in *.
  - split; [exact ZO|]. split; [exact FO|]. split; [unfold ENOUGH_CODES; lia|]. split; [lia|]. split; [lia|].
    split; [reflexivity | intros; lia].
  - destruct FR as (_ & FR1 & FR2).
    split; [lia|]. split; [exact FR2|]. split; [unfold ENOUGH_CODES; lia|]. split; [lia|]. split; [lia|].
    split; [reflexivity | intros; lia].
  - destruct FR as (W0 & Rt & Us & U1 & _ & ZT & FT & _).
    assert (C3: tab_ok CODES t root' used /\ used <= Zlength old).
    { destruct (C3S CODES L 7 old root' used t IN0 ltac:(intros; lia) CAP0 FO M) as (A & B & _). auto. }
    destruct C3 as [TO UO].
    pose proof (tv_rb _ _ _ _ TO) as RB.
    split; [lia|]. split; [exact FT|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [reflexivity | ]. intros _. exists used, t. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [exact TO | lia].
Qed.

(* the machine entering CODELENS (c_LENLENS_eq's last line), from the machine m1 after the first loop *)
Definition tl_mcl (m1: mst) : mst :=
  let sZ := lenlens_zero 19 (m_s m1) in
  set_mode (upd_s (set_m_ret (set_m_s m1 (tl_s1 sZ)) (tl_r sZ)) (fun s => set_i_have s 0)) CODELENS.

Lemma tl_tvalid_at: forall kind fx dx s k rb used t,
  0 <= k -> used <= ENOUGH_CODES - k ->
  (forall i, 0 <= i < used -> Znth (k + i) (i_codes s) = Znth i t) ->
  tab_ok kind t rb used -> tvalid kind fx dx s (TCodes k) rb.
Proof.
  intros kind fx dx s k rb used t Hk Hu E T. exists used. split; [simpl; lia|].
  unfold tvalid_b. apply tvalid_g_ext with (fun i => Znth i t); auto.
  intros i Hi. simpl. symmetry. apply E; auto.
Qed.

Lemma tl_r_eq: forall sZ, tl_r sZ =
  it_ret (inflate_table_model CODES (sublist 0 19 (i_lens sZ)) 7 (sublist 0 ENOUGH_CODES (i_codes sZ))).
Proof. intros. reflexivity. Qed.

(* it satisfies mwf3 when inflate_table succeeded (cover3_stmt: the CODES table is valid) *)
Lemma tl_mwf3_cl: forall m1, cover3_stmt -> mwf m1 -> m_mode m1 = LENLENS ->
  i_ncode (m_s m1) <= i_have (m_s m1) -> tl_r (lenlens_zero 19 (m_s m1)) = 0 -> mwf3 (tl_mcl m1).
Proof.
  intros m1 C3 W Md Hn R0.
  pose proof (mw_md _ W) as MD. pose proof (mw_s _ W) as S.
  destruct (md_lenlens _ MD Md) as (Hc & H0 & Hnl & Hnd & LE).
  destruct (sw_lens _ S) as [ZL FL].
  assert (Z0: tl_zok (m_s m1)) by (split; [lia|]; split; [exact ZL|]; split; [exact FL|]; exact LE).
  destruct (tl_zero_ok 19 (m_s m1) Z0 ltac:(simpl; lia)) as (ZZ & H19 & L & EZ).
  unfold tl_mcl. rewrite R0.
  set (sZ := lenlens_zero 19 (m_s m1)) in *.
  assert (SZ: swf sZ).
  { rewrite EZ. destruct ZZ as (_ & ZL' & FL' & _). rewrite EZ in ZL', FL'. simpl in ZL', FL'.
    destruct S; constructor; simpl; auto; lia. }
  destruct (tl_table_ok sZ C3 SZ ZZ H19) as (_ & _ & _ & _ & ZO & EO & ZT & FT & RA & RB & RR & ES1 & OK).
  rewrite tl_r_eq in R0.
  destruct (OK R0) as (used & t & _ & Eu & Et & TO & U).
  rewrite ES1. rewrite <- Et, <- Eu.
  generalize dependent (it_bits 7 (inflate_table_model CODES (sublist 0 19 (i_lens sZ)) 7
                                      (sublist 0 ENOUGH_CODES (i_codes sZ)))). intros b RB TO.
  rewrite <- Et in ZT, FT.
  assert (WR: mwf (set_m_ret m1 0)) by (destruct W; constructor; simpl; auto; lia).
  set (s' := set_i_mode (set_i_have (set_i_lenbits (set_i_next (set_i_codes (tl_s0 sZ) t) used) b) 0) CODELENS).
  assert (EQ: set_mode (upd_s (set_m_ret (set_m_s m1 (set_i_lenbits (set_i_next (set_i_codes (tl_s0 sZ) t) used) b)) 0)
                (fun s => set_i_have s 0)) CODELENS = set_m_s (set_m_ret m1 0) s') by reflexivity.
  rewrite EQ.
  assert (Nl: i_nlen sZ = i_nlen (m_s m1)) by (rewrite EZ; reflexivity).
  assert (Nd: i_ndist sZ = i_ndist (m_s m1)) by (rewrite EZ; reflexivity).
  split.
  - apply tl_mwf_new_s; auto.
    + unfold s', tl_s0. destruct SZ; constructor; simpl; auto; unfold tref_ok, ENOUGH_CODES in *; try lia; md_neq.
    + unfold s', tl_s0. constructor; simpl; intros; try md_neq.
      * split; [lia|]. split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [|intros; lia].
        apply tl_tvalid_at with used t; simpl; auto; unfold ENOUGH_CODES in *; try lia.
      * unfold decode_mode in *; md_neq.
    + left. simpl. apply tl_out_eq; auto.
  - simpl. apply tl_swf3_plain; unfold s'; cbn [i_mode set_i_mode]; [md_neq | unfold decode_mode; md_neq | md_neq | md_neq].
Qed.
