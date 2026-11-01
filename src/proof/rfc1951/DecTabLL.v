(* Part of DecTab: LENLENS (lenlens_loop, lenlens_zero, the code length code table).  Kit and statements: DecTabKit.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.rfc1951.Decode Zlib.proof.rfc1951.DecTabKit.
Import ListNotations.
Local Open Scope Z_scope.
Require Zlib.proof.inftrees.facts Zlib.proof.inftrees.part_result Zlib.proof.inftrees.part_sorted
  Zlib.proof.inftrees.part_rfc Zlib.proof.inftrees.part_bits Zlib.proof.inftrees.part_subbits
  Zlib.proof.inftrees.part_size.

(* ---------------------------------------------------------------------------------------------- *)
(* Finite facts on order and clpos                                                                *)

Lemma ll_fin19 (P: Z -> Prop) : (forall n, (n < 19)%nat -> P (Z.of_nat n)) -> forall i, 0 <= i < 19 -> P i.
Proof. intros H i Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia. apply H. lia. Qed.

Lemma ll_order_clpos i : 0 <= i < 19 -> 0 <= Znth i order < 19 /\ Znth (Znth i order) clpos = i.
Proof.
  revert i. apply ll_fin19. intros n Hn.
  do 19 (destruct n as [|n]; [split; [cbv; split; congruence | reflexivity]|]). lia.
Qed.

Lemma ll_clpos_order j : 0 <= j < 19 -> 0 <= Znth j clpos < 19 /\ Znth (Znth j clpos) order = j.
Proof.
  revert j. apply ll_fin19. intros n Hn.
  do 19 (destruct n as [|n]; [split; [cbv; split; congruence | reflexivity]|]). lia.
Qed.

Lemma ll_order_inj i j : 0 <= i < 19 -> 0 <= j < 19 -> Znth i order = Znth j order -> i = j.
Proof.
  intros Hi Hj E. destruct (ll_order_clpos i Hi) as [_ Ei]. destruct (ll_order_clpos j Hj) as [_ Ej].
  congruence.
Qed.

Lemma ll_Zlength_cl_lens cls : Zlength (cl_lens cls) = 19.
Proof. unfold cl_lens. rewrite Zlength_map, Zlength_correct, seq_length. reflexivity. Qed.

Lemma ll_Znth_cl_lens cls j : 0 <= j < 19 ->
  Znth j (cl_lens cls) = let i := Znth j clpos in if i <? Zlength cls then Znth i cls else 0.
Proof.
  intros Hj. unfold cl_lens. unfold Znth at 1. destruct (Z_lt_dec j 0) as [|_]; [lia|].
  set (f := fun s : nat => let i := Znth (Z.of_nat s) clpos in if i <? Zlength cls then Znth i cls else 0).
  rewrite nth_indep with (d' := f O) by (rewrite map_length, seq_length; lia).
  rewrite map_nth, seq_nth by lia. unfold f. simpl. rewrite Z2Nat.id by lia. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Blocks                                                                                         *)

Lemma ll_blocks_ok_nth : forall bs w out k, blocks_ok w out bs -> (k < length bs)%nat ->
  block_ok w (fold_left block_data (firstn k bs) out) (nth k bs (Stored [])).
Proof.
  induction bs as [|b bs IH]; intros w out k H Hk; simpl in Hk; [lia|].
  destruct H as [H1 H2]. destruct k as [|k]; simpl; [exact H1|]. apply IH; [exact H2 | lia].
Qed.

Lemma ll_blk_ok G k : dctx_ok G -> 0 <= k < nblk G -> block_ok (2 ^ dc_wb G) (outk G k) (blk G k).
Proof.
  intros ((_ & _ & _ & (_ & _ & BO)) & _) Hk. unfold outk, blk, expand. apply ll_blocks_ok_nth; [exact BO|].
  unfold nblk in Hk. rewrite Zlength_correct in Hk. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The state at LENLENS                                                                           *)

Lemma ll_at_mode G s c hold bits out : at_mode G s c hold bits out -> i_mode s = LENLENS ->
  hold_ok G c hold bits /\ at_lenlens G s (8 * c - bits) bits out.
Proof.
  intros [H A] M. split; [exact H|]. rewrite M in A.
  repeat match type of A with
  | _ \/ _ => destruct A as [A|A]
  end;
  repeat match type of A with
  | (?a = ?b \/ _) /\ _ => destruct A as [[E|[E|E]] _] || destruct A as [[E|E] _]
  | (LENLENS = LENLENS) /\ _ => destruct A as [_ A]
  | ?x = ?y /\ _ => destruct A as [E _]
  end; try exact A;
  unfold CODELENS, HEAD, FLAGS, TIME, OS, Zlib.proof.inflate.Model.TYPE, TYPEDO, STORED, COPY_, COPY, TABLE,
    LENLENS, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, CHECK, LENGTH, DONE in *; lia.
Qed.

Ltac ll_cbn := cbn [m_s m_inp m_ow m_aout m_out m_tout m_nx m_hold m_bits m_leave m_ret set_m_s set_m_ret
  i_mode i_last i_wrap i_flags i_check i_total i_head i_wbits i_wsize i_whave i_wnext i_wdata i_have i_lens
  i_codes i_nlen i_ndist i_ncode i_next i_lencode i_lenbits i_distcode
  set_i_have set_i_lens set_i_mode set_i_codes set_i_next set_i_lenbits set_i_lencode set_i_distcode] in *.

Lemma ll_kd_ret G pos inp ob m : Kd G pos inp ob m -> m_mode m = LENLENS -> m_ret m = Z_OK.
Proof. intros K Md. pose proof (kd_ret _ _ _ _ _ K) as E. rewrite Md in E. rewrite E. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The code length code table: its entries                                                        *)

Lemma ll_fact_result : facts.fact_result.
Proof.
  exact (part_result.fact_result_ok part_sorted.sorted_ok2 part_rfc.rfc_ok2 part_bits.bits_ok2
           part_subbits.subbits_ok2
           (part_size.size_ok2 part_sorted.sorted_ok2 part_rfc.rfc_ok2 part_bits.bits_ok2)).
Qed.

Lemma ll_maxlen : forall l, Forall (fun x => 0 <= x <= 7) l -> 0 <= maxlen l <= 7.
Proof.
  induction l as [|x l IH]; intros F; unfold maxlen in *; simpl; [lia|].
  inversion F; subst. specialize (IH H2). lia.
Qed.

Lemma ll_codes s r codes nxt lb :
  i_next s = 0 -> Zlength (i_lens s) = 320 -> Zlength (i_codes s) = ENOUGH_CODES -> Forall entry_ok (i_codes s) ->
  Forall (fun x => 0 <= x <= 7) (sublist 0 19 (i_lens s)) ->
  call_table CODES 0 19 7 s = (r, codes, nxt, lb) -> r = 0 ->
  Zlength codes = ENOUGH_CODES /\ Forall entry_ok codes.
Proof.
  intros N0 LL LC FC F7 E R0. unfold call_table in E. rewrite N0 in E.
  set (old := sublist 0 ENOUGH_CODES (i_codes s)) in *.
  set (L := sublist 0 (0 + 19) (i_lens s)) in *.
  assert (ZO: Zlength old = ENOUGH_CODES) by (unfold old; rewrite Zlength_sublist; unfold ENOUGH_CODES in *; lia).
  assert (FO: Forall entry_ok old) by (apply Forall_sublist; auto).
  assert (ZL: Zlength L = 19) by (unfold L; rewrite Zlength_sublist; lia).
  assert (FL: Forall (fun x => 0 <= x <= 7) L) by exact F7.
  pose proof (ll_maxlen L FL) as ML.
  assert (IN: inputs_ok CODES L 7).
  { split; [cbv; split; congruence|]. split; [rewrite ZL; cbv; congruence|]. split; [|lia].
    eapply Forall_impl; [|exact FL]. intros a Ha. cbv beta in Ha. unfold MAXBITS. lia. }
  assert (CAP: cap_ok CODES L 7 (Zlength old)).
  { rewrite ZO. split; [|split; intros H; cbv in H; congruence]. intros _. split; [lia|].
    split; [cbv; congruence|]. rewrite Z.shiftl_1_l.
    assert (2 ^ maxlen L <= 2 ^ 7) by (apply Z.pow_le_mono_r; lia). unfold ENOUGH_CODES. lia. }
  pose proof (ll_fact_result CODES L 7 old IN CAP FO) as FR.
  unfold ref.expected_call in FR.
  assert (Zpre: sublist 0 0 (i_codes s) = []) by (apply sublist_nil).
  destruct (inflate_table_model CODES L 7 old) as [ | t | root used t] eqn:M;
    cbn [it_ret it_tab it_adv it_bits] in E; inversion E; subst r codes nxt lb; clear E; try lia.
  destruct FR as (_ & _ & _ & _ & _ & ZT & FT & _).
  split; [congruence | exact FT].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* lenlens_zero                                                                                   *)

Lemma ll_set_have_lens_idem s A h1 B h2 :
  set_i_have (set_i_lens (set_i_have (set_i_lens s A) h1) B) h2 = set_i_have (set_i_lens s B) h2.
Proof. destruct s; reflexivity. Qed.

Definition ll_ext (cls: list Z) (i: Z) : Z := if i <? Zlength cls then Znth i cls else 0.

Lemma ll_zero cls : forall n s, 0 <= i_have s -> Zlength cls <= i_have s -> 19 <= i_have s + Z.of_nat n ->
  Zlength (i_lens s) = 320 ->
  (forall i, 0 <= i < i_have s -> i < 19 -> Znth (Znth i order) (i_lens s) = ll_ext cls i) ->
  exists L h, lenlens_zero n s = set_i_have (set_i_lens s L) h /\ Zlength L = 320 /\
    forall i, 0 <= i < 19 -> Znth (Znth i order) L = ll_ext cls i.
Proof.
  induction n; intros s H0 Hc Hn LL P; cbn [lenlens_zero].
  - exists (i_lens s), (i_have s). split; [destruct s; reflexivity|]. split; [exact LL|].
    intros i Hi. apply P; lia.
  - destruct (Z.ltb_spec (i_have s) 19) as [Lt|Ge].
    + set (h := i_have s) in *.
      destruct (ll_order_clpos h ltac:(lia)) as [Rh _].
      set (s1 := set_i_have (set_i_lens s (upd_Znth (Znth h order) (i_lens s) 0)) (h + 1)).
      assert (E1: i_have s1 = h + 1) by reflexivity.
      assert (E2: i_lens s1 = upd_Znth (Znth h order) (i_lens s) 0) by reflexivity.
      destruct (IHn s1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite E2, upd_Znth_Zlength; lia)) as (L & h' & F & LL' & P').
      { intros i Hi Hi19. rewrite E2. destruct (Z.eq_dec i h) as [->|Ne].
        - rewrite upd_Znth_same by lia. unfold ll_ext. destruct (Z.ltb_spec h (Zlength cls)); [lia|reflexivity].
        - rewrite upd_Znth_diff by (try lia; destruct (ll_order_clpos i ltac:(lia)); try lia;
            intros Eq; apply Ne; apply (ll_order_inj i h); lia).
          apply P; lia. }
      exists L, h'. split; [rewrite F; unfold s1; apply ll_set_have_lens_idem|]. split; [exact LL'|exact P'].
    + exists (i_lens s), (i_have s). split; [destruct s; reflexivity|]. split; [exact LL|].
      intros i Hi. apply P; lia.
Qed.

Lemma ll_zero_cl cls L : Zlength L = 320 -> (forall i, 0 <= i < 19 -> Znth (Znth i order) L = ll_ext cls i) ->
  sublist 0 19 L = cl_lens cls.
Proof.
  intros LL P. apply (list_solver.Znth_eq_ext (d := 0)); [rewrite Zlength_sublist, ll_Zlength_cl_lens by lia; lia|].
  intros j Hj. rewrite Zlength_sublist in Hj by lia.
  rewrite Znth_sublist by lia. rewrite Z.add_0_r. rewrite ll_Znth_cl_lens by lia. cbv zeta.
  destruct (ll_clpos_order j ltac:(lia)) as [R E].
  rewrite <- E at 1. rewrite P by lia. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Building at_mode                                                                               *)

Lemma ll_mk_at G s c hold bits out k nlen ndist cls toks syms :
  hold_ok G c hold bits -> i_mode s = LENLENS -> in_blk G s k -> blk G k = Dynamic nlen ndist cls toks syms ->
  out = outk G k -> i_nlen s = nlen -> i_ndist s = ndist -> i_ncode s = Zlength cls ->
  0 <= i_have s <= Zlength cls ->
  (forall i, 0 <= i < i_have s -> Znth (Znth i order) (i_lens s) = Znth i cls) ->
  8 * c - bits = bpos G k + 17 + 3 * i_have s -> bits < 8 ->
  at_mode G s c hold bits out.
Proof.
  intros HO Md IB BK Out Nl Nd Nc Hv Hls Q Bb. split; [exact HO|].
  right. right. right. right. right. right. left. split; [exact Md|].
  exists k, nlen, ndist, cls, toks, syms.
  refine (conj IB (conj BK (conj Out (conj Nl (conj Nd (conj Nc (conj Hv (conj Hls (conj Q Bb))))))))).
Qed.

Lemma ll_mk_cl G s c hold bits out k nlen ndist cls toks syms :
  hold_ok G c hold bits -> i_mode s = CODELENS -> in_blk G s k -> blk G k = Dynamic nlen ndist cls toks syms ->
  out = outk G k -> i_nlen s = nlen -> i_ndist s = ndist -> i_have s = 0 ->
  tdec s (i_lencode s) (i_lenbits s) CODES (cl_lens cls) ->
  8 * c - bits = bpos G k + 17 + 3 * Zlength cls -> bits < 8 ->
  at_mode G s c hold bits out.
Proof.
  intros HO Md IB BK Out Nl Nd Hv TD Q Bb. split; [exact HO|].
  right. right. right. right. right. right. right. left. split; [exact Md|].
  exists k, nlen, ndist, cls, toks, syms, 0.
  assert (T0: toks_upto toks 0 = []) by reflexivity.
  assert (O0: tok_off (cl_lens cls) toks 0 = 0) by reflexivity.
  refine (conj IB (conj BK (conj Out (conj Nl (conj Nd (conj _ (conj _ (conj _ (conj TD (conj _ _)))))))))).
  - pose proof (Zlength_nonneg toks). lia.
  - rewrite T0, Hv. reflexivity.
  - rewrite T0, Hv. reflexivity.
  - rewrite O0. lia.
  - left. exact Bb.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* One iteration of lenlens_loop                                                                  *)

Lemma ll_step (DK: dkit_stmt) G pos inp ob m :
  ictx G pos inp -> slen_ok G -> tin G pos inp ob m -> m_mode m = LENLENS -> i_have (m_s m) < i_ncode (m_s m) ->
  let m1 := needbits 3 m in
  (m_leave m1 = 1 /\ tt_ok G pos inp ob (m_ow m) (TTDone (IBrk m1))) \/
  (m_leave m1 = 0 /\
   let s := m_s m1 in
   let m3 := dropbits 3 (upd_s m1 (fun _ => set_i_have (set_i_lens s (upd_Znth (Znth (i_have s) order) (i_lens s)
                                                       (bitsn m1 3))) (i_have s + 1))) in
   tin G pos inp ob m3 /\ m_mode m3 = LENLENS /\ m_ow m3 = m_ow m /\
   i_have (m_s m3) = i_have (m_s m) + 1 /\ i_ncode (m_s m3) = i_ncode (m_s m)).
Proof.
  intros C SO TI Md Hlt m1.
  pose proof TI as (K & Lv & Nx & TB).
  pose proof C as (OK & P0 & PL & IE).
  destruct (ll_at_mode _ _ _ _ _ _ (kd_at _ _ _ _ _ K) Md) as [HO AL].
  destruct AL as (k & nlen & ndist & cls & toks & syms & IB & BK & Out & Nl & Nd & Nc & Hv & Hls & Q & Bb).
  pose proof (ll_blk_ok G k OK (proj1 IB)) as BO. rewrite BK in BO. cbn [block_ok] in BO.
  destruct BO as (Bn & Bd & Bc & Bcf & Bcl & _).
  pose proof (ll_kd_ret _ _ _ _ _ K Md) as R0.
  assert (Hm: hb G pos inp m) by (split; [apply (kd_inp _ _ _ _ _ K)|split; [exact Nx|split; [lia|exact HO]]]).
  pose proof (proj1 HO) as HB0.
  destruct (hb_needbits DK G pos inp C 4 3 m Hm ltac:(lia) ltac:(simpl; lia)) as (H1 & Q1 & S1 & R1 & F1 & Bm & O).
  fold (needbits 3 m) in *. fold m1 in H1, Q1, S1, R1, F1, Bm, O.
  assert (Qm: qp pos m = bpos G k + 17 + 3 * i_have (m_s m)) by (unfold qp; lia).
  pose proof (dyn_len G k nlen ndist cls toks syms BK) as DL.
  pose proof (bpos_succ DK G k OK (proj1 IB)) as BS.
  pose proof (bpos_endpos DK G (k + 1) OK ltac:(destruct IB; lia)) as BE.
  pose proof (Zlength_nonneg (dyn_tkb cls toks)).
  pose proof (Zlength_nonneg (send_syms (dyn_ll nlen toks) (dyn_dl nlen ndist toks) syms)).
  assert (Md1: m_mode m1 = LENLENS) by (unfold m_mode; rewrite S1; exact Md).
  destruct O as [(L1 & N1 & B1) | (L1 & B1)].
  - (* out of input *)
    left. split; [exact L1|]. cbn [tt_ok].
    destruct H1 as (I1 & Nx1 & B64 & HO1).
    split; [|split; [apply (tf_ow _ _ F1)|split; [exact L1|split; [exact N1|]]]].
    + apply (kd_tfr G pos inp ob m m1 K); [rewrite Md; right; left; reflexivity | exact F1
          | rewrite Md1; right; left; reflexivity | congruence |].
      rewrite (tf_ow _ _ F1).
      apply (ll_mk_at G (m_s m1) _ _ _ _ k nlen ndist cls toks syms HO1 Md1); rewrite ?S1; try assumption.
      * unfold qp in Q1. lia.
      * pose proof (hb_bits_le G pos inp m1). lia.
    + apply (leave_slen G pos inp m1 3 SO N1 B1). rewrite Q1, Qm. lia.
  - (* the 3 bits *)
    right. rewrite Lv in L1. split; [exact L1|].
    cbv zeta.
    set (s := m_s m1).
    set (v := bitsn m1 3).
    set (m2 := upd_s m1 (fun _ => set_i_have (set_i_lens s (upd_Znth (Znth (i_have s) order) (i_lens s) v)) (i_have s + 1))).
    assert (Es: s = m_s m) by exact S1.
    assert (Hv3: v = Znth (i_have (m_s m)) cls).
    { unfold v. rewrite (hb_bitsn DK G pos inp m1 3 H1 ltac:(lia)). rewrite Q1, Qm.
      rewrite (dyn_sub_cl DK G k nlen ndist cls toks syms OK (proj1 IB) BK) by lia.
      rewrite bval_bits_le by lia. apply Z.mod_small.
      pose proof (Forall_Znth _ cls (i_have (m_s m)) ltac:(lia) Bcf) as F. cbv beta in F. simpl. lia. }
    assert (H2: hb G pos inp m2) by exact H1.
    destruct (hb_drop DK G pos inp m2 3 H2 ltac:(change (m_bits m2) with (m_bits m1); lia)) as (H3 & Q3 & B3).
    change (qp pos m2) with (qp pos m1) in Q3. change (m_bits m2) with (m_bits m1) in B3.
    set (m3 := dropbits 3 m2) in *.
    assert (Sm3: m_s m3 = set_i_have (set_i_lens (m_s m) (upd_Znth (Znth (i_have (m_s m)) order) (i_lens (m_s m)) v))
                                     (i_have (m_s m) + 1)) by (rewrite <- Es; reflexivity).
    destruct (ll_order_clpos (i_have (m_s m)) ltac:(lia)) as [Ro _].
    destruct TB as (T1 & T2 & T3).
    assert (F3: tfr m m3).
    { apply (tfr_trans m m1 m3 F1). unfold m3, m2. constructor; reflexivity. }
    assert (Md3: m_mode m3 = LENLENS) by (unfold m_mode; rewrite Sm3; ll_cbn; exact Md).
    assert (Ow3: m_ow m3 = m_ow m) by (apply (tf_ow _ _ F3)).
    split; [|split; [exact Md3|split; [exact Ow3|split; rewrite Sm3; ll_cbn; reflexivity]]].
    destruct H3 as (I3 & Nx3 & B643 & HO3).
    split; [|split; [exact L1|split; [exact Nx3|]]].
    2:{ unfold tabs_ok. rewrite Sm3. ll_cbn. rewrite upd_Znth_Zlength by lia. split; [exact T1|split; assumption]. }
    apply (kd_tfr G pos inp ob m m3 K); [rewrite Md; right; left; reflexivity | exact F3
          | rewrite Md3; right; left; reflexivity | change (m_ret m3) with (m_ret m1); congruence |].
    rewrite Ow3.
    apply (ll_mk_at G (m_s m3) _ _ _ _ k nlen ndist cls toks syms HO3 Md3); rewrite ?Sm3; ll_cbn; try assumption; try lia.
    + intros i Hi. destruct (Z.eq_dec i (i_have (m_s m))) as [->|Ne].
      * rewrite upd_Znth_same by lia. exact Hv3.
      * rewrite upd_Znth_diff by (try lia; destruct (ll_order_clpos i ltac:(lia)); try lia;
          intros Eq; apply Ne; apply (ll_order_inj i (i_have (m_s m))); lia).
        apply Hls. lia.
    + unfold qp in Q3, Q1. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* lenlens_loop                                                                                   *)

Lemma ll_loop (DK: dkit_stmt) G pos inp ob : ictx G pos inp -> slen_ok G ->
  forall n m, tin G pos inp ob m -> m_mode m = LENLENS -> i_ncode (m_s m) - i_have (m_s m) <= Z.of_nat n ->
  let m' := lenlens_loop n m in
  (m_leave m' = 1 /\ tt_ok G pos inp ob (m_ow m) (TTDone (IBrk m'))) \/
  (m_leave m' = 0 /\ tin G pos inp ob m' /\ m_mode m' = LENLENS /\ m_ow m' = m_ow m /\
   i_ncode (m_s m') <= i_have (m_s m')).
Proof.
  intros C SO n. induction n as [|n IH]; intros m TI Md Hn; cbn [lenlens_loop].
  - right. split; [exact (proj1 (proj2 TI))|]. split; [exact TI|]. split; [exact Md|]. split; [reflexivity|lia].
  - destruct (Z.ltb_spec (i_have (m_s m)) (i_ncode (m_s m))) as [Lt|Ge].
    + destruct (ll_step DK G pos inp ob m C SO TI Md Lt) as [(L1 & T1) | (L1 & T3)].
      * replace (m_leave (needbits 3 m) =? 1) with true by (rewrite L1; reflexivity).
        left. split; [exact L1 | exact T1].
      * replace (m_leave (needbits 3 m) =? 1) with false by (rewrite L1; reflexivity).
        cbv zeta in T3. destruct T3 as (TI3 & Md3 & Ow3 & Hv3 & Nc3).
        destruct (IH _ TI3 Md3 ltac:(lia)) as [(L4 & T4) | (L4 & T4 & M4 & O4 & H4)].
        -- left. split; [exact L4|]. rewrite Ow3 in T4. exact T4.
        -- right. split; [exact L4|]. split; [exact T4|]. split; [exact M4|]. split; [congruence | exact H4].
    + right. split; [exact (proj1 (proj2 TI))|]. split; [exact TI|]. split; [exact Md|]. split; [reflexivity|lia].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* After the loop: the zeros, the code length code table, CODELENS                                *)

Lemma ll_post (DK: dkit_stmt) (TD: tabdec_stmt) G pos inp ob m ow0 :
  ictx G pos inp -> tin G pos inp ob m -> m_mode m = LENLENS -> i_ncode (m_s m) <= i_have (m_s m) ->
  m_ow m = ow0 ->
  (forall m', tin G pos inp ob m' -> m_mode m' = CODELENS -> m_ow m' = ow0 -> tt_ok G pos inp ob ow0 (ttab_cl m')) ->
  tt_ok G pos inp ob ow0 (ttab_llpost m).
Proof.
  intros C TI Md Hge Ow HC.
  pose proof TI as (K & Lv & Nx & TB). destruct TB as (T1 & T2 & T3).
  pose proof C as (OK & P0 & PL & IE).
  destruct (ll_at_mode _ _ _ _ _ _ (kd_at _ _ _ _ _ K) Md) as [HO AL].
  destruct AL as (k & nlen & ndist & cls & toks & syms & IB & BK & Out & Nl & Nd & Nc & Hv & Hls & Q & Bb).
  pose proof (ll_blk_ok G k OK (proj1 IB)) as BO. rewrite BK in BO. cbn [block_ok] in BO.
  destruct BO as (Bn & Bd & Bc & Bcf & Bcl & _).
  assert (Hh: i_have (m_s m) = Zlength cls) by lia.
  destruct (ll_zero cls 19 (m_s m) ltac:(lia) ltac:(lia) ltac:(simpl; lia) T1) as (L & h & EZ & LL & PZ).
  { intros i Hi Hi19. unfold ll_ext. destruct (Z.ltb_spec i (Zlength cls)); [apply Hls; lia | lia]. }
  pose proof (ll_zero_cl cls L LL PZ) as ECL.
  unfold ttab_llpost. rewrite EZ.
  set (s1 := set_i_lenbits (set_i_distcode (set_i_lencode (set_i_next (set_i_have (set_i_lens (m_s m) L) h) 0)
               (TCodes 0)) (TCodes 0)) 7).
  assert (Ls1: i_lens s1 = L) by reflexivity.
  pose proof (td_cl TD s1 eq_refl ltac:(rewrite Ls1; exact LL) T2 T3 ltac:(rewrite Ls1, ECL; exact Bcl)) as TC.
  destruct (call_table CODES 0 19 7 s1) as [[[r codes] nxt] lb] eqn:E.
  destruct TC as [R0 TDs]. subst r.
  destruct (ll_codes s1 0 codes nxt lb eq_refl ltac:(rewrite Ls1; exact LL) T2 T3
              ltac:(rewrite Ls1, ECL; exact (proj1 Bcl)) E eq_refl) as [ZC FC].
  change (negb (0 =? 0)) with false. cbv iota.
  set (m2 := set_mode (upd_s (set_m_ret (set_m_s m (set_i_lenbits (set_i_next (set_i_codes s1 codes) nxt) lb)) 0)
                (fun s => set_i_have s 0)) CODELENS).
  assert (F: tfr m m2) by (constructor; reflexivity).
  assert (Md2: m_mode m2 = CODELENS) by reflexivity.
  apply HC; [|exact Md2|exact Ow].
  split; [|split; [exact Lv|split; [exact Nx|]]].
  2:{ split; [exact LL|split; [exact ZC|exact FC]]. }
  apply (kd_tfr G pos inp ob m m2 K); [rewrite Md; right; left; reflexivity | exact F
        | rewrite Md2; right; right; left; reflexivity | reflexivity |].
  rewrite (tf_ow _ _ F).
  assert (TD2: tdec (m_s m2) (i_lencode (m_s m2)) (i_lenbits (m_s m2)) CODES (cl_lens cls)).
  { rewrite <- ECL. exact (TDs (m_s m2) eq_refl). }
  assert (Q2: 8 * (pos + m_nx m2) - m_bits m2 = bpos G k + 17 + 3 * Zlength cls).
  { change (m_nx m2) with (m_nx m). change (m_bits m2) with (m_bits m). lia. }
  apply (ll_mk_cl G (m_s m2) _ _ _ _ k nlen ndist cls toks syms HO Md2 IB BK Out Nl Nd eq_refl TD2 Q2 Bb).
Qed.

Lemma part_ll : part_ll_stmt.
Proof.
  intros G pos inp ob m DK TD C SO TI Md HC.
  pose proof TI as (K & _ & _ & _).
  pose proof C as (OK & _).
  destruct (ll_at_mode _ _ _ _ _ _ (kd_at _ _ _ _ _ K) Md) as [_ AL].
  destruct AL as (k & nlen & ndist & cls & toks & syms & IB & BK & _ & _ & _ & Nc & Hv & _).
  pose proof (ll_blk_ok G k OK (proj1 IB)) as BO. rewrite BK in BO. cbn [block_ok] in BO.
  destruct BO as (_ & _ & Bc & _).
  unfold ttab_ll.
  destruct (ll_loop DK G pos inp ob C SO 19 m TI Md ltac:(simpl; lia))
    as [(L1 & T) | (L1 & TI' & Md' & Ow' & Hge)].
  - rewrite L1. exact T.
  - rewrite L1. apply (ll_post DK TD G pos inp ob _ (m_ow m) C TI' Md' Hge Ow' HC).
Qed.
