(* RT-I: copy of rfc1951/DecTabIter.v over the generalized definitions RTIGDefs.v. *)
(* Part of DecTab: one token of CODELENS.  Kit and statements: DecTabKit.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTIGDefs Zlib.proof.roundtrip.RTIGDecTabKit.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* Bits                                                                                           *)

Lemma bval_prefix l b : 0 <= b <= Zlength l -> bval (sublist 0 b l) = bval l mod 2 ^ b.
Proof.
  intros Hb. rewrite <- (sublist_same 0 (Zlength l) l) at 2 by reflexivity.
  rewrite (sublist_split 0 b (Zlength l) l) by lia. rewrite bval_app.
  rewrite Zlength_sublist by lia. rewrite Z.sub_0_r.
  pose proof (bval_range (sublist 0 b l)) as R. rewrite Zlength_sublist in R by lia. rewrite Z.sub_0_r in R.
  rewrite Z.mul_comm, Z.mod_add by lia. rewrite Z.mod_small; lia.
Qed.

Lemma Zlength_bits_msb c n : 0 <= n -> Zlength (bits_msb c n) = n.
Proof. intros. unfold bits_msb. rewrite Zlength_rev. apply Zlength_bits_le. lia. Qed.

Lemma Z_lor_split a L : 0 <= a -> 0 <= L -> a = Z.lor (a mod 2 ^ L) (Z.shiftl (Z.shiftr a L) L).
Proof.
  intros Ha HL. apply Z.bits_inj'. intros j Hj.
  rewrite Z.lor_spec. destruct (Z.ltb_spec j L).
  - rewrite Z.shiftl_spec_low by lia. rewrite orb_false_r. rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite Z.mod_pow2_bits_high by lia. rewrite Z.shiftl_spec by lia. rewrite Z.shiftr_spec by lia.
    simpl. f_equal. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The lookup of a code length code                                                               *)

Section Lookup.
Variables (K: dkit_stmt) (G: dctx) (pos: Z) (inp: list Z).
Hypothesis (C: ictx G pos inp).
Variables (s: istate) (T: tref) (root L sy rev: Z).
Hypotheses (Hroot: 0 <= root) (HL: 1 <= L <= 15).
(* the table: never a link at the root; the code of sy, followed by any bits, is sy's entry; a pattern that
   agrees with the code on b < L bits has an entry of more than b bits *)
Hypothesis NL: forall i, 0 <= i < 2 ^ root -> ref.is_link (e_op (tab_entry lenfix_list distfix_list s T i)) = false.
Hypothesis DEC: forall x, 0 <= x -> exists op val,
  twalk s T root (Z.lor rev (Z.shiftl x L)) = Some (op, val, L) /\ val = sy.
Hypothesis PR: forall b pat, 0 <= b < L -> 0 <= pat -> pat mod 2 ^ b = rev mod 2 ^ b ->
  b < e_bits (tab_entry lenfix_list distfix_list s T (pat mod 2 ^ root)).

(* the stream at the position: the code (rev: its value as read, least significant bit first) *)
Variable (cbits: list bool).
Hypotheses (Hcb: Zlength cbits = L) (Hrev: bval cbits = rev).

Lemma lk_stream m n : sublist (qp pos m) (qp pos m + L) (sbits G) = cbits -> 0 <= n <= L -> 0 <= qp pos m ->
  bval (sublist (qp pos m) (qp pos m + n) (sbits G)) = rev mod 2 ^ n.
Proof.
  intros SB Hn Hq. rewrite <- Hrev, <- bval_prefix by lia. rewrite <- SB.
  rewrite sublist_sublist by lia. f_equal. f_equal; lia.
Qed.

Lemma lk_full m : hb G pos inp m -> m_s m = s -> L <= m_bits m ->
  sublist (qp pos m) (qp pos m + L) (sbits G) = cbits ->
  e_val (tab_entry lenfix_list distfix_list s T (bitsn m root)) = sy /\
  e_bits (tab_entry lenfix_list distfix_list s T (bitsn m root)) = L.
Proof.
  intros H S B SB. pose proof (hb_bits_le G pos inp m H) as Bb.
  pose proof (lk_stream m L SB ltac:(lia) ltac:(unfold qp; lia)) as R.
  pose proof (hb_bitsn K G pos inp m L H ltac:(lia)) as BL. rewrite R in BL. unfold bitsn in BL.
  destruct H as (I & N & B64 & HO).
  pose proof (dk_hold_lt K G _ _ _ HO (ictx_bytes G pos inp C)) as HR.
  assert (Rr: 0 <= rev < 2 ^ L) by (rewrite <- Hrev, <- Hcb; apply bval_range).
  rewrite (Z.mod_small rev) in BL by lia.
  destruct (DEC (Z.shiftr (m_hold m) L) ltac:(apply Z.shiftr_nonneg; lia)) as (op & val & W & V).
  rewrite <- BL, <- Z_lor_split in W by lia.
  unfold twalk in W. rewrite NL in W by (apply Z.mod_pos_bound; lia).
  injection W as E1 E2 E3. unfold bitsn. split; congruence.
Qed.

Lemma lk_partial m : hb G pos inp m -> m_s m = s -> m_bits m < L ->
  sublist (qp pos m) (qp pos m + L) (sbits G) = cbits ->
  m_bits m < e_bits (tab_entry lenfix_list distfix_list s T (bitsn m root)).
Proof.
  intros H S B SB. pose proof (hb_bits_le G pos inp m H) as Bb.
  pose proof (lk_stream m (m_bits m) SB ltac:(lia) ltac:(unfold qp; lia)) as R.
  pose proof (hb_bitsn K G pos inp m (m_bits m) H ltac:(lia)) as BL. rewrite R in BL. unfold bitsn in BL.
  destruct H as (I & N & B64 & HO).
  pose proof (dk_hold_lt K G _ _ _ HO (ictx_bytes G pos inp C)) as HR.
  unfold bitsn. apply PR; [lia | lia | exact BL].
Qed.

Lemma lk_lookup : forall k m here m1 ok, hb G pos inp m -> m_s m = s ->
  sublist (qp pos m) (qp pos m + L) (sbits G) = cbits ->
  L <= m_bits m + 8 * Z.of_nat k ->
  lookup1_f k lenfix_list distfix_list T root m = (here, m1, ok) ->
  hb G pos inp m1 /\ qp pos m1 = qp pos m /\ m_s m1 = m_s m /\ m_ret m1 = m_ret m /\ tfr m m1 /\
  (ok = true -> m_leave m1 = m_leave m /\ e_val here = sy /\ e_bits here = L /\ L <= m_bits m1 /\
                (m_bits m1 = m_bits m \/ m_bits m1 < L + 8)) /\
  (ok = false -> m_leave m1 = 1 /\ m_nx m1 = Zlength inp /\ m_bits m1 < L).
Proof.
  induction k; intros m here m1 ok H S SB Hk E; cbn [lookup1_f] in E.
  - injection E as <- <- <-. simpl in Hk.
    destruct (lk_full m H S ltac:(lia) SB) as [V Bt]. rewrite <- S in V, Bt.
    split; [exact H|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [apply tfr_refl|]. split; [|discriminate]. intros _. split; [reflexivity|].
    split; [exact V|]. split; [exact Bt|]. split; [lia|]. left; reflexivity.
  - destruct (Z_lt_le_dec (m_bits m) L) as [Lt|Ge].
    + pose proof (lk_partial m H S Lt SB) as P. rewrite <- S in P.
      replace (e_bits (tab_entry lenfix_list distfix_list (m_s m) T (bitsn m root)) <=? m_bits m) with false in E
        by (symmetry; apply Z.leb_gt; exact P).
      destruct (Z.eqb_spec (m_have m) 0) as [Hv|Hv].
      * injection E as <- <- <-. destruct H as (I & N & B64 & HO).
        split; [split; [exact I | split; [exact N | split; [exact B64 | exact HO]]]|].
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [apply tfr_leave|].
        split; [discriminate|]. intros _. unfold m_have in Hv. rewrite I in Hv. cbn. split; [reflexivity|]. lia.
      * destruct (hb_pull K G pos inp C m H Hv ltac:(lia)) as (H1 & Q1 & B1).
        destruct (IHk (pull m) here m1 ok H1 S ltac:(rewrite Q1; exact SB) ltac:(rewrite B1; lia) E)
          as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
        split; [exact A1|]. split; [congruence|]. split; [exact A3|]. split; [exact A4|].
        split; [eapply tfr_trans; [apply bop_pull | exact A5]|]. split; [|exact A7].
        intros Ok. destruct (A6 Ok) as (D1 & D2 & D3 & D4 & D5). split; [exact D1|]. split; [exact D2|].
        split; [exact D3|]. split; [exact D4|]. right. rewrite B1 in D5. lia.
    + destruct (lk_full m H S Ge SB) as [V Bt]. rewrite <- S in V, Bt.
      rewrite Bt in E. replace (L <=? m_bits m) with true in E by (symmetry; apply Z.leb_le; exact Ge).
      injection E as <- <- <-.
      split; [exact H|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [apply tfr_refl|]. split; [|discriminate]. intros _. split; [reflexivity|].
      split; [exact V|]. split; [exact Bt|]. split; [lia|]. left; reflexivity.
Qed.

End Lookup.

(* ---------------------------------------------------------------------------------------------- *)
(* Tokens                                                                                         *)

Lemma tok_expand_app : forall l1 l2 prev, tok_expand prev (l1 ++ l2) = tok_expand (tok_expand prev l1) l2.
Proof. induction l1; intros; simpl; auto. Qed.

Lemma tok_expand_prefix : forall l prev, exists r, tok_expand prev l = prev ++ r.
Proof.
  induction l as [|t l IH]; intros prev; simpl.
  - exists []. rewrite app_nil_r. reflexivity.
  - destruct (IH (prev ++ tok_vals prev t)) as [r E]. exists (tok_vals prev t ++ r). rewrite E, app_assoc. reflexivity.
Qed.

Lemma toks_upto_all toks : toks_upto toks (Zlength toks) = dyn_lens toks.
Proof. unfold toks_upto, dyn_lens. rewrite firstn_all2 by (rewrite Zlength_correct; lia). reflexivity. Qed.

Lemma toks_upto_succ toks t : 0 <= t < Zlength toks ->
  toks_upto toks (t + 1) = toks_upto toks t ++ tok_vals (toks_upto toks t) (tok_at toks t).
Proof.
  intros Ht. unfold toks_upto, tok_at. rewrite Z2Nat.inj_add by lia. rewrite Nat.add_1_r.
  rewrite (firstn_S_nth (CLen 0)) by (rewrite Zlength_correct in Ht; lia).
  rewrite tok_expand_app. reflexivity.
Qed.

Lemma toks_upto_le toks t : 0 <= t <= Zlength toks -> exists r, dyn_lens toks = toks_upto toks t ++ r.
Proof.
  intros Ht. replace (dyn_lens toks) with (tok_expand (toks_upto toks t) (skipn (Z.to_nat t) toks)).
  - apply tok_expand_prefix.
  - unfold toks_upto, dyn_lens. rewrite <- tok_expand_app, firstn_skipn. reflexivity.
Qed.

Lemma toks_ok_at : forall cl toks prev t, toks_ok cl prev toks -> (t < length toks)%nat ->
  tok_ok cl (tok_expand prev (firstn t toks)) (nth t toks (CLen 0)).
Proof.
  intros cl toks. induction toks as [|x toks IH]; intros prev t H Ht; simpl in Ht; [lia|].
  destruct H as [H1 H2]. destruct t as [|t]; simpl; [exact H1|].
  apply IH; [exact H2 | lia].
Qed.

Lemma tok_vals_len cl prev tk : tok_ok cl prev tk ->
  Zlength (tok_vals prev tk) = match tk with CLen _ => 1 | CRep r => r | CZeros r => r end.
Proof.
  intros H. destruct tk as [l|r|r]; simpl; [reflexivity| |];
    rewrite Zlength_correct, repeat_length; simpl in H; lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The state                                                                                      *)

Lemma at_mode_cl G s c hold bits out : at_mode G s c hold bits out -> i_mode s = CODELENS ->
  hold_ok G c hold bits /\ at_codelens G s (8 * c - bits) bits out.
Proof.
  intros [H A] M. split; [exact H|]. rewrite M in A.
  repeat match type of A with
  | _ \/ _ => destruct A as [A|A]
  end;
  repeat match type of A with
  | (?a = ?b \/ _) /\ _ => destruct A as [[E|[E|E]] _] || destruct A as [[E|E] _]
  | (CODELENS = CODELENS) /\ _ => destruct A as [_ A]
  | ?x = ?y /\ _ => destruct A as [E _]
  end; try exact A;
  unfold CODELENS, HEAD, FLAGS, TIME, OS, Zlib.proof.inflate.Model.TYPE, TYPEDO, STORED, COPY_, COPY, TABLE,
    LENLENS, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, CHECK, LENGTH, DONE in *; lia.
Qed.

Lemma blocks_ok_nth : forall bs w out k, blocks_ok w out bs -> (k < length bs)%nat ->
  block_ok w (fold_left block_data (firstn k bs) out) (nth k bs (Stored [])).
Proof.
  induction bs as [|b bs IH]; intros w out k H Hk; simpl in Hk; [lia|].
  destruct H as [H1 H2]. destruct k as [|k]; simpl; [exact H1|]. apply IH; [exact H2 | lia].
Qed.

Lemma blk_ok G k : dctx_ok G -> 0 <= k < nblk G -> block_ok (2 ^ dc_wb G) (outk G k) (blk G k).
Proof.
  intros ((_ & _ & _ & (_ & _ & BO)) & _) Hk. unfold outk, blk, expand. apply blocks_ok_nth; [exact BO|].
  unfold nblk in Hk. rewrite Zlength_correct in Hk. lia.
Qed.

Lemma set_have_lens_idem s A h1 B h2 :
  set_i_have (set_i_lens (set_i_have (set_i_lens s A) h1) B) h2 = set_i_have (set_i_lens s B) h2.
Proof. destruct s; reflexivity. Qed.

Lemma lens_fill_eq : forall n v s, 0 <= i_have s -> i_have s + Z.of_nat n <= Zlength (i_lens s) ->
  exists L', lens_fill n v s = set_i_have (set_i_lens s L') (i_have s + Z.of_nat n) /\
    Zlength L' = Zlength (i_lens s) /\
    sublist 0 (i_have s + Z.of_nat n) L' = sublist 0 (i_have s) (i_lens s) ++ repeat v n.
Proof.
  induction n; intros v s H0 Hn; cbn [lens_fill].
  - exists (i_lens s). rewrite Z.add_0_r. split; [destruct s; reflexivity|]. split; [reflexivity|].
    rewrite app_nil_r. reflexivity.
  - set (s1 := set_i_have (set_i_lens s (upd_Znth (i_have s) (i_lens s) v)) (i_have s + 1)).
    assert (E1: i_have s1 = i_have s + 1) by reflexivity.
    assert (E2: i_lens s1 = upd_Znth (i_have s) (i_lens s) v) by reflexivity.
    assert (E3: Zlength (i_lens s1) = Zlength (i_lens s)) by (rewrite E2, upd_Znth_Zlength; lia).
    destruct (IHn v s1 ltac:(lia) ltac:(lia)) as (L' & F & LL & SL).
    exists L'. rewrite F. split; [rewrite E1; unfold s1; rewrite set_have_lens_idem; f_equal; lia|].
    split; [congruence|].
    replace (i_have s + Z.of_nat (S n)) with (i_have s1 + Z.of_nat n) by lia. rewrite SL, E1, E2.
    rewrite (sublist_split 0 (i_have s) (i_have s + 1)) by (rewrite ?upd_Znth_Zlength; lia).
    rewrite sublist_upd_Znth_l by lia. rewrite (sublist_len_1 (i_have s)) by (rewrite ?upd_Znth_Zlength; lia).
    rewrite upd_Znth_same by lia. rewrite <- app_assoc. reflexivity.
Qed.

Lemma twalk_codes s s' t root pat : i_codes s' = i_codes s -> twalk s' t root pat = twalk s t root pat.
Proof. intros E. unfold twalk, tab_entry. destruct t; rewrite ?E; reflexivity. Qed.

Lemma tdec_codes s s' t root ty lens : i_codes s' = i_codes s -> tdec s t root ty lens -> tdec s' t root ty lens.
Proof.
  intros E (R & D & P & N).
  assert (TE: forall i, tab_entry lenfix_list distfix_list s' t i = tab_entry lenfix_list distfix_list s t i)
    by (intros i; unfold tab_entry; destruct t; rewrite ?E; reflexivity).
  split; [exact R|]. split; [|split].
  - intros sy Hs Hn x Hx. destruct (D sy Hs Hn x Hx) as (op & val & W & M).
    exists op, val. rewrite (twalk_codes s s') by exact E. split; assumption.
  - intros sy Hs Hn b pat Hb Hp Hm. pose proof (P sy Hs Hn b pat Hb Hp Hm) as Q. cbv zeta in Q |- *.
    rewrite !TE. exact Q.
  - intros Ht i Hi. rewrite TE. exact (N Ht i Hi).
Qed.

Ltac cbn_rec := cbn [m_s m_inp m_ow m_aout m_out m_tout m_nx m_hold m_bits m_leave m_ret set_m_s
  i_mode i_last i_wrap i_flags i_check i_total i_head i_wbits i_wsize i_whave i_wnext i_wdata i_have i_lens
  i_codes i_nlen i_ndist i_lencode i_lenbits set_i_have set_i_lens] in *.

(* the state after a whole token *)
Lemma iter_next G pos inp ob m m2 k nlen ndist cls toks syms t L' :
  tin G pos inp ob m -> m_mode m = CODELENS ->
  in_blk G (m_s m) k -> blk G k = Dynamic nlen ndist cls toks syms -> ob ++ m_ow m = outk G k ->
  i_nlen (m_s m) = nlen -> i_ndist (m_s m) = ndist ->
  0 <= t < Zlength toks -> i_have (m_s m) = Zlength (toks_upto toks t) ->
  tdec (m_s m) (i_lencode (m_s m)) (i_lenbits (m_s m)) CODES (cl_lens cls) ->
  hb G pos inp m2 -> qp pos m2 = bpos G k + 17 + 3 * Zlength cls + tok_off (cl_lens cls) toks (t + 1) ->
  m_bits m2 < 8 -> tfr m m2 -> m_leave m2 = 0 -> m_ret m2 = m_ret m -> m_s m2 = m_s m ->
  Zlength L' = 320 -> sublist 0 (Zlength (toks_upto toks (t + 1))) L' = toks_upto toks (t + 1) ->
  Zlength (toks_upto toks t) < Zlength (toks_upto toks (t + 1)) ->
  let m' := set_m_s m2 (set_i_have (set_i_lens (m_s m) L') (Zlength (toks_upto toks (t + 1)))) in
  tin G pos inp ob m' /\ m_mode m' = CODELENS /\ m_ow m' = m_ow m /\ i_have (m_s m) < i_have (m_s m').
Proof.
  intros (K & Lv & Nx & TB) Md IB BK Out Nl Nd Ht Hv TD H2 Q2 B2 F2 L2 R2 S2 LL SL Lt m'.
  assert (F: tfr m m').
  { destruct F2. unfold m'. constructor; cbn_rec; congruence. }
  assert (M': m_mode m' = CODELENS) by (unfold m', m_mode in *; cbn_rec; exact Md).
  assert (Ow: m_ow m' = m_ow m) by (apply (tf_ow _ _ F)).
  assert (R: m_ret m = Z_OK).
  { pose proof (kd_ret _ _ _ _ _ K) as E. rewrite Md in E. rewrite E. reflexivity. }
  destruct H2 as (I2 & N2 & B64 & HO2).
  split; [|split; [exact M'|split; [exact Ow|]]].
  2:{ unfold m'. cbn_rec. lia. }
  split; [|split; [unfold m'; cbn_rec; exact L2|split; [unfold m'; cbn_rec; lia|]]].
  2:{ destruct TB as (T1 & T2 & T3). unfold m', tabs_ok. cbn_rec. split; [exact LL|]. split; assumption. }
  apply (kd_tfr G pos inp ob m m' K); [rewrite Md; right; right; reflexivity | exact F
        | rewrite M'; right; right; left; reflexivity | unfold m'; cbn_rec; congruence |].
  split; [unfold m'; cbn_rec; exact HO2|].
  right. right. right. right. right. right. right. left. split; [exact M'|].
  exists k, nlen, ndist, cls, toks, syms, (t + 1).
  destruct IB as [IB1 IB2].
  unfold m'. cbn_rec. rewrite (tf_ow _ _ F2).
  split; [split; [exact IB1 | cbn_rec; exact IB2]|]. split; [exact BK|]. split; [exact Out|].
  split; [exact Nl|]. split; [exact Nd|]. split; [lia|]. split; [reflexivity|]. split; [exact SL|].
  split; [apply (tdec_codes (m_s m)); [reflexivity | exact TD]|].
  unfold qp in Q2. split; [lia|]. left; exact B2.
Qed.

(* leaving inside a token *)
Lemma iter_leave (DK: dkit_stmt) G pos inp ob m m1 k nlen ndist cls toks syms t :
  dctx_ok G -> slen_ok G -> tin G pos inp ob m -> m_mode m = CODELENS ->
  in_blk G (m_s m) k -> blk G k = Dynamic nlen ndist cls toks syms -> ob ++ m_ow m = outk G k ->
  i_nlen (m_s m) = nlen -> i_ndist (m_s m) = ndist ->
  0 <= t < Zlength toks -> i_have (m_s m) = Zlength (toks_upto toks t) ->
  sublist 0 (i_have (m_s m)) (i_lens (m_s m)) = toks_upto toks t ->
  tdec (m_s m) (i_lencode (m_s m)) (i_lenbits (m_s m)) CODES (cl_lens cls) ->
  hb G pos inp m1 -> qp pos m1 = bpos G k + 17 + 3 * Zlength cls + tok_off (cl_lens cls) toks t ->
  m_bits m1 < Zlength (send_tok (cl_lens cls) (tok_at toks t)) ->
  tfr m m1 -> m_leave m1 = 1 -> m_nx m1 = Zlength inp -> m_ret m1 = m_ret m -> m_s m1 = m_s m ->
  tt_ok G pos inp ob (m_ow m) (TTDone (IBrk m1)).
Proof.
  intros OK SO (K & Lv & Nx & TB) Md IB BK Out Nl Nd Ht Hv Ls TD H1 Q1 B1 F1 L1 N1 R1 S1.
  assert (R: m_ret m = Z_OK).
  { pose proof (kd_ret _ _ _ _ _ K) as E. rewrite Md in E. rewrite E. reflexivity. }
  cbn [tt_ok]. split; [|split; [apply (tf_ow _ _ F1)|split; [exact L1|split; [exact N1|]]]].
  - destruct H1 as (I1 & Nx1 & B64 & HO1).
    apply (kd_tfr G pos inp ob m m1 K); [rewrite Md; right; right; reflexivity | exact F1
          | unfold m_mode; rewrite S1; right; right; left; exact Md | congruence |].
    split; [exact HO1|].
    right. right. right. right. right. right. right. left. split; [unfold m_mode in Md; rewrite S1; exact Md|].
    exists k, nlen, ndist, cls, toks, syms, t. rewrite S1, (tf_ow _ _ F1).
    split; [exact IB|]. split; [exact BK|]. split; [exact Out|]. split; [exact Nl|]. split; [exact Nd|].
    split; [lia|]. split; [exact Hv|]. split; [exact Ls|]. split; [exact TD|].
    unfold qp in Q1. split; [lia|]. right. split; [lia | exact B1].
  - destruct IB as [IB1 _].
    apply (leave_slen G pos inp m1 (Zlength (send_tok (cl_lens cls) (tok_at toks t))) SO N1 B1).
    rewrite Q1. pose proof (tok_off_succ G k cls toks t Ht) as E.
    pose proof (tok_off_range G k cls toks (t + 1) ltac:(lia)) as RR.
    pose proof (dyn_toks_end DK G k nlen ndist cls toks syms OK IB1 BK) as DE.
    pose proof (bpos_endpos DK G (k + 1) OK ltac:(lia)). lia.
Qed.

(* a token: its code length code symbol, the number and value of its extra bits *)
Definition tsym (tk: cltok) : Z := match tk with CLen l => l | CRep _ => 16 | CZeros r => if r <=? 10 then 17 else 18 end.
Definition text (tk: cltok) : Z := match tk with CLen _ => 0 | CRep _ => 2 | CZeros r => if r <=? 10 then 3 else 7 end.
Definition tval (tk: cltok) : Z := match tk with CLen _ => 0 | CRep r => r - 3 | CZeros r => if r <=? 10 then r - 3 else r - 11 end.

Lemma send_tok_split cl tk : send_tok cl tk = send_sym cl (tsym tk) ++ bits_le (tval tk) (text tk).
Proof. destruct tk as [l|r|r]; simpl; [rewrite app_nil_r; reflexivity | reflexivity |]. destruct (r <=? 10); reflexivity. Qed.

(* NEEDBITS(L + e), DROPBITS(L), BITS(e), DROPBITS(e) after the lookup of a code of L bits *)
Lemma read_extra (K: dkit_stmt) G pos inp m1 q bits0 L e xv :
  ictx G pos inp -> hb G pos inp m1 -> qp pos m1 = q -> 1 <= L <= 15 -> L <= m_bits m1 ->
  (m_bits m1 = bits0 \/ m_bits m1 < L + 8) -> (bits0 < 8 \/ bits0 < L + e) -> 1 <= e <= 7 -> 0 <= xv < 2 ^ e ->
  sublist (q + L) (q + L + e) (sbits G) = bits_le xv e ->
  let m2 := needbits (L + e) m1 in
  m_s m2 = m_s m1 /\ m_ret m2 = m_ret m1 /\ tfr m1 m2 /\
  ((m_leave m2 = 1 /\ hb G pos inp m2 /\ qp pos m2 = q /\ m_bits m2 < L + e /\ m_nx m2 = Zlength inp) \/
   (m_leave m2 = m_leave m1 /\ L <= m_bits m2 /\ bitsn (dropbits L m2) e = xv /\
    let m4 := dropbits e (dropbits L m2) in
    hb G pos inp m4 /\ qp pos m4 = q + L + e /\ m_bits m4 < 8)).
Proof.
  intros C H1 Q1 HL B1 B10 B0 He Hx SE m2.
  destruct (hb_needbits K G pos inp C 4 (L + e) m1 H1 ltac:(lia) ltac:(simpl; lia))
    as (H2 & Q2 & S2 & R2 & F2 & Bm & O).
  fold (needbits (L + e) m1) in *. fold m2 in H2, Q2, S2, R2, F2, Bm, O.
  split; [exact S2|]. split; [exact R2|]. split; [exact F2|].
  destruct O as [(L2 & N2 & Bl) | (L2 & Bg)].
  - left. split; [exact L2|]. split; [exact H2|]. split; [congruence|]. split; [exact Bl | exact N2].
  - right. split; [exact L2|]. split; [lia|].
    destruct (hb_drop K G pos inp m2 L H2 ltac:(lia)) as (H3 & Q3 & B3).
    split.
    + rewrite (hb_bitsn K G pos inp _ e H3 ltac:(lia)). rewrite Q3, Q2, Q1, SE, bval_bits_le by lia.
      apply Z.mod_small; lia.
    + destruct (hb_drop K G pos inp _ e H3 ltac:(lia)) as (H4 & Q4 & B4).
      split; [exact H4|]. split; [lia|]. rewrite B4, B3.
      pose proof (Z.le_max_l (m_bits m1) (L + e + 7)). pose proof (Z.le_max_r (m_bits m1) (L + e + 7)).
      destruct (Z.max_spec (m_bits m1) (L + e + 7)) as [[Ea Eb]|[Ea Eb]]; rewrite Eb in Bm; lia.
Qed.

Lemma last_Znth_Z : forall (l: list Z), l <> [] -> last l 0 = Znth (Zlength l - 1) l.
Proof.
  induction l as [|x l IH]; intros H; [congruence|].
  destruct l as [|y l].
  - reflexivity.
  - change (last (x :: y :: l) 0) with (last (y :: l) 0). rewrite IH by discriminate.
    symmetry. rewrite Znth_pos_cons by (rewrite !Zlength_cons; pose proof (Zlength_nonneg l); lia).
    f_equal. rewrite !Zlength_cons. lia.
Qed.

(* the state after a whole token that fills n lengths of value v *)
Lemma iter_fill G pos inp ob m m2 k nlen ndist cls toks syms t n v :
  tin G pos inp ob m -> m_mode m = CODELENS ->
  in_blk G (m_s m) k -> blk G k = Dynamic nlen ndist cls toks syms -> ob ++ m_ow m = outk G k ->
  i_nlen (m_s m) = nlen -> i_ndist (m_s m) = ndist ->
  0 <= t < Zlength toks -> i_have (m_s m) = Zlength (toks_upto toks t) ->
  sublist 0 (i_have (m_s m)) (i_lens (m_s m)) = toks_upto toks t ->
  tdec (m_s m) (i_lencode (m_s m)) (i_lenbits (m_s m)) CODES (cl_lens cls) ->
  hb G pos inp m2 -> qp pos m2 = bpos G k + 17 + 3 * Zlength cls + tok_off (cl_lens cls) toks (t + 1) ->
  m_bits m2 < 8 -> tfr m m2 -> m_leave m2 = 0 -> m_ret m2 = m_ret m -> m_s m2 = m_s m ->
  1 <= n -> tok_vals (toks_upto toks t) (tok_at toks t) = repeat v (Z.to_nat n) ->
  i_have (m_s m) + n <= 320 ->
  let m' := upd_s m2 (lens_fill (Z.to_nat n) v) in
  tin G pos inp ob m' /\ m_mode m' = CODELENS /\ m_ow m' = m_ow m /\ i_have (m_s m) < i_have (m_s m').
Proof.
  intros TI Md IB BK Out Nl Nd Ht Hv Ls TD H2 Q2 B2 F2 L2 R2 S2 Hn Tv Hle m'.
  pose proof TI as (_ & _ & _ & (TL & _)). pose proof (Zlength_nonneg (toks_upto toks t)).
  destruct (lens_fill_eq (Z.to_nat n) v (m_s m) ltac:(lia) ltac:(lia)) as (L' & EF & LL & SL).
  assert (Hs: Zlength (toks_upto toks (t + 1)) = i_have (m_s m) + n).
  { rewrite toks_upto_succ by lia. rewrite Zlength_app, Tv. rewrite (Zlength_correct (repeat v _)), repeat_length.
    lia. }
  assert (E: m' = set_m_s m2 (set_i_have (set_i_lens (m_s m) L') (Zlength (toks_upto toks (t + 1))))).
  { unfold m', upd_s. rewrite S2, EF, Hs. do 2 f_equal. lia. }
  rewrite E. apply (iter_next G pos inp ob m m2 k nlen ndist cls toks syms t L'); auto; try lia.
  - rewrite Hs. rewrite Z2Nat.id in SL by lia. rewrite SL, Ls, toks_upto_succ, Tv by lia. reflexivity.
Qed.

Lemma means_codes sy op val : ref.means_symbol CODES sy op val = true -> val = sy.
Proof.
  intros M. unfold ref.means_symbol, ref.sym_kind, ref.sym_value in M. rewrite Z.eqb_refl in M.
  simpl in M. apply andb_true_iff in M. destruct M as [_ M]. apply Z.eqb_eq in M. exact M.
Qed.

Lemma ms_drop n x : m_s (dropbits n x) = m_s x.
Proof. reflexivity. Qed.
Lemma mmode_drop n x : m_mode (dropbits n x) = m_mode x.
Proof. reflexivity. Qed.
Lemma mleave_drop n x : m_leave (dropbits n x) = m_leave x.
Proof. reflexivity. Qed.
Lemma mret_drop n x : m_ret (dropbits n x) = m_ret x.
Proof. reflexivity. Qed.

Lemma Zlength_pos_nonnil {A} (l: list A) : l <> [] -> 0 < Zlength l.
Proof. destruct l; [congruence|]. rewrite Zlength_cons. pose proof (Zlength_nonneg l). lia. Qed.

(* what CODELENS's lookup needs of the code length code table beyond tdec *)
Definition cl_extra (s: istate) (T: tref) (root: Z) (lens: list Z) : Prop :=
  (forall i, 0 <= i < 2 ^ root -> ref.is_link (e_op (tab_entry lenfix_list distfix_list s T i)) = false) /\
  (forall sy, 0 <= sy < Zlength lens -> Znth sy lens <> 0 -> forall b pat, 0 <= b < Znth sy lens -> 0 <= pat ->
     pat mod 2 ^ b = ref.reverse_bits (code lens sy) (Znth sy lens) mod 2 ^ b ->
     b < e_bits (tab_entry lenfix_list distfix_list s T (pat mod 2 ^ root))).

Lemma part_iter_x (X: forall s T root lens, tdec s T root CODES lens -> cl_extra s T root lens) : part_iter_stmt.
Proof.
  intros G pos inp ob m DK C SO TI Md Hh.
  pose proof TI as (K & Lv & Nx & TB).
  pose proof C as (OK & P0 & PL & IE).
  pose proof (kd_at _ _ _ _ _ K) as A.
  destruct (at_mode_cl _ _ _ _ _ _ A Md) as [HO AC].
  destruct AC as (k & nlen & ndist & cls & toks & syms & t & IB & BK & Out & Nl & Nd & Ht & Hv & Ls & TD & Q & BB).
  pose proof (blk_ok G k OK (proj1 IB)) as BO. rewrite BK in BO. cbn [block_ok] in BO.
  destruct BO as (Bn & Bd & Bc & Bcf & Bcl & Btk & Blen & Bll & Bdl & Bsy).
  assert (Htt: t < Zlength toks).
  { destruct (Z.eq_dec t (Zlength toks)) as [E|E]; [|lia]. rewrite E, toks_upto_all in Hv. rewrite Hv, Nl, Nd in Hh. lia. }
  assert (Hcl: Zlength (cl_lens cls) = 19) by (unfold cl_lens; rewrite Zlength_map, Zlength_correct, seq_length; reflexivity).
  assert (TO: tok_ok (cl_lens cls) (toks_upto toks t) (tok_at toks t)).
  { unfold tok_at, toks_upto. apply toks_ok_at; [exact Btk | rewrite Zlength_correct in Htt; lia]. }
  pose proof (dyn_sub_tok DK G k nlen ndist cls toks syms OK (proj1 IB) BK t ltac:(lia)) as SBt. cbv zeta in SBt.
  pose proof (tok_off_succ G k cls toks t ltac:(lia)) as TOS.
  pose proof (tok_off_range G k cls toks t ltac:(lia)) as TOR.
  pose proof (bpos_ge_D0 G k). pose proof (D0_nonneg G).
  set (cl := cl_lens cls) in *.
  set (q := bpos G k + 17 + 3 * Zlength cls + tok_off cl toks t) in *.
  set (tk := tok_at toks t) in *.
  set (sy := tsym tk).
  assert (Hsy: 0 <= sy <= 18 /\ Znth sy cl <> 0).
  { unfold sy, tsym. clearbody tk. destruct tk as [l|r|r]; cbn [tok_ok] in TO; [lia | split; [lia | tauto] |].
    destruct (r <=? 10); split; try lia; tauto. }
  set (L := Znth sy cl).
  assert (HL: 1 <= L <= 7).
  { pose proof (Forall_Znth _ cl sy ltac:(lia) (proj1 Bcl)) as F. cbv beta in F. fold L in F. destruct Hsy. lia. }
  assert (Hte: 0 <= text tk <= 7) by (unfold text; destruct tk; [lia | lia | destruct (r <=? 10); lia]).
  assert (Hst: Zlength (send_tok cl tk) = L + text tk).
  { rewrite send_tok_split, Zlength_app. unfold send_sym. fold sy L. rewrite Zlength_bits_msb, Zlength_bits_le by lia.
    reflexivity. }
  rewrite Hst in SBt, TOS. replace (q + (L + text tk)) with (q + L + text tk) in SBt by lia.
  assert (SBc: sublist q (q + L) (sbits G) = send_sym cl sy).
  { replace (sublist q (q + L) (sbits G)) with (sublist 0 L (sublist q (q + L + text tk) (sbits G)))
      by (rewrite sublist_sublist by lia; f_equal; lia).
    rewrite SBt, send_tok_split. fold sy. unfold send_sym. fold L.
    rewrite sublist_app1 by (rewrite ?Zlength_bits_msb; lia).
    apply sublist_same; [reflexivity | rewrite Zlength_bits_msb; lia]. }
  assert (SBe: sublist (q + L) (q + L + text tk) (sbits G) = bits_le (tval tk) (text tk)).
  { replace (sublist (q + L) (q + L + text tk) (sbits G)) with (sublist L (L + text tk) (sublist q (q + L + text tk) (sbits G)))
      by (rewrite sublist_sublist by lia; f_equal; lia).
    rewrite SBt, send_tok_split. fold sy. unfold send_sym. fold L.
    rewrite sublist_app2 by (rewrite Zlength_bits_msb; lia).
    rewrite Zlength_bits_msb by lia. apply sublist_same; [lia | rewrite Zlength_bits_le; lia]. }
  destruct (X _ _ _ _ TD) as [NL PR].
  assert (Hm: hb G pos inp m).
  { split; [apply (kd_inp _ _ _ _ _ K)|]. split; [exact Nx|]. split; [|exact HO].
    destruct BB as [BB|[_ BB]]; [lia|]. rewrite Hst in BB. lia. }
  assert (Qm: qp pos m = q) by (unfold qp; exact Q).
  pose proof (proj1 HO) as HB0.
  assert (DEC: forall x, 0 <= x -> exists op val,
    twalk (m_s m) (i_lencode (m_s m)) (i_lenbits (m_s m)) (Z.lor (ref.reverse_bits (code cl sy) L) (Z.shiftl x L))
      = Some (op, val, L) /\ val = sy).
  { intros x Hx. destruct TD as (_ & TDc & _ & _). destruct (TDc sy ltac:(lia) (proj2 Hsy) x Hx) as (op & val & W & M).
    exists op, val. split; [exact W | exact (means_codes _ _ _ M)]. }
  unfold codelens_iter. cbv zeta.
  destruct (lookup1 lenfix_list distfix_list (i_lencode (m_s m)) (i_lenbits (m_s m)) m) as [[here m1] ok] eqn:E.
  destruct (lk_lookup DK G pos inp C (m_s m) (i_lencode (m_s m)) (i_lenbits (m_s m)) L sy
              (ref.reverse_bits (code cl sy) L) ltac:(destruct TD; lia) ltac:(lia) NL
              DEC (fun b pat Hb Hp Hq => PR sy ltac:(lia) (proj2 Hsy) b pat Hb Hp Hq) (send_sym cl sy)
              ltac:(unfold send_sym; apply Zlength_bits_msb; lia) ltac:(unfold send_sym; apply bval_bits_msb; lia)
              3 m here m1 ok Hm eq_refl ltac:(rewrite Qm; exact SBc) ltac:(simpl; lia) E)
    as (H1 & Q1 & S1 & R1 & F1 & OKt & OKf).
  rewrite Qm in Q1.
  assert (Ht1: 0 <= t < Zlength toks) by lia.
  assert (Lle: Zlength (toks_upto toks (t + 1)) <= nlen + ndist).
  { destruct (toks_upto_le toks (t + 1) ltac:(lia)) as [rr Er]. rewrite <- Blen, Er, Zlength_app.
    pose proof (Zlength_nonneg rr). lia. }
  assert (Etk: tok_at toks t = tk) by reflexivity.
  assert (Esy: sy = tsym tk) by reflexivity.
  assert (EL: L = Znth sy cl) by reflexivity.
  assert (Eq: q = bpos G k + 17 + 3 * Zlength cls + tok_off cl toks t) by reflexivity.
  clearbody L sy tk q.
  destruct ok.
  2:{ cbn [negb]. cbv iota. destruct (OKf eq_refl) as (L1 & N1 & B1).
      apply (iter_leave DK G pos inp ob m m1 k nlen ndist cls toks syms t OK SO TI Md IB BK Out Nl Nd Ht1 Hv Ls TD H1).
      - rewrite Q1, Eq. reflexivity.
      - fold cl. rewrite Etk, Hst. lia.
      - exact F1.
      - exact L1.
      - exact N1.
      - exact R1.
      - exact S1. }
  destruct (OKt eq_refl) as (L1 & Ev & Eb & BL1 & B1o). rewrite Ev, Eb. cbn [negb].
  rewrite Lv in L1.
  destruct tk as [l|r|r]; cbn [tsym text tval tok_ok] in Esy, TO, Hte, SBe, Hst, TOS, SBt.
  - (* CLen *)
    subst sy. replace (l <? 16) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota beta.
    destruct (hb_drop DK G pos inp m1 L H1 ltac:(lia)) as (H2 & Q2 & B2).
    change (upd_s (dropbits L m1) (fun s => set_i_have (set_i_lens s (upd_Znth (i_have s) (i_lens s) l)) (i_have s + 1)))
      with (upd_s (dropbits L m1) (lens_fill (Z.to_nat 1) l)).
    apply (iter_fill G pos inp ob m (dropbits L m1) k nlen ndist cls toks syms t 1 l TI Md IB BK Out Nl Nd Ht1 Hv Ls TD H2).
    + rewrite Q2, Q1, Eq. fold cl. rewrite TOS. lia.
    + rewrite B2. destruct B1o as [B1o|B1o]; [|lia]. destruct BB as [BB|[_ BB]]; [lia|]. rewrite Hst in BB. lia.
    + eapply tfr_trans; [exact F1 | apply bop_drop].
    + exact L1.
    + exact R1.
    + exact S1.
    + lia.
    + rewrite Etk. reflexivity.
    + rewrite Hv. lia.
  - (* CRep *)
    subst sy. destruct TO as (TOn & TOr & TO16).
    replace (16 <? 16) with false by reflexivity. replace (16 =? 16) with true by reflexivity. cbv iota beta.
    destruct (read_extra DK G pos inp m1 q (m_bits m) L 2 (r - 3) C H1 Q1 ltac:(lia) BL1 B1o
                ltac:(destruct BB as [BB|[_ BB]]; [left; lia | right; rewrite Hst in BB; lia]) ltac:(lia)
                ltac:(simpl; lia) SBe)
      as (S2 & R2 & F2 & [(Lv2 & H2 & Q2 & B2 & N2) | (Lv2 & BL2 & BV & H4 & Q4 & B4)]).
    + rewrite Lv2. replace (1 =? 1) with true by reflexivity. cbv iota beta. cbn [negb].
      apply (iter_leave DK G pos inp ob m (needbits (L + 2) m1) k nlen ndist cls toks syms t OK SO TI Md IB BK Out
               Nl Nd Ht1 Hv Ls TD H2).
      * rewrite Q2, Eq. reflexivity.
      * fold cl. rewrite Etk, Hst. lia.
      * eapply tfr_trans; [exact F1 | exact F2].
      * exact Lv2.
      * exact N2.
      * congruence.
      * congruence.
    + rewrite Lv2, L1. replace (0 =? 1) with false by reflexivity. cbv iota beta.
      rewrite !ms_drop, S2, S1.
      assert (Hv0: 0 < i_have (m_s m)) by (rewrite Hv; apply Zlength_pos_nonnil; exact TOn).
      replace (i_have (m_s m) =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota beta.
      rewrite BV. cbn [negb]. rewrite mmode_drop, mmode_drop.
      replace (m_mode (needbits (L + 2) m1) =? BAD) with false
        by (unfold m_mode; rewrite S2, S1; fold (m_mode m); rewrite Md; reflexivity).
      cbv iota beta. rewrite !ms_drop, S2, S1.
      assert (Hs1: Zlength (toks_upto toks (t + 1)) = i_have (m_s m) + r).
      { rewrite toks_upto_succ, Zlength_app, Etk by lia. cbn [tok_vals].
        rewrite (Zlength_correct (repeat _ _)), repeat_length, Hv. lia. }
      replace (i_nlen (m_s m) + i_ndist (m_s m) <? i_have (m_s m) + (3 + (r - 3))) with false
        by (symmetry; apply Z.ltb_ge; lia).
      cbv iota beta.
      apply (iter_fill G pos inp ob m (dropbits 2 (dropbits L (needbits (L + 2) m1))) k nlen ndist cls toks syms t
               (3 + (r - 3)) (Znth (i_have (m_s m) - 1) (i_lens (m_s m))) TI Md IB BK Out Nl Nd Ht1 Hv Ls TD H4).
      * rewrite Q4, Eq. fold cl. rewrite TOS. lia.
      * exact B4.
      * eapply tfr_trans; [exact F1|]. eapply tfr_trans; [exact F2|].
        eapply tfr_trans; apply bop_drop.
      * rewrite !mleave_drop, Lv2. exact L1.
      * rewrite !mret_drop. congruence.
      * rewrite !ms_drop. congruence.
      * lia.
      * rewrite Etk. cbn [tok_vals]. replace (3 + (r - 3)) with r by lia. f_equal.
        rewrite last_Znth_Z by exact TOn. rewrite <- Hv, <- Ls. rewrite Znth_sublist by lia. f_equal; lia.
      * lia.

  - (* CZeros *)
    destruct TO as (TOr & TOc).
    destruct (Z.leb_spec r 10) as [Hr|Hr].
    + replace (r <=? 10) with true in * by (symmetry; apply Z.leb_le; lia). subst sy.
      replace (17 <? 16) with false by reflexivity. replace (17 =? 16) with false by reflexivity.
      replace (17 =? 17) with true by reflexivity.
      cbv iota beta.
      destruct (read_extra DK G pos inp m1 q (m_bits m) L 3 (r - 3) C H1 Q1 ltac:(lia) BL1 B1o
                  ltac:(destruct BB as [BB|[_ BB]]; [left; lia | right; rewrite Hst in BB; lia]) ltac:(lia)
                  ltac:(simpl; lia) SBe)
        as (S2 & R2 & F2 & [(Lv2 & H2 & Q2 & B2 & N2) | (Lv2 & BL2 & BV & H4 & Q4 & B4)]).
      * rewrite Lv2. replace (1 =? 1) with true by reflexivity. cbv iota beta. cbn [negb].
        apply (iter_leave DK G pos inp ob m (needbits (L + 3) m1) k nlen ndist cls toks syms t OK SO TI Md IB BK Out
                 Nl Nd Ht1 Hv Ls TD H2).
        -- rewrite Q2, Eq. reflexivity.
        -- fold cl. rewrite Etk, Hst. lia.
        -- eapply tfr_trans; [exact F1 | exact F2].
        -- exact Lv2.
        -- exact N2.
        -- congruence.
        -- congruence.
      * rewrite Lv2, L1. replace (0 =? 1) with false by reflexivity. cbv iota beta.
        rewrite BV. cbn [negb]. rewrite mmode_drop, mmode_drop.
        replace (m_mode (needbits (L + 3) m1) =? BAD) with false
          by (unfold m_mode; rewrite S2, S1; fold (m_mode m); rewrite Md; reflexivity).
        cbv iota beta. rewrite !ms_drop, S2, S1.
        assert (Hs1: Zlength (toks_upto toks (t + 1)) = i_have (m_s m) + r).
        { rewrite toks_upto_succ, Zlength_app, Etk by lia. cbn [tok_vals].
          rewrite (Zlength_correct (repeat _ _)), repeat_length, Hv. lia. }
        replace (i_nlen (m_s m) + i_ndist (m_s m) <? i_have (m_s m) + (3 + (r - 3))) with false
          by (symmetry; apply Z.ltb_ge; lia).
        cbv iota beta.
        apply (iter_fill G pos inp ob m (dropbits 3 (dropbits L (needbits (L + 3) m1))) k nlen ndist cls toks syms t
                 (3 + (r - 3)) 0 TI Md IB BK Out Nl Nd Ht1 Hv Ls TD H4).
        -- rewrite Q4, Eq. fold cl. rewrite TOS. lia.
        -- exact B4.
        -- eapply tfr_trans; [exact F1|]. eapply tfr_trans; [exact F2|].
           eapply tfr_trans; apply bop_drop.
        -- rewrite !mleave_drop, Lv2. exact L1.
        -- rewrite !mret_drop. congruence.
        -- rewrite !ms_drop. congruence.
        -- lia.
        -- rewrite Etk. cbn [tok_vals]. replace (3 + (r - 3)) with r by lia. reflexivity.
        -- lia.
    + replace (r <=? 10) with false in * by (symmetry; apply Z.leb_gt; lia). subst sy.
      replace (18 <? 16) with false by reflexivity. replace (18 =? 16) with false by reflexivity.
      replace (18 =? 17) with false by reflexivity.
      cbv iota beta.
      destruct (read_extra DK G pos inp m1 q (m_bits m) L 7 (r - 11) C H1 Q1 ltac:(lia) BL1 B1o
                  ltac:(destruct BB as [BB|[_ BB]]; [left; lia | right; rewrite Hst in BB; lia]) ltac:(lia)
                  ltac:(simpl; lia) SBe)
        as (S2 & R2 & F2 & [(Lv2 & H2 & Q2 & B2 & N2) | (Lv2 & BL2 & BV & H4 & Q4 & B4)]).
      * rewrite Lv2. replace (1 =? 1) with true by reflexivity. cbv iota beta. cbn [negb].
        apply (iter_leave DK G pos inp ob m (needbits (L + 7) m1) k nlen ndist cls toks syms t OK SO TI Md IB BK Out
                 Nl Nd Ht1 Hv Ls TD H2).
        -- rewrite Q2, Eq. reflexivity.
        -- fold cl. rewrite Etk, Hst. lia.
        -- eapply tfr_trans; [exact F1 | exact F2].
        -- exact Lv2.
        -- exact N2.
        -- congruence.
        -- congruence.
      * rewrite Lv2, L1. replace (0 =? 1) with false by reflexivity. cbv iota beta.
        rewrite BV. cbn [negb]. rewrite mmode_drop, mmode_drop.
        replace (m_mode (needbits (L + 7) m1) =? BAD) with false
          by (unfold m_mode; rewrite S2, S1; fold (m_mode m); rewrite Md; reflexivity).
        cbv iota beta. rewrite !ms_drop, S2, S1.
        assert (Hs1: Zlength (toks_upto toks (t + 1)) = i_have (m_s m) + r).
        { rewrite toks_upto_succ, Zlength_app, Etk by lia. cbn [tok_vals].
          rewrite (Zlength_correct (repeat _ _)), repeat_length, Hv. lia. }
        replace (i_nlen (m_s m) + i_ndist (m_s m) <? i_have (m_s m) + (11 + (r - 11))) with false
          by (symmetry; apply Z.ltb_ge; lia).
        cbv iota beta.
        apply (iter_fill G pos inp ob m (dropbits 7 (dropbits L (needbits (L + 7) m1))) k nlen ndist cls toks syms t
                 (11 + (r - 11)) 0 TI Md IB BK Out Nl Nd Ht1 Hv Ls TD H4).
        -- rewrite Q4, Eq. fold cl. rewrite TOS. lia.
        -- exact B4.
        -- eapply tfr_trans; [exact F1|]. eapply tfr_trans; [exact F2|].
           eapply tfr_trans; apply bop_drop.
        -- rewrite !mleave_drop, Lv2. exact L1.
        -- rewrite !mret_drop. congruence.
        -- rewrite !ms_drop. congruence.
        -- lia.
        -- rewrite Etk. cbn [tok_vals]. replace (11 + (r - 11)) with r by lia. reflexivity.
        -- lia.

Qed.

Lemma cl_extra_of_tdec s T root lens : tdec s T root CODES lens -> cl_extra s T root lens.
Proof.
  intros (R & _ & P & NLc). split; [exact (NLc eq_refl)|].
  intros sy Hs Hn b pat Hb Hp Hm. destruct (P sy Hs Hn b pat Hb Hp Hm) as [H|[H _]]; [exact H|].
  rewrite (NLc eq_refl) in H by (apply Z.mod_pos_bound; lia). discriminate.
Qed.

Lemma part_iter : part_iter_stmt.
Proof. exact (part_iter_x cl_extra_of_tdec). Qed.
