(* RT-I: copy of rfc1951/DecTabCL.v over the generalized definitions RTIGDefs.v. *)
(* Part of DecTab: CODELENS (the loop and the literal/length and distance tables).  Kit and statements: DecTabKit.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTIGDefs Zlib.proof.roundtrip.RTIGDecTabKit.
Import ListNotations.
Local Open Scope Z_scope.

(* the well-formedness of block k *)
Lemma dcl_blocks_ok_nth w : forall bs out n, blocks_ok w out bs -> (n < length bs)%nat ->
  exists o, block_ok w o (nth n bs (Stored [])).
Proof.
  induction bs as [|b bs IH]; intros out n H Hn; [simpl in Hn; lia|].
  destruct H as [H1 H2]. destruct n as [|n]; [exists out; exact H1|].
  simpl. apply (IH _ n H2). simpl in Hn; lia.
Qed.

Lemma dcl_dyn_ok G k nlen ndist cls toks syms : dctx_ok G -> 0 <= k < nblk G ->
  blk G k = Dynamic nlen ndist cls toks syms ->
  257 <= nlen <= 286 /\ 1 <= ndist <= 30 /\ toks_ok (cl_lens cls) [] toks /\
  Zlength (dyn_lens toks) = nlen + ndist /\ ll_code_ok (dyn_ll nlen toks) /\ dl_code_ok (dyn_dl nlen ndist toks).
Proof.
  intros OK Hk B. destruct OK as ((_ & _ & _ & (_ & _ & BS)) & _).
  destruct (dcl_blocks_ok_nth _ _ _ (Z.to_nat k) BS) as [o Bo].
  { unfold nblk in Hk. rewrite Zlength_correct in Hk. lia. }
  unfold blk in B. rewrite B in Bo. cbn [block_ok] in Bo. tauto.
Qed.

(* the code length tokens *)
Lemma dcl_tok_expand_app : forall a prev b, tok_expand prev (a ++ b) = tok_expand (tok_expand prev a) b.
Proof. induction a as [|x a IH]; intros; simpl; auto. Qed.

Lemma dcl_toks_ok_app : forall cl a prev b, toks_ok cl prev (a ++ b) -> toks_ok cl (tok_expand prev a) b.
Proof. induction a as [|x a IH]; intros prev b H; simpl in *; [exact H | apply IH; tauto]. Qed.

Lemma dcl_tok_vals_len cl prev t : tok_ok cl prev t -> 1 <= Zlength (tok_vals prev t).
Proof.
  destruct t; simpl; intros H.
  - reflexivity.
  - rewrite Zlength_correct, repeat_length. lia.
  - rewrite Zlength_correct, repeat_length. lia.
Qed.

Lemma dcl_tok_expand_len : forall cl toks prev, toks_ok cl prev toks ->
  Zlength prev + Zlength toks <= Zlength (tok_expand prev toks).
Proof.
  induction toks as [|t r IH]; intros prev H; simpl.
  - rewrite Zlength_nil. lia.
  - destruct H as [H1 H2]. specialize (IH _ H2). rewrite Zlength_app in IH.
    pose proof (dcl_tok_vals_len _ _ _ H1). rewrite Zlength_cons. lia.
Qed.

(* CODELENS's position *)
Lemma dcl_kd_codelens G pos inp ob m : Kd G pos inp ob m -> m_mode m = CODELENS ->
  hold_ok G (pos + m_nx m) (m_hold m) (m_bits m) /\
  at_codelens G (m_s m) (8 * (pos + m_nx m) - m_bits m) (m_bits m) (ob ++ m_ow m).
Proof.
  intros K M. destruct (kd_at _ _ _ _ _ K) as [H A]. split; [exact H|]. unfold m_mode in M. rewrite M in A.
  repeat (destruct A as [[E X]|A]; [first [exact X | exfalso; cbv in E; lia] |]).
  destruct A as [E _]. exfalso; cbv in E; lia.
Qed.

Lemma dcl_bounds G pos inp ob m : dctx_ok G -> tin G pos inp ob m -> m_mode m = CODELENS ->
  0 <= i_have (m_s m) /\ i_nlen (m_s m) + i_ndist (m_s m) <= 316.
Proof.
  intros OK (Kd1 & _) M. destruct (dcl_kd_codelens _ _ _ _ _ Kd1 M) as [_ A].
  destruct A as (k & nlen & ndist & cls & toks & syms & t & IB & B & _ & En & Ed & _ & Hh & _).
  destruct (dcl_dyn_ok G k _ _ _ _ _ OK (proj1 IB) B) as (Bn & Bd & _).
  rewrite Hh, En, Ed. split; [apply Zlength_nonneg | lia].
Qed.

(* the loop *)
Lemma dcl_loop G pos inp ob m0 (K: dkit_stmt) (C: ictx G pos inp) (S: slen_ok G) (IT: part_iter_stmt) :
  forall n m, tin G pos inp ob m -> m_mode m = CODELENS -> m_ow m = m_ow m0 ->
  316 - i_have (m_s m) <= Z.of_nat n ->
  match codelens_loop lenfix_list distfix_list n m with
  | CLnext m' => tin G pos inp ob m' /\ m_mode m' = CODELENS /\ m_ow m' = m_ow m0 /\
                 i_nlen (m_s m') + i_ndist (m_s m') <= i_have (m_s m')
  | CLleave m' => tt_ok G pos inp ob (m_ow m0) (TTDone (IBrk m'))
  | CLbad _ => False
  end.
Proof.
  induction n as [|n IH]; intros m T M W H.
  - cbn [codelens_loop]. pose proof (dcl_bounds G pos inp ob m (proj1 C) T M).
    split; [exact T|]. split; [exact M|]. split; [exact W|]. lia.
  - cbn [codelens_loop]. destruct (Z.ltb_spec (i_have (m_s m)) (i_nlen (m_s m) + i_ndist (m_s m))) as [Lt|Ge].
    + pose proof (IT G pos inp ob m K C S T M Lt) as I.
      destruct (codelens_iter lenfix_list distfix_list m) as [m1|m1|m1]; [|rewrite <- W; exact I | exact I].
      destruct I as (T1 & M1 & W1 & Hh). apply IH; [exact T1 | exact M1 | congruence | lia].
    + split; [exact T|]. split; [exact M|]. split; [exact W|]. lia.
Qed.

(* inflate_table reads only next, codes and lens *)
Lemma dcl_call_table_ext ty lo n req s s' :
  i_next s = i_next s' -> i_codes s = i_codes s' -> i_lens s = i_lens s' ->
  call_table ty lo n req s = call_table ty lo n req s'.
Proof. intros A B C. unfold call_table. rewrite A, B, C. reflexivity. Qed.

(* after the loop: the tables *)
Lemma dcl_post G pos inp ob m1 (K: dkit_stmt) (T: tabdec_stmt) (C: ictx G pos inp) :
  tin G pos inp ob m1 -> m_mode m1 = CODELENS -> i_nlen (m_s m1) + i_ndist (m_s m1) <= i_have (m_s m1) ->
  tt_ok G pos inp ob (m_ow m1) (ttab_clpost m1).
Proof.
  intros (Kd1 & L1 & N1 & TB) M1 Hx.
  destruct (dcl_kd_codelens _ _ _ _ _ Kd1 M1) as [HO A].
  destruct A as (k & nlen & ndist & cls & toks & syms & t & IB & B & Eout & En & Ed & Ht & Hh & Hl & TD & Hq & Hb).
  destruct C as (OK & _).
  destruct (dcl_dyn_ok G k _ _ _ _ _ OK (proj1 IB) B) as (Bn & Bd & TO & DL & LL & DLok).
  assert (Et: t = Zlength toks).
  { assert (E: dyn_lens toks = tok_expand (toks_upto toks t) (skipn (Z.to_nat t) toks)).
    { unfold dyn_lens, toks_upto. rewrite <- dcl_tok_expand_app, firstn_skipn. reflexivity. }
    assert (TO2: toks_ok (cl_lens cls) (toks_upto toks t) (skipn (Z.to_nat t) toks)).
    { unfold toks_upto. apply dcl_toks_ok_app. rewrite firstn_skipn. exact TO. }
    pose proof (dcl_tok_expand_len _ _ _ TO2) as Le. rewrite <- E in Le.
    rewrite Zlength_skipn in Le. lia. }
  subst t.
  assert (Eu: toks_upto toks (Zlength toks) = dyn_lens toks).
  { unfold toks_upto, dyn_lens. rewrite firstn_all2 by (rewrite Zlength_correct; lia). reflexivity. }
  rewrite Eu in Hh, Hl.
  rewrite Hh, DL in Hl.
  assert (Hb8: m_bits m1 < 8) by lia. clear Hb Ht.
  destruct TB as (TL320 & TC & TF).
  assert (Ell: sublist 0 nlen (i_lens (m_s m1)) = dyn_ll nlen toks).
  { unfold dyn_ll. rewrite <- Hl, sublist_sublist by lia. f_equal; lia. }
  assert (Edl: sublist nlen (nlen + ndist) (i_lens (m_s m1)) = dyn_dl nlen ndist toks).
  { unfold dyn_dl. rewrite <- Hl, sublist_sublist by lia. f_equal; lia. }
  assert (E256: Znth 256 (i_lens (m_s m1)) <> 0).
  { destruct LL as (_ & L256 & _). rewrite <- Ell, Znth_sublist in L256 by lia. rewrite Z.add_0_r in L256. exact L256. }
  unfold ttab_clpost.
  replace (Znth 256 (i_lens (m_s m1)) =? 0) with false by (symmetry; apply Z.eqb_neq; exact E256).
  set (s0 := set_i_lenbits (set_i_lencode (set_i_next (m_s m1) 0) (TCodes 0)) 9).
  assert (En0: i_nlen s0 = nlen) by exact En.
  rewrite En0.
  pose proof (td_lld T s0 nlen ndist Bn Bd eq_refl TL320 TC TF
    ltac:(change (i_lens s0) with (i_lens (m_s m1)); rewrite Ell; exact LL)
    ltac:(change (i_lens s0) with (i_lens (m_s m1)); rewrite Edl; exact DLok)) as TLD.
  destruct (call_table LENS 0 nlen 9 s0) as [[[r1 c1] n1] lb] eqn:E1.
  destruct TLD as [R1 TLD]. subst r1.
  change (negb (0 =? 0)) with false. cbv iota beta.
  set (s1 := set_i_lenbits (set_i_next (set_i_codes s0 c1) n1) lb).
  set (s2 := set_i_distbits (set_i_distcode s1 (TCodes (i_next s1))) 6).
  assert (E2: call_table DISTS (i_nlen s2) (i_ndist s2) 6 s2 =
              call_table DISTS nlen ndist 6 (set_i_next (set_i_codes s0 c1) n1)).
  { change (i_nlen s2) with (i_nlen (m_s m1)). change (i_ndist s2) with (i_ndist (m_s m1)).
    rewrite En, Ed. apply dcl_call_table_ext; reflexivity. }
  rewrite E2. cbv zeta in TLD.
  destruct (call_table DISTS nlen ndist 6 (set_i_next (set_i_codes s0 c1) n1)) as [[[r2 c2] n2] db] eqn:E3.
  destruct TLD as [R2 TLD]. subst r2.
  change (negb (0 =? 0)) with false. cbv iota beta.
  set (m3 := set_mode (set_m_ret (set_m_s (set_m_ret (set_m_s m1 s1) 0)
                (set_i_distbits (set_i_next (set_i_codes s2 c2) n2) db)) 0) LEN_).
  destruct (TLD (m_s m3) eq_refl) as [TDL TDD].
  change (i_lens s0) with (i_lens (m_s m1)) in TDL, TDD. rewrite Ell in TDL. rewrite Edl in TDD.
  cbn [tt_ok].
  split; [|split; [reflexivity|split; [exact L1|reflexivity]]].
  apply (kd_tfr G pos inp ob m1 m3 Kd1).
  - unfold md_tab. right; right; exact M1.
  - constructor; reflexivity.
  - unfold md_tabl. right; right; right; reflexivity.
  - reflexivity.
  - change (m_nx m3) with (m_nx m1). change (m_hold m3) with (m_hold m1). change (m_bits m3) with (m_bits m1).
    change (m_ow m3) with (m_ow m1).
    unfold at_mode. split; [exact HO|].
    do 8 right. left. split; [left; reflexivity|].
    unfold at_len. exists k, 0, (dyn_ll nlen toks), (dyn_dl nlen ndist toks), syms, (8 * (pos + m_nx m1) - m_bits m1).
    split; [|split; [|split; [reflexivity | left; exact Hb8]]].
    + unfold in_huff. split; [exact IB|]. split; [right; exists nlen, ndist, cls, toks; auto|].
      split; [pose proof (Zlength_nonneg syms); lia|].
      split; [exact TDL|]. split; [exact TDD|].
      rewrite B. cbn [hb_hdr]. unfold sym_off. cbn [firstn flat_map]. rewrite Zlength_nil.
      rewrite Hq, (tok_off_all G k cls toks). unfold dyn_tkb. lia.
    + rewrite Eout. unfold outj. reflexivity.
Qed.

Lemma part_cl : part_cl_stmt.
Proof.
  intros G pos inp ob m K T C S Tin M IT.
  unfold ttab_cl.
  pose proof (dcl_bounds G pos inp ob m (proj1 C) Tin M) as [H0 _].
  pose proof (dcl_loop G pos inp ob m K C S IT 320 m Tin M eq_refl ltac:(lia)) as L.
  destruct (codelens_loop lenfix_list distfix_list 320 m) as [m1|m1|m1]; [|exact L|destruct L].
  destruct L as (T1 & M1 & W1 & Hx). rewrite <- W1.
  exact (dcl_post G pos inp ob m1 K T C T1 M1 Hx).
Qed.
