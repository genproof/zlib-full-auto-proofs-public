(* case CODELENS: the while loop (CLKit5.cl_while; model codelens_loop) from its parts *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.CLKit5.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.inflate.MwfLemmas.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* pure facts (as StepKit.v / Step3Tables.v, over mwf)                                             *)

Ltac cw_neq := cbv [HEAD TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT LENGTH DONE BAD SYNC] in *;
  lia.

Lemma cw_bitsn_range: forall m n, 0 <= n -> 0 <= bitsn m n < 2 ^ n.
Proof. intros m n H. unfold bitsn. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. Qed.

Lemma cw_tv_root_bits: forall kind get rb sz i,
  tvalid_g kind get rb sz -> 0 <= i < 2 ^ rb -> 0 <= e_bits (get i) <= 15 /\ entry_ok (get i).
Proof.
  intros kind get rb sz i [R S T] Hi. destruct (T i Hi) as [E F]. cbv zeta in F.
  split; auto. destruct E as (_ & E & _).
  destruct (islink kind (e_op (get i))); [destruct F as (F & _); lia | lia].
Qed.

Lemma cw_lookup1_f_ok: forall k fx dx t nb m,
  mwf m -> m_leave m = 0 -> 0 <= nb ->
  (forall i, 0 <= i < 2 ^ nb -> e_bits (tab_entry fx dx (m_s m) t i) <= 15) ->
  15 <= m_bits m + 8 * (Z.of_nat k - 1) ->
  let '(here, m', ok) := lookup1_f k fx dx t nb m in
  mwf m' /\ m_s m' = m_s m /\
  (ok = true -> m_leave m' = 0 /\ e_bits here <= m_bits m' /\
                exists i, 0 <= i < 2 ^ nb /\ here = tab_entry fx dx (m_s m) t i) /\
  (ok = false -> m_leave m' = 1).
Proof.
  induction k; intros fx dx t nb m W L Hnb Hb F; simpl.
  - split; [auto|]. split; [auto|]. split; [|discriminate].
    intros _. split; [auto|]. pose proof (cw_bitsn_range m nb Hnb). split.
    + specialize (Hb _ H). lia.
    + eexists; split; [eassumption | reflexivity].
  - pose proof (cw_bitsn_range m nb Hnb) as BR.
    destruct (Z.leb_spec (e_bits (tab_entry fx dx (m_s m) t (bitsn m nb))) (m_bits m)).
    + split; [auto|]. split; [auto|]. split; [|discriminate].
      intros _. split; [auto|]. split; [auto|]. eexists; split; [eassumption | reflexivity].
    + destruct (Z.eqb_spec (m_have m) 0).
      * split; [apply mwf_set_leave; auto|]. split; [reflexivity|]. split; [discriminate|]. auto.
      * pose proof (Hb _ BR) as Hb1.
        assert (W': mwf (pull m)) by (apply mwf_pull; auto; lia).
        assert (Bp: m_bits (pull m) = m_bits m + 8)
          by (unfold pull; simpl; unfold u32; rewrite Z.mod_small; destruct W; lia).
        specialize (IHk fx dx t nb (pull m) W' L Hnb Hb ltac:(rewrite Bp; lia)).
        destruct (lookup1_f k fx dx t nb (pull m)) as [[h m'] ok]. exact IHk.
Qed.

Lemma cw_needbits_f_s: forall k n m, m_s (needbits_f k n m) = m_s m.
Proof.
  induction k; intros n m; simpl; auto.
  destruct (m_bits m <? n); auto. destruct (m_have m =? 0); auto. rewrite IHk. reflexivity.
Qed.

Lemma cw_needbits_f_ok: forall k n m,
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

Lemma cw_needbits_ok: forall n m,
  mwf m -> m_leave m = 0 -> n <= 32 -> m_leave (needbits n m) <> 1 ->
  n <= m_bits (needbits n m) /\ m_leave (needbits n m) = 0.
Proof. intros n m W L N E. apply cw_needbits_f_ok; auto; try (destruct W; simpl; lia). Qed.

(* the lookup of one pass *)
Lemma cw_lookup: forall m here m1 ok,
  mwf m -> m_mode m = CODELENS -> m_leave m = 0 ->
  lookup1 lenfix_list distfix_list (i_lencode (m_s m)) (i_lenbits (m_s m)) m = (here, m1, ok) ->
  mwf m1 /\ m_s m1 = m_s m /\
  (ok = true -> m_leave m1 = 0 /\ e_bits here <= m_bits m1 /\ e_bits here <= 15 /\ entry_ok here) /\
  (ok = false -> m_leave m1 = 1).
Proof.
  intros m here m1 ok W Md L E.
  pose proof (mw_md _ W) as MD.
  destruct (md_codelens _ MD Md) as (H0 & Hnl & Hnd & LC & TV & _).
  destruct TV as (sz & _ & TVb).
  pose proof (tv_rb _ _ _ _ TVb) as RB.
  pose proof (cw_lookup1_f_ok 3 lenfix_list distfix_list (i_lencode (m_s m)) (i_lenbits (m_s m)) m W L
                ltac:(lia) (fun i Hi => proj2 (proj1 (cw_tv_root_bits _ _ _ _ i TVb Hi)))
                ltac:(destruct W; simpl; lia)) as LK.
  unfold lookup1 in E. rewrite E in LK.
  destruct LK as (W1 & S1 & LKt & LKf).
  split; [auto | split; [auto | split; [ | auto]]].
  intros T. destruct (LKt T) as (L1 & B1 & i & Hi & Eh).
  destruct (cw_tv_root_bits _ _ _ _ i TVb Hi) as [Bh Eok]. rewrite <- Eh in Bh, Eok.
  split; [auto | split; [auto | split; [lia | auto]]].
Qed.

(* the lens / have updates of CODELENS *)
Lemma cw_codelens_upd: forall m L h, mwf m -> m_mode m = CODELENS ->
  i_have (m_s m) <= h <= i_nlen (m_s m) + i_ndist (m_s m) -> Zlength L = 320 ->
  Forall (fun x => 0 <= x <= 65535) L -> (forall k, 0 <= k < h -> Znth k L <= 15) ->
  mwf (set_m_s m (set_i_have (set_i_lens (m_s m) L) h)).
Proof.
  intros m L h W Md H ZL FL LE.
  pose proof (mw_md _ W) as MD. pose proof (mw_s _ W) as S.
  destruct (md_codelens _ MD Md) as (H0 & Hnl & Hnd & LC & TV & _).
  unfold m_mode in Md.
  destruct W; constructor; simpl; auto.
  - constructor; simpl; intros; try cw_neq.
    + split; [lia|]. split; [lia|]. split; [lia|]. split; [auto|]. split; [exact TV | auto].
    + unfold decode_mode in *; cw_neq.
  - destruct S; constructor; simpl; auto. lia.
Qed.

Lemma cw_lens_fill: forall n len s, 0 <= len <= 15 -> 0 <= i_have s -> i_have s + Z.of_nat n <= 320 ->
  Zlength (i_lens s) = 320 -> Forall (fun x => 0 <= x <= 65535) (i_lens s) ->
  (forall k, 0 <= k < i_have s -> Znth k (i_lens s) <= 15) ->
  exists L, lens_fill n len s = set_i_have (set_i_lens s L) (i_have s + Z.of_nat n) /\
    Zlength L = 320 /\ Forall (fun x => 0 <= x <= 65535) L /\
    (forall k, 0 <= k < i_have s + Z.of_nat n -> Znth k L <= 15).
Proof.
  induction n; intros len s HL H0 Hn ZL FL LE.
  - exists (i_lens s). simpl. rewrite Z.add_0_r. split; [destruct s; reflexivity|]. auto.
  - cbn [lens_fill]. set (s1 := set_i_have (set_i_lens s (upd_Znth (i_have s) (i_lens s) len)) (i_have s + 1)).
    rewrite Nat2Z.inj_succ in Hn.
    destruct (IHn len s1) as (L & E & ZL1 & FL1 & LE1); simpl; auto; try lia.
    + rewrite upd_Znth_Zlength; lia.
    + apply Forall_upd_Znth; auto; lia.
    + intros k Hk. destruct (Z.eq_dec k (i_have s)).
      * subst. rewrite upd_Znth_same; lia.
      * rewrite upd_Znth_diff by lia. apply LE; lia.
    + exists L. rewrite E. split; [|split; [auto | split; [auto|]]].
      * transitivity (set_i_have (set_i_lens s L) (i_have s + 1 + Z.of_nat n)); [reflexivity | f_equal; lia].
      * intros k Hk. apply LE1. simpl. lia.
Qed.

(* the invariant facts of a machine in the loop *)
Definition cw_ok (m: mst) : Prop := mwf m /\ m_mode m = CODELENS /\ m_leave m = 0.

Lemma cw_small: forall m1 here,
  mwf m1 -> m_mode m1 = CODELENS -> m_leave m1 = 0 -> entry_ok here -> e_bits here <= m_bits m1 ->
  e_val here < 16 -> i_have (m_s m1) < i_nlen (m_s m1) + i_ndist (m_s m1) ->
  cw_ok (cl_small_m here m1) /\ i_have (m_s (cl_small_m here m1)) = i_have (m_s m1) + 1 /\
  i_nlen (m_s (cl_small_m here m1)) = i_nlen (m_s m1) /\ i_ndist (m_s (cl_small_m here m1)) = i_ndist (m_s m1).
Proof.
  intros m1 here W Md L Eok B V Hh. destruct Eok as (Eo & Eb & Ev).
  pose proof (mw_md _ W) as MD. pose proof (mw_s _ W) as S.
  destruct (md_codelens _ MD Md) as (H0 & Hnl & Hnd & LC & TV & LE).
  destruct (sw_lens _ S) as [ZL FL].
  set (m2 := dropbits (e_bits here) m1).
  assert (W2: mwf m2) by (apply mwf_dropbits; auto; lia).
  assert (E2: m_s m2 = m_s m1) by reflexivity.
  unfold cl_small_m. fold m2. unfold upd_s. rewrite E2.
  split; [split; [|split] | split; [|split]]; try reflexivity.
  - replace (m_s m1) with (m_s m2) by exact E2.
    apply cw_codelens_upd; auto; rewrite ?E2; auto; try lia.
    + rewrite upd_Znth_Zlength; lia.
    + apply Forall_upd_Znth; [auto | lia].
    + intros k Hk. destruct (Z.eq_dec k (i_have (m_s m1))).
      * subst k. rewrite upd_Znth_same by lia. lia.
      * rewrite upd_Znth_diff by lia. apply LE; lia.
  - exact Md.
  - exact L.
Qed.

Lemma cw_rep: forall m1 here m2 len copy,
  mwf m1 -> m_mode m1 = CODELENS -> m_leave m1 = 0 -> 0 <= e_bits here <= 15 ->
  i_have (m_s m1) < i_nlen (m_s m1) + i_ndist (m_s m1) ->
  cl_rep_m here m1 = (m2, len, copy, true) -> m_mode m2 = CODELENS ->
  mwf m2 /\ m_s m2 = m_s m1 /\ m_leave m2 = 0 /\ 0 <= len <= 15 /\ 1 <= copy <= 138.
Proof.
  intros m1 here m2 len copy W Md L Bh Hh E M2.
  pose proof (mw_md _ W) as MD. pose proof (mw_s _ W) as S.
  destruct (md_codelens _ MD Md) as (H0 & Hnl & Hnd & LC & TV & LE).
  destruct (sw_lens _ S) as [ZL FL].
  unfold cl_rep_m in E.
  destruct (e_val here =? 16).
  - set (m3 := needbits (e_bits here + 2) m1) in E.
    destruct (Z.eqb_spec (m_leave m3) 1) as [EL|EL]; [discriminate|].
    destruct (cw_needbits_ok (e_bits here + 2) m1 W L ltac:(lia) EL) as [NB NL]. fold m3 in NB, NL.
    assert (W3: mwf m3) by (apply mwf_needbits; auto; lia).
    assert (E3: m_s m3 = m_s m1) by (unfold m3, needbits; apply cw_needbits_f_s).
    set (m4 := dropbits (e_bits here) m3) in E.
    assert (W4: mwf m4) by (apply mwf_dropbits; auto; lia).
    assert (B4: m_bits m4 = m_bits m3 - e_bits here)
      by (unfold m4, dropbits; simpl; unfold u32; rewrite Z.mod_small; destruct W3; lia).
    assert (E4: m_s m4 = m_s m1) by exact E3.
    rewrite E4 in E.
    destruct (Z.eqb_spec (i_have (m_s m1)) 0).
    + inversion E; subst m2. unfold m_mode in M2. simpl in M2. cw_neq.
    + inversion E; subst m2 len copy.
      pose proof (cw_bitsn_range m4 2 ltac:(lia)).
      split; [apply mwf_dropbits; auto; lia|]. split; [exact E4|]. split; [exact NL|].
      split; [|simpl in *; lia].
      assert (IN: In (Znth (i_have (m_s m1) - 1) (i_lens (m_s m1))) (i_lens (m_s m1))) by (apply Znth_In; lia).
      rewrite Forall_forall in FL. specialize (FL _ IN). pose proof (LE (i_have (m_s m1) - 1) ltac:(lia)). lia.
  - destruct (e_val here =? 17).
    + set (m3 := needbits (e_bits here + 3) m1) in E.
      destruct (Z.eqb_spec (m_leave m3) 1) as [EL|EL]; [discriminate|].
      destruct (cw_needbits_ok (e_bits here + 3) m1 W L ltac:(lia) EL) as [NB NL]. fold m3 in NB, NL.
      assert (W3: mwf m3) by (apply mwf_needbits; auto; lia).
      assert (E3: m_s m3 = m_s m1) by (unfold m3, needbits; apply cw_needbits_f_s).
      set (m4 := dropbits (e_bits here) m3) in E.
      assert (W4: mwf m4) by (apply mwf_dropbits; auto; lia).
      assert (B4: m_bits m4 = m_bits m3 - e_bits here)
        by (unfold m4, dropbits; simpl; unfold u32; rewrite Z.mod_small; destruct W3; lia).
      inversion E; subst m2 len copy.
      pose proof (cw_bitsn_range m4 3 ltac:(lia)).
      split; [apply mwf_dropbits; auto; lia|]. split; [exact E3|]. split; [exact NL|].
      simpl in *; lia.
    + set (m3 := needbits (e_bits here + 7) m1) in E.
      destruct (Z.eqb_spec (m_leave m3) 1) as [EL|EL]; [discriminate|].
      destruct (cw_needbits_ok (e_bits here + 7) m1 W L ltac:(lia) EL) as [NB NL]. fold m3 in NB, NL.
      assert (W3: mwf m3) by (apply mwf_needbits; auto; lia).
      assert (E3: m_s m3 = m_s m1) by (unfold m3, needbits; apply cw_needbits_f_s).
      set (m4 := dropbits (e_bits here) m3) in E.
      assert (W4: mwf m4) by (apply mwf_dropbits; auto; lia).
      assert (B4: m_bits m4 = m_bits m3 - e_bits here)
        by (unfold m4, dropbits; simpl; unfold u32; rewrite Z.mod_small; destruct W3; lia).
      inversion E; subst m2 len copy.
      pose proof (cw_bitsn_range m4 7 ltac:(lia)).
      split; [apply mwf_dropbits; auto; lia|]. split; [exact E3|]. split; [exact NL|].
      simpl in *; lia.
Qed.

Lemma cw_fill: forall m2 len copy,
  mwf m2 -> m_mode m2 = CODELENS -> m_leave m2 = 0 -> 0 <= len <= 15 -> 1 <= copy ->
  i_have (m_s m2) + copy <= i_nlen (m_s m2) + i_ndist (m_s m2) ->
  let m' := upd_s m2 (lens_fill (Z.to_nat copy) len) in
  cw_ok m' /\ i_have (m_s m') = i_have (m_s m2) + copy /\
  i_nlen (m_s m') = i_nlen (m_s m2) /\ i_ndist (m_s m') = i_ndist (m_s m2).
Proof.
  intros m2 len copy W Md L HL Hc Hh m'.
  pose proof (mw_md _ W) as MD. pose proof (mw_s _ W) as S.
  destruct (md_codelens _ MD Md) as (H0 & Hnl & Hnd & LC & TV & LE).
  destruct (sw_lens _ S) as [ZL FL].
  destruct (cw_lens_fill (Z.to_nat copy) len (m_s m2)) as (L' & E & ZL' & FL' & LE'); auto; try lia.
  unfold m', upd_s. rewrite E. rewrite Z2Nat.id in * by lia.
  split; [split; [|split] | split; [|split]]; try reflexivity.
  - apply cw_codelens_upd; auto. lia.
  - exact Md.
  - exact L.
Qed.

(* the model of one pass, cut like the code *)
Lemma cw_loop_step: forall k m, i_have (m_s m) < i_nlen (m_s m) + i_ndist (m_s m) ->
  codelens_loop lenfix_list distfix_list (S k) m =
  match codelens_iter lenfix_list distfix_list m with
  | CLnext m' => codelens_loop lenfix_list distfix_list k m'
  | o => o
  end.
Proof.
  intros k m H. cbn [codelens_loop]. destruct (Z.ltb_spec (i_have (m_s m)) (i_nlen (m_s m) + i_ndist (m_s m)));
  [reflexivity | lia].
Qed.

Lemma cw_loop_done: forall k m, i_nlen (m_s m) + i_ndist (m_s m) <= i_have (m_s m) ->
  codelens_loop lenfix_list distfix_list k m = CLnext m.
Proof.
  intros k m H. destruct k; [reflexivity|]. cbn [codelens_loop].
  destruct (Z.ltb_spec (i_have (m_s m)) (i_nlen (m_s m) + i_ndist (m_s m))); [lia | reflexivity].
Qed.

Lemma cw_iter_leave: forall m here m1,
  lookup1 lenfix_list distfix_list (i_lencode (m_s m)) (i_lenbits (m_s m)) m = (here, m1, false) ->
  codelens_iter lenfix_list distfix_list m = CLleave m1.
Proof. intros m here m1 E. rewrite codelens_iter_eq, E. reflexivity. Qed.

Lemma cw_iter_small: forall m here m1,
  lookup1 lenfix_list distfix_list (i_lencode (m_s m)) (i_lenbits (m_s m)) m = (here, m1, true) ->
  e_val here < 16 -> codelens_iter lenfix_list distfix_list m = CLnext (cl_small_m here m1).
Proof.
  intros m here m1 E V. rewrite codelens_iter_eq, E. cbn [negb].
  destruct (Z.ltb_spec (e_val here) 16); [reflexivity | lia].
Qed.

Lemma cw_iter_rep: forall m here m1 m2 len copy ok2,
  lookup1 lenfix_list distfix_list (i_lencode (m_s m)) (i_lenbits (m_s m)) m = (here, m1, true) ->
  16 <= e_val here -> cl_rep_m here m1 = (m2, len, copy, ok2) ->
  codelens_iter lenfix_list distfix_list m =
  if negb ok2 then CLleave m2 else
  if m_mode m2 =? BAD then CLbad m2 else
  if i_nlen (m_s m2) + i_ndist (m_s m2) <? i_have (m_s m2) + copy then CLbad (set_bad m2 M_repeat) else
  CLnext (upd_s m2 (lens_fill (Z.to_nat copy) len)).
Proof.
  intros m here m1 m2 len copy ok2 E V R. rewrite codelens_iter_eq, E. cbn [negb].
  destruct (Z.ltb_spec (e_val here) 16); [lia |]. rewrite R. reflexivity.
Qed.

Ltac cw_ff := apply andp_left2; intro rho; simpl; apply prop_left; intros [].

Definition cw_inv (F: frame) (m: mst) : environ -> mpred :=
  @exp (environ -> mpred) _ mst (fun mc => @exp (environ -> mpred) _ (reptype t_code) (fun hv =>
  @exp (environ -> mpred) _ nat (fun k =>
  !! (cw_ok mc /\ codelens_loop lenfix_list distfix_list 320 m = codelens_loop lenfix_list distfix_list k mc /\
      i_nlen (m_s mc) + i_ndist (m_s mc) + 1 <= i_have (m_s mc) + Z.of_nat k) && loop_state_h F mc hv))).

Definition cw_post (F: frame) (m: mst) : environ -> mpred :=
  @exp (environ -> mpred) _ mst (fun m1 => @exp (environ -> mpred) _ (reptype t_code) (fun hv =>
  !! cl_exit m m1 && loop_state_h F m1 hv)).

Lemma cl_while_ok : cl_lookup_stmt -> cl_small_stmt -> cl_rep_stmt -> cl_fill_stmt -> cl_while_stmt.
Proof.
  intros HLK HSM HRP HFL Espec F m HF W Md L.
  pose proof (mw_md _ W) as MD.
  destruct (md_codelens _ MD Md) as (H0 & Hnl & Hnd & _).
  rewrite cl_while_eq, loop_state_h_def.
  apply semax_pre with (cw_inv F m).
  { unfold cw_inv. Exists m (default_val t_code) 320%nat.
    apply andp_left2. apply andp_right; [apply prop_right | apply derives_refl].
    split; [split; auto | split; [reflexivity | lia]]. }
  apply semax_loop with (Q' := cw_inv F m).
  - unfold cw_inv at 1. Intros mc hv k. apply semax_extract_prop. intros (OK & EK & HK).
    destruct OK as (Wc & Mc & Lc).
    pose proof (mw_md _ Wc) as MDc.
    destruct (md_codelens _ MDc Mc) as (H0c & Hnlc & Hndc & _).
    apply semax_seq with (!! (i_have (m_s mc) < i_nlen (m_s mc) + i_ndist (m_s mc)) && loop_state_h F mc hv).
    + rewrite loop_state_h_cl. unfold loop_state_clh, cl_sep, loop_locals. cl_stmt. abbreviate_semax.
      forward. forward. forward.
      forward_if. { forward. rewrite prop_true_andp by exact H2. entailer!. }
      assert (EX1: cl_exit m mc)
        by (left; rewrite EK, cw_loop_done by lia;
            split; [reflexivity | split; [exact Wc | split; [exact Mc | split; [exact Lc | lia]]]]).
      forward. Exists mc hv. rewrite prop_true_andp by exact EX1. rewrite loop_state_h_cl.
      unfold loop_state_clh, cl_sep, loop_locals. entailer!.
    + apply semax_extract_prop. intros Hh.
      destruct k as [|k]; [simpl in HK; lia |]. rewrite (cw_loop_step k mc Hh) in EK.
      rewrite cl_iter_eq.
      eapply semax_seq'. { apply HLK; auto. }
      apply extract_exists_pre; intros here. apply extract_exists_pre; intros m1.
      apply extract_exists_pre; intros ok. apply semax_extract_prop. intros E1.
      destruct (cw_lookup mc here m1 ok Wc Mc Lc E1) as (W1 & S1 & OKt & OKf).
      unfold loop_state_h, loop_locals. abbreviate_semax.
      forward_if.
      * destruct ok; [destruct (OKt eq_refl); lia |].
        assert (EX1: cl_exit m m1)
          by (right; left; rewrite EK, (cw_iter_leave mc here m1 E1); split; [reflexivity | auto]).
        forward. Exists m1 (ent here). rewrite prop_true_andp by exact EX1.
        unfold loop_state_h, loop_locals. entailer!.
      * destruct ok; [| rewrite (OKf eq_refl) in H; discriminate].
        destruct (OKt eq_refl) as (L1 & B1 & B15 & Eok).
        assert (M1: m_mode m1 = CODELENS) by (unfold m_mode; rewrite S1; exact Mc).
        assert (Hh1: i_have (m_s m1) < i_nlen (m_s m1) + i_ndist (m_s m1)) by (rewrite S1; exact Hh).
        pose proof Eok as (Eo & Eb & Ev).
        forward. { unfold ent; entailer!. rep_lia. }
        change (let (_, y) := let (_, y) := ent here in y in y) with (Vint (Int.repr (e_val here))).
        rewrite Nat2Z.inj_succ in HK.
        forward_if.
        -- destruct (cw_small m1 here W1 M1 L1 Eok B1 H3 Hh1) as ((Ws & Ms & Ls) & Hs & Ns & Ds).
           eapply semax_pre; [| eapply semax_post_flipped; [apply (HSM Espec F m1 here HF W1 M1 L1 Eok B1 H3 Hh1) | | | | ]].
           ++ unfold loop_state_h, loop_locals. entailer!.
           ++ simpl RA_normal. apply andp_left2. unfold cw_inv.
              Exists (cl_small_m here m1) (ent here) k. apply andp_right; [apply prop_right | apply derives_refl].
              split; [split; auto | split].
              ** rewrite EK, (cw_iter_small mc here m1 E1 H3). reflexivity.
              ** rewrite Hs, Ns, Ds, S1. lia.
           ++ cw_ff.
           ++ cw_ff.
           ++ intros vl. cw_ff.
        -- assert (V16: 16 <= e_val here) by lia.
           rewrite cl_big_eq.
           apply semax_seq with (EX m2: mst, EX len: Z, EX copy: Z,
             !! (cl_rep_m here m1 = (m2, len, copy, true) /\ m_mode m2 = CODELENS /\ m_leave m2 = 0) &&
             loop_state_hc F m2 (ent here) len copy).
           ++ eapply semax_pre; [| eapply semax_post_flipped;
                [apply (HRP Espec F m1 here HF W1 M1 L1 Eok B1 B15 V16 Hh1) | | | | ]].
              ** unfold loop_state_h, loop_locals. entailer!.
              ** apply andp_left2. apply derives_refl.
              ** apply andp_left2. apply exp_left; intro m2. apply derives_extract_prop.
                 intros [(E2 & L2) | (E2 & M2 & L2)].
                 { assert (EX1: cl_exit m m2)
                     by (right; left; rewrite EK, (cw_iter_rep mc here m1 m2 0 0 false E1 V16 E2);
                         split; [reflexivity | exact L2]).
                   apply derives_trans with (cw_post F m); [| apply derives_refl]. unfold cw_post.
                   Exists m2 (ent here). rewrite prop_true_andp by exact EX1. apply derives_refl. }
                 { assert (EX1: cl_exit m m2).
                   { right; right. rewrite EK, (cw_iter_rep mc here m1 m2 0 0 true E1 V16 E2). cbn [negb].
                     rewrite M2, Z.eqb_refl. split; [reflexivity | split; auto]. }
                   apply derives_trans with (cw_post F m); [| apply derives_refl]. unfold cw_post.
                   Exists m2 (ent here). rewrite prop_true_andp by exact EX1. apply derives_refl. }
              ** cw_ff.
              ** intros vl. cw_ff.
           ++ apply extract_exists_pre; intros m2. apply extract_exists_pre; intros len.
              apply extract_exists_pre; intros copy. apply semax_extract_prop. intros (E2 & M2 & L2).
              destruct (cw_rep m1 here m2 len copy W1 M1 L1 (conj (proj1 Eb) B15) Hh1 E2 M2)
                as (W2 & S2 & _ & Hlen & Hcopy).
              assert (Hh2: i_have (m_s m2) <= i_nlen (m_s m2) + i_ndist (m_s m2)) by (rewrite S2, S1; lia).
              assert (MB: (m_mode m2 =? BAD) = false) by (rewrite M2; reflexivity).
              eapply semax_post_flipped;
                [apply (HFL Espec F m2 here len copy HF W2 M2 L2 ltac:(lia) Hcopy Hh2) | | | | ].
              ** apply andp_left2. apply derives_extract_prop; intro Hf.
                 pose proof (cw_fill m2 len copy W2 M2 L2 Hlen ltac:(lia) Hf) as FL. cbv zeta in FL.
                 destruct FL as ((Wf & Mf & Lf) & Hf' & Nf & Df).
                 apply derives_trans with (cw_inv F m); [| apply derives_refl]. unfold cw_inv.
                 Exists (upd_s m2 (lens_fill (Z.to_nat copy) len)) (ent here) k.
                 apply andp_right; [apply prop_right | apply derives_refl].
                 split; [split; auto | split].
                 { rewrite EK, (cw_iter_rep mc here m1 m2 len copy true E1 V16 E2). cbn [negb]. rewrite MB.
                   destruct (Z.ltb_spec (i_nlen (m_s m2) + i_ndist (m_s m2)) (i_have (m_s m2) + copy));
                     [lia | reflexivity]. }
                 { rewrite Hf', Nf, Df, S2, S1. lia. }
              ** apply andp_left2. apply derives_extract_prop; intro Hb.
                 assert (EX1: cl_exit m (set_bad m2 M_repeat)).
                 { right; right. rewrite EK, (cw_iter_rep mc here m1 m2 len copy true E1 V16 E2). cbn [negb].
                   rewrite MB.
                   destruct (Z.ltb_spec (i_nlen (m_s m2) + i_ndist (m_s m2)) (i_have (m_s m2) + copy));
                     [| lia].
                   split; [reflexivity | split; [exact L2 | reflexivity]]. }
                 apply derives_trans with (cw_post F m); [| apply derives_refl]. unfold cw_post.
                 Exists (set_bad m2 M_repeat) (ent here). rewrite prop_true_andp by exact EX1. apply derives_refl.
              ** cw_ff.
              ** intros vl. cw_ff.
  - forward. apply andp_left2, derives_refl.
Qed.
