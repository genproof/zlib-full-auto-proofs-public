(* Law inflate_reset, TABLE / LENLENS / CODELENS: LENLENS (loop, zeros, the code length code), then CODELENS
   (IRTabKit.irt_ll_stmt). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_reset.IRDefs.
Require Import Zlib.proof.harness.inflate_reset.IRTabKit.
Require Import Zlib.proof.inflate.Step3Tables.
Import ListNotations.
Local Open Scope Z_scope.

Ltac irl_cst := unfold HEAD, TABLE, LENLENS, CODELENS, BAD, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, COPY_,
  COPY, EXTRA in *.

(* ---------------------------------------------------------------------------------------------- *)
(* The loop: lens[order[have++]] = BITS(3)                                                       *)

Definition irl_step (m: mst) : mst :=
  let m := needbits 3 m in
  let s := m_s m in
  dropbits 3 (upd_s m (fun _ => set_i_have (set_i_lens s (upd_Znth (Znth (i_have s) order) (i_lens s) (bitsn m 3)))
                                          (i_have s + 1))).

Lemma irl_loop_S k m : lenlens_loop (S k) m =
  if i_have (m_s m) <? i_ncode (m_s m) then
    (if m_leave (needbits 3 m) =? 1 then needbits 3 m else lenlens_loop k (irl_step m))
  else m.
Proof. reflexivity. Qed.

Lemma irl_step_wf m : mwf3x m -> m_mode m = LENLENS -> m_leave m = 0 ->
  i_have (m_s m) < i_ncode (m_s m) -> m_leave (needbits 3 m) <> 1 ->
  mwf3x (irl_step m) /\ m_mode (irl_step m) = LENLENS /\ m_leave (irl_step m) = 0.
Proof.
  intros W Md L H N.
  destruct (tb_lenlens_loop 1 m W Md L) as [W1 M1].
  rewrite irl_loop_S, (proj2 (Z.ltb_lt _ _) H), (proj2 (Z.eqb_neq _ _) N) in W1, M1.
  cbn [lenlens_loop] in W1, M1. split; [exact W1|]. split; [exact M1|].
  destruct (needbits_ok 3 m (m3_w _ W) L ltac:(lia) N) as [_ NL].
  exact NL.
Qed.

Lemma irl_upd_order (la lb: list Z) h v k :
  0 <= h < 19 -> Zlength la = 320 -> Zlength lb = 320 -> 0 <= k < h + 1 ->
  (forall k, 0 <= k < h -> Znth (Znth k order) la = Znth (Znth k order) lb) ->
  Znth (Znth k order) (upd_Znth (Znth h order) la v) = Znth (Znth k order) (upd_Znth (Znth h order) lb v).
Proof.
  intros H Za Zb Hk LL.
  pose proof (tb_order_range h H) as OR.
  destruct (Z.eq_dec k h).
  - subst k. rewrite !upd_Znth_same by lia. reflexivity.
  - pose proof (tb_order_range k ltac:(lia)).
    assert (Znth k order <> Znth h order) by (intros E; apply n; apply tb_order_inj; auto; lia).
    rewrite !upd_Znth_diff by lia. apply LL; lia.
Qed.

Lemma irl_srel_upd no sa sb v :
  srel no sa sb -> i_mode sb = LENLENS -> 0 <= i_have sb < 19 ->
  Zlength (i_lens sa) = 320 -> Zlength (i_lens sb) = 320 ->
  srel no (set_i_have (set_i_lens sa (upd_Znth (Znth (i_have sa) order) (i_lens sa) v)) (i_have sa + 1))
          (set_i_have (set_i_lens sb (upd_Znth (Znth (i_have sb) order) (i_lens sb) v)) (i_have sb + 1)).
Proof.
  intros S Md H Za Zb.
  destruct (sr_nlen _ _ _ S (or_introl Md)) as (En & Ed & Eh).
  pose proof (sr_lenlens _ _ _ S Md) as LL.
  rewrite Eh.
  destruct S; constructor; cbn [i_mode i_last i_wrap i_havedict i_flags i_dmax i_check i_total i_head i_wbits
    i_wsize i_whave i_wnext i_wdata i_hold i_bits i_lencode i_distcode i_next i_sane i_back i_length i_offset
    i_extra i_lenbits i_distbits i_ncode i_nlen i_ndist i_have i_lens i_codes set_i_have set_i_lens]; auto.
  - intros _ k Hk. apply irl_upd_order; auto.
  - intros C. exfalso. rewrite Md in C. unfold LENLENS, CODELENS in C. discriminate.
Qed.

Lemma irl_kr_step W0 wrap src pos inp aout ma mb :
  Kr W0 wrap src pos inp aout ma mb -> mwf3x ma -> mwf3x mb -> m_mode mb = LENLENS ->
  i_have (m_s mb) < i_ncode (m_s mb) ->
  Kr W0 wrap src pos inp aout (needbits 3 ma) (needbits 3 mb) /\
  (m_leave (needbits 3 mb) <> 1 -> Kr W0 wrap src pos inp aout (irl_step ma) (irl_step mb)).
Proof.
  intros K Wa Wb Md Hc.
  assert (Hh: m_mode mb <> HEAD) by (rewrite Md; unfold LENLENS, HEAD; lia).
  destruct (irk_needbits 4 3 ma mb (irk_mf_of_Kr _ _ _ _ _ _ _ _ K)) as (E2 & Sa2 & Sb2 & I2 & A2 & O2).
  assert (K2: Kr W0 wrap src pos inp aout (needbits 3 ma) (needbits 3 mb)) by (apply irk_mach with ma mb; auto).
  split; [exact K2|]. intros _.
  pose proof (mr_s _ _ (kr_rel _ _ _ _ _ _ _ _ K2)) as S2.
  pose proof (kr_wrap _ _ _ _ _ _ _ _ K2) as Kw2. pose proof (kr_head _ _ _ _ _ _ _ _ K2) as Kh2.
  assert (Hd: bitsn (needbits 3 ma) 3 = bitsn (needbits 3 mb) 3) by (unfold irk_mf, bitsn, needbits in *; congruence).
  pose proof (mw_md _ (m3_w _ Wb)) as MD. pose proof (mw_s _ (m3_w _ Wb)) as Sb.
  destruct (md_lenlens _ MD Md) as (Hc1 & H0 & _).
  destruct (sw_lens _ (mw_s _ (m3_w _ Wa))) as [ZLa _]. destruct (sw_lens _ Sb) as [ZLb _].
  unfold irl_step. rewrite Hd.
  change (needbits_f 4 3 ma) with (needbits 3 ma) in Sa2, E2.
  change (needbits_f 4 3 mb) with (needbits 3 mb) in Sb2, E2.
  set (ma2 := needbits 3 ma) in *. set (mb2 := needbits 3 mb) in *. clearbody ma2 mb2.
  assert (Md2: i_mode (m_s mb2) = LENLENS) by (rewrite Sb2; exact Md).
  apply irk_mach with (upd_s ma2 (fun _ => set_i_have (set_i_lens (m_s ma2) (upd_Znth (Znth (i_have (m_s ma2)) order)
        (i_lens (m_s ma2)) (bitsn mb2 3))) (i_have (m_s ma2) + 1)))
     (upd_s mb2 (fun _ => set_i_have (set_i_lens (m_s mb2) (upd_Znth (Znth (i_have (m_s mb2)) order)
        (i_lens (m_s mb2)) (bitsn mb2 3))) (i_have (m_s mb2) + 1))); try reflexivity.
  - unfold upd_s. apply irk_state; auto.
    + apply irl_srel_upd; auto; rewrite ?Sa2, ?Sb2; auto; lia.
    + cbn. rewrite Md2. unfold LENLENS, HEAD; lia.
  - unfold m_mode, upd_s; cbn. rewrite Md2. unfold LENLENS, HEAD; lia.
  - apply irk_dropbits. apply irk_set_s. exact E2.
Qed.

Lemma irl_loop : forall k W0 wrap src pos inp aout ma mb,
  Kr W0 wrap src pos inp aout ma mb -> mwf3x ma -> mwf3x mb -> m_mode mb = LENLENS -> m_leave mb = 0 ->
  Kr W0 wrap src pos inp aout (lenlens_loop k ma) (lenlens_loop k mb).
Proof.
  induction k; intros W0 wrap src pos inp aout ma mb K Wa Wb Md L; [exact K|].
  pose proof (mr_s _ _ (kr_rel _ _ _ _ _ _ _ _ K)) as S.
  assert (Ma: m_mode ma = LENLENS) by (unfold m_mode in *; rewrite (sr_mode _ _ _ S); exact Md).
  assert (La: m_leave ma = 0) by (rewrite (mr_leave _ _ (kr_rel _ _ _ _ _ _ _ _ K)); exact L).
  destruct (sr_nlen _ _ _ S (or_introl Md)) as (_ & _ & Eh).
  assert (Ec: i_ncode (m_s ma) = i_ncode (m_s mb)) by (apply (sr_ncode _ _ _ S Md)).
  rewrite !irl_loop_S, Eh, Ec.
  destruct (Z.ltb_spec (i_have (m_s mb)) (i_ncode (m_s mb))) as [Hc|Hc]; [|exact K].
  destruct (irl_kr_step _ _ _ _ _ _ ma mb K Wa Wb Md Hc) as [K2 K3].
  assert (EL: m_leave (needbits 3 ma) = m_leave (needbits 3 mb))
    by (apply (mr_leave _ _ (kr_rel _ _ _ _ _ _ _ _ K2))).
  rewrite EL. destruct (Z.eqb_spec (m_leave (needbits 3 mb)) 1) as [L2|L2]; [exact K2|].
  destruct (irl_step_wf ma Wa Ma La ltac:(rewrite Eh, Ec; exact Hc) ltac:(rewrite EL; exact L2)) as (Wa3 & Ma3 & La3).
  destruct (irl_step_wf mb Wb Md L Hc L2) as (Wb3 & Mb3 & Lb3).
  apply IHk; auto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* After the loop: zeros, then the code length code                                               *)

Lemma irl_zero_val : forall n s k, 0 <= i_have s <= 19 -> 19 <= i_have s + Z.of_nat n ->
  Zlength (i_lens s) = 320 -> 0 <= k < 19 ->
  Znth (Znth k order) (i_lens (lenlens_zero n s)) =
  if k <? i_have s then Znth (Znth k order) (i_lens s) else 0.
Proof.
  induction n; intros s k H0 Hn ZL Hk.
  - cbn [lenlens_zero]. destruct (Z.ltb_spec k (i_have s)); [reflexivity | simpl in Hn; lia].
  - cbn [lenlens_zero]. destruct (Z.ltb_spec (i_have s) 19) as [Hl|Hl].
    + pose proof (tb_order_range (i_have s) ltac:(lia)) as OR.
      rewrite IHn; cbn [i_have i_lens set_i_have set_i_lens]; try (rewrite ?upd_Znth_Zlength; lia).
      destruct (Z.eq_dec k (i_have s)).
      * subst k. rewrite upd_Znth_same by lia.
        destruct (Z.ltb_spec (i_have s) (i_have s + 1)); [|lia].
        destruct (Z.ltb_spec (i_have s) (i_have s)); [lia|reflexivity].
      * pose proof (tb_order_range k Hk).
        assert (Znth k order <> Znth (i_have s) order) by (intros E; apply n0; apply tb_order_inj; auto; lia).
        rewrite upd_Znth_diff by lia.
        destruct (Z.ltb_spec k (i_have s + 1)), (Z.ltb_spec k (i_have s)); try reflexivity; lia.
    + destruct (Z.ltb_spec k (i_have s)); [reflexivity|lia].
Qed.

Lemma irl_L_eq (sa sb: istate) La Lb :
  0 <= i_have sb <= 19 -> i_have sa = i_have sb -> Zlength (i_lens sa) = 320 -> Zlength (i_lens sb) = 320 ->
  (forall k, 0 <= k < i_have sb -> Znth (Znth k order) (i_lens sa) = Znth (Znth k order) (i_lens sb)) ->
  lenlens_zero 19 sa = set_i_have (set_i_lens sa La) 19 -> lenlens_zero 19 sb = set_i_have (set_i_lens sb Lb) 19 ->
  Zlength La = 320 -> Zlength Lb = 320 ->
  sublist 0 19 La = sublist 0 19 Lb.
Proof.
  intros H Eh Za Zb LL EZa EZb ZLa ZLb.
  assert (E: forall k, 0 <= k < 19 -> Znth (Znth k order) La = Znth (Znth k order) Lb).
  { intros k Hk.
    change La with (i_lens (set_i_have (set_i_lens sa La) 19)). rewrite <- EZa.
    change Lb with (i_lens (set_i_have (set_i_lens sb Lb) 19)). rewrite <- EZb.
    rewrite !irl_zero_val by (simpl; lia). rewrite Eh.
    destruct (Z.ltb_spec k (i_have sb)); [apply LL; lia | reflexivity]. }
  apply Znth_eq_ext; [rewrite !Zlength_sublist; lia|].
  intros i Hi. rewrite Zlength_sublist in Hi by lia. rewrite !Znth_sublist by lia.
  destruct (tb_order_surj i ltac:(lia)) as (k & Hk & <-). rewrite !Z.add_0_r. apply E; auto.
Qed.

Definition irl_s0 (s: istate) (L: list Z) : istate :=
  set_i_lenbits (set_i_distcode (set_i_lencode (set_i_next (set_i_have (set_i_lens s L) 19) 0) (TCodes 0)) (TCodes 0)) 7.
Definition irl_s1 (s: istate) (L: list Z) (c: list entry) (n b: Z) : istate :=
  set_i_lenbits (set_i_next (set_i_codes (irl_s0 s L) c) n) b.
Definition irl_old (s: istate) := sublist 0 ENOUGH_CODES (i_codes s).

Definition irl_rhs (m: mst) (L: list Z) : irt_res :=
  let r := inflate_table_model CODES (sublist 0 19 L) 7 (irl_old (m_s m)) in
  let m1 := set_m_ret (set_m_s m (irl_s1 (m_s m) L (sublist 0 0 (i_codes (m_s m)) ++ it_tab (irl_old (m_s m)) r)
                                     (0 + it_adv r) (it_bits 7 r))) (it_ret r) in
  if negb (it_ret r =? 0) then ITDone (IBrk (set_bad m1 M_cl_set)) else
  irt_cl (set_mode (upd_s m1 (fun s => set_i_have s 0)) CODELENS).

Lemma irl_post_eq m L :
  lenlens_zero 19 (m_s m) = set_i_have (set_i_lens (m_s m) L) 19 -> irt_llpost m = irl_rhs m L.
Proof. intros EZ. unfold irt_llpost. rewrite EZ. reflexivity. Qed.

Lemma irl_cl_eq m s r :
  set_mode (upd_s (set_m_ret (set_m_s m s) r) (fun s => set_i_have s 0)) CODELENS =
  set_m_s (set_m_ret m r) (set_i_mode (set_i_have s 0) CODELENS).
Proof. destruct m; reflexivity. Qed.

Lemma irl_bad_eq m s r e :
  set_bad (set_m_ret (set_m_s m s) r) e = set_m_s (set_m_msg (set_m_ret m r) (Some e)) (set_i_mode s BAD).
Proof. destruct m; reflexivity. Qed.

(* one stream: the preconditions of inflate_table and the CODELENS machine's invariant (Step3Tables.LENLENS_ok) *)
Lemma irl_pre m1 :
  mwf3x m1 -> m_mode m1 = LENLENS ->
  exists L0, lenlens_zero 19 (m_s m1) = set_i_have (set_i_lens (m_s m1) L0) 19 /\ Zlength L0 = 320 /\
    Forall (fun x => 0 <= x <= 65535) L0 /\ (forall x, 0 <= x < 19 -> 0 <= Znth x L0 <= 7) /\
    inputs_ok CODES (sublist 0 19 L0) 7 /\ cap_ok CODES (sublist 0 19 L0) 7 (Zlength (irl_old (m_s m1))) /\
    Forall entry_ok (irl_old (m_s m1)) /\ Zlength (irl_old (m_s m1)) = ENOUGH_CODES.
Proof.
  intros W1 Md1.
  pose proof (mw_md _ (m3_w _ W1)) as MD. pose proof (mw_s _ (m3_w _ W1)) as S.
  destruct (md_lenlens _ MD Md1) as (Hc & H0 & Hnl & Hnd & LE).
  destruct (sw_lens _ S) as [ZL FL]. destruct (sw_codes _ S) as [ZC FC].
  destruct (tb_lenlens_zero 19 (m_s m1) ltac:(lia) ltac:(simpl; lia) ZL FL LE) as (L0 & EZ & ZL0 & FL0 & LE0).
  exists L0. split; [exact EZ|]. split; [exact ZL0|]. split; [exact FL0|].
  assert (LE7: forall x, 0 <= x < 19 -> 0 <= Znth x L0 <= 7).
  { intros x Hx. destruct (tb_order_surj x Hx) as (k & Hk & <-). split; [|apply LE0; auto].
    rewrite Forall_forall in FL0. apply FL0. apply Znth_In. pose proof (tb_order_range k Hk). lia. }
  split; [exact LE7|].
  assert (F07: Forall (fun x => 0 <= x <= 7) (sublist 0 19 L0)).
  { apply tb_forall_sublist; simpl; try lia. intros k Hk. apply LE7; lia. }
  assert (ZO: Zlength (irl_old (m_s m1)) = ENOUGH_CODES)
    by (unfold irl_old; rewrite Zlength_sublist; unfold ENOUGH_CODES in *; lia).
  split.
  { unfold inputs_ok. rewrite Zlength_sublist by lia. split; [unfold CODES; lia|].
    split; [unfold max_codes; simpl; lia|]. split; [|lia].
    eapply Forall_impl; [|exact F07]. unfold MAXBITS; simpl; intros; lia. }
  split.
  { rewrite ZO. pose proof (tb_maxlen_le _ F07) as ML.
    unfold cap_ok. unfold LENS, CODES, DISTS, ENOUGH_CODES. split; [|split; intros; lia].
    intros _. split; [lia|]. split; [lia|]. rewrite Z.shiftl_1_l.
    assert (2 ^ maxlen (sublist 0 19 L0) <= 2 ^ 7) by (apply Z.pow_le_mono_r; lia).
    change (2 ^ 7) with 128 in *. lia. }
  split; [unfold irl_old; apply Forall_sublist; auto | exact ZO].
Qed.

Lemma irl_ct s L0 root used t :
  inflate_table_model CODES (sublist 0 19 L0) 7 (irl_old s) = ROk root used t ->
  call_table CODES 0 19 7 (irl_s0 s L0) = (0, sublist 0 0 (i_codes s) ++ t, 0 + used, root).
Proof.
  intros M. unfold call_table.
  change (i_next (irl_s0 s L0)) with 0. change (sublist 0 (0 + 19) (i_lens (irl_s0 s L0))) with (sublist 0 19 L0).
  change (sublist 0 ENOUGH_CODES (i_codes (irl_s0 s L0))) with (irl_old s).
  change (i_codes (irl_s0 s L0)) with (i_codes s).
  rewrite M. reflexivity.
Qed.

Lemma irl_tab (C3: Zlib.proof.inflate.Cover3.cover3_stmt) s L0 root used t :
  swf s -> Zlength L0 = 320 -> Forall (fun x => 0 <= x <= 65535) L0 ->
  inputs_ok CODES (sublist 0 19 L0) 7 -> cap_ok CODES (sublist 0 19 L0) 7 ENOUGH_CODES ->
  inflate_table_model CODES (sublist 0 19 L0) 7 (irl_old s) = ROk root used t ->
  Zlength t = ENOUGH_CODES /\ Forall entry_ok t /\ tab_ok CODES t root used /\ 1 <= used <= ENOUGH_CODES.
Proof.
  intros S ZL0 FL0 IN0 CAP0 M. pose proof (irk_cover2 C3) as C2.
  pose proof (irl_ct _ _ _ _ _ M) as CT.
  assert (S0: swf (irl_s0 s L0))
    by (unfold irl_s0; destruct S; constructor; simpl; auto; unfold tref_ok, ENOUGH_CODES; lia).
  destruct (tb_call_table CODES 0 19 7 (irl_s0 s L0) _ _ _ _ C2 S0 ltac:(lia) ltac:(lia) ltac:(lia)
              IN0 CAP0 ltac:(intros; lia) CT) as (ZC1 & FC1 & R1 & Rn1 & Ry1).
  destruct (Ry1 eq_refl) as (used1 & t1 & M1 & En & Ec & Zt & T & U & _).
  change (sublist 0 (0 + 19) (i_lens (irl_s0 s L0))) with (sublist 0 19 L0) in M1.
  change (sublist (i_next (irl_s0 s L0)) ENOUGH_CODES (i_codes (irl_s0 s L0))) with (irl_old s) in M1.
  rewrite M in M1. inversion M1; subst used1 t1; clear M1.
  rewrite sublist_nil, app_nil_l in FC1.
  split; [|split; [|split]]; auto; lia.
Qed.

Lemma irl_wf m1 L0 root used t :
  mwf3x m1 -> m_mode m1 = LENLENS -> Zlength L0 = 320 -> Forall (fun x => 0 <= x <= 65535) L0 ->
  Zlength t = ENOUGH_CODES -> Forall entry_ok t -> tab_ok CODES t root used -> 1 <= used <= ENOUGH_CODES ->
  mwf3x (set_mode (upd_s (set_m_ret (set_m_s m1 (irl_s1 (m_s m1) L0 (sublist 0 0 (i_codes (m_s m1)) ++ t)
           (0 + used) root)) 0) (fun s => set_i_have s 0)) CODELENS).
Proof.
  intros W1 Md1 ZL0 FL0 Zt Ft T U.
  pose proof (mw_s _ (m3_w _ W1)) as S.
  pose proof (mw_md _ (m3_w _ W1)) as MD.
  destruct (md_lenlens _ MD Md1) as (_ & _ & Hnl & Hnd & _). clear MD.
  rewrite sublist_nil, app_nil_l.
  pose proof (tv_rb _ _ _ _ T) as RB.
  rewrite irl_cl_eq. unfold irl_s1.
  apply tb_new_s.
  + apply tb_set_ret; auto; lia.
  + apply swf_set_mode; [|md_neq]. unfold irl_s0. destruct S; constructor; simpl; auto; unfold ENOUGH_CODES in *; try lia.
  + constructor; simpl; intros; try md_neq.
    * split; [lia|]. split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [|intros; lia].
      apply tb_tvalid_at with used t; [lia | unfold ENOUGH_CODES in *; lia | | exact T].
      intros i Hi. cbn [i_codes set_i_mode set_i_have set_i_lenbits set_i_next set_i_codes].
      rewrite Z.add_0_l. reflexivity.
    * unfold decode_mode in *; md_neq.
  + simpl. first [apply (x3_head _ (m3_x _ W1)) | (intros ?HH; exfalso; revert HH; md_neq)].
  + simpl; intros; md_neq.
  + simpl; intros; md_neq.
  + simpl; intros D; unfold decode_mode in D; md_neq.
  + apply mwf_out_eq; [apply (m3_w _ (tb_set_ret m1 0 W1 ltac:(lia))) |
      change (m_mode (set_m_ret m1 0)) with (m_mode m1); rewrite Md1; md_neq ..].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The two streams after the loop                                                                 *)

(* treach_eq CODES at TCodes 0, on the code spaces *)
Definition irl_tl (ca cb: list entry) (rb: Z) : Prop :=
  forall i, 0 <= i < 2 ^ rb ->
    let e := Znth (0 + i) ca in
    e = Znth (0 + i) cb /\
    (islink CODES (e_op e) = true -> forall j, 0 <= j < 2 ^ e_op e ->
       Znth (0 + (e_val e + j)) ca = Znth (0 + (e_val e + j)) cb).

Lemma irl_tl_of t1 t2 (xa xb: list entry) rb :
  treach_l CODES t1 t2 rb -> irl_tl (sublist 0 0 xa ++ t1) (sublist 0 0 xb ++ t2) rb.
Proof.
  intros TL i Hi. cbv zeta. rewrite !sublist_nil, !app_nil_l, !Z.add_0_l.
  destruct (TL i Hi) as [E1 E2]. split; [exact E1|]. intros LK j Hj. rewrite !Z.add_0_l. apply E2; auto.
Qed.

Lemma irl_srel_bad no sa sb La Lb ca cb n b :
  srel no sa sb -> i_mode sb = LENLENS ->
  srel no (set_i_mode (irl_s1 sa La ca n b) BAD) (set_i_mode (irl_s1 sb Lb cb n b) BAD).
Proof.
  intros S Md. destruct sa, sb. destruct S; cbn in *. subst.
  unfold irl_s1, irl_s0. constructor; cbn; auto; intros;
    try (exfalso; unfold lenlive, decode_mode in *; cbn in *; irl_cst; lia).
  all: destruct sr_check as [?|[?|[_ ?]]]; auto.
Qed.

Lemma irl_srel_cl no sa sb La Lb ca cb n b :
  srel no sa sb -> i_mode sb = LENLENS -> irl_tl ca cb b ->
  srel no (set_i_mode (set_i_have (irl_s1 sa La ca n b) 0) CODELENS)
          (set_i_mode (set_i_have (irl_s1 sb Lb cb n b) 0) CODELENS).
Proof.
  intros S Md T. destruct sa, sb. destruct S; cbn in *. subst.
  destruct (sr_nlen (or_introl eq_refl)) as (En & Ed & _). subst.
  unfold irl_s1, irl_s0. constructor; cbn; auto; intros;
    try (exfalso; unfold lenlive, decode_mode in *; cbn in *; irl_cst; lia).
  all: first [destruct sr_wbits as [?|[?|?]]; auto; exfalso; irl_cst; lia
             | destruct sr_check as [?|[?|[[?|?] _]]]; auto; exfalso; irl_cst; lia
             | exact T ].
Qed.

Lemma irl_kr W0 wrap src pos inp aout ma mb sa sb r :
  Kr W0 wrap src pos inp aout ma mb -> m_mode mb <> HEAD -> i_mode sb <> HEAD ->
  srel (m_ow mb = []) sa sb -> i_wrap sb = i_wrap (m_s mb) -> i_head sb = i_head (m_s mb) ->
  i_wbits sa = i_wbits (m_s ma) -> i_wbits sb = i_wbits (m_s mb) ->
  (forall e, Kr W0 wrap src pos inp aout (set_m_s (set_m_msg (set_m_ret ma r) e) sa)
                                        (set_m_s (set_m_msg (set_m_ret mb r) e) sb)) /\
  Kr W0 wrap src pos inp aout (set_m_s (set_m_ret ma r) sa) (set_m_s (set_m_ret mb r) sb).
Proof.
  intros K Hh Hs S Ew Ed Ea Eb.
  pose proof (kr_wrap _ _ _ _ _ _ _ _ K) as Kw. pose proof (kr_head _ _ _ _ _ _ _ _ K) as Kh.
  pose proof (irk_mf_of_Kr _ _ _ _ _ _ _ _ K) as E.
  split; [intros e|].
  - assert (K1: Kr W0 wrap src pos inp aout (set_m_msg (set_m_ret ma r) e) (set_m_msg (set_m_ret mb r) e)).
    { apply irk_mach with ma mb; auto; try reflexivity.
      unfold irk_mf in *. destruct ma, mb; cbn in *. injection E; intros; subst; reflexivity. }
    apply irk_state; [exact K1 | exact S | exact Hs | rewrite Ew; exact Kw | rewrite Ed; exact Kh | exact Ea | exact Eb].
  - assert (K1: Kr W0 wrap src pos inp aout (set_m_ret ma r) (set_m_ret mb r)).
    { apply irk_mach with ma mb; auto; try reflexivity. apply irk_ret; exact E. }
    apply irk_state; [exact K1 | exact S | exact Hs | rewrite Ew; exact Kw | rewrite Ed; exact Kh | exact Ea | exact Eb].
Qed.

Lemma irl_post (C3: Zlib.proof.inflate.Cover3.cover3_stmt) (TD: tabdet_stmt) (CL: irt_cl_stmt)
  W0 wrap src pos inp aout ma mb :
  Kr W0 wrap src pos inp aout ma mb -> mwf3x ma -> mwf3x mb -> m_mode mb = LENLENS -> m_leave mb = 0 ->
  irt_rr W0 wrap src pos inp aout (irt_llpost ma) (irt_llpost mb).
Proof.
  intros K Wa Wb Md L.
  pose proof (mr_s _ _ (kr_rel _ _ _ _ _ _ _ _ K)) as S.
  assert (Mdb: i_mode (m_s mb) = LENLENS) by exact Md.
  assert (Hh: m_mode mb <> HEAD) by (rewrite Md; unfold LENLENS, HEAD; lia).
  assert (Ma: m_mode ma = LENLENS) by (unfold m_mode in *; rewrite (sr_mode _ _ _ S); exact Md).
  destruct (sr_nlen _ _ _ S (or_introl Mdb)) as (_ & _ & Eh).
  pose proof (sr_lenlens _ _ _ S Mdb) as LL.
  pose proof (mw_md _ (m3_w _ Wb)) as MD. destruct (md_lenlens _ MD Mdb) as (Hc & H0 & _). clear MD.
  destruct (sw_lens _ (mw_s _ (m3_w _ Wa))) as [ZLa _]. destruct (sw_lens _ (mw_s _ (m3_w _ Wb))) as [ZLb _].
  destruct (irl_pre ma Wa Ma) as (La & EZa & ZLa0 & FLa0 & _ & INa & CAPa & FOa & ZOa).
  destruct (irl_pre mb Wb Md) as (Lb & EZb & ZLb0 & FLb0 & _ & INb & CAPb & FOb & ZOb).
  assert (EL: sublist 0 19 La = sublist 0 19 Lb)
    by (apply (irl_L_eq (m_s ma) (m_s mb)); auto; lia).
  rewrite (irl_post_eq _ _ EZa), (irl_post_eq _ _ EZb). unfold irl_rhs. cbv zeta.
  rewrite EL. rewrite EL in CAPa, INa.
  destruct (TD CODES (sublist 0 19 Lb) 7 (irl_old (m_s ma)) (irl_old (m_s mb)) INb
              ltac:(intros; rewrite Zlength_sublist; lia) CAPa FOa ltac:(lia) FOb) as (Er & Eadv & Eb & Ok).
  rewrite Er, Eadv, Eb.
  destruct (Z.eqb_spec (it_ret (inflate_table_model CODES (sublist 0 19 Lb) 7 (irl_old (m_s mb)))) 0) as [R0|R0].
  2:{ cbn [negb irt_rr]. rewrite !irl_bad_eq.
      apply irl_kr; auto; [unfold BAD, HEAD; cbn; lia | apply irl_srel_bad; auto | reflexivity ..]. }
  cbn [negb].
  destruct (inflate_table_model CODES (sublist 0 19 Lb) 7 (irl_old (m_s ma))) as [ | ta | root used t1] eqn:MA;
    cbn [it_ret] in Er; [rewrite <- Er in R0; discriminate .. |].
  destruct (Ok root used t1 eq_refl) as (t2 & MB & TL).
  rewrite MB. cbn [it_tab it_adv it_bits].
  rewrite ZOa in CAPa. rewrite ZOb in CAPb. rewrite <- EL in MA, CAPa, INa.
  destruct (irl_tab C3 (m_s ma) La root used t1 (mw_s _ (m3_w _ Wa)) ZLa0 FLa0 INa CAPa MA) as (Zt1 & Ft1 & T1 & U1).
  destruct (irl_tab C3 (m_s mb) Lb root used t2 (mw_s _ (m3_w _ Wb)) ZLb0 FLb0 INb CAPb MB) as (Zt2 & Ft2 & T2 & U2).
  pose proof (irl_wf ma La root used t1 Wa Ma ZLa0 FLa0 Zt1 Ft1 T1 U1) as Wa'.
  pose proof (irl_wf mb Lb root used t2 Wb Md ZLb0 FLb0 Zt2 Ft2 T2 U2) as Wb'.
  apply CL; [ | exact Wa' | exact Wb' | exact L | reflexivity].
  rewrite !irl_cl_eq.
  apply irl_kr; auto; [unfold CODELENS, HEAD; cbn; lia | apply irl_srel_cl; auto; apply irl_tl_of; exact TL
                      | reflexivity ..].
Qed.

Lemma irt_ll_ok : Zlib.proof.inflate.Cover3.cover3_stmt -> tabdet_stmt -> irt_cl_stmt -> irt_ll_stmt.
Proof.
  intros C3 TD CL W0 wrap src pos inp aout ma mb K Wa Wb L Md.
  pose proof (mr_s _ _ (kr_rel _ _ _ _ _ _ _ _ K)) as S.
  assert (Ma: m_mode ma = LENLENS) by (unfold m_mode in *; rewrite (sr_mode _ _ _ S); exact Md).
  assert (La: m_leave ma = 0) by (rewrite (mr_leave _ _ (kr_rel _ _ _ _ _ _ _ _ K)); exact L).
  pose proof (irl_loop 19 _ _ _ _ _ _ ma mb K Wa Wb Md L) as K1.
  destruct (tb_lenlens_loop 19 ma Wa Ma La) as [Wa1 Ma1].
  destruct (tb_lenlens_loop 19 mb Wb Md L) as [Wb1 Mb1].
  unfold irt_ll.
  set (ma1 := lenlens_loop 19 ma) in *. set (mb1 := lenlens_loop 19 mb) in *. clearbody ma1 mb1.
  assert (EL: m_leave ma1 = m_leave mb1) by (apply (mr_leave _ _ (kr_rel _ _ _ _ _ _ _ _ K1))).
  rewrite EL. destruct (Z.eqb_spec (m_leave mb1) 1) as [L1|L1]; [exact K1|].
  assert (L1': m_leave mb1 = 0) by (destruct (leave_cases _ (m3_w _ Wb1)); auto; contradiction).
  apply irl_post; auto.
Qed.
