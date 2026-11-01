(* The decode cases LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT preserve mwf3x (Step3Stmts.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.inflate.Step3Stmts.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* Helpers                                                                                       *)

(* the state fields the decode cases write *)
Definition sfix (r: istate) (md len off ex bk was: Z) : istate :=
  IS md (i_last r) (i_wrap r) (i_havedict r) (i_flags r) (i_dmax r) (i_check r) (i_total r) (i_head r)
     (i_wbits r) (i_wsize r) (i_whave r) (i_wnext r) (i_win r) (i_wdata r) (i_hold r) (i_bits r) len off ex
     (i_lencode r) (i_distcode r) (i_lenbits r) (i_distbits r) (i_ncode r) (i_nlen r) (i_ndist r) (i_have r)
     (i_next r) (i_lens r) (i_codes r) (i_sane r) bk was.

Lemma mwf3x_sfix: forall m md len off ex bk was,
  mwf3x m -> decode_mode (m_mode m) ->
  HEAD < md <= SYNC -> md <> LENLENS -> md <> CODELENS ->
  urange len -> urange off -> 0 <= ex <= 15 -> -1 <= bk <= 1000 -> urange was ->
  (md = LENEXT -> ex <= 5 /\ len <= 258 /\ bk <= 15 /\ 1 <= len) ->
  (md = DIST -> bk <= 20 /\ 1 <= len) ->
  (md = DISTEXT -> ex <= 13 /\ off <= 32768 /\ bk <= 35 /\ 1 <= len /\ 1 <= off) ->
  (md = MATCH -> 1 <= len /\ 1 <= off) ->
  mwf3x (set_m_s m (sfix (m_s m) md len off ex bk was)).
Proof.
  intros m md len off ex bk was [W X] D HR3 H1 H2 UL UO UE UB UW HLE HD HDE HM.
  assert (HR: HEAD <= md <= SYNC) by lia.
  assert (OE: m_out m = m_aout m).
  { apply mwf_out_eq; auto; destruct D as [D|[D|[D|[D|[D|[D|D]]]]]]; rewrite D;
    unfold LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, LENGTH, DONE, BAD; lia. }
  destruct (md_tables _ (mw_md _ W) D) as [TL TD].
  pose proof (x3_lens _ X D) as XL.
  destruct W as [MD SW HW INP AOUT NX OW HOLD BITS IN OUT RET LEAVE ADLER TIN TOUT SNX SOW OUTEQ].
  destruct SW. destruct X as [XA XB XC XD].
  assert (MW: modewf (sfix (m_s m) md len off ex bk was)).
  { constructor; cbn [sfix i_mode i_length i_offset i_extra i_back i_was]; intros; try subst md; try congruence; auto.
    + destruct (HLE eq_refl) as (? & ? & ? & ?); auto.
    + destruct (HDE eq_refl) as (? & ? & ? & ? & ?); auto.
    + destruct (HM eq_refl) as (? & ?); auto.
    + destruct H as [H|[H|H]]; subst md; [destruct (HLE eq_refl) | destruct (HD eq_refl) | destruct (HDE eq_refl)]; tauto.
    + destruct H as [H|H]; subst md; [destruct (HDE eq_refl) | destruct (HM eq_refl)]; tauto.
    + repeat split; intros; subst md; [destruct (HLE eq_refl) | destruct (HD eq_refl) | destruct (HDE eq_refl)]; tauto. }
  assert (SWF: swf (sfix (m_s m) md len off ex bk was)).
  { constructor; cbn [sfix i_mode i_length i_offset i_extra i_back i_was i_last i_wrap i_havedict i_flags i_dmax
      i_check i_total i_wbits i_wsize i_whave i_wnext i_win i_wdata i_hold i_bits i_lencode i_distcode
      i_lenbits i_distbits i_ncode i_nlen i_ndist i_have i_next i_lens i_codes i_sane]; auto. }
  split; split; unfold m_mode; cbn [set_m_s m_s m_h m_inp m_aout m_nx m_ow m_hold
    m_bits m_in m_out m_ret m_leave m_adler m_tin m_tout m_snx m_sow]; auto;
    cbn [sfix i_mode i_length i_offset i_wbits i_wsize i_lencode i_lenbits].
  all: try (match goal with |- ?x = HEAD -> _ => intros ?HH; exfalso; clear -HR3 HH; lia end).
  all: try (left; exact OE).
  all: try (intros; subst md; destruct (HLE eq_refl) as (? & ? & ? & ?); auto; fail).
  all: try (intros; subst md; destruct (HDE eq_refl) as (? & ? & ? & ? & ?); auto; fail).
  all: try (intros; exact XL).
Qed.

(* a state update of a machine in a decode mode that writes only mode, length, offset, extra, back, was *)
Lemma mwf3x_upd_s: forall m f,
  mwf3x m -> decode_mode (m_mode m) ->
  f (m_s m) = sfix (m_s m) (i_mode (f (m_s m))) (i_length (f (m_s m))) (i_offset (f (m_s m)))
                   (i_extra (f (m_s m))) (i_back (f (m_s m))) (i_was (f (m_s m))) ->
  HEAD < i_mode (f (m_s m)) <= SYNC -> i_mode (f (m_s m)) <> LENLENS -> i_mode (f (m_s m)) <> CODELENS ->
  urange (i_length (f (m_s m))) -> urange (i_offset (f (m_s m))) -> 0 <= i_extra (f (m_s m)) <= 15 ->
  -1 <= i_back (f (m_s m)) <= 1000 -> urange (i_was (f (m_s m))) ->
  (i_mode (f (m_s m)) = LENEXT -> i_extra (f (m_s m)) <= 5 /\ i_length (f (m_s m)) <= 258 /\
                                  i_back (f (m_s m)) <= 15 /\ 1 <= i_length (f (m_s m))) ->
  (i_mode (f (m_s m)) = DIST -> i_back (f (m_s m)) <= 20 /\ 1 <= i_length (f (m_s m))) ->
  (i_mode (f (m_s m)) = DISTEXT -> i_extra (f (m_s m)) <= 13 /\ i_offset (f (m_s m)) <= 32768 /\
                                   i_back (f (m_s m)) <= 35 /\ 1 <= i_length (f (m_s m)) /\ 1 <= i_offset (f (m_s m))) ->
  (i_mode (f (m_s m)) = MATCH -> 1 <= i_length (f (m_s m)) /\ 1 <= i_offset (f (m_s m))) ->
  mwf3x (upd_s m f).
Proof.
  intros m f M D E. unfold upd_s. rewrite E. apply mwf3x_sfix; auto.
Qed.

(* the machine updates as one state update of a base machine *)
Lemma set_mode_upd_s: forall m f md, set_mode (upd_s m f) md = upd_s m (fun s => set_i_mode (f s) md).
Proof. reflexivity. Qed.
Lemma upd_s_upd_s: forall m f g, upd_s (upd_s m f) g = upd_s m (fun s => g (f s)).
Proof. reflexivity. Qed.
Lemma dropbits_upd_s: forall n m f, dropbits n (upd_s m f) = upd_s (dropbits n m) f.
Proof. reflexivity. Qed.
Lemma set_bad_upd_s: forall m f e, set_bad (upd_s m f) e = upd_s (set_m_msg m (Some e)) (fun s => set_i_mode (f s) BAD).
Proof. reflexivity. Qed.
Lemma set_bad_eq: forall m e, set_bad m e = upd_s (set_m_msg m (Some e)) (fun s => set_i_mode s BAD).
Proof. reflexivity. Qed.

Lemma dropbits0: forall m, mwf m -> dropbits 0 (upd_s m (fun s => set_i_back s (i_back s + 0))) = m.
Proof.
  intros m W. pose proof (mw_bits _ W) as B.
  destruct m as [s h inp aout nx ow hold bits in_ out ret leave adler msg tin tout snx sow].
  destruct s. simpl in B.
  unfold dropbits, upd_s, set_m_bits, set_m_hold, set_m_s, set_i_back; simpl.
  rewrite Z.add_0_r, Z.shiftr_0_r, Z.sub_0_r. unfold u32. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma m_bits_dropbits: forall m n, 0 <= n <= m_bits m -> m_bits m <= 39 -> m_bits (dropbits n m) = m_bits m - n.
Proof. intros m n H1 H2. unfold dropbits; simpl. unfold u32. rewrite Z.mod_small by lia. reflexivity. Qed.

Lemma Znth_byte: forall l i, bytes_ok l -> 0 <= Znth i l <= 255.
Proof.
  intros l i B. unfold Znth. destruct (Z_lt_dec i 0). { unfold default, Inhabitant_Z; lia. }
  destruct (nth_in_or_default (Z.to_nat i) l Inhabitant_Z) as [I|E].
  - unfold bytes_ok in B. rewrite Forall_forall in B. specialize (B _ I). rep_lia.
  - rewrite E. unfold default, Inhabitant_Z; lia.
Qed.

Lemma copy_f_ok: forall n w sr ow, bytes_ok w -> bytes_ok ow ->
  Zlength (fst (copy_f n w sr ow)) = Zlength ow + Z.of_nat n /\ bytes_ok (fst (copy_f n w sr ow)).
Proof.
  induction n; intros w sr ow BW BO; simpl.
  - split; [lia | auto].
  - assert (A: forall x, 0 <= x <= 255 -> Zlength (ow ++ [x]) = Zlength ow + 1 /\ bytes_ok (ow ++ [x])).
    { intros x Hx. rewrite Zlength_app, Zlength_cons, Zlength_nil. split; [lia|].
      apply Forall_app; split; [auto | constructor; [rep_lia | constructor]]. }
    destruct sr as [i|i].
    + destruct (A (Znth i w) (Znth_byte w i BW)) as [A1 A2].
      destruct (IHn w (SWin (i + 1)) (ow ++ [Znth i w]) BW A2) as [C1 C2]. split; auto. lia.
    + destruct (A (Znth i ow) (Znth_byte ow i BO)) as [A1 A2].
      destruct (IHn w (SOut (i + 1)) (ow ++ [Znth i ow]) BW A2) as [C1 C2]. split; auto. lia.
Qed.

Lemma mwf3x_set_ow: forall m ow', mwf3x m -> bytes_ok ow' -> Zlength (m_ow m) <= Zlength ow' <= m_aout m ->
  mwf3x (set_m_ow m ow').
Proof.
  intros m ow' [W X] B L. apply mwf3x_intro with m; auto.
  destruct W; constructor; simpl; auto; try (split; [|auto]); lia.
Qed.

Lemma mwf3x_set_msg: forall m e, mwf3x m -> mwf3x (set_m_msg m e).
Proof. intros m e [W X]. apply mwf3x_intro with m; auto. destruct W; constructor; simpl; auto. Qed.

Lemma land15: forall x, 16 <= x <= 31 -> Z.land x 15 = x - 16.
Proof.
  intros x H. change 15 with (Z.ones 4). rewrite Z.land_ones by lia.
  symmetry. apply Z.mod_unique with (q := 1); [left; simpl; lia | simpl; lia].
Qed.

Lemma TYPE_val : Model.TYPE = 16191.
Proof. reflexivity. Qed.

Ltac rw_s := repeat match goal with H: m_s ?x = m_s ?y |- _ => progress rewrite H end.

(* the ranges of the state's fields *)
Ltac sw_facts W := let S := fresh in pose proof (mw_s _ W) as S; destruct S.

Ltac side :=
  try reflexivity; unfold urange, decode_mode, m_mode in *;
  cbn [m_s set_m_msg set_m_ow set_m_s dropbits set_m_bits set_m_hold upd_s set_mode i_mode i_length
       i_offset i_extra i_back i_was set_i_mode set_i_length set_i_offset set_i_extra set_i_back set_i_was];
  rw_s;
  rewrite ?TYPE_val in *;
  unfold HEAD, SYNC, LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, BAD in *;
  try (intros; repeat split; rep_lia).


Lemma match_fin: forall m sr c, mwf3x m -> m_mode m = MATCH -> 1 <= c <= i_length (m_s m) -> m_left m <> 0 ->
  iout_ok mwf3x (let s := m_s m in
    let copy := Z.min c (m_left m) in
    let '(ow', _) := copy_bytes (i_wdata s) sr copy (m_ow m) in
    let len' := i_length s - copy in
    let m := upd_s (set_m_ow m ow') (fun s => set_i_length s len') in
    IBrk (if len' =? 0 then set_mode m LEN else m)).
Proof.
  intros m sr c M2 Md Hc Hl. pose proof M2 as [W X].
  pose proof (mwf_left m W) as LR.
  assert (Wd: bytes_ok (i_wdata (m_s m))) by apply (sw_wdata _ (mw_s _ W)).
  assert (Ob: bytes_ok (m_ow m)) by apply (mw_ow _ W).
  pose proof (sw_length _ (mw_s _ W)) as SL. pose proof (sw_offset _ (mw_s _ W)) as SO.
  pose proof (sw_extra _ (mw_s _ W)) as SE. pose proof (sw_back _ (mw_s _ W)) as SB.
  pose proof (sw_was _ (mw_s _ W)) as SW.
  pose proof (md_offset _ (mw_md _ W) (or_intror Md)) as MO.
  cbv zeta. unfold copy_bytes.
  assert (Hn: 1 <= Z.min c (m_left m) <= i_length (m_s m) /\ Z.min c (m_left m) <= m_left m) by lia.
  destruct (copy_f_ok (Z.to_nat (Z.min c (m_left m))) (i_wdata (m_s m)) sr (m_ow m) Wd Ob) as [CL CB].
  destruct (copy_f (Z.to_nat (Z.min c (m_left m))) (i_wdata (m_s m)) sr (m_ow m)) as [ow' sr'] eqn:CF.
  cbn [fst] in CL, CB. rewrite Z2Nat.id in CL by lia.
  assert (M2': mwf3x (set_m_ow m ow')) by (apply mwf3x_set_ow; auto; unfold m_left in *; lia).
  assert (Dm: decode_mode (m_mode (set_m_ow m ow'))) by (change (m_mode (set_m_ow m ow')) with (m_mode m); rewrite Md; unfold decode_mode; auto 10).
  destruct (Z.eqb_spec (i_length (m_s m) - Z.min c (m_left m)) 0); cbn [iout_ok].
  - rewrite set_mode_upd_s. apply mwf3x_upd_s; auto; side.
  - apply mwf3x_upd_s; auto; side.
Qed.

Lemma MATCH_ok : ok_MATCH.
Proof.
  intros m M2 L Md. pose proof M2 as [W X]. sw_facts W. unfold c_MATCH.
  destruct (Z.eqb_spec (m_left m) 0) as [E|E].
  { cbn [iout_ok]. apply mwf3x_set_leave; auto. }
  assert (OE: m_out m = m_aout m) by (apply mwf_out_eq; auto; rewrite Md; unfold MATCH, LENGTH, DONE, BAD; lia).
  pose proof (mwf_left m W) as LR.
  assert (C0: u32 (m_out m - m_left m) = Zlength (m_ow m)).
  { pose proof (mw_ow _ W). pose proof (mw_aout _ W). pose proof (Zlength_nonneg (m_ow m)).
    unfold u32, m_left in *. rewrite OE. rewrite Z.mod_small; rep_lia. }
  rewrite C0.
  pose proof (md_match _ (mw_md _ W) Md) as ML.
  destruct (Z.ltb_spec (Zlength (m_ow m)) (i_offset (m_s m))).
  - rewrite sw_sane. cbn [Z.eqb negb andb].
    destruct (Z.ltb_spec (i_whave (m_s m)) (i_offset (m_s m) - Zlength (m_ow m))); cbn [andb].
    + cbn [iout_ok]. rewrite set_bad_eq. apply mwf3x_upd_s; [apply mwf3x_set_msg; auto | ..]; side.
    + destruct (Z.ltb_spec (i_wnext (m_s m)) (i_offset (m_s m) - Zlength (m_ow m))).
      * apply match_fin; auto; lia.
      * apply match_fin; auto; lia.
  - apply match_fin; auto; lia.
Qed.

Lemma DISTEXT_ok : ok_DISTEXT.
Proof.
  intros m M2 L Md. pose proof M2 as [W X].
  pose proof (md_distext _ (mw_md _ W) Md) as XT.
  pose proof (md_offset _ (mw_md _ W) (or_introl Md)) as OF1.
  pose proof (x3_distext _ X Md) as OF2.
  pose proof (md_length _ (mw_md _ W) (or_intror (or_intror Md))) as LN.
  pose proof (proj2 (proj2 (md_back _ (mw_md _ W))) Md) as BK.
  pose proof (mw_bits _ W) as BT.
  sw_facts W. unfold c_DISTEXT.
  destruct (Z.eqb_spec (i_extra (m_s m)) 0) as [E0|E0]; cbn [negb].
  - apply MATCH_ok; [ | exact L | reflexivity].
    unfold set_mode. apply mwf3x_upd_s; auto; side.
  - pose proof (needbits_ok (i_extra (m_s m)) m W L ltac:(lia)) as NB.
    pose proof (mwf3x_needbits (i_extra (m_s m)) m M2 ltac:(lia)) as M2n.
    pose proof (needbits_s (i_extra (m_s m)) m) as NS.
    remember (needbits (i_extra (m_s m)) m) as m1 eqn:Em1.
    destruct (Z.eqb_spec (m_leave m1) 1) as [L1|L1]; cbn [iout_ok].
    { exact M2n. }
    destruct (NB L1) as [B1 L1'].
    pose proof (mw_bits _ (m3_w _ M2n)) as BT1.
    pose proof (bitsn_range m1 (i_extra (m_s m)) ltac:(lia)) as BR.
    assert (P13: 2 ^ i_extra (m_s m) <= 2 ^ 13) by (apply Z.pow_le_mono_r; lia).
    change (2 ^ 13) with 8192 in P13.
    assert (U: u32 (i_offset (m_s m) + bitsn m1 (i_extra (m_s m))) = i_offset (m_s m) + bitsn m1 (i_extra (m_s m))).
    { unfold u32. rewrite Z.mod_small; [reflexivity|]. unfold urange in *. change (2 ^ 32) with 4294967296. lia. }
    apply MATCH_ok; [ | exact L1' | reflexivity].
    rewrite dropbits_upd_s, set_mode_upd_s.
    apply mwf3x_upd_s; [apply mwf3x_dropbits; auto; lia | ..]; side.
Qed.

Lemma dist_tail: forall M0 b1 h, mwf3x M0 -> m_leave M0 = 0 -> m_mode M0 = DIST ->
  0 <= b1 -> 0 <= e_bits h -> b1 + e_bits h <= 15 -> b1 + e_bits h <= m_bits M0 ->
  final_ok DISTS h -> entry_ok h ->
  iout_ok mwf3x (
    let m := dropbits b1 (upd_s M0 (fun s => set_i_back s (i_back s + b1))) in
    let m := dropbits (e_bits h) (upd_s m (fun s => set_i_back s (i_back s + e_bits h))) in
    if negb (Z.land (e_op h) 64 =? 0) then IBrk (set_bad m M_d_code) else
    let m := upd_s m (fun s => set_i_extra (set_i_offset s (e_val h)) (Z.land (e_op h) 15)) in
    c_DISTEXT (set_mode m DISTEXT)).
Proof.
  intros M0 b1 h M2 L Md B0 B1 B2 B3 F EO. pose proof M2 as [W X].
  pose proof (md_length _ (mw_md _ W) (or_intror (or_introl Md))) as LN.
  pose proof (proj1 (proj2 (md_back _ (mw_md _ W))) Md) as BK.
  pose proof (mw_bits _ W) as BT.
  sw_facts W. destruct EO as (EO1 & EO2 & EO3).
  assert (M2a: mwf3x (dropbits (e_bits h) (dropbits b1 M0))).
  { apply mwf3x_dropbits; [apply mwf3x_dropbits; auto; lia|]. rewrite m_bits_dropbits by lia. lia. }
  assert (La: m_leave (dropbits (e_bits h) (dropbits b1 M0)) = 0) by exact L.
  cbv zeta. repeat (rewrite dropbits_upd_s || rewrite upd_s_upd_s || rewrite set_mode_upd_s || rewrite set_bad_upd_s).
  destruct (Z.eqb_spec (Z.land (e_op h) 64) 0) as [E64|E64]; cbn [negb iout_ok].
  - assert (F': (16 <= e_op h <= 29 /\ 1 <= e_val h <= 32768) \/
                (Z.land (e_op h) 64 <> 0 /\ Z.land (e_op h) 48 = 0)) by exact F.
    destruct F' as [[OP VL] | [C _]]; [| congruence].
    rewrite land15 by lia.
    apply DISTEXT_ok; [ | exact La | reflexivity].
    apply mwf3x_upd_s; auto; side.
  - apply mwf3x_upd_s; [apply mwf3x_set_msg; auto | ..]; side.
Qed.

Lemma DIST_ok : ok_DIST.
Proof.
  intros m M2 L Md. pose proof M2 as [W X]. unfold c_DIST. cbv zeta.
  assert (D: decode_mode (i_mode (m_s m))) by (change (i_mode (m_s m)) with (m_mode m); rewrite Md; unfold decode_mode; auto 10).
  destruct (md_tables _ (mw_md _ W) D) as [_ (sz & SZ & TV)].
  pose proof (tv_rb _ _ _ _ TV) as RB.
  pose proof (lookup1_ok lenfix_list distfix_list (i_distcode (m_s m)) (i_distbits (m_s m)) m W L ltac:(lia)
                (fun i Hi => proj2 (proj1 (tv_root_bits _ _ _ _ i TV Hi)))) as LK.
  destruct (lookup1 lenfix_list distfix_list (i_distcode (m_s m)) (i_distbits (m_s m)) m) as [[here m1] ok] eqn:E1.
  destruct LK as (W1 & S1 & OK1 & NOK1).
  assert (M21: mwf3x m1) by (apply mwf3x_intro with m; auto).
  destruct ok; cbn [negb iout_ok]; [ | exact M21 ].
  destruct (OK1 eq_refl) as (L1 & B1 & i & Hi & Eh).
  pose proof (tv_root_bits _ _ _ _ i TV Hi) as [RBh EOh]. rewrite <- Eh in RBh, EOh.
  assert (Md1: m_mode m1 = DIST) by (unfold m_mode in *; rewrite S1; exact Md).
  destruct (Z.eqb_spec (Z.land (e_op here) 240) 0) as [LK0|LK0].
  - assert (ISL: islink DISTS (e_op here) = true) by (unfold islink; rewrite LK0; reflexivity).
    rewrite Eh in ISL. pose proof (tv_sub _ _ _ _ i TV Hi ISL) as SO. rewrite <- Eh in SO.
    destruct SO as (SB & SO1 & SO2 & SBT).
    assert (SB2: forall j, 0 <= j < 2 ^ e_op here ->
      e_bits here + e_bits (tab_entry lenfix_list distfix_list (m_s m1) (i_distcode (m_s m)) (e_val here + j)) <= 15).
    { intros j Hj. rewrite S1. destruct (SBT j Hj) as (_ & _ & _ & A & _). lia. }
    pose proof (lookup2_ok lenfix_list distfix_list (i_distcode (m_s m)) here m1 W1 L1 ltac:(lia) ltac:(lia) SB2) as LK2.
    destruct (lookup2 lenfix_list distfix_list (i_distcode (m_s m)) here m1) as [[h2 m2] ok2] eqn:E2.
    destruct LK2 as (W2 & S2 & OK2 & NOK2).
    assert (M22: mwf3x m2) by (apply mwf3x_intro with m; auto; congruence).
    destruct ok2; cbn [negb iout_ok]; [ | exact M22 ].
    destruct (OK2 eq_refl) as (L2 & B2 & j & Hj & Eh2). rewrite S1 in Eh2.
    destruct (SBT j Hj) as (_ & EO2 & _ & A2 & F2). cbv zeta in EO2, A2, F2. rewrite <- Eh2 in EO2, A2, F2.
    pose proof (proj1 (proj2 EO2)) as BH2.
    apply (dist_tail m2 (e_bits here) h2); auto; try lia.
    unfold m_mode in *; rewrite S2; exact Md1.
  - assert (ISL: islink DISTS (e_op here) = false)
      by (unfold islink; rewrite (proj2 (Z.eqb_neq _ _) LK0); apply andb_false_r).
    rewrite Eh in ISL. destruct (tv_final _ _ _ _ i TV Hi ISL) as [FB FF]. rewrite <- Eh in FB, FF.
    cbn [negb iout_ok].
    rewrite <- (dropbits0 m1 W1).
    apply (dist_tail m1 0 here); auto; lia.
Qed.

Lemma LENEXT_ok : ok_LENEXT.
Proof.
  intros m M2 L Md. pose proof M2 as [W X].
  pose proof (md_lenext _ (mw_md _ W) Md) as XT.
  pose proof (x3_lenext _ X Md) as LN2.
  pose proof (md_length _ (mw_md _ W) (or_introl Md)) as LN.
  pose proof (proj1 (md_back _ (mw_md _ W)) Md) as BK.
  pose proof (mw_bits _ W) as BT.
  sw_facts W. unfold c_LENEXT.
  destruct (Z.eqb_spec (i_extra (m_s m)) 0) as [E0|E0]; cbn [negb].
  - apply DIST_ok; [ | exact L | reflexivity].
    rewrite set_mode_upd_s. apply mwf3x_upd_s; auto; side.
  - pose proof (needbits_ok (i_extra (m_s m)) m W L ltac:(lia)) as NB.
    pose proof (mwf3x_needbits (i_extra (m_s m)) m M2 ltac:(lia)) as M2n.
    pose proof (needbits_s (i_extra (m_s m)) m) as NS.
    remember (needbits (i_extra (m_s m)) m) as m1 eqn:Em1.
    destruct (Z.eqb_spec (m_leave m1) 1) as [L1|L1]; cbn [iout_ok].
    { exact M2n. }
    destruct (NB L1) as [B1 L1'].
    pose proof (mw_bits _ (m3_w _ M2n)) as BT1.
    pose proof (bitsn_range m1 (i_extra (m_s m)) ltac:(lia)) as BR.
    assert (P5: 2 ^ i_extra (m_s m) <= 2 ^ 5) by (apply Z.pow_le_mono_r; lia).
    change (2 ^ 5) with 32 in P5.
    assert (U: u32 (i_length (m_s m) + bitsn m1 (i_extra (m_s m))) = i_length (m_s m) + bitsn m1 (i_extra (m_s m))).
    { unfold u32. rewrite Z.mod_small; [reflexivity|]. unfold urange in *. change (2 ^ 32) with 4294967296. lia. }
    apply DIST_ok; [ | exact L1' | reflexivity].
    rewrite dropbits_upd_s, upd_s_upd_s, set_mode_upd_s.
    apply mwf3x_upd_s; [apply mwf3x_dropbits; auto; lia | ..]; side.
Qed.

Lemma LIT_ok : ok_LIT.
Proof.
  intros m M2 L Md. pose proof M2 as [W X]. pose proof (mw_ow _ W) as OW. sw_facts W. unfold c_LIT.
  destruct (Z.eqb_spec (m_left m) 0) as [E|E]; cbn [iout_ok].
  - apply mwf3x_set_leave; auto.
  - pose proof (mwf_left m W) as LR.
    assert (B: bytes_ok (m_ow m ++ [i_length (m_s m) mod 256])).
    { apply Forall_app; split; [apply OW | constructor; [|constructor]].
      pose proof (Z.mod_pos_bound (i_length (m_s m)) 256 ltac:(lia)). rep_lia. }
    unfold set_mode. apply mwf3x_upd_s;
      [apply mwf3x_set_ow; [auto | auto | rewrite Zlength_app, Zlength_cons, Zlength_nil; unfold m_left in *; lia] | ..];
      side.
Qed.

Lemma len_tail: forall M0 b1 h, mwf3x M0 -> m_leave M0 = 0 -> m_mode M0 = LEN -> i_back (m_s M0) = 0 ->
  0 <= b1 -> 0 <= e_bits h -> b1 + e_bits h <= 15 -> b1 + e_bits h <= m_bits M0 ->
  final_ok LENS h -> entry_ok h ->
  iout_ok mwf3x (
    let m := dropbits b1 (upd_s M0 (fun s => set_i_back s (i_back s + b1))) in
    let m := dropbits (e_bits h) (upd_s m (fun s => set_i_back s (i_back s + e_bits h))) in
    let m := upd_s m (fun s => set_i_length s (e_val h)) in
    if e_op h =? 0 then IBrk (set_mode m LIT) else
    if negb (Z.land (e_op h) 32 =? 0) then IBrk (set_mode (upd_s m (fun s => set_i_back s (-1))) Model.TYPE) else
    if negb (Z.land (e_op h) 64 =? 0) then IBrk (set_bad m M_ll_code) else
    c_LENEXT lenfix_list distfix_list (set_mode (upd_s m (fun s => set_i_extra s (Z.land (e_op h) 15))) LENEXT)).
Proof.
  intros M0 b1 h M2 L Md BK B0 B1 B2 B3 F EO. pose proof M2 as [W X].
  pose proof (mw_bits _ W) as BT.
  sw_facts W. destruct EO as (EO1 & EO2 & EO3).
  assert (M2a: mwf3x (dropbits (e_bits h) (dropbits b1 M0))).
  { apply mwf3x_dropbits; [apply mwf3x_dropbits; auto; lia|]. rewrite m_bits_dropbits by lia. lia. }
  assert (La: m_leave (dropbits (e_bits h) (dropbits b1 M0)) = 0) by exact L.
  cbv zeta. repeat (rewrite dropbits_upd_s || rewrite upd_s_upd_s || rewrite set_mode_upd_s || rewrite set_bad_upd_s).
  destruct (Z.eqb_spec (e_op h) 0) as [O0|O0]; cbn [iout_ok].
  - apply mwf3x_upd_s; auto; side.
  - destruct (Z.eqb_spec (Z.land (e_op h) 32) 0) as [O32|O32]; cbn [negb iout_ok].
    + destruct (Z.eqb_spec (Z.land (e_op h) 64) 0) as [O64|O64]; cbn [negb iout_ok].
      * assert (F': (e_op h = 0 /\ 0 <= e_val h <= 255) \/ (16 <= e_op h <= 21 /\ 3 <= e_val h <= 258) \/
                    e_op h = 96 \/ (Z.land (e_op h) 64 <> 0 /\ Z.land (e_op h) 48 = 0)) by exact F.
        destruct F' as [[? ?] | [[OP VL] | [O96 | [C _]]]];
          [lia | | rewrite O96 in O32; vm_compute in O32; discriminate | congruence].
        rewrite land15 by lia.
        apply LENEXT_ok; [ | exact La | reflexivity].
        apply mwf3x_upd_s; auto; side.
      * apply mwf3x_upd_s; [apply mwf3x_set_msg; auto | ..]; side.
    + apply mwf3x_upd_s; auto; side.
Qed.

Lemma LEN_ok : fast_stmt -> ok_LEN.
Proof.
  intros FS m M2 L Md. unfold c_LEN.
  destruct (andb (andb (6 <=? m_have m) (258 <=? m_left m)) (m_bits m <? 8)) eqn:FC.
  { rewrite !andb_true_iff, !Z.leb_le, Z.ltb_lt in FC. destruct FC as [[F1 F2] F3].
    exact (FS m M2 L Md F1 F2 F3). }
  pose proof M2 as [W X].
  cbv beta iota zeta.
  remember (upd_s m (fun s => set_i_back s 0)) as m0 eqn:Em0.
  assert (M20: mwf3x m0) by (subst m0; sw_facts W; apply mwf3x_upd_s; auto; side).
  assert (Md0: m_mode m0 = LEN) by (subst m0; exact Md).
  assert (L0: m_leave m0 = 0) by (subst m0; exact L).
  assert (BK0: i_back (m_s m0) = 0) by (subst m0; reflexivity).
  clear Em0 W X M2 Md L FC. clear m. rename m0 into m. rename M20 into M2. pose proof M2 as [W X].
  assert (D: decode_mode (i_mode (m_s m))) by (change (i_mode (m_s m)) with (m_mode m); rewrite Md0; unfold decode_mode; auto 10).
  destruct (md_tables _ (mw_md _ W) D) as [(sz & SZ & TV) _].
  pose proof (tv_rb _ _ _ _ TV) as RB.
  pose proof (lookup1_ok lenfix_list distfix_list (i_lencode (m_s m)) (i_lenbits (m_s m)) m W L0 ltac:(lia)
                (fun i Hi => proj2 (proj1 (tv_root_bits _ _ _ _ i TV Hi)))) as LK.
  destruct (lookup1 lenfix_list distfix_list (i_lencode (m_s m)) (i_lenbits (m_s m)) m) as [[here m1] ok] eqn:E1.
  destruct LK as (W1 & S1 & OK1 & NOK1).
  assert (M21: mwf3x m1) by (apply mwf3x_intro with m; auto).
  destruct ok; cbn [negb iout_ok]; [ | exact M21 ].
  destruct (OK1 eq_refl) as (L1 & B1 & i & Hi & Eh).
  pose proof (tv_root_bits _ _ _ _ i TV Hi) as [RBh EOh]. rewrite <- Eh in RBh, EOh.
  assert (Md1: m_mode m1 = LEN) by (unfold m_mode in *; rewrite S1; exact Md0).
  assert (BK1: i_back (m_s m1) = 0) by (rewrite S1; exact BK0).
  destruct (andb (negb (e_op here =? 0)) (Z.land (e_op here) 240 =? 0)) eqn:ISL.
  - change (islink LENS (e_op here) = true) in ISL.
    rewrite Eh in ISL. pose proof (tv_sub _ _ _ _ i TV Hi ISL) as SO. rewrite <- Eh in SO.
    destruct SO as (SB & SO1 & SO2 & SBT).
    assert (SB2: forall j, 0 <= j < 2 ^ e_op here ->
      e_bits here + e_bits (tab_entry lenfix_list distfix_list (m_s m1) (i_lencode (m_s m)) (e_val here + j)) <= 15).
    { intros j Hj. rewrite S1. destruct (SBT j Hj) as (_ & _ & _ & A & _). lia. }
    pose proof (lookup2_ok lenfix_list distfix_list (i_lencode (m_s m)) here m1 W1 L1 ltac:(lia) ltac:(lia) SB2) as LK2.
    destruct (lookup2 lenfix_list distfix_list (i_lencode (m_s m)) here m1) as [[h2 m2] ok2] eqn:E2.
    destruct LK2 as (W2 & S2 & OK2 & NOK2).
    assert (M22: mwf3x m2) by (apply mwf3x_intro with m; auto; congruence).
    destruct ok2; cbn [negb iout_ok]; [ | exact M22 ].
    destruct (OK2 eq_refl) as (L2 & B2 & j & Hj & Eh2). rewrite S1 in Eh2.
    destruct (SBT j Hj) as (_ & EO2 & _ & A2 & F2). cbv zeta in EO2, A2, F2. rewrite <- Eh2 in EO2, A2, F2.
    pose proof (proj1 (proj2 EO2)) as BH2.
    apply (len_tail m2 (e_bits here) h2); auto; try lia.
    + unfold m_mode in *; rewrite S2; exact Md1.
    + rewrite S2; exact BK1.
  - change (islink LENS (e_op here) = false) in ISL.
    rewrite Eh in ISL. destruct (tv_final _ _ _ _ i TV Hi ISL) as [FB FF]. rewrite <- Eh in FB, FF.
    cbn [negb iout_ok].
    rewrite <- (dropbits0 m1 W1).
    apply (len_tail m1 0 here); auto; lia.
Qed.

Lemma LEN__ok : fast_stmt -> ok_LEN_.
Proof.
  intros FS m M2 L Md. pose proof M2 as [W X]. sw_facts W. unfold c_LEN_.
  apply (LEN_ok FS); [ | exact L | reflexivity].
  unfold set_mode. apply mwf3x_upd_s; auto; side.
Qed.

(* all the cases of this file *)
Lemma decode_all : ok_MATCH /\ ok_DISTEXT /\ ok_DIST /\ ok_LENEXT /\ ok_LIT /\
  (fast_stmt -> ok_LEN) /\ (fast_stmt -> ok_LEN_).
Proof.
  split; [exact MATCH_ok|]. split; [exact DISTEXT_ok|]. split; [exact DIST_ok|].
  split; [exact LENEXT_ok|]. split; [exact LIT_ok|]. split; [exact LEN_ok | exact LEN__ok].
Qed.
