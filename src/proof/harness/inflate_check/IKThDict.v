(* Law inflate_check, theory part: cases DICTID, DICT, TYPE, TYPEDO keep Kx. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_check.IKTheoryDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* stepf2 per mode                                                                                *)

Lemma ikd_step_DICTID fl fx dx m : m_mode m = DICTID -> stepf2 fl fx dx m = c_DICTID fl m.
Proof. intros H. unfold stepf2, Zlib.proof.inflate.Model2.step2. rewrite H. reflexivity. Qed.
Lemma ikd_step_DICT fl fx dx m : m_mode m = DICT -> stepf2 fl fx dx m = c_DICT fl m.
Proof. intros H. unfold stepf2, Zlib.proof.inflate.Model2.step2. rewrite H. reflexivity. Qed.
Lemma ikd_step_TYPE fl fx dx m : m_mode m = Zlib.proof.inflate.Model.TYPE -> stepf2 fl fx dx m = c_TYPE fl m.
Proof. intros H. unfold stepf2, Zlib.proof.inflate.Model2.step2. rewrite H. reflexivity. Qed.
Lemma ikd_step_TYPEDO fl fx dx m : m_mode m = TYPEDO -> stepf2 fl fx dx m = c_TYPEDO fl m.
Proof. intros H. unfold stepf2, Zlib.proof.inflate.Model2.step2. rewrite H. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Kx after one of these cases                                                                    *)

Ltac ikd_cst := unfold HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT,
  Zlib.proof.inflate.Model.TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS, LEN_, LEN, LENEXT,
  DIST, DISTEXT, MATCH, LIT, CHECK, LENGTH, DONE, BAD, MEM, SYNC in *.

Ltac ikd_md := unfold ik_pre_mode, ik_gzhdr_mode, ik_post_mode, decode_mode in *; ikd_cst; lia.

(* the fields Kx reads besides the bit buffer, the mode, check and adler *)
Definition ikd_keep (m m': mst) : Prop :=
  m_out m' = m_out m /\ m_aout m' = m_aout m /\ m_ow m' = m_ow m /\ m_tout m' = m_tout m /\
  i_total (m_s m') = i_total (m_s m) /\ i_flags (m_s m') = i_flags (m_s m).

(* the modes TYPE / TYPEDO go to *)
Definition ikd_pm (md b: Z) : Prop :=
  md = Zlib.proof.inflate.Model.TYPE \/ md = TYPEDO \/ md = STORED \/ md = LEN_ \/ md = TABLE \/ md = BAD \/
  (md = CHECK /\ b mod 8 = 0).

Lemma ikd_Kx_post wrap src pos out a0 m m' :
  Kx wrap src pos out a0 m -> ikd_keep m m' ->
  i_check (m_s m') = i_check (m_s m) -> m_adler m' = m_adler m ->
  (m_mode m = Zlib.proof.inflate.Model.TYPE \/ m_mode m = TYPEDO) ->
  ik_bitbuf src (pos + m_nx m') (m_hold m') (m_bits m') ->
  8 * (pos + m_nx m) - m_bits m <= 8 * (pos + m_nx m') - m_bits m' ->
  ikd_pm (m_mode m') (m_bits m') ->
  Kx wrap src pos out a0 m'.
Proof.
  intros X (Ho & Ha & Hw & Ht & Htot & Hf) Hck Had Hmd Hb Hc Hpm.
  assert (Hpost : wrap <> 0 -> ik_post wrap src pos out m').
  { intros W. pose proof (kx_post _ _ _ _ _ _ X W) as P.
    assert (PM : ik_post_mode (m_mode m)) by ikd_md.
    specialize (P PM). unfold ik_post in *. rewrite Hf, Hck, Had, Ho, Ha, Hw.
    destruct P as [P1 [P2 P3]]. split; [|split; auto]. destruct P1 as [P1|P1]; [left|right]; intuition lia. }
  unfold ikd_pm in Hpm.
  constructor.
  - exact (kx_wrap _ _ _ _ _ _ X).
  - exact Hb.
  - split; intros; exfalso; ikd_md.
  - unfold m_left. rewrite Ho, Ha, Hw. exact (kx_out _ _ _ _ _ _ X).
  - rewrite Htot, Ho, Ha. exact (kx_total _ _ _ _ _ _ X).
  - rewrite Ht, Ho, Ha. exact (kx_tout _ _ _ _ _ _ X).
  - intros W. destruct (kx_raw _ _ _ _ _ _ X W) as (A & _). split; [congruence|]. ikd_md.
  - intros _ P. exfalso. ikd_md.
  - intros _ P. exfalso. ikd_md.
  - intros _ P. exfalso. ikd_md.
  - intros W _. apply Hpost; auto.
  - intros W _. right. apply Hpost; auto.
  - intros W. unfold ik_trail. split; [|split]; intros E; [|exfalso; ikd_md..]. ikd_md.
Qed.

Lemma ikd_Kx_pre wrap src pos out a0 m m' :
  Kx wrap src pos out a0 m -> ikd_keep m m' ->
  (m_mode m = DICTID \/ m_mode m = DICT) -> (m_mode m' = DICTID \/ m_mode m' = DICT) ->
  ik_bitbuf src (pos + m_nx m') (m_hold m') (m_bits m') ->
  8 * (pos + m_nx m) - m_bits m <= 8 * (pos + m_nx m') - m_bits m' ->
  Kx wrap src pos out a0 m'.
Proof.
  intros X (Ho & Ha & Hw & Ht & Htot & Hf) Hmd Hmd' Hb Hc.
  assert (W : wrap <> 0).
  { intros W. destruct (kx_raw _ _ _ _ _ _ X W) as (_ & _ & D1 & D2). destruct Hmd; contradiction. }
  constructor.
  - exact (kx_wrap _ _ _ _ _ _ X).
  - exact Hb.
  - split; intros; exfalso; ikd_md.
  - unfold m_left. rewrite Ho, Ha, Hw. exact (kx_out _ _ _ _ _ _ X).
  - rewrite Htot, Ho, Ha. exact (kx_total _ _ _ _ _ _ X).
  - rewrite Ht, Ho, Ha. exact (kx_tout _ _ _ _ _ _ X).
  - intros W'. contradiction.
  - intros _ _. assert (PM : ik_pre_mode (m_mode m)) by ikd_md.
    destruct (kx_pre _ _ _ _ _ _ X W PM) as (O1 & O2 & O3).
    split; [exact O1|]. rewrite Hw, Ho, Ha. auto.
  - intros _ P. exfalso. ikd_md.
  - intros _ _. destruct (kx_zh _ _ _ _ _ _ X W Hmd) as (Z1 & Z2 & Z3 & Z4 & Z5).
    unfold ik_zh_ok. rewrite Hf. refine (conj Z1 (conj Z2 (conj Z3 (conj Z4 _)))). lia.
  - intros _ P. exfalso. ikd_md.
  - intros _ P. exfalso. ikd_md.
  - intros _. unfold ik_trail. split; [|split]; intros E; exfalso; ikd_md.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The cases                                                                                      *)

Ltac ikd_red := unfold m_mode, set_bad, dropbits, set_mode, set_leave, upd_s, bytebits, initbits, restore,
    bitsn in *;
  cbn [m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler m_msg m_tin m_tout
       m_snx m_sow set_m_s set_m_h set_m_nx set_m_hold set_m_bits set_m_msg set_m_adler set_m_tin
       set_m_leave set_m_snx set_m_sow i_mode i_flags i_total i_check set_i_mode set_i_check set_i_last
       set_i_lencode set_i_lenbits set_i_distcode set_i_distbits set_i_bits set_i_hold] in *.

Lemma ikd_u32 x : 0 <= x < 2 ^ 32 -> u32 x = x.
Proof. intros. unfold u32. apply Z.mod_small. lia. Qed.

Lemma ikd_same m m' : ik_same_but_buf m m' ->
  ikd_keep m m' /\ m_s m' = m_s m /\ m_adler m' = m_adler m /\ m_inp m' = m_inp m.
Proof.
  intros (Ss & _ & Si & Sa & So & _ & Sout & _ & Sad & _ & _ & St & _).
  unfold ikd_keep. rewrite Ss. repeat split; auto.
Qed.

Lemma ikd_typedo (KIT: ik_kit) wrap src pos out a0 inp flush m :
  ctx_ok src pos inp -> m_inp m = inp -> 0 <= m_nx m <= Zlength inp -> 0 <= m_bits m <= 31 ->
  m_leave m = 0 -> Kx wrap src pos out a0 m ->
  (m_mode m = Zlib.proof.inflate.Model.TYPE \/ m_mode m = TYPEDO) ->
  stepx_post wrap src pos out a0 (c_TYPEDO flush m).
Proof.
  intros Hc Hi Hn Hb Hl X Hmd.
  pose proof (kx_buf _ _ _ _ _ _ X) as Bf.
  unfold c_TYPEDO.
  destruct (negb _).
  { cbn [stepx_post]. apply (ikd_Kx_post wrap src pos out a0 m); auto.
    - unfold ikd_keep. ikd_red. repeat split; reflexivity.
    - apply (kk_bb_bytebits KIT). exact Bf.
    - ikd_red. pose proof (Z.mod_pos_bound (m_bits m) 8 ltac:(lia)). lia.
    - unfold ikd_pm. ikd_red. right; right; right; right; right; right. split; [reflexivity|].
      rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia. reflexivity. }
  pose proof (kk_needbits KIT src pos inp 3 m Hc Hi Hn ltac:(lia) ltac:(lia) Bf) as NB. cbv zeta in NB.
  destruct NB as (B3 & S3 & N3 & D3 & L3 & E3 & V3).
  assert (R3 : m_bits (needbits 3 m) <= 31).
  { destruct (Z_lt_le_dec (m_bits m) 3) as [Lt|Ge]; [specialize (L3 Lt); lia|rewrite (E3 Ge); lia]. }
  destruct (ikd_same _ _ S3) as (K3 & Ss & Sad & Si3).
  set (m3 := needbits 3 m) in *. clearbody m3.
  destruct (m_leave m3 =? 1) eqn:EL.
  { cbn [stepx_post]. apply (ikd_Kx_post wrap src pos out a0 m); auto.
    - rewrite Ss. reflexivity.
    - lia.
    - unfold ikd_pm. unfold m_mode in *. rewrite Ss. tauto. }
  destruct V3 as [(Lv & _ & _)|(Lv & Hn3)]; [apply Z.eqb_neq in EL; contradiction|].
  assert (U : u32 (u32 (m_bits m3 - 1) - 2) = m_bits m3 - 1 - 2)
    by (rewrite (ikd_u32 (m_bits m3 - 1)) by lia; apply ikd_u32; lia).
  assert (Bd : ik_bitbuf src (pos + m_nx m3) (Z.shiftr (Z.shiftr (m_hold m3) 1) 2) (m_bits m3 - 1 - 2)).
  { apply (kk_bb_drop KIT); [lia|]. apply (kk_bb_drop KIT); [lia|exact B3]. }
  destruct K3 as (Ko & Ka & Kw & Kt & Ktot & Kf).
  cbv zeta. clear EL.
  set (bt := bitsn (dropbits 1 (upd_s m3 (fun s => set_i_last s (bitsn m3 1)))) 2).
  destruct (bt =? 0); [|destruct (bt =? 1); [destruct (flush =? Z_TREES)|destruct (bt =? 2)]];
    cbn [stepx_post]; apply (ikd_Kx_post wrap src pos out a0 m); auto;
    unfold ikd_keep, ikd_pm; ikd_red; rewrite ?U; rewrite ?Ss, ?Ko, ?Ka, ?Kw, ?Kt, ?Ktot, ?Kf, ?Sad;
    try exact Bd; try (repeat split; reflexivity); ikd_cst; lia.
Qed.

Lemma ikd_type (KIT: ik_kit) wrap src pos out a0 inp flush m :
  ctx_ok src pos inp -> m_inp m = inp -> 0 <= m_nx m <= Zlength inp -> 0 <= m_bits m <= 31 ->
  m_leave m = 0 -> Kx wrap src pos out a0 m -> m_mode m = Zlib.proof.inflate.Model.TYPE ->
  stepx_post wrap src pos out a0 (c_TYPE flush m).
Proof.
  intros Hc Hi Hn Hb Hl X Hmd.
  unfold c_TYPE. destruct (orb _ _).
  - cbn [stepx_post]. pose proof (kx_buf _ _ _ _ _ _ X) as Bf.
    apply (ikd_Kx_post wrap src pos out a0 m); auto;
      unfold ikd_keep, ikd_pm; ikd_red; try exact Bf; try (repeat split; reflexivity); ikd_cst; lia.
  - apply (ikd_typedo KIT wrap src pos out a0 inp); auto.
Qed.

(* DICT with a dictionary: check = adler = 1, the Adler-32 of nothing *)
Lemma ikd_Kx_dict_post (KIT: ik_kit) wrap src pos out a0 m :
  Kx wrap src pos out a0 m -> m_mode m = DICT ->
  Kx wrap src pos out a0
    (set_mode (set_m_adler (upd_s m (fun s => set_i_check s 1)) 1) Zlib.proof.inflate.Model.TYPE).
Proof.
  intros X Hmd.
  assert (W : wrap <> 0).
  { intros W. destruct (kx_raw _ _ _ _ _ _ X W) as (_ & _ & D1 & D2). contradiction. }
  assert (PM : ik_pre_mode (m_mode m)) by ikd_md.
  destruct (kx_pre _ _ _ _ _ _ X W PM) as (O1 & O2 & O3).
  destruct (kx_zh _ _ _ _ _ _ X W (or_intror Hmd)) as (Z1 & Z2 & Z3 & Z4 & Z5).
  pose proof (kx_buf _ _ _ _ _ _ X) as Bf.
  assert (Pre : ik_pre out (set_mode (set_m_adler (upd_s m (fun s => set_i_check s 1)) 1)
                              Zlib.proof.inflate.Model.TYPE)).
  { unfold ik_pre. ikd_red. auto. }
  assert (Post : ik_post wrap src pos out (set_mode (set_m_adler (upd_s m (fun s => set_i_check s 1)) 1)
                              Zlib.proof.inflate.Model.TYPE)).
  { unfold ik_post. ikd_red. rewrite Z4, O1, O2, O3, Z.sub_diag, sublist_nil. cbn [app].
    split; [left; auto|]. split; [|reflexivity]. unfold ik_chk. cbn [negb Z.eqb].
    symmetry. exact (kk_adler_nil KIT). }
  constructor.
  - exact (kx_wrap _ _ _ _ _ _ X).
  - ikd_red. exact Bf.
  - ikd_red. split; intros; exfalso; ikd_cst; lia.
  - unfold m_left. ikd_red. exact (kx_out _ _ _ _ _ _ X).
  - ikd_red. exact (kx_total _ _ _ _ _ _ X).
  - ikd_red. exact (kx_tout _ _ _ _ _ _ X).
  - intros W'. contradiction.
  - intros _ _. exact Pre.
  - intros _ P. exfalso. revert P. ikd_red. ikd_md.
  - intros _ P. exfalso. revert P. ikd_red. ikd_md.
  - intros _ _. exact Post.
  - intros _ _. left. exact Pre.
  - intros _. unfold ik_trail. ikd_red. split; [|split]; intros E; exfalso; ikd_cst; lia.
Qed.

Lemma ikd_dict (KIT: ik_kit) wrap src pos out a0 inp flush m :
  ctx_ok src pos inp -> m_inp m = inp -> 0 <= m_nx m <= Zlength inp -> 0 <= m_bits m <= 31 ->
  m_leave m = 0 -> Kx wrap src pos out a0 m -> m_mode m = DICT ->
  stepx_post wrap src pos out a0 (c_DICT flush m).
Proof.
  intros Hc Hi Hn Hb Hl X Hmd.
  pose proof (kx_buf _ _ _ _ _ _ X) as Bf.
  unfold c_DICT. destruct (i_havedict (m_s m) =? 0).
  - cbn [stepx_post]. apply (ikd_Kx_pre wrap src pos out a0 m); auto;
      unfold ikd_keep; ikd_red; try exact Bf; try (repeat split; reflexivity); try lia; ikd_cst; lia.
  - apply (ikd_type KIT wrap src pos out a0 inp); try (ikd_red; auto; fail).
    + apply (ikd_Kx_dict_post KIT); auto.
Qed.

Lemma ikx_dict : dictx_stmt.
Proof.
  intros KIT wrap src pos out a0 inp aout flush m Hc K X Hw Hl Hmd. unfold md_dict in Hmd.
  pose proof (Inv.mw_nx _ (proj1 Hw)) as Hnx.
  pose proof (kc_inp _ _ _ _ _ _ K) as Hinp. subst inp.
  pose proof (kx_buf _ _ _ _ _ _ X) as Bf.
  assert (Hb : 0 <= m_bits m <= 31)
    by (apply (kc_bits _ _ _ _ _ _ K); destruct Hmd as [E|[E|[E|E]]]; rewrite E; ikd_cst; lia).
  destruct Hmd as [D|[D|[D|D]]].
  - rewrite ikd_step_DICTID by exact D. unfold c_DICTID.
    pose proof (kk_needbits KIT src pos (m_inp m) 32 m Hc eq_refl Hnx ltac:(lia) ltac:(lia) Bf) as NB.
    cbv zeta in NB. destruct NB as (B2 & S2 & N2 & D2 & L2 & E2 & V2).
    destruct (ikd_same _ _ S2) as (K2 & Ss & Sad & Si2).
    set (m2 := needbits 32 m) in *. clearbody m2.
    destruct (m_leave m2 =? 1) eqn:EL.
    { cbn [stepx_post]. apply (ikd_Kx_pre wrap src pos out a0 m); auto.
      - left. unfold m_mode. rewrite Ss. exact D.
      - lia. }
    destruct V2 as [(Lv & _ & _)|(Lv & Hn2)]; [apply Z.eqb_neq in EL; contradiction|].
    pose proof Hc as (Hpos & Hsrc & Hbytes & _).
    destruct K2 as (Ko & Ka & Kw & Kt & Ktot & Kf).
    cbv zeta.
    apply (ikd_dict KIT wrap src pos out a0 (m_inp m)); auto; ikd_red; try rewrite Si2; auto; try lia.
    apply (ikd_Kx_pre wrap src pos out a0 m); auto;
      unfold ikd_keep; ikd_red; rewrite ?Ss, ?Ko, ?Ka, ?Kw, ?Kt, ?Ktot, ?Kf;
      try (repeat split; reflexivity); try lia.
    apply (kk_bb_init KIT); auto. lia.
  - rewrite ikd_step_DICT by exact D. apply (ikd_dict KIT wrap src pos out a0 (m_inp m)); auto.
  - rewrite ikd_step_TYPE by exact D. apply (ikd_type KIT wrap src pos out a0 (m_inp m)); auto.
  - rewrite ikd_step_TYPEDO by exact D. apply (ikd_typedo KIT wrap src pos out a0 (m_inp m)); auto.
Qed.
