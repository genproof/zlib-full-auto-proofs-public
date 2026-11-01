(* Law inflate_check, theory part: cases STORED, COPY_, COPY, CHECK, LENGTH, DONE, BAD, MEM keep Kx (gzip
   CHECK needs bytes_ok out for the CRC-32 continuation: groupx_okb). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_check.IKTheoryDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* Generic facts                                                                                  *)

Ltac ikb_cst := unfold HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT,
  Zlib.proof.inflate.Model.TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS, LEN_, LEN, LENEXT,
  DIST, DISTEXT, MATCH, LIT, CHECK, LENGTH, DONE, BAD, MEM, SYNC in *.

Ltac ikb_md := unfold ik_pre_mode, ik_gzhdr_mode, ik_post_mode, decode_mode in *; ikb_cst; lia.

Ltac ikb_red := unfold m_mode, m_left, set_bad, set_mode, set_leave, upd_s, bytebits, initbits in *;
  cbn [m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler m_msg m_tin m_tout
       m_snx m_sow set_m_s set_m_h set_m_nx set_m_hold set_m_bits set_m_msg set_m_adler set_m_tin
       set_m_leave set_m_snx set_m_sow set_m_ret set_m_out set_m_tout set_m_ow
       i_mode i_flags i_total i_check i_wrap i_length
       set_i_mode set_i_check set_i_total set_i_length] in *.

(* the modes this group reaches *)
Definition ikb_md (md: Z) : Prop :=
  md = STORED \/ md = COPY_ \/ md = COPY \/ md = CHECK \/ md = LENGTH \/ md = DONE \/ md = BAD \/
  md = Zlib.proof.inflate.Model.TYPE.

Ltac ikb_close := try (unfold ikb_md, m_left, m_mode in *; intros; ikb_cst; lia).


Lemma ikb_Kx wrap src pos out a0 m m' :
  Kx wrap src pos out a0 m -> ikb_md (m_mode m') ->
  ik_bitbuf src (pos + m_nx m') (m_hold m') (m_bits m') ->
  (m_mode m' = COPY_ \/ m_mode m' = COPY -> m_bits m' = 0) ->
  (m_out m' = m_aout m' \/ m_out m' = m_left m') ->
  i_total (m_s m') = (Zlength out + (m_aout m' - m_out m')) mod 2 ^ 64 ->
  m_tout m' = (Zlength out + (m_aout m' - m_out m')) mod 2 ^ 64 ->
  (wrap = 0 -> m_adler m' = m_adler m) ->
  (wrap <> 0 -> ik_post wrap src pos out m') ->
  (wrap <> 0 -> ik_trail src pos m') ->
  Kx wrap src pos out a0 m'.
Proof.
  intros X Hmd Hb H0 Ho Htot Ht Had Hpost Htr. unfold ikb_md in Hmd.
  constructor.
  - exact (kx_wrap _ _ _ _ _ _ X).
  - exact Hb.
  - split; [intros E; apply H0; ikb_md|intros E; exfalso; ikb_md].
  - exact Ho.
  - exact Htot.
  - exact Ht.
  - intros W. destruct (kx_raw _ _ _ _ _ _ X W) as (A & _). split; [rewrite Had; auto|]. ikb_md.
  - intros _ P. exfalso. ikb_md.
  - intros _ P. exfalso. ikb_md.
  - intros _ P. exfalso. ikb_md.
  - intros W P. apply Hpost; auto.
  - intros W P. right. apply Hpost; auto.
  - exact Htr.
Qed.

Lemma ikb_post_tr wrap src pos out m m' :
  ik_post wrap src pos out m ->
  i_flags (m_s m') = i_flags (m_s m) -> i_check (m_s m') = i_check (m_s m) -> m_adler m' = m_adler m ->
  sublist 0 (m_aout m' - m_out m') (m_ow m') = sublist 0 (m_aout m - m_out m) (m_ow m) ->
  8 * (pos + m_nx m) - m_bits m <= 8 * (pos + m_nx m') - m_bits m' ->
  ik_post wrap src pos out m'.
Proof.
  intros P Hf Hc Ha Hs Hg. unfold ik_post in *. rewrite Hf, Hc, Ha, Hs.
  destruct P as [P1 [P2 P3]]. split; [|split; auto]. destruct P1 as [P1|P1]; [left|right]; intuition lia.
Qed.

(* the trail outside CHECK / LENGTH / DONE *)
Lemma ikb_trail_other src pos m :
  m_mode m <> CHECK -> m_mode m <> LENGTH -> m_mode m <> DONE -> ik_trail src pos m.
Proof. intros A B C. unfold ik_trail. split; [|split]; intros E; contradiction. Qed.

Ltac ikb_rw := repeat match goal with
  | H: m_s ?a = m_s ?b |- context [m_s ?a] => rewrite H
  | H: m_aout ?a = m_aout ?b |- context [m_aout ?a] => rewrite H
  | H: m_ow ?a = m_ow ?b |- context [m_ow ?a] => rewrite H
  | H: m_out ?a = m_out ?b |- context [m_out ?a] => rewrite H
  | H: m_adler ?a = m_adler ?b |- context [m_adler ?a] => rewrite H
  | H: m_tout ?a = m_tout ?b |- context [m_tout ?a] => rewrite H
  end.

Ltac ikb_post_trail wrap src pos out m :=
  try (intros _; apply ikb_trail_other; ikb_red; ikb_rw; ikb_cst; lia);
  try (intros ?W; apply (ikb_post_tr wrap src pos out m); ikb_red; ikb_rw; auto;
       try (replace (m_aout m - m_out m) with 0 by lia; rewrite !sublist_nil; reflexivity); lia).

Lemma ikb_u32 x : 0 <= x < 2 ^ 32 -> u32 x = x.
Proof. intros. unfold u32. apply Z.mod_small. lia. Qed.

Lemma ikb_adler_upd l d : adler32_z_val (ref_adler32 1 l) d = ref_adler32 1 (l ++ d).
Proof.
  assert (V : adler_valid 1) by (unfold adler_valid, adler_lo, adler_hi, ADLER_BASE; split; [lia|]; split; reflexivity).
  rewrite adler32_z_val_ref by (apply ref_adler32_valid, V).
  apply ref_adler32_app, V.
Qed.

Lemma ikb_same m m' : ik_same_but_buf m m' ->
  m_s m' = m_s m /\ m_inp m' = m_inp m /\ m_aout m' = m_aout m /\ m_ow m' = m_ow m /\ m_out m' = m_out m /\
  m_adler m' = m_adler m /\ m_tout m' = m_tout m /\ m_ret m' = m_ret m.
Proof.
  intros (Ss & _ & Si & Sa & So & _ & Sout & Sr & Sad & _ & _ & St & _). repeat split; auto.
Qed.

(* leave / ret do not matter *)
Lemma ikb_Kx_lr wrap src pos out a0 m r :
  Kx wrap src pos out a0 m -> Kx wrap src pos out a0 (set_leave (set_m_ret m r)).
Proof.
  intros X. destruct X. constructor; ikb_red; auto.
Qed.

Lemma ikb_Kx_l wrap src pos out a0 m :
  Kx wrap src pos out a0 m -> Kx wrap src pos out a0 (set_leave m).
Proof. intros X. destruct X. constructor; ikb_red; auto. Qed.

Lemma ikb_done wrap src pos out a0 m :
  Kx wrap src pos out a0 m -> stepx_post wrap src pos out a0 (c_DONE m).
Proof. intros X. unfold c_DONE. cbn [stepx_post]. apply ikb_Kx_lr. exact X. Qed.

Lemma ikb_bad wrap src pos out a0 m :
  Kx wrap src pos out a0 m -> stepx_post wrap src pos out a0 (c_BAD m).
Proof. intros X. unfold c_BAD. cbn [stepx_post]. apply ikb_Kx_lr. exact X. Qed.

(* pulling whole bytes keeps bits a multiple of 8 and the position of the bit buffer's first byte *)
Lemma ikb_q P b b2 d : b mod 8 = 0 -> b2 - b = 8 * d ->
  b2 mod 8 = 0 /\ (P + d) - b2 / 8 = P - b / 8.
Proof.
  intros H E. assert (b = 8 * (b / 8)) by (pose proof (Z.div_mod b 8); lia).
  assert (E2 : b2 = 8 * (b / 8 + d)) by lia.
  rewrite E2, (Z.mul_comm 8), Z.div_mul, Z_mod_mult by lia. split; lia.
Qed.

Lemma ikb_wrap4 wrap : wrap = 0 \/ wrap = 5 \/ wrap = 6 \/ wrap = 7 \/ wrap = 13 \/ wrap = 14 \/ wrap = 15 ->
  wrap <> 0 -> Z.land wrap 4 =? 0 = false.
Proof. intros [E|[E|[E|[E|[E|[E|E]]]]]] W; subst; try reflexivity; contradiction. Qed.

Lemma ikb_length (KIT: ik_kit) wrap src pos out a0 inp m :
  ctx_ok src pos inp -> m_inp m = inp -> 0 <= m_nx m <= Zlength inp -> 0 <= m_bits m <= 31 ->
  i_wrap (m_s m) = wrap -> Kx wrap src pos out a0 m -> m_mode m = LENGTH ->
  stepx_post wrap src pos out a0 (c_LENGTH m).
Proof.
  intros Hc Hi Hn Hb Hw X Hmd.
  pose proof Hc as (Hpos & Hsrc & Hbytes & _).
  pose proof (kx_buf _ _ _ _ _ _ X) as Bf.
  pose proof Hmd as Hmd'. unfold m_mode in Hmd'.
  unfold c_LENGTH. cbv zeta. rewrite Hw.
  destruct ((negb (wrap =? 0) && negb (i_flags (m_s m) =? 0))%bool) eqn:C.
  - apply andb_true_iff in C. destruct C as [W F]. apply negb_true_iff, Z.eqb_neq in W, F.
    destruct (kx_trail _ _ _ _ _ _ X W) as (_ & TL & _). destruct (TL Hmd) as (Eo & Bm & _ & TG).
    destruct (TG F) as (Q14 & Qle). clear TL TG.
    assert (Po : ik_post wrap src pos out m) by (apply (kx_post _ _ _ _ _ _ X W); ikb_md).
    pose proof (kk_needbits KIT src pos inp 32 m Hc Hi Hn ltac:(lia) ltac:(lia) Bf) as NB. cbv zeta in NB.
    destruct NB as (B2 & S2 & N2 & D2 & L2 & E2 & V2).
    destruct (ikb_same _ _ S2) as (Ss & Si & Sa & So & Sout & Sad & St & Sr).
    set (m2 := needbits 32 m) in *. clearbody m2.
    destruct (ikb_q (pos + m_nx m) _ _ (m_nx m2 - m_nx m) Bm D2) as [Bm2 Q2].
    assert (QQ : pos + m_nx m2 - m_bits m2 / 8 = pos + m_nx m - m_bits m / 8) by lia.
    pose proof (kx_out _ _ _ _ _ _ X) as Ko. pose proof (kx_total _ _ _ _ _ _ X) as Kt.
    pose proof (kx_tout _ _ _ _ _ _ X) as Ktt.
    destruct (m_leave m2 =? 1) eqn:EL.
    { cbn [stepx_post]. apply (ikb_Kx wrap src pos out a0 m); auto; unfold ikb_md, m_left, m_mode;
        rewrite ?Ss, ?Sa, ?So, ?Sout, ?Sad, ?St; ikb_close.
      - intros _. apply (ikb_post_tr wrap src pos out m); auto; rewrite ?Ss, ?Sa, ?So, ?Sout, ?Sad; auto; lia.
      - intros _. unfold ik_trail, m_mode, m_left. rewrite Ss, Sa, So, Sout, QQ.
        split; [|split]; intros E; try (exfalso; ikb_cst; lia).
        split; [exact Eo|]. split; [exact Bm2|]. split; intros; [contradiction|auto]. }
    destruct V2 as [(Lv & _ & _)|(Lv & Hn2)]; [apply Z.eqb_neq in EL; contradiction|].
    assert (B32 : m_bits m2 = 32) by (specialize (L2 ltac:(lia)); pose proof (Z.div_mod (m_bits m2) 8); lia).
    assert (HP : 0 <= pos + m_nx m2 <= Zlength src) by lia.
    assert (H4 : m_hold m2 = le_val (sublist (pos + m_nx m2 - 4) (pos + m_nx m2) src)).
    { apply (kk_bb_bytes KIT); auto; try lia. replace (8 * 4) with (m_bits m2) by lia. exact B2. }
    rewrite B32 in QQ. change (32 / 8) with 4 in QQ.
    assert (L4 : Zlength (sublist (pos + m_nx m2 - 4) (pos + m_nx m2) src) = 4)
      by (rewrite Zlength_sublist; lia).
    rewrite (kk_le32 KIT _ L4) in H4.
    rewrite Ss, Hw, (ikb_wrap4 wrap (kx_wrap _ _ _ _ _ _ X) W). cbn [negb andb].
    destruct (m_hold m2 =? i_total (m_s m) mod 2 ^ 32) eqn:EH; cbn [negb].
    + apply ikb_done. apply (ikb_Kx wrap src pos out a0 m); ikb_red; rewrite ?Ss, ?Sa, ?So, ?Sout, ?Sad, ?St;
        auto; ikb_close.
      * apply (kk_bb_init KIT); auto.
      * intros _. apply (ikb_post_tr wrap src pos out m); ikb_red; rewrite ?Ss, ?Sa, ?So, ?Sout, ?Sad; auto; lia.
      * intros _. unfold ik_trail. ikb_red. rewrite ?Ss, ?Sa, ?So, ?Sout.
        split; [|split]; intros E; try (exfalso; ikb_cst; lia).
        split; [exact Eo|]. split; [reflexivity|]. split; intros; [contradiction|].
        apply Z.eqb_eq in EH. rewrite <- H4, EH.
        replace (pos + m_nx m2 - 8) with (pos + m_nx m - m_bits m / 8 - 4) by lia.
        replace (pos + m_nx m2 - 4) with (pos + m_nx m - m_bits m / 8) by lia.
        split; [lia|]. split; [exact Qle|]. reflexivity.
    + cbn [stepx_post]. apply (ikb_Kx wrap src pos out a0 m); ikb_red; rewrite ?Ss, ?Sa, ?So, ?Sout, ?Sad, ?St;
        auto; ikb_close.
      * intros _. apply (ikb_post_tr wrap src pos out m); ikb_red; rewrite ?Ss, ?Sa, ?So, ?Sout, ?Sad; auto; lia.
      * intros _. apply ikb_trail_other; ikb_red; ikb_cst; lia.
  - apply ikb_done. pose proof (kx_out _ _ _ _ _ _ X) as Ko. pose proof (kx_total _ _ _ _ _ _ X) as Kt.
    pose proof (kx_tout _ _ _ _ _ _ X) as Ktt.
    apply (ikb_Kx wrap src pos out a0 m); ikb_red; auto; ikb_close.
    + intros W. apply (ikb_post_tr wrap src pos out m); ikb_red; auto; try lia.
      apply (kx_post _ _ _ _ _ _ X W). unfold m_mode in *. ikb_md.
    + intros W. destruct (kx_trail _ _ _ _ _ _ X W) as (_ & TL & _). destruct (TL Hmd) as (Eo & Bm & TZ & _).
      assert (F : i_flags (m_s m) = 0).
      { apply andb_false_iff in C. destruct C as [C|C]; apply negb_false_iff, Z.eqb_eq in C; [contradiction|exact C]. }
      destruct (TZ F) as (B0 & Q6 & Qbe). rewrite B0 in Q6, Qbe. change (0 / 8) with 0 in Q6, Qbe.
      rewrite Z.sub_0_r in Q6, Qbe.
      unfold ik_trail. ikb_red. split; [|split]; intros E; try (exfalso; ikb_cst; lia).
      split; [exact Eo|]. split; [exact B0|]. split; intros; [split; auto|contradiction].
Qed.

(* CHECK after NEEDBITS(32) succeeded and the output was counted: the comparison *)
Lemma ikb_check_tail (KIT: ik_kit) wrap src pos out a0 inp m m3 :
  ctx_ok src pos inp -> Kx wrap src pos out a0 m -> wrap <> 0 -> m_mode m = CHECK ->
  m_inp m3 = inp -> 0 <= m_nx m3 <= Zlength inp -> m_bits m3 = 32 ->
  ik_bitbuf src (pos + m_nx m3) (m_hold m3) (m_bits m3) ->
  m_hold m3 = le_val (sublist (pos + m_nx m3 - 4) (pos + m_nx m3) src) ->
  8 * (pos + m_nx m3) - 32 = 8 * (pos + m_nx m) - m_bits m ->
  i_mode (m_s m3) = CHECK -> i_flags (m_s m3) = i_flags (m_s m) -> i_wrap (m_s m3) = wrap ->
  i_check (m_s m3) = ik_chk (negb (i_flags (m_s m) =? 0)) (out ++ m_ow m3) -> m_adler m3 = i_check (m_s m3) ->
  m_out m3 = m_left m3 ->
  i_total (m_s m3) = (Zlength out + Zlength (m_ow m3)) mod 2 ^ 64 ->
  m_tout m3 = (Zlength out + Zlength (m_ow m3)) mod 2 ^ 64 ->
  stepx_post wrap src pos out a0
    (if (negb (Z.land (i_wrap (m_s m3)) 4 =? 0) &&
         negb ((if i_flags (m_s m3) =? 0 then swap32 (m_hold m3) else m_hold m3) =? i_check (m_s m3)))%bool
     then IBrk (set_bad m3 M_dcheck)
     else c_LENGTH (set_mode (initbits m3) LENGTH)).
Proof.
  intros Hc X W Hmd Hi3 Hn3 B32 B3 H4 HP Hmd3 Hf3 Hw3 Hck3 Had3 Ho3 Ht3 Htt3.
  pose proof Hc as (Hpos & Hsrc & Hbytes & _).
  assert (Po : ik_post wrap src pos out m) by (apply (kx_post _ _ _ _ _ _ X W); ikb_md).
  assert (Sow : sublist 0 (m_aout m3 - m_out m3) (m_ow m3) = m_ow m3).
  { rewrite Ho3. unfold m_left. replace (m_aout m3 - (m_aout m3 - Zlength (m_ow m3))) with (Zlength (m_ow m3)) by lia.
    apply sublist_same; lia. }
  assert (HL : 0 <= pos + m_nx m3 <= Zlength src) by lia.
  assert (L4 : Zlength (sublist (pos + m_nx m3 - 4) (pos + m_nx m3) src) = 4).
  { rewrite Zlength_sublist; [lia| |lia]. destruct Po as [[P1|P1] _]; lia. }
  assert (B4 : bytes_ok (sublist (pos + m_nx m3 - 4) (pos + m_nx m3) src)) by (apply Forall_sublist; exact Hbytes).
  (* the post facts of the machines after the comparison *)
  assert (Post : forall m', m_s m' = set_i_mode (m_s m3) (i_mode (m_s m')) -> m_adler m' = m_adler m3 ->
            m_nx m' = m_nx m3 -> m_aout m' = m_aout m3 -> m_out m' = m_out m3 -> m_ow m' = m_ow m3 ->
            0 <= m_bits m' <= 32 -> ik_post wrap src pos out m').
  { intros m' E1 E2 E3 E4 E5 E6 E7. unfold ik_post. rewrite E1, E2, E3, E4, E5, E6. cbn [i_flags i_check set_i_mode].
    rewrite Sow, Hf3, <- Hck3, Had3. split; [|split; reflexivity].
    destruct Po as [[P1|P1] _]; [left|right]; intuition lia. }
  rewrite Hw3, (ikb_wrap4 wrap (kx_wrap _ _ _ _ _ _ X) W). cbn [negb andb].
  destruct ((if i_flags (m_s m3) =? 0 then swap32 (m_hold m3) else m_hold m3) =? i_check (m_s m3)) eqn:EC;
    cbn [negb].
  - apply Z.eqb_eq in EC.
    apply (ikb_length KIT wrap src pos out a0 inp); ikb_red; auto; try lia.
    apply (ikb_Kx wrap src pos out a0 m); ikb_red; auto; ikb_close.
    + apply (kk_bb_init KIT); auto.
    + rewrite Ht3. f_equal. lia.
    + rewrite Htt3. f_equal. lia.
    + intros _. apply Post; ikb_red; auto; lia.
    + intros _. unfold ik_trail. ikb_red. split; [|split]; intros E; try (exfalso; ikb_cst; lia).
      split; [exact Ho3|]. split; [reflexivity|]. change (0 / 8) with 0. rewrite Z.sub_0_r.
      rewrite Hf3 in EC. split; intros F.
      * rewrite Hf3 in F. rewrite F in EC. cbn in EC. rewrite H4, (kk_swap32 KIT _ B4 L4) in EC.
        split; [reflexivity|]. split; [|exact EC].
        destruct Po as [[P1|P1] _]; [lia|]. exfalso. destruct P1 as [P1 _]. rewrite F in P1. discriminate.
      * rewrite Hf3 in F. apply Z.eqb_neq in F. rewrite F in EC. rewrite H4, (kk_le32 KIT _ L4) in EC.
        split; [|exact EC].
        destruct Po as [[P1|P1] _]; [|lia]. exfalso. destruct P1 as [P1 _]. apply Z.eqb_neq in F. contradiction.
  - cbn [stepx_post]. apply (ikb_Kx wrap src pos out a0 m); ikb_red; auto; ikb_close.
    + rewrite Ht3. f_equal. lia.
    + rewrite Htt3. f_equal. lia.
    + intros _. apply Post; ikb_red; auto; lia.
    + intros _. apply ikb_trail_other; ikb_red; ikb_cst; lia.
Qed.

Lemma ikb_check (KIT: ik_kit) wrap src pos out a0 inp m :
  ctx_ok src pos inp -> m_inp m = inp -> 0 <= m_nx m <= Zlength inp -> 0 <= m_bits m <= 31 ->
  i_wrap (m_s m) = wrap -> Kx wrap src pos out a0 m -> m_mode m = CHECK -> m_out m = m_aout m ->
  Zlength (m_ow m) <= m_aout m <= Int.max_signed -> bytes_ok (m_ow m) -> bytes_ok out ->
  stepx_post wrap src pos out a0 (c_CHECK m).
Proof.
  intros Hc Hi Hn Hb Hw X Hmd Hout Hab Hob Houtb.
  pose proof Hc as (Hpos & Hsrc & Hbytes & _).
  pose proof (kx_buf _ _ _ _ _ _ X) as Bf.
  pose proof Hmd as Hmd'. unfold m_mode in Hmd'.
  pose proof (kx_total _ _ _ _ _ _ X) as Kt0. pose proof (kx_tout _ _ _ _ _ _ X) as Ktt0.
  pose proof (kx_out _ _ _ _ _ _ X) as Ko.
  pose proof Kt0 as Kt. pose proof Ktt0 as Ktt.
  rewrite Hout, Z.sub_diag, Z.add_0_r in Kt, Ktt.
  unfold c_CHECK. rewrite Hw.
  destruct (negb (wrap =? 0)) eqn:W0.
  2:{ apply negb_false_iff, Z.eqb_eq in W0.
      apply (ikb_length KIT wrap src pos out a0 inp); ikb_red; auto.
      apply (ikb_Kx wrap src pos out a0 m); ikb_red; auto; ikb_close. }
  apply negb_true_iff, Z.eqb_neq in W0. rename W0 into W.
  destruct (kx_trail _ _ _ _ _ _ X W) as (TC & _ & _). specialize (TC Hmd) as Bm.
  assert (Po : ik_post wrap src pos out m) by (apply (kx_post _ _ _ _ _ _ X W); ikb_md).
  pose proof (kk_needbits KIT src pos inp 32 m Hc Hi Hn ltac:(lia) ltac:(lia) Bf) as NB. cbv zeta in NB.
  destruct NB as (B2 & S2 & N2 & D2 & L2 & E2 & V2).
  destruct (ikb_same _ _ S2) as (Ss & Si & Sa & So & Sout & Sad & St & Sr).
  set (m2 := needbits 32 m) in *. clearbody m2.
  destruct (ikb_q (pos + m_nx m) _ _ (m_nx m2 - m_nx m) Bm D2) as [Bm2 Q2].
  assert (QQ : pos + m_nx m2 - m_bits m2 / 8 = pos + m_nx m - m_bits m / 8) by lia.
  destruct (m_leave m2 =? 1) eqn:EL.
  { cbn [stepx_post]. apply (ikb_Kx wrap src pos out a0 m); auto; unfold m_left, m_mode;
      rewrite ?Ss, ?Sa, ?So, ?Sout, ?Sad, ?St; ikb_close.
    - intros _. apply (ikb_post_tr wrap src pos out m); auto; rewrite ?Ss, ?Sa, ?So, ?Sout, ?Sad; auto; lia.
    - intros _. unfold ik_trail, m_mode. rewrite Ss.
      split; [|split]; intros E; try (exfalso; ikb_cst; lia). exact Bm2. }
  destruct V2 as [(Lv & _ & _)|(Lv & Hn2)]; [apply Z.eqb_neq in EL; contradiction|].
  assert (B32 : m_bits m2 = 32) by (specialize (L2 ltac:(lia)); pose proof (Z.div_mod (m_bits m2) 8); lia).
  assert (HP : 0 <= pos + m_nx m2 <= Zlength src) by lia.
  assert (H4 : m_hold m2 = le_val (sublist (pos + m_nx m2 - 4) (pos + m_nx m2) src)).
  { apply (kk_bb_bytes KIT); auto; try lia. replace (8 * 4) with (m_bits m2) by lia. exact B2. }
  rewrite B32 in QQ. change (32 / 8) with 4 in QQ.
  assert (QP : 16 <= 8 * (pos + m_nx m) - m_bits m) by (destruct Po as [[P1|P1] _]; lia).
  assert (QP' : 2 <= pos + m_nx m - m_bits m / 8) by (pose proof (Z.div_mod (m_bits m) 8); lia).
  assert (L4 : Zlength (sublist (pos + m_nx m2 - 4) (pos + m_nx m2) src) = 4)
    by (rewrite Zlength_sublist; lia).
  assert (EO : u32 (m_out m2 - m_left m2) = Zlength (m_ow m))
    by (unfold m_left; rewrite Sout, Sa, So, Hout;
        replace (m_aout m - (m_aout m - Zlength (m_ow m))) with (Zlength (m_ow m)) by lia;
        apply ikb_u32; pose proof (Zlength_nonneg (m_ow m)); rep_lia).
  assert (Ck : i_check (m_s m) = ik_chk (negb (i_flags (m_s m) =? 0)) out /\ m_adler m = i_check (m_s m)).
  { destruct Po as [_ [P2 P3]]. rewrite Hout, Z.sub_diag, sublist_nil, app_nil_r in P2. auto. }
  destruct Ck as [Ck Ad].
  cbv zeta. set (m3 := set_m_out _ _).
  assert (F3 : m_inp m3 = m_inp m /\ m_nx m3 = m_nx m2 /\ m_hold m3 = m_hold m2 /\ m_bits m3 = m_bits m2 /\
               m_ow m3 = m_ow m /\ i_mode (m_s m3) = CHECK /\ i_flags (m_s m3) = i_flags (m_s m) /\
               i_wrap (m_s m3) = wrap /\
               i_check (m_s m3) = ik_chk (negb (i_flags (m_s m) =? 0)) (out ++ m_ow m) /\
               m_adler m3 = i_check (m_s m3) /\ m_out m3 = m_left m3 /\
               i_total (m_s m3) = (Zlength out + Zlength (m_ow m)) mod 2 ^ 64 /\
               m_tout m3 = (Zlength out + Zlength (m_ow m)) mod 2 ^ 64).
  { assert (U : u64 (Zlength out mod 2 ^ 64 + Zlength (m_ow m)) = (Zlength out + Zlength (m_ow m)) mod 2 ^ 64)
      by (unfold u64; apply Zplus_mod_idemp_l).
    unfold m3. rewrite EO. ikb_red. rewrite ?Ss, ?Si, ?Sa, ?So, ?Sout, ?Sad, ?St, Hw, Kt, Ktt,
      (ikb_wrap4 wrap (kx_wrap _ _ _ _ _ _ X) W).
    destruct (Zlength (m_ow m) =? 0) eqn:E0; cbn [negb andb]; ikb_red; rewrite ?Ss, ?Si, ?Sa, ?So, ?Sout, ?Sad, ?St.
    - apply Z.eqb_eq, Zlength_nil_inv in E0. rewrite E0, app_nil_r. rewrite E0 in U.
      repeat split; auto; congruence.
    - rewrite Z.sub_diag, sublist_same by lia. rewrite Ck.
      assert (UC : update_check (i_flags (m_s m)) (ik_chk (negb (i_flags (m_s m) =? 0)) out) (m_ow m) =
                   ik_chk (negb (i_flags (m_s m) =? 0)) (out ++ m_ow m)).
      { unfold update_check, ik_chk. destruct (i_flags (m_s m) =? 0); cbn [negb].
        - apply ikb_adler_upd.
        - apply (kk_crc_upd KIT); auto. }
      rewrite UC. repeat split; auto. }
  destruct F3 as (F1 & F2 & F3' & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13).
  apply (ikb_check_tail KIT wrap src pos out a0 inp m m3); auto; rewrite ?F1, ?F2, ?F3', ?F4, ?F5; auto; try lia.
Qed.

Lemma ikb_copy (KIT: ik_kit) wrap src pos out a0 inp m :
  ctx_ok src pos inp -> m_inp m = inp -> 0 <= m_nx m <= Zlength inp -> Kx wrap src pos out a0 m ->
  m_mode m = COPY -> m_out m = m_aout m -> Zlength (m_ow m) <= m_aout m -> 0 <= i_length (m_s m) ->
  stepx_post wrap src pos out a0 (c_COPY m).
Proof.
  intros Hc Hi Hn X Hmd Hout Hab Hlen. subst inp.
  pose proof Hc as (Hpos & Hsrc & Hbytes & _).
  pose proof (kx_buf _ _ _ _ _ _ X) as Bf.
  pose proof (kx_total _ _ _ _ _ _ X) as Kt0. pose proof (kx_tout _ _ _ _ _ _ X) as Ktt0.
  pose proof (kx_out _ _ _ _ _ _ X) as Ko.
  assert (B0 : m_bits m = 0) by (apply (proj1 (kx_bits0 _ _ _ _ _ _ X)); auto).
  assert (H0 : m_hold m = 0).
  { pose proof (kk_bb_range KIT src (pos + m_nx m) (m_hold m) (m_bits m) Hbytes ltac:(lia) Bf) as R.
    rewrite B0 in R. change (2 ^ 0) with 1 in R. lia. }
  pose proof Hmd as Hmd'. unfold m_mode in Hmd'.
  assert (Po : wrap <> 0 -> ik_post wrap src pos out m) by (intros W; apply (kx_post _ _ _ _ _ _ X W); ikb_md).
  unfold c_COPY. cbv zeta.
  destruct (negb (i_length (m_s m) =? 0)).
  - set (cp := Z.min (Z.min (i_length (m_s m)) (m_have m)) (m_left m)).
    assert (Cp : 0 <= cp <= m_have m).
    { unfold cp, m_have, m_left. pose proof (Z.le_min_l (Z.min (i_length (m_s m)) (Zlength (m_inp m) - m_nx m))
        (m_aout m - Zlength (m_ow m))). pose proof (Z.le_min_l (i_length (m_s m)) (Zlength (m_inp m) - m_nx m)).
      pose proof (Z.le_min_r (i_length (m_s m)) (Zlength (m_inp m) - m_nx m)).
      split; [|lia]. apply Z.min_glb; [apply Z.min_glb|]; lia. }
    unfold m_have in Cp. clearbody cp.
    destruct (cp =? 0); cbn [stepx_post]; apply (ikb_Kx wrap src pos out a0 m); ikb_red; auto; ikb_close;
      ikb_post_trail wrap src pos out m.
    rewrite H0, B0. apply (kk_bb_init KIT); auto; lia.
  - cbn [stepx_post]. apply (ikb_Kx wrap src pos out a0 m); ikb_red; auto; ikb_close;
      ikb_post_trail wrap src pos out m.
Qed.

Lemma ikb_copy_ (KIT: ik_kit) wrap src pos out a0 inp m :
  ctx_ok src pos inp -> m_inp m = inp -> 0 <= m_nx m <= Zlength inp -> Kx wrap src pos out a0 m ->
  m_mode m = COPY_ -> m_out m = m_aout m -> Zlength (m_ow m) <= m_aout m -> 0 <= i_length (m_s m) ->
  stepx_post wrap src pos out a0 (c_COPY_ m).
Proof.
  intros Hc Hi Hn X Hmd Hout Hab Hlen.
  pose proof (kx_buf _ _ _ _ _ _ X) as Bf.
  pose proof (kx_total _ _ _ _ _ _ X) as Kt0. pose proof (kx_tout _ _ _ _ _ _ X) as Ktt0.
  pose proof (kx_out _ _ _ _ _ _ X) as Ko.
  assert (B0 : m_bits m = 0) by (apply (proj1 (kx_bits0 _ _ _ _ _ _ X)); auto).
  pose proof Hmd as Hmd'. unfold m_mode in Hmd'.
  assert (Po : wrap <> 0 -> ik_post wrap src pos out m) by (intros W; apply (kx_post _ _ _ _ _ _ X W); ikb_md).
  unfold c_COPY_. apply (ikb_copy KIT wrap src pos out a0 inp); ikb_red; auto.
  apply (ikb_Kx wrap src pos out a0 m); ikb_red; auto; ikb_close; ikb_post_trail wrap src pos out m.
Qed.

Lemma ikb_stored (KIT: ik_kit) wrap src pos out a0 inp flush m :
  ctx_ok src pos inp -> m_inp m = inp -> 0 <= m_nx m <= Zlength inp -> 0 <= m_bits m <= 31 ->
  Kx wrap src pos out a0 m -> m_mode m = STORED -> m_out m = m_aout m -> Zlength (m_ow m) <= m_aout m ->
  stepx_post wrap src pos out a0 (c_STORED flush m).
Proof.
  intros Hc Hi Hn Hb X Hmd Hout Hab.
  pose proof Hc as (Hpos & Hsrc & Hbytes & _).
  pose proof (kx_buf _ _ _ _ _ _ X) as Bf.
  pose proof (kx_total _ _ _ _ _ _ X) as Kt0. pose proof (kx_tout _ _ _ _ _ _ X) as Ktt0.
  pose proof (kx_out _ _ _ _ _ _ X) as Ko.
  pose proof Hmd as Hmd'. unfold m_mode in Hmd'.
  assert (Po : wrap <> 0 -> ik_post wrap src pos out m) by (intros W; apply (kx_post _ _ _ _ _ _ X W); ikb_md).
  pose proof (kk_bb_bytebits KIT _ _ _ _ Bf) as Bb.
  assert (M8 : 0 <= m_bits m mod 8 < 8) by (apply Z.mod_pos_bound; lia).
  assert (M8le : m_bits m mod 8 <= m_bits m) by (apply Z.mod_le; lia).
  assert (Bb2 : 0 <= m_bits (bytebits m) <= 32) by (cbn [bytebits m_bits set_m_bits set_m_hold]; lia).
  assert (N32 : 0 <= 32 <= 32) by lia.
  pose proof (kk_needbits KIT src pos inp 32 (bytebits m) Hc Hi Hn N32 Bb2 Bb) as NB.
  cbv zeta in NB. destruct NB as (B2 & S2 & N2 & D2 & L2 & E2 & V2).
  destruct (ikb_same _ _ S2) as (Ss & Si & Sa & So & Sout & Sad & St & Sr).
  unfold c_STORED. cbv zeta.
  set (m2 := needbits 32 (bytebits m)) in *. clearbody m2.
  cbn [bytebits m_bits m_nx m_s m_inp m_aout m_ow m_out m_adler m_tout m_ret set_m_bits set_m_hold] in *.
  destruct (m_leave m2 =? 1) eqn:EL.
  { cbn [stepx_post]. apply (ikb_Kx wrap src pos out a0 m); auto; unfold m_left, m_mode;
      rewrite ?Ss, ?Sa, ?So, ?Sout, ?Sad, ?St; ikb_close; ikb_post_trail wrap src pos out m. }
  destruct V2 as [(Lv & _ & _)|(Lv & Hn2)]; [apply Z.eqb_neq in EL; contradiction|].
  destruct (negb _).
  { cbn [stepx_post]. apply (ikb_Kx wrap src pos out a0 m); ikb_red; rewrite ?Ss, ?Sa, ?So, ?Sout, ?Sad, ?St;
      auto; ikb_close; ikb_post_trail wrap src pos out m. }
  assert (Kx3 : Kx wrap src pos out a0
     (set_mode (initbits (upd_s m2 (fun s => set_i_length s (m_hold m2 mod 65536)))) COPY_)).
  { apply (ikb_Kx wrap src pos out a0 m); ikb_red; rewrite ?Ss, ?Sa, ?So, ?Sout, ?Sad, ?St;
      auto; ikb_close; ikb_post_trail wrap src pos out m.
    apply (kk_bb_init KIT); auto; lia. }
  destruct (flush =? Z_TREES).
  - cbn [stepx_post]. apply ikb_Kx_l. exact Kx3.
  - apply (ikb_copy_ KIT wrap src pos out a0 inp); try exact Kx3; ikb_red; rewrite ?Ss, ?Si, ?Sa, ?So, ?Sout; auto; try lia.
    apply Z.mod_pos_bound. lia.
Qed.

Lemma ikx_block : blockx_stmt.
Proof.
  intros KIT wrap src pos out a0 inp aout flush m Hc K X Hw Hl Hmd Houtb. unfold md_block in Hmd.
  pose proof (proj1 Hw) as W.
  pose proof (Inv.mw_nx _ W) as Hnx. pose proof (proj1 (Inv.mw_ow _ W)) as Ho.
  pose proof (proj2 (Inv.mw_ow _ W)) as Hob. pose proof (Inv.mw_aout _ W) as Ha.
  pose proof (Inv.sw_length _ (Inv.mw_s _ W)) as Hlen. unfold Inv.urange in Hlen.
  pose proof (kc_inp _ _ _ _ _ _ K) as Hinp. subst inp.
  pose proof (kc_wrap _ _ _ _ _ _ K) as Hwr.
  assert (Hb : m_mode m <> BAD -> m_mode m <> MEM -> 0 <= m_bits m <= 31) by apply (kc_bits _ _ _ _ _ _ K).
  assert (Hout : m_mode m <> LENGTH -> m_mode m <> DONE -> m_mode m <> BAD -> m_out m = m_aout m)
    by (apply Inv.mwf_out_eq; exact W).
  repeat match type of Hmd with _ \/ _ => destruct Hmd as [Hmd|Hmd] end;
  rewrite Hmd in Hb, Hout; ikb_cst;
  try specialize (Hb ltac:(lia) ltac:(lia)); try specialize (Hout ltac:(lia) ltac:(lia) ltac:(lia));
  fold STORED COPY_ COPY CHECK LENGTH DONE BAD MEM in Hmd.
  - replace (stepf2 _ _ _ m) with (c_STORED flush m) by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    apply (ikb_stored KIT wrap src pos out a0 (m_inp m)); auto.
  - replace (stepf2 _ _ _ m) with (c_COPY_ m) by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    apply (ikb_copy_ KIT wrap src pos out a0 (m_inp m)); auto; lia.
  - replace (stepf2 _ _ _ m) with (c_COPY m) by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    apply (ikb_copy KIT wrap src pos out a0 (m_inp m)); auto; lia.
  - replace (stepf2 _ _ _ m) with (c_CHECK m) by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    apply (ikb_check KIT wrap src pos out a0 (m_inp m)); auto; try lia.
  - replace (stepf2 _ _ _ m) with (c_LENGTH m) by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    apply (ikb_length KIT wrap src pos out a0 (m_inp m)); auto.
  - replace (stepf2 _ _ _ m) with (c_DONE m) by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    apply ikb_done; auto.
  - replace (stepf2 _ _ _ m) with (c_BAD m) by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    apply ikb_bad; auto.
  - replace (stepf2 _ _ _ m) with (IRet Z_MEM_ERROR m) by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    exact X.
Qed.
