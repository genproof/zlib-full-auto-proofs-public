(* Law api_reset, TABLE / LENLENS / CODELENS: TABLE, then LENLENS, under the wide invariant mwf3xW
   (x_inflate_reset's IRTabTab.v).  Only the lemmas that take the invariant are restated; the new states of
   TABLE and their relation are reused from IRTabTab.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_reset.IRDefs.
Require Import Zlib.proof.harness.inflate_reset.IRTabKit.
Require Import Zlib.proof.harness.inflate_reset.IRTabTab.
Require Import Zlib.proof.inflate.Step3Tables.
Require Import Zlib.proof.inflate.StepWTables.
Require Import Zlib.proof.harness.api_reset.ARSimTabKit.
Import ListNotations.
Local Open Scope Z_scope.

(* the one-stream facts of TABLE (StepWTables.TABLE_ok) *)
Lemma irtt_mwfW m2 :
  mwf3xW m2 -> 14 <= m_bits m2 -> m_mode m2 = TABLE ->
  bitsn m2 5 + 257 <= 286 -> bitsn (dropbits 5 m2) 5 + 1 <= 30 ->
  mwf3xW (set_mode (upd_s (upd_s (dropbits 4 (dropbits 5 (dropbits 5 m2)))
          (fun s => set_i_ncode (set_i_ndist (set_i_nlen s (bitsn m2 5 + 257))
                      (bitsn (dropbits 5 m2) 5 + 1))
                      (bitsn (dropbits 5 (dropbits 5 m2)) 4 + 4)))
          (fun s => set_i_have s 0)) LENLENS).
Proof.
  intros W2 NB Md T1 T2.
  pose proof (mwW_bits _ (m3W_w _ W2)) as B2.
  set (m3 := dropbits 5 m2) in *. set (m4 := dropbits 5 m3) in *. set (m5 := dropbits 4 m4).
  assert (B3: m_bits m3 = m_bits m2 - 5) by (apply tb_drop_bits; lia).
  assert (B4: m_bits m4 = m_bits m2 - 10) by (unfold m4; rewrite tb_drop_bits; lia).
  assert (W5: mwf3xW m5).
  { apply mwf3xW_dropbits; [|unfold m4 in *; lia]. apply mwf3xW_dropbits; [|lia]. apply mwf3xW_dropbits; auto; lia. }
  assert (E5: m_s m5 = m_s m2) by reflexivity.
  pose proof (bitsn_range m2 5 ltac:(lia)) as R1.
  pose proof (bitsn_range m3 5 ltac:(lia)) as R2.
  pose proof (bitsn_range m4 4 ltac:(lia)) as R3.
  change (2 ^ 5) with 32 in *. change (2 ^ 4) with 16 in *.
  set (s' := set_i_ncode (set_i_ndist (set_i_nlen (m_s m5) (bitsn m2 5 + 257)) (bitsn m3 5 + 1)) (bitsn m4 4 + 4)).
  pose proof (mwW_s _ (m3W_w _ W5)) as S5.
  assert (S': swf s') by (destruct S5; constructor; simpl; auto; lia).
  change (mwf3xW (set_m_s m5 (set_i_mode (set_i_have s' 0) LENLENS))).
  apply tb_new_s; auto.
  + apply swf_set_mode; [|md_neq]. destruct S'; constructor; simpl; auto; lia.
  + constructor; simpl; intros; try md_neq.
    * split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. intros; lia.
    * unfold decode_mode in *; md_neq.
  + simpl. first [apply (x3_head _ (m3W_x _ W5)) | (intros ?HH; exfalso; revert HH; md_neq)].
  + simpl; intros; md_neq.
  + simpl; intros; md_neq.
  + simpl; intros D; unfold decode_mode in D; md_neq.
  + apply mwfW_out_eq; [apply (m3W_w _ W5) | unfold m_mode; rewrite E5; fold (m_mode m2); rewrite Md; md_neq ..].
  + simpl; split; md_neq.
Qed.

Lemma irtt_afterW (LL: irt_ll_stmtW) W0 wrap src pos inp aout ma2 mb2 :
  Kr W0 wrap src pos inp aout ma2 mb2 -> mwf3xW ma2 -> mwf3xW mb2 ->
  14 <= m_bits ma2 -> 14 <= m_bits mb2 -> m_mode ma2 = TABLE -> m_mode mb2 = TABLE -> m_leave mb2 = 0 ->
  irt_rr W0 wrap src pos inp aout (irtt_rest ma2) (irtt_rest mb2).
Proof.
  intros K2 Wa2 Wb2 Ba2 Bb2 Ma2 Mb2 Lb2.
  assert (Hh: m_mode mb2 <> HEAD) by (rewrite Mb2; unfold TABLE, HEAD; lia).
  pose proof (irk_mf_of_Kr _ _ _ _ _ _ _ _ K2) as E2.
  pose proof (irtt_mwfW ma2 Wa2 Ba2 Ma2) as Xa.
  pose proof (irtt_mwfW mb2 Wb2 Bb2 Mb2) as Xb.
  unfold irtt_rest.
  assert (Hd: forall n m m', irk_mf m = irk_mf m' -> bitsn m n = bitsn m' n)
    by (intros n m m' E; unfold irk_mf, bitsn in *; congruence).
  pose proof (irk_dropbits 5 _ _ E2) as E3.
  pose proof (irk_dropbits 5 _ _ E3) as E4.
  pose proof (irk_dropbits 4 _ _ E4) as E5.
  rewrite (Hd 5 _ _ E2), (Hd 5 _ _ E3), (Hd 4 _ _ E4) in *.
  set (x := bitsn mb2 5 + 257) in *. set (y := bitsn (dropbits 5 mb2) 5 + 1) in *.
  set (z := bitsn (dropbits 5 (dropbits 5 mb2)) 4 + 4) in *.
  set (ma5 := dropbits 4 (dropbits 5 (dropbits 5 ma2))) in *.
  set (mb5 := dropbits 4 (dropbits 5 (dropbits 5 mb2))) in *.
  assert (K5: Kr W0 wrap src pos inp aout ma5 mb5)
    by (apply irk_mach with ma2 mb2; auto; try reflexivity).
  assert (Sb5: m_s mb5 = m_s mb2) by reflexivity.
  assert (L5: m_leave mb5 = 0) by exact Lb2.
  clearbody ma5 mb5.
  set (f := fun s => set_i_ncode (set_i_ndist (set_i_nlen s x) y) z) in *.
  assert (K6: Kr W0 wrap src pos inp aout (upd_s ma5 f) (upd_s mb5 f)).
  { pose proof (mr_s _ _ (kr_rel _ _ _ _ _ _ _ _ K5)) as S5.
    pose proof (kr_wrap _ _ _ _ _ _ _ _ K5) as Kw5. pose proof (kr_head _ _ _ _ _ _ _ _ K5) as Kh5.
    unfold upd_s. apply irk_state; auto.
    - apply irtt_srel; auto. rewrite Sb5. exact Mb2.
    - unfold f; cbn. rewrite Sb5. fold (m_mode mb2). rewrite Mb2. unfold TABLE, HEAD; lia. }
  assert (Hh6: m_mode (upd_s mb5 f) <> HEAD)
    by (unfold m_mode, upd_s, f; cbn; rewrite Sb5; fold (m_mode mb2); rewrite Mb2; unfold TABLE, HEAD; lia).
  assert (Md6: i_mode (m_s (upd_s mb5 f)) = TABLE) by (unfold upd_s, f; cbn; rewrite Sb5; exact Mb2).
  assert (L6: m_leave (upd_s mb5 f) = 0) by exact L5.
  assert (N6: i_ncode (m_s (upd_s ma5 f)) = i_ncode (m_s (upd_s mb5 f)) /\
              i_nlen (m_s (upd_s ma5 f)) = i_nlen (m_s (upd_s mb5 f)) /\
              i_ndist (m_s (upd_s ma5 f)) = i_ndist (m_s (upd_s mb5 f))) by (split; [|split]; reflexivity).
  destruct N6 as (N6c & N6l & N6d).
  rewrite !irtt_mode_upd in Xa, Xb |- *.
  set (ma6 := upd_s ma5 f) in *. set (mb6 := upd_s mb5 f) in *.
  clearbody ma6 mb6.
  destruct (orb (286 <? x) (30 <? y)) eqn:TM.
  { cbn [irt_rr]. apply irtt_bad; auto. }
  apply orb_false_iff in TM. destruct TM as [T1 T2]. apply Z.ltb_ge in T1. apply Z.ltb_ge in T2.
  specialize (Xa T1 T2). specialize (Xb T1 T2).
  apply (LL W0 wrap src pos inp aout (set_m_s ma6 (set_i_mode (set_i_have (m_s ma6) 0) LENLENS))
           (set_m_s mb6 (set_i_mode (set_i_have (m_s mb6) 0) LENLENS))); [ | exact Xa | exact Xb | exact L6 | reflexivity].
  pose proof (mr_s _ _ (kr_rel _ _ _ _ _ _ _ _ K6)) as S6.
  pose proof (kr_wrap _ _ _ _ _ _ _ _ K6) as Kw6. pose proof (kr_head _ _ _ _ _ _ _ _ K6) as Kh6.
  apply irk_state; auto.
  - apply irtt_srel_ll; auto.
  - unfold LENLENS, HEAD; cbn; lia.
Qed.

Lemma irt_tab_okW : irt_ll_stmtW -> irt_tab_stmtW.
Proof.
  intros LL W0 wrap src pos inp aout ma mb K Wa Wb L Md.
  pose proof (mr_s _ _ (kr_rel _ _ _ _ _ _ _ _ K)) as S.
  assert (Hh: m_mode mb <> HEAD) by (rewrite Md; unfold TABLE, HEAD; lia).
  assert (Ma: m_mode ma = TABLE) by (unfold m_mode in *; rewrite (sr_mode _ _ _ S); exact Md).
  assert (La: m_leave ma = 0) by (rewrite (mr_leave _ _ (kr_rel _ _ _ _ _ _ _ _ K)); exact L).
  rewrite !irtt_tab_eq.
  destruct (irk_needbits 4 14 ma mb (irk_mf_of_Kr _ _ _ _ _ _ _ _ K)) as (E2 & Sa2 & Sb2 & I2 & A2 & O2).
  pose proof (mwf3xW_needbits 14 ma Wa ltac:(lia)) as Wa2.
  pose proof (mwf3xW_needbits 14 mb Wb ltac:(lia)) as Wb2.
  pose proof (needbits_ok 14 ma (m3W_w _ Wa) La ltac:(lia)) as NBa.
  pose proof (needbits_ok 14 mb (m3W_w _ Wb) L ltac:(lia)) as NBb.
  unfold needbits in *.
  set (ma2 := needbits_f 4 14 ma) in *. set (mb2 := needbits_f 4 14 mb) in *.
  clearbody ma2 mb2.
  assert (K2: Kr W0 wrap src pos inp aout ma2 mb2) by (apply irk_mach with ma mb; auto).
  assert (EL: m_leave ma2 = m_leave mb2) by (unfold irk_mf in E2; congruence).
  rewrite EL. destruct (Z.eqb_spec (m_leave mb2) 1) as [L2|L2]; [exact K2|].
  destruct (NBa ltac:(rewrite EL; exact L2)) as [Ba2 La2].
  destruct (NBb L2) as [Bb2 Lb2].
  apply irtt_afterW; auto.
  - unfold m_mode; rewrite Sa2; exact Ma.
  - unfold m_mode; rewrite Sb2; exact Md.
Qed.

