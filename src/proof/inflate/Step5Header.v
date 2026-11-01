(* The header cases of the corrected model (Model2.v: c_FLAGS2 .. c_COMMENT2, c_COMMENT2 without the length
   reset) preserve mwf3x: Step3Header.v's proofs over them. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.inflate.Step3Header.
Require Export Zlib.proof.inflate.Model2.
Import ListNotations.
Local Open Scope Z_scope.

Definition ok_FLAGS2 : Prop := ok_at FLAGS c_FLAGS2.
Definition ok_TIME2 : Prop := ok_at TIME c_TIME2.
Definition ok_OS2 : Prop := ok_at OS c_OS2.
Definition ok_EXLEN2 : Prop := ok_at EXLEN c_EXLEN2.
Definition ok_EXTRA2 : Prop := ok_at EXTRA c_EXTRA2.
Definition ok_NAME2 : Prop := ok_at NAME c_NAME2.
Definition ok_COMMENT2 : Prop := ok_at COMMENT c_COMMENT2.

Lemma COMMENT2_ok : ok_COMMENT2.
Proof.
  intros m W L M. unfold c_COMMENT2. cbv beta zeta.
  assert (HM: HEAD <= m_mode m <= TYPEDO) by (rewrite M; unfold_modes; lia).
  destruct (negb (Z.land (i_flags (m_s m)) 4096 =? 0)) eqn:F.
  - destruct (m_have m =? 0) eqn:HV; [simpl; apply mwf3x_set_leave; auto |].
    apply Z.eqb_neq in HV.
    pose proof (m3_w _ W) as W0. pose proof (mw_h _ W0) as HW. pose proof (mw_s _ W0) as SW.
    pose proof (zstr_f_ok (Z.to_nat (m_have m)) (sublist (m_nx m) (Zlength (m_inp m)) (m_inp m))
                  (m_have m) (i_length (m_s m)) (h_comm_max (m_h m)) (i_head (m_s m) && h_cp (m_h m))%bool
                  (h_cbuf (m_h m)) 0) as ZS.
    unfold m_have in *.
    destruct (zstr_f _ _ _ _ _ _ _ _) as [[[c b] ln] buf] eqn:ZE.
    destruct ZS as (Z1 & Z2 & Z3 & Z4).
    { apply Forall_sublist. apply (mw_inp _ W0). }
    { rewrite Zlength_sublist; pose proof (mw_nx _ W0); lia. }
    { pose proof (mw_nx _ W0); lia. }
    { apply (sw_length _ SW). }
    { rewrite (proj1 (hw_cbuf _ HW)). lia. }
    { apply (hw_cbuf _ HW). }
    pose proof (sw_length _ SW). pose proof (hw_comm_max _ HW). pose proof (hw_cbuf _ HW).
    unfold urange in *. clear ZE F HV.
    destruct (negb (b =? 0)).
    + simpl. apply mwf3x_set_leave. fin2 W HM.
    + go HCRC_ok W HM.
  - destruct (i_head (m_s m)) eqn:HD; go HCRC_ok W HM.
Qed.

Lemma NAME2_ok : ok_NAME2.
Proof.
  intros m W L M. unfold c_NAME2. cbv beta zeta.
  assert (HM: HEAD <= m_mode m <= TYPEDO) by (rewrite M; unfold_modes; lia).
  destruct (negb (Z.land (i_flags (m_s m)) 2048 =? 0)) eqn:F.
  - destruct (m_have m =? 0) eqn:HV; [simpl; apply mwf3x_set_leave; auto |].
    apply Z.eqb_neq in HV.
    pose proof (m3_w _ W) as W0. pose proof (mw_h _ W0) as HW. pose proof (mw_s _ W0) as SW.
    pose proof (zstr_f_ok (Z.to_nat (m_have m)) (sublist (m_nx m) (Zlength (m_inp m)) (m_inp m))
                  (m_have m) (i_length (m_s m)) (h_name_max (m_h m)) (i_head (m_s m) && h_np (m_h m))%bool
                  (h_nbuf (m_h m)) 0) as ZS.
    unfold m_have in *.
    destruct (zstr_f _ _ _ _ _ _ _ _) as [[[c b] ln] buf] eqn:ZE.
    destruct ZS as (Z1 & Z2 & Z3 & Z4).
    { apply Forall_sublist. apply (mw_inp _ W0). }
    { rewrite Zlength_sublist; pose proof (mw_nx _ W0); lia. }
    { pose proof (mw_nx _ W0); lia. }
    { apply (sw_length _ SW). }
    { rewrite (proj1 (hw_nbuf _ HW)). lia. }
    { apply (hw_nbuf _ HW). }
    pose proof (sw_length _ SW). pose proof (hw_name_max _ HW). pose proof (hw_nbuf _ HW).
    unfold urange in *. clear ZE F HV.
    destruct (negb (b =? 0)).
    + simpl. apply mwf3x_set_leave. fin2 W HM.
    + go COMMENT2_ok W HM.
  - destruct (i_head (m_s m)) eqn:HD; go COMMENT2_ok W HM.
Qed.

Lemma EXTRA2_ok : ok_EXTRA2.
Proof.
  intros m W L M. unfold c_EXTRA2. cbv beta zeta.
  assert (HM: HEAD <= m_mode m <= TYPEDO) by (rewrite M; unfold_modes; lia).
  destruct (negb (Z.land (i_flags (m_s m)) 1024 =? 0)) eqn:F; [| go NAME2_ok W HM].
  match goal with |- context [if negb (Z.min ?a ?b =? 0) then ?X else m] =>
    remember (if negb (Z.min a b =? 0) then X else m) as m2 eqn:E2 end.
  assert (W2: mwf3x m2 /\ m_leave m2 = 0 /\ HEAD <= m_mode m2 <= TYPEDO).
  { subst m2. pose proof (m3_w _ W) as W0. pose proof (mw_h _ W0) as HW. pose proof (mw_s _ W0) as SW.
    pose proof (mw_nx _ W0) as NX. pose proof (sw_length _ SW) as LN. pose proof (hw_extra_max _ HW) as XM.
    pose proof (hw_xbuf _ HW) as XB. pose proof (proj1 (mw_inp _ W0)) as IN. unfold m_have in *.
    unfold urange in *.
    remember (Z.min (i_length (m_s m)) (Zlength (m_inp m) - m_nx m)) as copy eqn:EC.
    assert (CP: 0 <= copy <= i_length (m_s m) /\ copy <= Zlength (m_inp m) - m_nx m) by (rewrite EC; lia).
    clear EC.
    destruct (negb (copy =? 0)); [| split; [auto | split; [auto | auto]]].
    remember (u32 (h_extra_len (m_h m) - i_length (m_s m))) as len eqn:EL.
    assert (LR: urange len) by (rewrite EL; apply u32_range). clear EL. unfold urange in LR.
    destruct (andb (andb (i_head (m_s m)) (h_xp (m_h m))) (len <? h_extra_max (m_h m))) eqn:C.
    + apply andb_prop in C; destruct C as [_ C]; apply Z.ltb_lt in C.
      remember (if h_extra_max (m_h m) <? u32 (len + copy) then h_extra_max (m_h m) - len else copy)
        as n eqn:EN.
      assert (NR: 0 <= n <= copy /\ len + n <= h_extra_max (m_h m)).
      { rewrite EN. unfold u32. rewrite (Z.mod_small (len + copy)) by rep_lia.
        destruct (Z.ltb_spec (h_extra_max (m_h m)) (len + copy)); lia. }
      clear EN.
      assert (IB: Zlength (inbytes m n) = n) by (unfold inbytes; rewrite Zlength_sublist; lia).
      destruct (put_bytes_ok (h_xbuf (m_h m)) len (inbytes m n)) as [PB1 PB2]; [lia | lia |].
      rewrite (proj1 XB) in PB1.
      specialize (PB2 (proj2 XB) (inbytes_bytes m n W0)).
      split; [fin2 W HM |]. rewrite crc_if_eq. simpl. split; [auto |]. unfold m_mode in HM. auto.
    + split; [fin2 W HM |]. rewrite crc_if_eq. simpl. split; [auto |]. unfold m_mode in HM. auto. }
  destruct W2 as (W2 & L2 & HM2).
  destruct (negb (i_length (m_s m2) =? 0)); [simpl; apply mwf3x_set_leave; auto | go NAME2_ok W2 HM2].
Qed.

Lemma EXLEN2_ok : ok_EXLEN2.
Proof.
  intros m W L M. unfold c_EXLEN2.
  assert (HM: HEAD <= m_mode m <= TYPEDO) by (rewrite M; unfold_modes; lia).
  destruct (negb (Z.land (i_flags (m_s m)) 1024 =? 0)) eqn:F.
  - nb 16 m W L.
    assert (HM1: HEAD <= m_mode m1 <= TYPEDO) by (unfold m_mode in *; rewrite S1, M; unfold_modes; lia).
    go EXTRA2_ok W1 HM1.
  - cbv beta zeta. go EXTRA2_ok W HM.
Qed.

Lemma OS2_ok : ok_OS2.
Proof.
  intros m W L M. unfold c_OS2. nb 16 m W L.
  assert (HM1: HEAD <= m_mode m1 <= TYPEDO) by (unfold m_mode in *; rewrite S1, M; unfold_modes; lia).
  go EXLEN2_ok W1 HM1.
Qed.

Lemma TIME2_ok : ok_TIME2.
Proof.
  intros m W L M. unfold c_TIME2. nb 32 m W L.
  assert (HM1: HEAD <= m_mode m1 <= TYPEDO) by (unfold m_mode in *; rewrite S1, M; unfold_modes; lia).
  go OS2_ok W1 HM1.
Qed.

Lemma FLAGS2_ok : ok_FLAGS2.
Proof.
  intros m W L M. unfold c_FLAGS2. nb 16 m W L.
  assert (HM1: HEAD <= m_mode m1 <= TYPEDO) by (unfold m_mode in *; rewrite S1, M; unfold_modes; lia).
  destruct (negb (Z.land (s32 (m_hold m1)) 255 =? 8)); [simpl; apply mwf3x_set_bad; fin2 W1 HM1 |].
  destruct (negb (Z.land (s32 (m_hold m1)) 57344 =? 0)); [simpl; apply mwf3x_set_bad; fin2 W1 HM1 |].
  go TIME2_ok W1 HM1.
Qed.

