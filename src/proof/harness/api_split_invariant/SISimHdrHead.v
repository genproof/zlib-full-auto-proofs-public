(* The header simulation, HEAD: no header (raw deflate), the gzip magic, or the zlib header with its
   checks (FCHECK, method, window size) and the FDICT flag. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_split_invariant.SIDefs.
Require Import Zlib.proof.harness.api_split_invariant.SISimHdrKit.
Require Import Zlib.proof.harness.api_split_invariant.SISimHdrFix.
Require Import Zlib.proof.harness.api_split_invariant.SISimHdrEnd.
Import ListNotations.
Local Open Scope Z_scope.

Lemma nolive_TYPEDO : ~ len_live TYPEDO /\ ~ off_live TYPEDO /\ ~ ext_live TYPEDO /\
                      data_mode TYPEDO /\ ~ hdr_mode TYPEDO.
Proof. unfold len_live, off_live, ext_live, data_mode, decode_mode, hdr_mode. vm_compute. lia. Qed.

Lemma nolive_FLAGS : ~ len_live FLAGS /\ ~ off_live FLAGS /\ ~ ext_live FLAGS /\
                     ~ data_mode FLAGS /\ hdr_mode FLAGS.
Proof. unfold len_live, off_live, ext_live, data_mode, decode_mode, hdr_mode. vm_compute. lia. Qed.

Lemma nolive_DICTID : ~ len_live DICTID /\ ~ off_live DICTID /\ ~ ext_live DICTID /\
                      ~ data_mode DICTID /\ hdr_mode DICTID.
Proof. unfold len_live, off_live, ext_live, data_mode, decode_mode, hdr_mode. vm_compute. lia. Qed.

(* sh_field when only the shape of the abstract step is known before the case analysis *)
Lemma sh_field_ex n flush src P0 O0 R m a (K: mst -> iout) :
  kit_bits_stmt -> rel src P0 O0 m a -> hbits m -> m_leave m = 0 -> hdr_mode (m_mode m) ->
  ~ (m_mode m = EXTRA \/ m_mode m = NAME \/ m_mode m = COMMENT \/
     (m_mode m = EXLEN /\ Z.land (i_flags (m_s m)) 1024 = 0)) ->
  n = (if orb (m_mode m =? TIME) (m_mode m =? DICTID) then 32 else 16) ->
  (exists w a1, astep lenfix_list distfix_list src a = AGo (a_q a + n) w a1) ->
  (forall nx1 h1,
     bitbuf src P0 (set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx1) h1) n) 0) ->
     mq P0 (set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx1) h1) n) 0) = mq P0 m ->
     h1 = sbits src (a_q a) n -> a_q a = mq P0 m -> a_q a + n <= 8 * (P0 + Zlength (m_inp m)) ->
     hgoal flush src P0 O0 (P0 + Zlength (m_inp m)) R a
       (K (set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx1) h1) n) 0))) ->
  hgoal flush src P0 O0 (P0 + Zlength (m_inp m)) R a
    (if m_leave (needbits n m) =? 1 then IBrk (needbits n m) else K (needbits n m)).
Proof. intros KB Rl Hb L0 Hh NS En (w & a1 & ST) HK. eapply sh_field; eauto. Qed.

Ltac sh_apply_ex n :=
  lazymatch goal with |- context [if m_leave (needbits n ?m) =? 1 then IBrk (needbits n ?m) else ?B] =>
    let B' := eval pattern (needbits n m) in B in
    lazymatch B' with ?F _ => eapply (sh_field_ex n) with (K := F) end end.

Lemma sh_head : kit_stmt -> awf_stmt -> hcase_ok (fun md => md = HEAD).
Proof.
  intros KIT AW flush src P0 O0 m a [Rl Hb] Aw L0 Md.
  rewrite stepf2_HEAD by exact Md. unfold c_HEAD2.
  assert (Hh: hdr_mode (m_mode m)) by (rewrite Md; unfold hdr_mode; auto 20).
  destruct (hdr_not_bad _ Hh) as [NB _].
  assert (MdA: a_mode a = HEAD) by (rewrite <- (rl_mode _ _ _ _ _ Rl); exact Md).
  pose proof (rl_s _ _ _ _ _ Rl NB) as SQ.
  destruct (rl_chk _ _ _ _ _ Rl) as (CK & _).
  pose proof (rl_bb _ _ _ _ _ Rl) as BB.
  pose proof (rl_q _ _ _ _ _ Rl NB) as Q.
  pose proof (hdr_O0 _ _ _ _ _ Rl Aw Hh) as O0n.
  assert (WE: i_wrap (m_s m) = i_wrap (a_s a)) by apply (se_wrap _ _ SQ).
  assert (WbE: i_wbits (m_s m) = i_wbits (a_s a)) by apply (se_wbits _ _ SQ).
  pose proof (rl_head _ _ _ _ _ Rl) as HdF.
  destruct (Z.eqb_spec (i_wrap (m_s m)) 0) as [W0|W0]; cbv iota.
  - (* raw deflate: no header *)
    destruct nolive_TYPEDO as (N1 & N2 & N3 & D1 & D2).
    eapply hgoal_final; [ | exact (q_in _ _ _ _ _ Rl NB) | | exact L0].
    { rewrite astep_HEAD by exact MdA. unfold a_HEAD. rewrite <- WE, W0. reflexivity. }
    apply hrel_mk; [intros BO | | hrel_md].
    + eapply rel_hdr_next; [exact Rl | exact Hh | | reflexivity | reflexivity | reflexivity | reflexivity
                           | reflexivity | reflexivity | reflexivity | reflexivity | | reflexivity | | | | | | | | exact BO].
      * eapply bitbuf_ext; [exact BB | reflexivity ..].
      * exact Q.
      * cbn. apply seq_mode_nolive; auto.
      * intros H. exfalso. exact (D2 H).
      * intros _ W. exfalso. exact (W W0).
      * right. exact D1.
      * reflexivity.
      * unfold win_eq. cbn. repeat split; reflexivity.
      * exact HdF.
    + intros H. exfalso. exact (D2 H).
  - set (h := sbits src (a_q a) 16).
    assert (W0a: (i_wrap (a_s a) =? 0) = false) by (rewrite <- WE; apply Z.eqb_neq; exact W0).
    cbv zeta.
    destruct (negb (Z.land (i_wrap (a_s a)) 2 =? 0) && (h =? 35615))%bool eqn:C1.
    + (* the gzip magic *)
      sh_apply 16; [exact (proj1 KIT) | exact Rl | exact Hb | exact L0 | exact Hh
        | rewrite Md; intros [E|[E|[E|[E _]]]]; discriminate | rewrite Md; reflexivity
        | rewrite astep_HEAD by exact MdA; unfold a_HEAD; cbv zeta; rewrite W0a; fold h; rewrite C1; reflexivity
        | ].
      intros nx1 h1 BB1 Q1 Eh Q' Lim.
      cbn [m_hold m_s set_m_leave set_m_bits set_m_hold set_m_nx].
      subst h1. fold h in BB1, Q1. fold h. rewrite WE, C1. cbv iota.
      set (M := set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx1) h) 16) 0) in *.
      destruct (proj1 (proj2 (proj2 (proj2 (proj1 KIT)))) src P0 M BB1) as (BBi & Qi).
      destruct nolive_FLAGS as (N1 & N2 & N3 & D1 & D2).
      eapply hgoal_final; [rewrite astep_HEAD by exact MdA; unfold a_HEAD; cbv zeta; rewrite W0a; fold h;
                           rewrite C1; reflexivity | exact Lim | | reflexivity].
      apply hrel_mk; [intros BO | | hrel_md].
      * eapply rel_hdr_next; [exact Rl | exact Hh | | reflexivity | reflexivity | reflexivity | reflexivity
                             | reflexivity | reflexivity | reflexivity | reflexivity | | reflexivity | | | | | | | | exact BO].
        -- eapply bitbuf_ext; [exact BBi | reflexivity ..].
        -- cbn [a_q]. unfold mq in *. cbn in *. lia.
        -- cbn. rewrite WbE. apply seq_mode_nolive; auto. apply seq_check, seq_wbits. exact SQ.
        -- intros _. clearbody h. cbn - [ref_crc32]. reflexivity.
        -- intros D. exfalso. exact (D1 D).
        -- left. exact D2.
        -- reflexivity.
        -- unfold win_eq. cbn. repeat split; reflexivity.
        -- exact HdF.
      * intros _. cbn. split; [reflexivity|]. split; [lia|]. intros [E|[E|[E|[E _]]]]; discriminate.
    + (* a zlib header *)
      sh_apply_ex 16; [exact (proj1 KIT) | exact Rl | exact Hb | exact L0 | exact Hh
        | rewrite Md; intros [E|[E|[E|[E _]]]]; discriminate | rewrite Md; reflexivity
        | rewrite astep_HEAD by exact MdA; unfold a_HEAD; cbv zeta; rewrite W0a; fold h; rewrite C1;
          repeat match goal with |- context [if ?c then _ else _] => destruct c end; eexists _, _; reflexivity
        | ].
      intros nx1 h1 BB1 Q1 Eh Q' Lim.
      cbn [m_hold m_s set_m_leave set_m_bits set_m_hold set_m_nx].
      subst h1. fold h in BB1, Q1. fold h. rewrite WE, C1. cbv iota.
      rewrite HdF. cbv iota.
      set (M := set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx1) h) 16) 0) in *.
      assert (H4: m_hold (dropbits 4 M) = Z.shiftr h 4) by reflexivity.
      assert (S4: m_s (dropbits 4 M) = m_s m) by reflexivity.
      assert (HU: forall X f, m_hold (upd_s X f) = m_hold X) by reflexivity.
      rewrite !HU, H4, S4, WbE.
      change (m_hold M) with h.
      destruct (proj1 (proj2 (proj2 (proj1 KIT))) src P0 M 4 BB1 ltac:(cbn; lia)) as (BBd & Qd & _).
      Ltac st_head MdA W0a h :=
        rewrite astep_HEAD by exact MdA; unfold a_HEAD; cbv zeta; rewrite W0a; fold h;
        repeat match goal with C: ?c = _ |- context [if ?c then _ else _] => rewrite C end; reflexivity.
      Ltac bad_head Rl Hh MdA W0a h Lim BB HdF :=
        eapply sh_bad; [exact Rl | exact Hh | st_head MdA W0a h | exact Lim | reflexivity | reflexivity
                       | eapply bitbuf_ext; [exact BB | reflexivity ..] | reflexivity | reflexivity | reflexivity
                       | reflexivity | reflexivity | reflexivity | reflexivity | exact HdF | reflexivity ].
      match goal with |- context [if ?c then IBrk (set_bad M M_hdr_check) else _] => destruct c eqn:C2 end;
        [bad_head Rl Hh MdA W0a h Lim BB1 HdF|].
      match goal with |- context [if ?c then IBrk (set_bad M M_method) else _] => destruct c eqn:C3 end;
        [bad_head Rl Hh MdA W0a h Lim BB1 HdF|].
      match goal with |- context [if ?c then IBrk (set_bad (dropbits 4 M) M_wsize) else _] =>
        destruct c eqn:C4 end;
        [bad_head Rl Hh MdA W0a h Lim BBd HdF|].
      match goal with |- context [initbits ?Y] => set (Y0 := Y) end.
      assert (BBY: bitbuf src P0 Y0) by (eapply bitbuf_ext; [exact BBd | reflexivity ..]).
      assert (QY: mq P0 Y0 = mq P0 M + 4) by (rewrite <- Qd; reflexivity).
      assert (BY: m_bits Y0 = 12) by reflexivity.
      destruct (proj1 (proj2 (proj2 (proj2 (proj1 KIT)))) src P0 Y0 BBY) as (BBi & Qi).
      assert (SY: m_s Y0 = set_i_check (set_i_flags (set_i_dmax (set_i_wbits (m_s m)
                    (if i_wbits (a_s a) =? 0 then Z.shiftr h 4 mod 16 + 8 else i_wbits (a_s a)))
                    (2 ^ (Z.shiftr h 4 mod 16 + 8))) 0) 1) by (cbn; rewrite WbE; reflexivity).
      assert (SQ': seq (m_s Y0) (set_i_check (set_i_flags (set_i_dmax (set_i_wbits (a_s a)
                    (if i_wbits (a_s a) =? 0 then Z.shiftr h 4 mod 16 + 8 else i_wbits (a_s a)))
                    (2 ^ (Z.shiftr h 4 mod 16 + 8))) 0) 1))
        by (rewrite SY; apply seq_check, seq_flags, seq_dmax, seq_wbits; exact SQ).
      assert (Qf: forall md, mq P0 (set_mode (initbits Y0) md) = a_q a + 16).
      { intros md. rewrite (mq_ext P0 (initbits Y0) (set_mode (initbits Y0) md)) by reflexivity.
        rewrite Qi, BY, QY, Q1, <- Q'. lia. }
      assert (Wf: forall md, win_eq (m_s (set_mode (initbits Y0) md)) (m_s m))
        by (intros md; unfold win_eq; cbn; repeat split; reflexivity).
      destruct (Z.land (Z.shiftr h 4) 512 =? 0) eqn:C5.
      * (* no preset dictionary: the data *)
        destruct nolive_TYPE as (N1 & N2 & N3). destruct type_data as (D1 & D2).
        eapply hgoal_final; [st_head MdA W0a h | exact Lim | | reflexivity].
        apply hrel_mk; [intros BO | | hrel_md].
        -- eapply rel_hdr_next; [exact Rl | exact Hh | | reflexivity | reflexivity | reflexivity | reflexivity
                               | reflexivity | reflexivity | reflexivity | reflexivity | | reflexivity | | | | | | | | exact BO].
           ++ eapply bitbuf_ext; [exact BBi | reflexivity ..].
           ++ symmetry. apply Qf.
           ++ apply seq_mode_nolive; auto.
           ++ intros H. exfalso. exact (D2 H).
           ++ intros _ _. rewrite O0n. reflexivity.
           ++ right. exact D1.
           ++ reflexivity.
           ++ apply Wf.
           ++ exact HdF.
        -- intros H. exfalso. exact (D2 H).
      * (* the dictionary id follows *)
        destruct nolive_DICTID as (N1 & N2 & N3 & D1 & D2).
        eapply hgoal_final; [st_head MdA W0a h | exact Lim | | reflexivity].
        apply hrel_mk; [intros BO | | hrel_md].
        -- eapply rel_hdr_next; [exact Rl | exact Hh | | reflexivity | reflexivity | reflexivity | reflexivity
                               | reflexivity | reflexivity | reflexivity | reflexivity | | reflexivity | | | | | | | | exact BO].
           ++ eapply bitbuf_ext; [exact BBi | reflexivity ..].
           ++ symmetry. apply Qf.
           ++ apply seq_mode_nolive; auto.
           ++ intros _. reflexivity.
           ++ intros H. exfalso. exact (D1 H).
           ++ left. exact D2.
           ++ reflexivity.
           ++ apply Wf.
           ++ exact HdF.
        -- intros _. cbn. split; [reflexivity|]. split; [lia|]. intros [E|[E|[E|[E _]]]]; discriminate.
Qed.
