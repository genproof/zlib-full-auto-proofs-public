(* Law inflate_header, theory part: cases HEAD (c_HEAD2) and FLAGS (c_FLAGS2) *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_header.IHTDefs.
Require Import Zlib.proof.harness.inflate_header.IHTCaseKit.
Import ListNotations.
Local Open Scope Z_scope.

Lemma ihc_head : ihc_head_stmt.
Proof.
  intros KIT g h0 pos inp m G HW X K L0 MD.
  pose proof (k_lay KIT g G) as LY.
  pose proof K as [Ki Kn Kw Ko Kt Kr Kl Kc Kj].
  assert (Rok: m_ret m = Z_OK) by (apply (ihk_ret m HEAD); auto; unfold HEAD, DONE, BAD; lia).
  unfold m_mode in MD.
  destruct Kj as [E Pr B Dn Hx Hn Hc La|E|E|E|E|E|E|E|E|E|E|E|E|E|E|E]; try solve [ihk_nomode].
  assert (W0: (i_wrap (m_s m) =? 0) = false) by (destruct (jc_wrap _ _ _ Kc) as [W|[W|[W|W]]]; rewrite W; reflexivity).
  assert (W2: negb (Z.land (i_wrap (m_s m)) 2 =? 0) = true)
    by (destruct (jc_wrap _ _ _ Kc) as [W|[W|[W|W]]]; rewrite W; reflexivity).
  destruct X as (X0 & X1 & X2). destruct B as [Bb Bh].
  unfold c_HEAD2. rewrite W0. cbv zeta.
  destruct (k_nb KIT (ih_src g) inp pos 0 16 m (ly_bytes _ LY) X0 X1 X2 Ki Kn ltac:(lia) ltac:(lia)
              ltac:(change ((16 + 7) / 8) with 2; lia) Bb Bh)
    as (nx' & lv' & EN & R & C).
  rewrite EN. ihk_red.
  change ((16 + 7) / 8) with 2 in C.
  destruct C as [(-> & -> & C) | (-> & C)].
  - rewrite Z.eqb_refl. cbn [ok_out].
    constructor; ihk_red; auto; try lia; try ihk_jc.
    apply J_HEAD; auto; try lia. split; [lia | reflexivity].
  - rewrite L0. cbn [Z.eqb]. rewrite W2.
    assert (P2: pos + nx' = 2) by lia. rewrite P2 in *. rewrite (proj1 (ly_id _ LY)), Z.eqb_refl. cbn [andb].
    cbn [ok_out]. constructor; ihk_red; auto; try lia; try ihk_jc.
    apply J_FLAGS; ihk_red; auto; try lia; try (rewrite P2; apply ihk_bb0);
      try (rewrite (proj2 (ly_id _ LY)); reflexivity).
Qed.

Lemma ihc_flags : ihc_flags_stmt.
Proof.
  intros KIT CT g h0 pos inp m G HW X K L0 MD.
  pose proof (k_lay KIT g G) as LY.
  pose proof K as [Ki Kn Kw Ko Kt Kr Kl Kc Kj].
  assert (Rok: m_ret m = Z_OK) by (apply (ihk_ret m FLAGS); auto; unfold FLAGS, DONE, BAD; lia).
  unfold m_mode in MD.
  destruct Kj as [E|E Pr B Ck Dn Hx Hn Hc La|E|E|E|E|E|E|E|E|E|E|E|E|E|E]; try solve [ihk_nomode].
  pose proof (ihk_flg g G) as FR.
  destruct (proj1 (k_bits KIT) (g_flg g) FR) as (S32 & F255 & F57 & _ & _ & _ & _ & F8 & _).
  pose proof X as (X0 & X1 & X2). destruct B as [Bb Bh].
  unfold c_FLAGS2. cbv zeta.
  destruct (k_nb KIT (ih_src g) inp pos 2 16 m (ly_bytes _ LY) X0 X1 X2 Ki Kn ltac:(lia) ltac:(lia)
              ltac:(change ((16 + 7) / 8) with 2; lia) Bb Bh)
    as (nx' & lv' & EN & R & C).
  rewrite EN. ihk_red.
  change ((16 + 7) / 8) with 2 in C.
  destruct C as [(-> & -> & C) | (-> & C)].
  - rewrite Z.eqb_refl. cbn [ok_out].
    constructor; ihk_red; [exact Ki | lia | exact Kw | exact Ko | exact Kt | left; exact Rok | right; reflexivity
                          | ihk_jc | ].
    apply J_FLAGS; [exact E | lia | split; [lia | reflexivity] | exact Ck | exact Dn | exact Hx | exact Hn
                   | exact Hc | exact La].
  - rewrite L0. cbn [Z.eqb].
    assert (P4: pos + nx' = 4) by lia. rewrite P4 in *. rewrite (proj1 (ly_fl _ LY)).
    rewrite S32, F255, Z.eqb_refl. cbn [negb]. rewrite F57.
    destruct (Z.land (g_flg g) 224 =? 0) eqn:RS; cbn [negb].
    + (* no reserved bit: text, CRC, then TIME *)
      rewrite (jc_head _ _ _ Kc). ihk_red.
      rewrite (ihk_crc_if KIT g); ihk_red; [| exact FR | reflexivity | apply (jc_wrap _ _ _ Kc)].
      assert (NR: ih_reserved g = false) by (unfold ih_reserved; rewrite RS; reflexivity).
      assert (L4: 4 <= Zlength (ih_src g))
        by (pose proof (ly_len _ LY); pose proof (ly_ord _ LY); unfold ih_xs in *; destruct (fl g 4); lia).
      unfold hT in *.
      destruct (fl g 2) eqn:F2; ihk_red; (apply CT; [exact G | exact HW | exact X | | reflexivity | reflexivity]);
        (constructor; ihk_red; [exact Ki | lia | exact Kw | exact Ko | exact Kt | left; exact Rok | left; reflexivity
                               | eapply ihk_jc; [exact Kc | ..]; reflexivity | ]);
        (apply J_TIME; [reflexivity | lia | rewrite P4; apply ihk_bb0 | unfold fg; reflexivity | exact NR
                       | | exact Dn | exact F8 | exact Hx | exact Hn | exact Hc | exact La ]);
        unfold ck; intros F2'.
      * cbn [i_check set_i_mode set_i_check set_i_flags]. rewrite Ck, (proj2 (ly_fl _ LY)).
        apply (k_crc KIT); [apply (ly_bytes _ LY) | lia | lia].
      * congruence.
    + (* a reserved bit: BAD *)
      cbn [ok_out]. constructor; ihk_red; [exact Ki | lia | exact Kw | exact Ko | exact Kt | left; exact Rok
                                          | left; reflexivity | ihk_jc | ].
      apply J_BAD; ihk_red; [reflexivity | exact Dn | unfold ih_reserved; rewrite RS; reflexivity].
Qed.

Lemma ihc_hf : ihc_head_stmt /\ ihc_flags_stmt.
Proof. exact (conj ihc_head ihc_flags). Qed.
