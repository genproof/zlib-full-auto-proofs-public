(* Law inflate_header, theory part: cases TIME, OS, EXLEN *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_header.IHTDefs.
Require Import Zlib.proof.harness.inflate_header.IHTCaseKit.
Import ListNotations.
Local Open Scope Z_scope.

Lemma ihc_time : ihc_time_stmt.
Proof.
  intros KIT CN g h0 pos inp m G HW X K L0 MD.
  pose proof (k_lay KIT g G) as LY. destruct (ihk_lay_src g LY) as [LS XS].
  pose proof K as [Ki Kn Kw Ko Kt Kr Kl Kc Kj].
  assert (Rok: m_ret m = Z_OK) by (apply (ihk_ret m TIME); auto; unfold TIME, DONE, BAD; lia).
  unfold m_mode in MD.
  destruct Kj as [E|E|E Pr B Fg Rs Ck Dn Ht Hx Hn Hc La|E|E|E|E|E|E|E|E|E|E|E|E|E]; try solve [ihk_nomode].
  pose proof (ihk_flg g G) as FR.
  pose proof X as (X0 & X1 & X2). destruct B as [Bb Bh].
  unfold c_TIME2. cbv zeta.
  destruct (k_nb KIT (ih_src g) inp pos 4 32 m (ly_bytes _ LY) X0 X1 X2 Ki Kn ltac:(lia) ltac:(lia)
              ltac:(change ((32 + 7) / 8) with 4; lia) Bb Bh)
    as (nx' & lv' & EN & R & C).
  rewrite EN. ihk_red.
  change ((32 + 7) / 8) with 4 in C.
  destruct C as [(-> & -> & C) | (-> & C)].
  - rewrite Z.eqb_refl. cbn [ok_out].
    constructor; ihk_red; [exact Ki | lia | exact Kw | exact Ko | exact Kt | left; exact Rok | right; reflexivity
                          | ihk_jc | ].
    apply J_TIME; [exact E | lia | split; [lia | reflexivity] | exact Fg | exact Rs | exact Ck | exact Dn | exact Ht
                  | exact Hx | exact Hn | exact Hc | exact La].
  - rewrite L0. cbn [Z.eqb].
    assert (P8: pos + nx' = 8) by lia. rewrite P8 in *. rewrite (proj1 (ly_mt _ LY)).
    rewrite (jc_head _ _ _ Kc). ihk_red.
    unfold fg in Fg.
    rewrite (ihk_crc_if KIT g); ihk_red; [| exact FR | exact Fg | apply (jc_wrap _ _ _ Kc)].
    unfold hT in *.
    destruct (fl g 2) eqn:F2; ihk_red; (apply CN; [exact G | exact HW | exact X | | reflexivity | reflexivity]);
      (constructor; ihk_red; [exact Ki | lia | exact Kw | exact Ko | exact Kt | left; exact Rok | left; reflexivity
                             | eapply ihk_jc; [exact Kc | ..]; reflexivity | ]);
      (apply J_OS; [reflexivity | lia | rewrite P8; apply ihk_bb0 | exact Fg | exact Rs
                   | | exact Dn | exact Ht | reflexivity | exact Hx | exact Hn | exact Hc | exact La ]);
      unfold ck in *; intros F2'.
    + cbn [i_check set_i_mode set_i_check]. rewrite (Ck F2'), (proj2 (ly_mt _ LY)).
      apply (k_crc KIT); [apply (ly_bytes _ LY) | lia | lia].
    + congruence.
Qed.

Lemma ihc_os : ihc_os_stmt.
Proof.
  intros KIT CN g h0 pos inp m G HW X K L0 MD.
  pose proof (k_lay KIT g G) as LY. destruct (ihk_lay_src g LY) as [LS XS].
  pose proof K as [Ki Kn Kw Ko Kt Kr Kl Kc Kj].
  assert (Rok: m_ret m = Z_OK) by (apply (ihk_ret m OS); auto; unfold OS, DONE, BAD; lia).
  unfold m_mode in MD.
  destruct Kj as [E|E|E|E Pr B Fg Rs Ck Dn Ht Hm Hx Hn Hc La|E|E|E|E|E|E|E|E|E|E|E|E]; try solve [ihk_nomode].
  pose proof (ihk_flg g G) as FR.
  assert (XO: 0 <= g_xfl g <= 255 /\ 0 <= g_os g <= 255) by (unfold ih_ok in G; lia).
  destruct (proj2 (k_bits KIT) (g_xfl g) (g_os g) ltac:(lia) ltac:(lia)) as [Bx Bo].
  pose proof X as (X0 & X1 & X2). destruct B as [Bb Bh].
  unfold c_OS2. cbv zeta.
  destruct (k_nb KIT (ih_src g) inp pos 8 16 m (ly_bytes _ LY) X0 X1 X2 Ki Kn ltac:(lia) ltac:(lia)
              ltac:(change ((16 + 7) / 8) with 2; lia) Bb Bh)
    as (nx' & lv' & EN & R & C).
  rewrite EN. ihk_red.
  change ((16 + 7) / 8) with 2 in C.
  destruct C as [(-> & -> & C) | (-> & C)].
  - rewrite Z.eqb_refl. cbn [ok_out].
    constructor; ihk_red; [exact Ki | lia | exact Kw | exact Ko | exact Kt | left; exact Rok | right; reflexivity
                          | ihk_jc | ].
    apply J_OS; [exact E | lia | split; [lia | reflexivity] | exact Fg | exact Rs | exact Ck | exact Dn | exact Ht
                | exact Hm | exact Hx | exact Hn | exact Hc | exact La].
  - rewrite L0. cbn [Z.eqb].
    assert (P10: pos + nx' = 10) by lia. rewrite P10 in *. rewrite (proj1 (ly_os _ LY)).
    rewrite (jc_head _ _ _ Kc). ihk_red.
    unfold fg in Fg.
    rewrite (ihk_crc_if KIT g); ihk_red; [| exact FR | exact Fg | apply (jc_wrap _ _ _ Kc)].
    unfold hT, hM in *.
    destruct (fl g 2) eqn:F2; ihk_red; (apply CN; [exact G | exact HW | exact X | | reflexivity | reflexivity]);
      (constructor; ihk_red; [exact Ki | lia | exact Kw | exact Ko | exact Kt | left; exact Rok | left; reflexivity
                             | eapply ihk_jc; [exact Kc | ..]; reflexivity | ]);
      (apply J_EXLEN; [reflexivity | destruct (fl g 4); lia | rewrite P10; apply ihk_bb0 | exact Fg | exact Rs
                      | | exact Dn | exact Ht | exact Hm | split; [exact Bx | exact Bo]
                      | exact Hx | exact Hn | exact Hc | exact La ]);
      unfold ck in *; intros F2'.
    + cbn [i_check set_i_mode set_i_check]. rewrite (Ck F2'), (proj2 (ly_os _ LY)).
      apply (k_crc KIT); [apply (ly_bytes _ LY) | lia | lia].
    + congruence.
Qed.

Lemma ihc_exlen : ihc_exlen_stmt.
Proof.
  intros KIT CN g h0 pos inp m G HW X K L0 MD.
  pose proof (k_lay KIT g G) as LY. destruct (ihk_lay_src g LY) as [LS XS].
  pose proof K as [Ki Kn Kw Ko Kt Kr Kl Kc Kj].
  assert (Rok: m_ret m = Z_OK) by (apply (ihk_ret m EXLEN); auto; unfold EXLEN, DONE, BAD; lia).
  unfold m_mode in MD.
  destruct Kj as [E|E|E|E|E Pr B Fg Rs Ck Dn Ht Hm Ho Hx Hn Hc La|E|E|E|E|E|E|E|E|E|E|E]; try solve [ihk_nomode].
  pose proof (ihk_flg g G) as FR.
  destruct (proj1 (k_bits KIT) (g_flg g) FR) as (_ & _ & _ & _ & F1024 & _).
  assert (XL: Zlength (g_xf g) <= 65535) by (unfold ih_ok in G; lia).
  pose proof X as (X0 & X1 & X2). destruct B as [Bb Bh].
  unfold fg in Fg.
  unfold c_EXLEN2. cbv zeta. rewrite Fg, F1024.
  unfold hT, hM, hO, hx0 in *.
  destruct (fl g 4) eqn:F4.
  - (* FEXTRA *)
    replace (negb (Z.land (g_flg g) 4 =? 0)) with true by (unfold fl in F4; rewrite F4; reflexivity).
    destruct (k_nb KIT (ih_src g) inp pos 10 16 m (ly_bytes _ LY) X0 X1 X2 Ki Kn ltac:(lia) ltac:(lia)
                ltac:(change ((16 + 7) / 8) with 2; lia) Bb Bh)
      as (nx' & lv' & EN & R & C).
    rewrite EN. ihk_red.
    change ((16 + 7) / 8) with 2 in C.
    destruct C as [(-> & -> & C) | (-> & C)].
    + rewrite Z.eqb_refl. cbn [ok_out].
      constructor; ihk_red; [exact Ki | lia | exact Kw | exact Ko | exact Kt | left; exact Rok | right; reflexivity
                            | ihk_jc | ].
      apply J_EXLEN; [exact E | rewrite F4; lia | split; [lia | reflexivity] | exact Fg | exact Rs | exact Ck | exact Dn
                     | exact Ht | exact Hm | exact Ho | exact Hx | exact Hn | exact Hc | exact La].
    + rewrite L0. cbn [Z.eqb].
      assert (P12: pos + nx' = 12) by lia. rewrite P12 in *. rewrite (proj1 (ly_xl _ LY F4)).
      assert (U: u32 (Zlength (g_xf g)) = Zlength (g_xf g))
        by (unfold u32; apply Z.mod_small; pose proof (Zlength_nonneg (g_xf g)); lia).
      rewrite U. rewrite (jc_head _ _ _ Kc). ihk_red.
      rewrite (ihk_crc_if KIT g); ihk_red; [| exact FR | exact Fg | apply (jc_wrap _ _ _ Kc)].
      assert (NE: ih_ne g = 12 + Zlength (g_xf g)) by (unfold ih_ne; rewrite F4; lia).
      assert (XS12: ih_xs g = 12) by (unfold ih_xs; rewrite F4; reflexivity).
      destruct (fl g 2) eqn:F2; ihk_red; (apply CN; [exact G | exact HW | exact X | | reflexivity | reflexivity]);
        (constructor; ihk_red; [exact Ki | lia | exact Kw | exact Ko | exact Kt | left; exact Rok | left; reflexivity
                               | eapply ihk_jc; [exact Kc | ..]; reflexivity | ]);
        (apply J_EXTRA; [reflexivity | pose proof (Zlength_nonneg (g_xf g)); lia | reflexivity | reflexivity
                        | intros _; cbn [i_length set_i_mode set_i_check set_i_length]; lia
                        | exact Fg | exact Rs | | exact Dn | exact Ht | exact Hm | exact Ho
                        | | exact Hn | exact Hc | exact La ]).
      * unfold ck in *; intros F2'.
        cbn [i_check set_i_mode set_i_check set_i_length]. rewrite (Ck F2'), (proj2 (ly_xl _ LY F4)), P12.
        apply (k_crc KIT); [apply (ly_bytes _ LY) | lia | lia].
      * unfold hxk. rewrite F4. cbn [h_extra_len h_xp h_xbuf set_h_extra_len].
        split; [reflexivity|]. split; [apply Hx|]. intros _. rewrite P12, XS12, Z.sub_diag, sublist_nil, ihk_fbuf_nil.
        apply Hx.
      * unfold ck in *; intros F2'. congruence.
      * unfold hxk. rewrite F4. cbn [h_extra_len h_xp h_xbuf set_h_extra_len].
        split; [reflexivity|]. split; [apply Hx|]. intros _. rewrite P12, XS12, Z.sub_diag, sublist_nil, ihk_fbuf_nil.
        apply Hx.
  - (* no FEXTRA *)
    replace (negb (Z.land (g_flg g) 4 =? 0)) with false by (unfold fl in F4; rewrite F4; reflexivity).
    assert (P10: pos + m_nx m = 10) by lia.
    assert (Bz: m_bits m = 0 /\ m_hold m = 0) by (rewrite Bb, Bh, P10, sublist_nil; split; reflexivity || lia).
    assert (NE: ih_ne g = 10) by (unfold ih_ne; rewrite F4; lia).
    assert (XS10: ih_xs g = 10) by (unfold ih_xs; rewrite F4; reflexivity).
    rewrite (jc_head _ _ _ Kc). ihk_red.
    apply CN; [exact G | exact HW | exact X | | exact L0 | reflexivity].
    constructor; ihk_red; [exact Ki | lia | exact Kw | exact Ko | exact Kt | left; exact Rok | left; exact L0
                          | eapply ihk_jc; [exact Kc | ..]; reflexivity | ].
    apply J_EXTRA; [reflexivity | lia | apply Bz | apply Bz | intros; congruence
                   | exact Fg | exact Rs | rewrite P10; exact Ck | exact Dn | exact Ht | exact Hm | exact Ho
                   | | exact Hn | exact Hc | exact La ].
    unfold hxk. rewrite F4. reflexivity.
Qed.

Lemma ihc_toe : ihc_time_stmt /\ ihc_os_stmt /\ ihc_exlen_stmt.
Proof. exact (conj ihc_time (conj ihc_os ihc_exlen)). Qed.
