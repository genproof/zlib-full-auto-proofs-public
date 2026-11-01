(* Law inflate_header, theory part: the cases after the header: TYPE, TYPEDO, STORED, COPY_, COPY, CHECK, LENGTH,
   DONE, BAD *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_header.IHTDefs.
Require Import Zlib.proof.harness.inflate_header.IHTCaseKit.
Import ListNotations.
Local Open Scope Z_scope.

Lemma ihb_done : case_ok DONE c_DONE.
Proof.
  intros g h0 pos inp m G HW X K L0 MD.
  pose proof K as [Ki Kn Kw Ko Kt Kr Kl Kc Kj].
  unfold c_DONE. cbn [ok_out].
  constructor; ihk_red; [exact Ki | lia | exact Kw | exact Ko | exact Kt | right; left; split; [reflexivity | exact MD]
                        | right; reflexivity | ihk_jc | exact Kj].
Qed.

Lemma ihb_bad : case_ok BAD c_BAD.
Proof.
  intros g h0 pos inp m G HW X K L0 MD.
  pose proof K as [Ki Kn Kw Ko Kt Kr Kl Kc Kj].
  unfold c_BAD. cbn [ok_out].
  constructor; ihk_red; [exact Ki | lia | exact Kw | exact Ko | exact Kt | right; right; split; [reflexivity | exact MD]
                        | right; reflexivity | ihk_jc | exact Kj].
Qed.

(* the 13 bytes after the header *)
Lemma ihb_tail g i j : ih_lay g -> 0 <= i <= j -> j <= 13 ->
  sublist (ih_nh g + i) (ih_nh g + j) (ih_src g) = sublist i j [1; 0; 0; 255; 255; 0; 0; 0; 0; 0; 0; 0; 0].
Proof.
  intros LY I J.
  assert (T: sublist (ih_nh g) (ih_nh g + 13) (ih_src g) = [1; 0; 0; 255; 255; 0; 0; 0; 0; 0; 0; 0; 0]).
  { rewrite (sublist_split (ih_nh g) (ih_nh g + 5) (ih_nh g + 13)).
    - rewrite (ly_blk _ LY), (ly_tr _ LY). reflexivity.
    - pose proof (ly_ord _ LY). unfold ih_xs in *. destruct (fl g 4); lia.
    - rewrite (ly_len _ LY). lia. }
  apply (ihk_sub _ _ _ 13); auto.
  pose proof (ly_ord _ LY). unfold ih_xs in *. destruct (fl g 4); lia.
Qed.

Lemma ihb_nh g : ih_lay g -> 10 <= ih_nh g /\ Zlength (ih_src g) = ih_nh g + 13.
Proof. intros LY. pose proof (ly_ord _ LY). pose proof (ly_len _ LY). unfold ih_xs in *. destruct (fl g 4); lia. Qed.

Lemma ihb_length : ih_kit -> case_ok LENGTH c_LENGTH.
Proof.
  intros KIT g h0 pos inp m G HW X K L0 MD.
  pose proof (k_lay KIT g G) as LY. destruct (ihb_nh g LY) as [NH LEN].
  pose proof K as [Ki Kn Kw Ko Kt Kr Kl Kc Kj].
  assert (Rok: m_ret m = Z_OK) by (apply (ihk_ret m LENGTH); auto; unfold LENGTH, DONE, BAD; lia).
  unfold m_mode in MD.
  destruct Kj as [E|E|E|E|E|E|E|E|E|E|E|E|E| E Pr B Fg Rs Bc Dk |E|E]; try solve [ihk_nomode].
  pose proof (ihk_flg g G) as FR.
  pose proof X as (X0 & X1 & X2). destruct B as [Bb Bh].
  unfold fg in Fg.
  assert (W0: negb (i_wrap (m_s m) =? 0) = true) by (destruct (jc_wrap _ _ _ Kc) as [W|[W|[W|W]]]; rewrite W; reflexivity).
  assert (W4: negb (Z.land (i_wrap (m_s m)) 4 =? 0) = true)
    by (destruct (jc_wrap _ _ _ Kc) as [W|[W|[W|W]]]; rewrite W; reflexivity).
  assert (F0: negb (i_flags (m_s m) =? 0) = true) by (rewrite Fg; destruct (Z.eqb_spec (8 + 256 * g_flg g) 0); [lia | reflexivity]).
  unfold c_LENGTH. cbv zeta. rewrite W0, F0. cbn [andb].
  destruct (k_nb KIT (ih_src g) inp pos (ih_nh g + 9) 32 m (ly_bytes _ LY) X0 X1 X2 Ki Kn ltac:(lia) ltac:(lia)
              ltac:(change ((32 + 7) / 8) with 4; lia) Bb Bh)
    as (nx' & lv' & EN & R & C).
  rewrite EN. ihk_red.
  change ((32 + 7) / 8) with 4 in C.
  destruct C as [(-> & -> & C) | (-> & C)].
  - rewrite Z.eqb_refl. cbn [ok_out].
    constructor; ihk_red; [exact Ki | lia | exact Kw | exact Ko | exact Kt | left; exact Rok | right; reflexivity
                          | ihk_jc | ].
    apply J_LENGTH; [exact E | lia | split; [lia | reflexivity] | exact Fg | exact Rs | exact Bc | exact Dk].
  - rewrite L0. cbn [Z.eqb]. rewrite W4.
    assert (P13: pos + nx' = ih_nh g + 13) by lia.
    rewrite P13, (ihb_tail g 9 13 LY ltac:(lia) ltac:(lia)), (jc_total _ _ _ Kc). cbn.
    unfold c_DONE. cbn [ok_out].
    constructor; ihk_red; [exact Ki | lia | exact Kw | exact Ko | exact Kt | right; left; split; reflexivity
                          | right; reflexivity | ihk_jc | ].
    apply J_DONE; [reflexivity | exact P13 | exact Rs | exact Bc | exact Dk].
Qed.

Lemma ihb_check : ih_kit -> case_ok CHECK c_CHECK.
Proof.
  intros KIT g h0 pos inp m G HW X K L0 MD.
  pose proof (k_lay KIT g G) as LY. destruct (ihb_nh g LY) as [NH LEN].
  pose proof K as [Ki Kn Kw Ko Kt Kr Kl Kc Kj].
  assert (Rok: m_ret m = Z_OK) by (apply (ihk_ret m CHECK); auto; unfold CHECK, DONE, BAD; lia).
  unfold m_mode in MD.
  destruct Kj as [E|E|E|E|E|E|E|E|E|E|E|E| E Pr B Ck Fg Rs Bc Dk |E|E|E]; try solve [ihk_nomode].
  pose proof (ihk_flg g G) as FR.
  pose proof X as (X0 & X1 & X2). destruct B as [Bb Bh].
  unfold fg in Fg.
  assert (W0: negb (i_wrap (m_s m) =? 0) = true) by (destruct (jc_wrap _ _ _ Kc) as [W|[W|[W|W]]]; rewrite W; reflexivity).
  assert (W4: negb (Z.land (i_wrap (m_s m)) 4 =? 0) = true)
    by (destruct (jc_wrap _ _ _ Kc) as [W|[W|[W|W]]]; rewrite W; reflexivity).
  assert (F0: (i_flags (m_s m) =? 0) = false) by (rewrite Fg; destruct (Z.eqb_spec (8 + 256 * g_flg g) 0); [lia | reflexivity]).
  unfold c_CHECK. cbv zeta. rewrite W0.
  destruct (k_nb KIT (ih_src g) inp pos (ih_nh g + 5) 32 m (ly_bytes _ LY) X0 X1 X2 Ki Kn ltac:(lia) ltac:(lia)
              ltac:(change ((32 + 7) / 8) with 4; lia) Bb Bh)
    as (nx' & lv' & EN & R & C).
  rewrite EN. ihk_red.
  change ((32 + 7) / 8) with 4 in C.
  destruct C as [(-> & -> & C) | (-> & C)].
  - rewrite Z.eqb_refl. cbn [ok_out].
    constructor; ihk_red; [exact Ki | lia | exact Kw | exact Ko | exact Kt | left; exact Rok | right; reflexivity
                          | ihk_jc | ].
    apply J_CHECK; [exact E | lia | split; [lia | reflexivity] | exact Ck | exact Fg | exact Rs | exact Bc | exact Dk].
  - rewrite L0. cbn [Z.eqb].
    rewrite Ko, Kw, Zlength_nil, Z.sub_0_r, Z.sub_diag. change (u32 0) with 0.
    cbn [Z.eqb negb]. rewrite andb_false_r. ihk_red.
    rewrite W4, F0. cbn [andb negb].
    assert (P9: pos + nx' = ih_nh g + 9) by lia.
    rewrite P9, (ihb_tail g 5 9 LY ltac:(lia) ltac:(lia)), Ck.
    assert (H0: ih_le (sublist 5 9 [1; 0; 0; 255; 255; 0; 0; 0; 0; 0; 0; 0; 0]) = 0) by reflexivity.
    rewrite H0. cbn [Z.eqb negb andb].
    apply (ihb_length KIT); [exact G | exact HW | exact X | | reflexivity | reflexivity].
    constructor; ihk_red; [exact Ki | lia | exact Kw | rewrite ?Kw, ?Zlength_nil; lia | rewrite Kt; reflexivity
                          | left; exact Rok | left; reflexivity | | ].
    + eapply ihk_jc; [exact Kc | ..]; ihk_red; try reflexivity. rewrite (jc_total _ _ _ Kc). reflexivity.
    + apply J_LENGTH; [reflexivity | lia | rewrite P9; apply ihk_bb0 | exact Fg | exact Rs | exact Bc | exact Dk].
Qed.

Lemma ihb_copy : case_ok COPY c_COPY.
Proof.
  intros g h0 pos inp m G HW X K L0 MD.
  pose proof K as [Ki Kn Kw Ko Kt Kr Kl Kc Kj].
  assert (Rok: m_ret m = Z_OK) by (apply (ihk_ret m COPY); auto; unfold COPY, DONE, BAD; lia).
  unfold m_mode in MD.
  destruct Kj as [E|E|E|E|E|E|E|E|E|E|E| E Pr Ho Bi Ln La Ck Fg Rs Bc Dk |E|E|E|E]; try solve [ihk_nomode].
  unfold c_COPY. rewrite Ln. cbn [Z.eqb negb]. cbn [ok_out].
  constructor; ihk_red; [exact Ki | lia | exact Kw | exact Ko | exact Kt | left; exact Rok | left; exact L0
                        | ihk_jc | ].
  apply J_TYPE; [left; reflexivity | right; split; [exact Pr | exact La] | exact Ho | exact Bi | exact Ck | exact Fg
                | exact Rs | exact Bc | exact Dk].
Qed.

Lemma ihb_copy_ : case_ok COPY_ c_COPY_.
Proof.
  intros g h0 pos inp m G HW X K L0 MD.
  pose proof K as [Ki Kn Kw Ko Kt Kr Kl Kc Kj].
  unfold m_mode in MD.
  destruct Kj as [E|E|E|E|E|E|E|E|E|E|E| E Pr Ho Bi Ln La Ck Fg Rs Bc Dk |E|E|E|E]; try solve [ihk_nomode].
  unfold c_COPY_. apply ihb_copy; [exact G | exact HW | exact X | | exact L0 | reflexivity].
  assert (Rok: m_ret m = Z_OK) by (apply (ihk_ret m COPY_); auto; unfold COPY_, DONE, BAD; lia).
  constructor; ihk_red; [exact Ki | lia | exact Kw | exact Ko | exact Kt | left; exact Rok | left; exact L0
                        | ihk_jc | ].
  apply J_COPY; [right; reflexivity | exact Pr | exact Ho | exact Bi | exact Ln | exact La | exact Ck | exact Fg
                | exact Rs | exact Bc | exact Dk].
Qed.

Lemma ihb_stored : ih_kit -> forall flush, case_ok STORED (c_STORED flush).
Proof.
  intros KIT flush g h0 pos inp m G HW X K L0 MD.
  pose proof (k_lay KIT g G) as LY. destruct (ihb_nh g LY) as [NH LEN].
  pose proof K as [Ki Kn Kw Ko Kt Kr Kl Kc Kj].
  assert (Rok: m_ret m = Z_OK) by (apply (ihk_ret m STORED); auto; unfold STORED, DONE, BAD; lia).
  unfold m_mode in MD.
  destruct Kj as [E|E|E|E|E|E|E|E|E|E| E La Pr B Ck Fg Rs Bc Dk |E|E|E|E|E]; try solve [ihk_nomode].
  pose proof X as (X0 & X1 & X2).
  (* BYTEBITS(): back to whole bytes *)
  assert (BB: m_bits (bytebits m) = 8 * (pos + m_nx (bytebits m) - (ih_nh g + 1)) /\
              m_hold (bytebits m) = ih_le (sublist (ih_nh g + 1) (pos + m_nx (bytebits m)) (ih_src g))).
  { unfold bytebits. ihk_red. destruct B as [[Bb Bh] | (Pe & Ho & Bi)].
    - rewrite Bb. rewrite Z.mul_comm, Z_mod_mult, Z.shiftr_0_r, Z.sub_0_r, <- Bh. split; [lia | reflexivity].
    - rewrite Bi, Ho, Pe. cbn. split; [lia | rewrite sublist_nil; reflexivity]. }
  destruct BB as [Bb Bh].
  unfold c_STORED. cbv zeta.
  destruct (k_nb KIT (ih_src g) inp pos (ih_nh g + 1) 32 (bytebits m) (ly_bytes _ LY) X0 X1 X2 Ki Kn
              ltac:(lia) ltac:(lia) ltac:(unfold bytebits; ihk_red; change ((32 + 7) / 8) with 4; lia) Bb Bh)
    as (nx' & lv' & EN & R & C).
  rewrite EN. unfold bytebits in *. ihk_red.
  change ((32 + 7) / 8) with 4 in C.
  destruct C as [(-> & -> & C) | (-> & C)].
  - rewrite Z.eqb_refl. cbn [ok_out].
    constructor; ihk_red; [exact Ki | lia | exact Kw | exact Ko | exact Kt | left; exact Rok | right; reflexivity
                          | ihk_jc | ].
    apply J_STORED; [exact E | exact La | lia | left; split; [lia | reflexivity] | exact Ck | exact Fg | exact Rs
                    | exact Bc | exact Dk].
  - rewrite L0. cbn [Z.eqb].
    assert (P5: pos + nx' = ih_nh g + 5) by lia.
    rewrite P5, (ihb_tail g 1 5 LY ltac:(lia) ltac:(lia)). cbn.
    destruct (Z.eqb_spec flush Z_TREES) as [FT|FT].
    + cbn [ok_out].
      constructor; ihk_red; [exact Ki | lia | exact Kw | exact Ko | exact Kt | left; exact Rok | right; reflexivity
                            | ihk_jc | ].
      apply J_COPY; [left; reflexivity | exact P5 | reflexivity | reflexivity | reflexivity | exact La | exact Ck
                    | exact Fg | exact Rs | exact Bc | exact Dk].
    + cbn [ok_out].
      constructor; ihk_red; [exact Ki | lia | exact Kw | exact Ko | exact Kt | left; exact Rok | left; reflexivity
                            | ihk_jc | ].
      apply J_TYPE; [left; reflexivity | right; split; [exact P5 | exact La] | reflexivity | reflexivity | exact Ck
                    | exact Fg | exact Rs | exact Bc | exact Dk].
Qed.

Lemma ihb_typedo_any : ih_kit -> forall flush g h0 pos inp m,
  ih_ok g -> hwf h0 -> ih_ctx g pos inp -> Km g h0 pos inp m -> m_leave m = 0 ->
  (m_mode m = Zlib.proof.inflate.Model.TYPE \/ m_mode m = TYPEDO) ->
  ok_out g h0 pos inp (c_TYPEDO flush m).
Proof.
  intros KIT flush g h0 pos inp m G HW X K L0 MD.
  pose proof (k_lay KIT g G) as LY. destruct (ihb_nh g LY) as [NH LEN].
  pose proof K as [Ki Kn Kw Ko Kt Kr Kl Kc Kj].
  assert (Rok: m_ret m = Z_OK).
  { destruct MD as [MD|MD]; [apply (ihk_ret m Zlib.proof.inflate.Model.TYPE) | apply (ihk_ret m TYPEDO)]; auto;
    unfold Zlib.proof.inflate.Model.TYPE, TYPEDO, DONE, BAD; lia. }
  unfold m_mode in MD.
  destruct Kj as [E|E|E|E|E|E|E|E|E| E Pl Ho Bi Ck Fg Rs Bc Dk |E|E|E|E|E|E]; try solve [ihk_nomode].
  pose proof X as (X0 & X1 & X2).
  unfold c_TYPEDO. cbv zeta.
  destruct Pl as [(Pe & La) | (Pe & La)].
  - (* the block header: NEEDBITS(3) *)
    rewrite La. cbn [Z.eqb negb].
    destruct (k_nb KIT (ih_src g) inp pos (ih_nh g) 3 m (ly_bytes _ LY) X0 X1 X2 Ki Kn ltac:(lia) ltac:(lia)
                ltac:(change ((3 + 7) / 8) with 1; lia) ltac:(rewrite Bi, Pe; lia)
                ltac:(rewrite Ho, Pe, sublist_nil; reflexivity))
      as (nx' & lv' & EN & R & C).
    rewrite EN. ihk_red.
    change ((3 + 7) / 8) with 1 in C.
    destruct C as [(-> & -> & C) | (-> & C)].
    + rewrite Z.eqb_refl. cbn [ok_out].
      assert (Pe': pos + Zlength inp = ih_nh g) by lia.
      constructor; ihk_red; [exact Ki | lia | exact Kw | exact Ko | exact Kt | left; exact Rok | right; reflexivity
                            | ihk_jc | ].
      rewrite Pe', sublist_nil, Z.sub_diag.
      apply J_TYPE; [exact E | left; split; [reflexivity | exact La] | reflexivity | reflexivity | exact Ck | exact Fg
                    | exact Rs | exact Bc | exact Dk].
    + rewrite L0. cbn [Z.eqb].
      assert (P1: pos + nx' = ih_nh g + 1) by lia.
      assert (B1: ih_le (sublist (ih_nh g) (ih_nh g + 1) (ih_src g)) = 1).
      { rewrite <- (Z.add_0_r (ih_nh g)) at 1. rewrite (ihb_tail g 0 1 LY ltac:(lia) ltac:(lia)). reflexivity. }
      rewrite P1, B1. replace (8 * (ih_nh g + 1 - ih_nh g)) with 8 by lia.
      unfold bitsn, dropbits. ihk_red. cbn [Z.eqb Z.shiftr Z.modulo Z.pow u32].
      replace (Z.shiftr 1 1 mod Z.pow_pos 2 2 =? 0) with true by reflexivity.
      cbn [ok_out].
      constructor; ihk_red; [exact Ki | lia | exact Kw | exact Ko | exact Kt | left; exact Rok | left; reflexivity
                            | ihk_jc | ].
      apply J_STORED; [reflexivity | reflexivity | lia | right; split; [lia | split; reflexivity] | exact Ck
                      | exact Fg | exact Rs | exact Bc | exact Dk].
  - (* last block done: CHECK *)
    rewrite La. cbn [Z.eqb negb]. cbn [ok_out].
    constructor; ihk_red; [exact Ki | lia | exact Kw | exact Ko | exact Kt | left; exact Rok | left; exact L0
                          | ihk_jc | ].
    apply J_CHECK; [reflexivity | lia | | exact Ck | exact Fg | exact Rs | exact Bc | exact Dk].
    rewrite Bi, Ho, Pe. apply ihk_bb0.
Qed.

Lemma ihb_typedo : ih_kit -> forall flush, case_ok TYPEDO (c_TYPEDO flush).
Proof. intros KIT flush g h0 pos inp m G HW X K L0 MD. apply (ihb_typedo_any KIT); auto. Qed.

Lemma ihb_type : ih_kit -> forall flush, case_ok Zlib.proof.inflate.Model.TYPE (c_TYPE flush).
Proof.
  intros KIT flush g h0 pos inp m G HW X K L0 MD.
  unfold c_TYPE.
  destruct ((flush =? Z_BLOCK) || (flush =? Z_TREES))%bool.
  - pose proof K as [Ki Kn Kw Ko Kt Kr Kl Kc Kj]. cbn [ok_out].
    constructor; ihk_red; [exact Ki | lia | exact Kw | exact Ko | exact Kt | exact Kr | right; reflexivity
                          | ihk_jc | exact Kj].
  - apply (ihb_typedo_any KIT); auto.
Qed.

Lemma ihc_blk : ihc_block_stmt.
Proof.
  intros KIT.
  split; [exact (ihb_type KIT)|]. split; [exact (ihb_typedo KIT)|]. split; [exact (ihb_stored KIT)|].
  split; [exact ihb_copy_|]. split; [exact ihb_copy|]. split; [exact (ihb_check KIT)|].
  split; [exact (ihb_length KIT)|]. split; [exact ihb_done | exact ihb_bad].
Qed.
