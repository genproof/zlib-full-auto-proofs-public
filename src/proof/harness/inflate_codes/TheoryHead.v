(* Law inflate_codes, theory part: the case HEAD (header tracking into DICTID) *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_codes.TheoryDefs.
Import ListNotations.
Local Open Scope Z_scope.

Lemma thh_byte src pos inp k :
  ctx_ok src pos inp -> 0 <= k < Zlength inp ->
  Znth k inp = Znth (pos + k) src /\ 0 <= Znth (pos + k) src <= 255.
Proof.
  intros (Hp & Hl & Hb & He) Hk. split; [apply He; auto|].
  unfold bytes_ok in Hb. rewrite Forall_forall in Hb.
  assert (0 <= pos + k < Zlength src) by lia.
  pose proof (Hb (Znth (pos + k) src)) as X. replace Byte.max_unsigned with 255 in X by reflexivity.
  apply X. apply Znth_In; lia.
Qed.

Lemma thh_pull m src pos :
  ctx_ok src pos (m_inp m) -> 0 <= m_nx m < Zlength (m_inp m) ->
  0 <= pos + m_nx m <= 1 -> m_bits m = 8 * (pos + m_nx m) ->
  m_hold m = le_val (sublist 0 (pos + m_nx m) src) ->
  pull m = set_m_bits (set_m_hold (set_m_nx m (m_nx m + 1)) (le_val (sublist 0 (pos + (m_nx m + 1)) src)))
                      (8 * (pos + (m_nx m + 1))).
Proof.
  intros Hc Hn Hp Hb Hh.
  destruct (thh_byte src pos (m_inp m) (m_nx m) Hc Hn) as [Eb Rb].
  pose proof Hc as (H0 & Hl & _).
  unfold pull. rewrite Eb, Hb, Hh. f_equal; [f_equal|].
  - assert (pos + m_nx m = 0 \/ pos + m_nx m = 1) as [E|E] by lia.
    + rewrite E in *. replace (pos + (m_nx m + 1)) with 1 by lia.
      rewrite (sublist_one 0 1 src) by lia. rewrite sublist_nil. cbn [le_val].
      change (2 ^ (8 * 0)) with 1. unfold u64. rewrite Z.mod_small; lia.
    + rewrite E in *. replace (pos + (m_nx m + 1)) with 2 by lia.
      rewrite (sublist_one 0 1 src) by lia.
      rewrite (sublist_split 0 1 2 src), (sublist_one 0 1 src), (sublist_one 1 2 src) by lia.
      cbn [le_val app].
      assert (0 <= Znth 0 src <= 255).
      { destruct Hc as (_ & _ & Hbo & _). unfold bytes_ok in Hbo. rewrite Forall_forall in Hbo.
        pose proof (Hbo (Znth 0 src)) as X. replace Byte.max_unsigned with 255 in X by reflexivity. apply X, Znth_In; lia. }
      change (2 ^ (8 * 1)) with 256. unfold u64. rewrite Z.mod_small; lia.
  - unfold u32. rewrite Z.mod_small; lia.
Qed.

Lemma thh_same m : set_m_bits (set_m_hold (set_m_nx m (m_nx m)) (m_hold m)) (m_bits m) = m.
Proof. destruct m; reflexivity. Qed.

Lemma thh_nbS k n m :
  needbits_f (S k) n m = if m_bits m <? n then if m_have m =? 0 then set_leave m else needbits_f k n (pull m) else m.
Proof. reflexivity. Qed.

Lemma thh_nb m src pos :
  ctx_ok src pos (m_inp m) -> 0 <= m_nx m <= Zlength (m_inp m) ->
  hd_head src (pos + m_nx m) (m_hold m) (m_bits m) ->
  exists nx', m_nx m <= nx' <= Zlength (m_inp m) /\
   ((needbits 16 m = set_leave (set_m_bits (set_m_hold (set_m_nx m nx') (le_val (sublist 0 (pos + nx') src)))
                                          (8 * (pos + nx'))) /\ pos + nx' <= 1) \/
    (needbits 16 m = set_m_bits (set_m_hold (set_m_nx m nx') (le_val (sublist 0 2 src))) 16 /\ pos + nx' = 2)).
Proof.
  intros Hc Hn (Hp & Hb & Hh). unfold needbits. rewrite thh_nbS.
  rewrite Hb. replace (8 * (pos + m_nx m) <? 16) with true by (symmetry; apply Z.ltb_lt; lia).
  destruct (m_have m =? 0) eqn:E0.
  { exists (m_nx m). split; [lia|]. left. split; [|lia]. rewrite <- Hh, <- Hb, thh_same. reflexivity. }
  unfold m_have in E0. apply Z.eqb_neq in E0.
  rewrite (thh_pull m src pos) by (auto; lia).
  set (m1 := set_m_bits _ _).
  assert (Hc1 : ctx_ok src pos (m_inp m1)) by exact Hc.
  change (m_inp m1) with (m_inp m) in Hc1.
  assert (Hnx1 : m_nx m1 = m_nx m + 1) by reflexivity.
  assert (Hb1 : m_bits m1 = 8 * (pos + (m_nx m + 1))) by reflexivity.
  assert (Hh1 : m_hold m1 = le_val (sublist 0 (pos + (m_nx m + 1)) src)) by reflexivity.
  assert (Hi1 : m_inp m1 = m_inp m) by reflexivity.
  assert (pos + m_nx m = 0 \/ pos + m_nx m = 1) as [P|P] by lia.
  - rewrite thh_nbS, Hb1. replace (8 * (pos + (m_nx m + 1)) <? 16) with true by (symmetry; apply Z.ltb_lt; lia).
    destruct (m_have m1 =? 0) eqn:E1.
    { exists (m_nx m + 1). split; [lia|]. left. split; [|lia].
      reflexivity. }
    unfold m_have in E1. apply Z.eqb_neq in E1. rewrite Hi1, Hnx1 in E1.
    rewrite (thh_pull m1 src pos) by (rewrite ?Hi1, ?Hnx1; auto; lia).
    rewrite thh_nbS. cbn [m_bits set_m_bits]. rewrite Hnx1.
    replace (8 * (pos + (m_nx m + 1 + 1)) <? 16) with false by (symmetry; apply Z.ltb_ge; lia).
    exists (m_nx m + 1 + 1). split; [lia|]. right. split; [|lia].
    replace (pos + (m_nx m + 1 + 1)) with 2 by lia. unfold m1.
    destruct m; reflexivity.
  - rewrite thh_nbS, Hb1. replace (8 * (pos + (m_nx m + 1)) <? 16) with false by (symmetry; apply Z.ltb_ge; lia).
    exists (m_nx m + 1). split; [lia|]. right. split; [|lia].
    unfold m1. replace (pos + (m_nx m + 1)) with 2 by lia. reflexivity.
Qed.

Lemma thh_Kc wrap src pos inp aout m m' :
  Kc wrap src pos inp aout m -> m_mode m = HEAD -> m_leave m = 0 ->
  m_inp m' = m_inp m -> m_aout m' = m_aout m -> i_wrap (m_s m') = i_wrap (m_s m) ->
  i_head (m_s m') = i_head (m_s m) -> m_out m' = m_out m -> m_ret m' = m_ret m -> m_nx m <= m_nx m' ->
  m_mode m' <> SYNC -> m_mode m' <> DONE -> m_mode m' <> DICT ->
  (m_leave m' = 0 \/ m_mode m' = HEAD) ->
  (m_mode m' = BAD -> m_msg m' <> None) ->
  (m_mode m' <> BAD -> 0 <= m_bits m' <= 31) ->
  (wrap <> 0 -> m_mode m' = HEAD -> hd_head src (pos + m_nx m') (m_hold m') (m_bits m')) ->
  (m_mode m' = DICTID -> Z.land wrap 1 <> 0 /\ hd_dictid src (pos + m_nx m') (m_hold m') (m_bits m')) ->
  Kc wrap src pos inp aout m'.
Proof.
  intros K Hmd Hl Hi Ha Hw Hh Ho Hr Hn Hs Hd Hdi Hlv Hmsg Hb Hhd Hdid.
  constructor.
  - rewrite Hi; apply (kc_inp _ _ _ _ _ _ K).
  - rewrite Ha; apply (kc_aout _ _ _ _ _ _ K).
  - rewrite Hw; apply (kc_wrap _ _ _ _ _ _ K).
  - rewrite Hh; apply (kc_head _ _ _ _ _ _ K).
  - exact Hs.
  - intros B D. rewrite Hr. apply (kc_ret _ _ _ _ _ _ K); rewrite Hmd; unfold HEAD, BAD, DONE; lia.
  - intros L. destruct Hlv as [Hlv|Hlv]; [lia|]. rewrite Hlv; unfold HEAD, BAD, DONE; split; intro; lia.
  - exact Hmsg.
  - intros B _. auto.
  - intros O. rewrite Ho, Ha in O. pose proof (kc_out _ _ _ _ _ _ K O). lia.
  - exact Hhd.
  - exact Hdid.
  - intros D; contradiction.
Qed.

Definition thh_upto (n: nat) : list Z := map Z.of_nat (seq 0 n).

Lemma thh_in_upto x n : 0 <= x < Z.of_nat n -> In x (thh_upto n).
Proof. intros. unfold thh_upto. apply in_map_iff. exists (Z.to_nat x). split; [lia|]. apply in_seq; lia. Qed.

Lemma thh_fd_tab :
  forallb (fun c => forallb (fun b => Bool.eqb (Z.land (c + 16 * b) 512 =? 0) (Z.land b 32 =? 0))
                            (thh_upto 256)) (thh_upto 16) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma thh_fdict b0 b1 : 0 <= b0 <= 255 -> 0 <= b1 <= 255 ->
  (Z.land (Z.shiftr (b0 + 256 * (b1 + 256 * 0)) 4) 512 =? 0) = (Z.land b1 32 =? 0).
Proof.
  intros H0 H1. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
  replace (b0 + 256 * (b1 + 256 * 0)) with (b0 + (16 * b1) * 16) by lia.
  rewrite Z.div_add by lia.
  pose proof thh_fd_tab as T. rewrite forallb_forall in T.
  assert (0 <= b0 / 16 < 16) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  specialize (T (b0 / 16) (thh_in_upto (b0 / 16) 16 ltac:(change (Z.of_nat 16) with 16; lia))).
  rewrite forallb_forall in T. specialize (T b1 (thh_in_upto b1 256 ltac:(change (Z.of_nat 256) with 256; lia))).
  apply Bool.eqb_prop in T. exact T.
Qed.

Ltac thh_red :=
  unfold m_mode; cbn [m_nx m_bits m_hold m_msg m_s m_inp m_aout m_out m_ret m_leave m_adler
       set_mode upd_s set_m_s set_m_h upd_h set_m_nx set_m_hold set_m_bits set_m_msg set_m_adler
       set_leave set_m_leave set_bad initbits dropbits
       i_mode i_wrap i_head set_i_mode set_i_check set_i_wbits set_i_flags set_i_dmax].

Ltac thh_side :=
  repeat match goal with x := _ |- _ => subst x end;
  thh_red; try match goal with H: i_mode (m_s ?x) = HEAD |- _ => rewrite H end; unfold HEAD, FLAGS, DICTID, TYPEDO, SYNC, DONE, DICT, BAD, Zlib.proof.inflate.Model.TYPE;
  intros; first [lia | congruence | discriminate].

Lemma thh_lv1 x : (m_leave (set_leave x) =? 1) = true.
Proof. reflexivity. Qed.

Lemma th_head : head_stmt.
Proof.
  intros wrap src pos inp aout flush m Hc K Hw Hl Hmd. unfold md_head in Hmd.
  pose proof (Inv.mw_nx _ (proj1 Hw)) as Hnx.
  pose proof (kc_inp _ _ _ _ _ _ K) as Hinp. subst inp.
  assert (HB : 0 <= m_bits m <= 31)
    by (apply (kc_bits _ _ _ _ _ _ K); rewrite Hmd; unfold HEAD, BAD, MEM; lia).
  pose proof Hc as (Hpos & Hsrc & Hbytes & _).
  assert (Hmd' : i_mode (m_s m) = HEAD) by exact Hmd.
  unfold stepf2, step2. cbv beta zeta. rewrite Hmd, Z.eqb_refl.
  unfold c_HEAD2. cbv beta zeta. rewrite (kc_wrap _ _ _ _ _ _ K).
  destruct (Z.eqb_spec wrap 0) as [W0|W0].
  { cbn [step_post]. split.
    - apply (thh_Kc wrap src pos (m_inp m) aout m); auto; thh_side.
    - thh_side. }
  pose proof (kc_hd _ _ _ _ _ _ K W0 Hmd) as Hhd.
  destruct (thh_nb m src pos Hc Hnx Hhd) as (nx' & Hn' & [[E Hp]|[E Hp]]); rewrite E.
  { rewrite thh_lv1. cbn [step_post]. split.
    - apply (thh_Kc wrap src pos (m_inp m) aout m); auto; try thh_side.
      thh_red. intros _ _. unfold hd_head. split; [lia|]. split; reflexivity.
    - thh_side. }
  set (H2 := le_val (sublist 0 2 src)).
  set (m2 := set_m_bits (set_m_hold (set_m_nx m nx') H2) 16).
  assert (E1 : (m_leave m2 =? 1) = false) by (cbn; rewrite Hl; reflexivity).
  assert (E2 : m_s m2 = m_s m) by reflexivity.
  assert (E3 : m_hold m2 = H2) by reflexivity.
  rewrite E1, E2, E3, (kc_wrap _ _ _ _ _ _ K), (kc_head _ _ _ _ _ _ K).
  cbv iota.
  destruct (andb (negb (Z.land wrap 2 =? 0)) (H2 =? 35615)) eqn:G.
  { cbn [step_post]. split.
    - apply (thh_Kc wrap src pos (m_inp m) aout m); auto; thh_side.
    - thh_side. }
  destruct (orb (Z.land wrap 1 =? 0) _) eqn:G1.
  { cbn [step_post]. split.
    - apply (thh_Kc wrap src pos (m_inp m) aout m); auto; thh_side.
    - thh_side. }
  apply orb_false_iff in G1. destruct G1 as [G1 _]. apply Z.eqb_neq in G1.
  destruct (negb (m_hold m2 mod 16 =? 8)).
  { cbn [step_post]. split.
    - apply (thh_Kc wrap src pos (m_inp m) aout m); auto; thh_side.
    - thh_side. }
  destruct (orb _ _).
  { cbn [step_post]. split.
    - apply (thh_Kc wrap src pos (m_inp m) aout m); auto; thh_side.
    - thh_side. }
  match goal with |- context [if Z.land ?x 512 =? 0 then _ else _] => destruct (Z.land x 512 =? 0) eqn:G3 end.
  { cbn [step_post]. split.
    - apply (thh_Kc wrap src pos (m_inp m) aout m); auto; thh_side.
    - thh_side. }
  cbn [step_post]. split.
  - apply (thh_Kc wrap src pos (m_inp m) aout m); auto; try thh_side.
    intros _. split; [exact G1|].
    assert (G3' : (Z.land (Z.shiftr H2 4) 512 =? 0) = false) by exact G3.
    assert (L2 : 2 <= Zlength src) by lia.
    assert (Bk : forall k, 0 <= k < 2 -> 0 <= Znth k src <= 255).
    { intros k Hk. unfold bytes_ok in Hbytes. rewrite Forall_forall in Hbytes.
      pose proof (Hbytes (Znth k src)) as X. replace Byte.max_unsigned with 255 in X by reflexivity.
      apply X, Znth_In; lia. }
    assert (EH : H2 = Znth 0 src + 256 * (Znth 1 src + 256 * 0)).
    { unfold H2. rewrite (sublist_split 0 1 2 src), (sublist_one 0 1 src), (sublist_one 1 2 src) by lia.
      reflexivity. }
    rewrite EH, thh_fdict in G3' by (apply Bk; lia).
    thh_red. unfold hd_dictid. split; [unfold fdict; apply Z.eqb_neq; exact G3'|].
    change (m_nx m2) with nx'.
    split; [lia|]. split; [lia|]. rewrite Hp, sublist_nil. reflexivity.
  - thh_side.
Qed.
