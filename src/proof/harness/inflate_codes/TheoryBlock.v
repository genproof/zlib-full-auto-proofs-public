(* Law inflate_codes, theory part: the cases STORED, COPY_, COPY, CHECK, LENGTH, DONE, BAD, MEM *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_codes.TheoryDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* the modes the cases of this group reach *)
Definition tb_md (x: Z) : Prop := md_block x \/ x = Zlib.proof.inflate.Model.TYPE.

Definition tb_P (wrap: Z) (src: list Z) (pos: Z) (inp: list Z) (aout: Z) (o: iout) : Prop :=
  match o with
  | IBrk m' => Kc wrap src pos inp aout m' /\ (m_leave m' = 0 -> m_mode m' <> DICT)
  | IRet _ _ => False
  end.

Lemma tb_md_ne x : tb_md x -> x <> SYNC /\ x <> HEAD /\ x <> DICTID /\ x <> DICT.
Proof.
  unfold tb_md, md_block. intros H.
  repeat match type of H with _ \/ _ => destruct H as [H|H] end; subst x;
  unfold STORED, COPY_, COPY, CHECK, LENGTH, DONE, BAD, MEM, Zlib.proof.inflate.Model.TYPE,
    SYNC, HEAD, DICTID, DICT; repeat split; lia.
Qed.

Lemma tb_Kc wrap src pos inp aout m m' :
  Kc wrap src pos inp aout m ->
  m_inp m' = m_inp m -> m_aout m' = m_aout m -> i_wrap (m_s m') = i_wrap (m_s m) ->
  i_head (m_s m') = i_head (m_s m) ->
  tb_md (m_mode m') ->
  (m_mode m' <> BAD -> m_mode m' <> DONE -> m_ret m' = Z_OK) ->
  (m_leave m' = 1 ->
     (m_mode m' = DONE -> m_ret m' = Z_STREAM_END) /\ (m_mode m' = BAD -> m_ret m' = Z_DATA_ERROR)) ->
  (m_mode m' = BAD -> m_msg m' <> None) ->
  (m_mode m' <> BAD -> m_mode m' <> MEM -> 0 <= m_bits m' <= 31) ->
  (m_out m' <> m_aout m' -> 0 < m_nx m') ->
  Kc wrap src pos inp aout m'.
Proof.
  intros K Hi Ha Hw Hhd Hmd Hr Hrx Hmsg Hb Ho.
  destruct (tb_md_ne _ Hmd) as (N1 & N2 & N3 & N4).
  constructor; auto.
  - rewrite Hi; apply (kc_inp _ _ _ _ _ _ K).
  - rewrite Ha; apply (kc_aout _ _ _ _ _ _ K).
  - rewrite Hw; apply (kc_wrap _ _ _ _ _ _ K).
  - rewrite Hhd; apply (kc_head _ _ _ _ _ _ K).
  - intros _ E; contradiction.
  - intros E; contradiction.
  - intros E; contradiction.
Qed.

Lemma tb_brk wrap src pos inp aout m' :
  Kc wrap src pos inp aout m' -> tb_md (m_mode m') -> tb_P wrap src pos inp aout (IBrk m').
Proof.
  intros K Hmd. destruct (tb_md_ne _ Hmd) as (_ & _ & _ & N). cbn [tb_P]. split; auto.
Qed.

(* NEEDBITS(n): a success from bits < n pulled a byte *)
Lemma tb_nbf n k m :
  0 < n <= 32 -> 0 <= m_bits m <= 39 -> n <= m_bits m + 8 * Z.of_nat k ->
  0 <= m_nx m <= Zlength (m_inp m) ->
  exists nx' h' b' lv',
    needbits_f k n m = set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx') h') b') lv' /\
    m_nx m <= nx' <= Zlength (m_inp m) /\
    ((lv' = 1 /\ 0 <= b' < n) \/ (lv' = m_leave m /\ n <= b' <= 39 /\ (m_bits m < n -> m_nx m < nx'))).
Proof.
  intros Hn. revert m. induction k as [|k IH]; intros m Hb Hk Hx.
  - exists (m_nx m), (m_hold m), (m_bits m), (m_leave m). split; [destruct m; reflexivity|].
    split; [lia|]. right. lia.
  - cbn [needbits_f]. destruct (Z.ltb_spec (m_bits m) n) as [L|L].
    + destruct (Z.eqb_spec (m_have m) 0) as [H0|H0].
      * exists (m_nx m), (m_hold m), (m_bits m), 1. split; [destruct m; reflexivity|].
        split; [lia|]. left. split; [reflexivity|lia].
      * unfold m_have in H0.
        assert (Hb' : m_bits (pull m) = m_bits m + 8).
        { cbn [pull m_bits set_m_bits]. unfold u32. rewrite Z.mod_small; lia. }
        assert (Hx' : 0 <= m_nx (pull m) <= Zlength (m_inp (pull m))) by (cbn; lia).
        destruct (IH (pull m) ltac:(lia) ltac:(lia) Hx') as (nx' & h' & b' & lv' & E & R & C).
        rewrite E. exists nx', h', b', lv'. split; [destruct m; reflexivity|].
        cbn [pull m_nx m_inp m_leave set_m_nx set_m_hold set_m_bits] in R, C. split; [lia|].
        destruct C as [C|C]; [left; exact C|right; lia].
    + exists (m_nx m), (m_hold m), (m_bits m), (m_leave m). split; [destruct m; reflexivity|].
      split; [lia|]. right. lia.
Qed.

Lemma tb_nb m :
  0 <= m_bits m <= 31 -> 0 <= m_nx m <= Zlength (m_inp m) ->
  exists nx' h' b' lv',
    needbits 32 m = set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx') h') b') lv' /\
    m_nx m <= nx' <= Zlength (m_inp m) /\
    ((lv' = 1 /\ 0 <= b' < 32) \/ (lv' = m_leave m /\ 32 <= b' <= 39 /\ m_nx m < nx')).
Proof.
  intros Hb Hx. destruct (tb_nbf 32 4 m ltac:(lia) ltac:(lia) ltac:(cbn; lia) Hx)
    as (nx' & h' & b' & lv' & E & R & C).
  exists nx', h', b', lv'. split; [exact E|]. split; [exact R|]. lia.
Qed.

Ltac tb_red :=
  unfold m_mode, m_have, m_left in *;
  cbn [m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler m_msg m_tin m_tout
       m_snx m_sow set_m_s set_m_h set_m_nx set_m_hold set_m_bits set_m_leave set_m_msg set_m_adler
       set_m_ret set_m_out set_m_tout set_m_ow
       upd_s upd_h set_mode set_leave set_bad initbits bytebits andb negb
       i_mode i_wrap i_head i_length i_flags i_check i_total
       set_i_mode set_i_check set_i_length set_i_flags set_i_total] in *.

Lemma tb_01 : (0 =? 1) = false.
Proof. reflexivity. Qed.

Ltac tb_side :=
  tb_red;
  unfold tb_md, md_block, STORED, COPY_, COPY, CHECK, LENGTH, DONE, BAD, MEM,
    Zlib.proof.inflate.Model.TYPE, Z_OK, Z_STREAM_END, Z_DATA_ERROR in *;
  intros;
  repeat match goal with H: ?A -> _, H2: ?A |- _ => specialize (H H2) end;
  first [reflexivity | discriminate | lia | (exfalso; lia) | congruence | idtac].

Ltac tb_if :=
  match goal with |- tb_P _ _ _ _ _ (if ?c then _ else _) => destruct c end.

Lemma tb_done wrap src pos inp aout m :
  Kc wrap src pos inp aout m -> m_mode m = DONE -> 0 <= m_bits m <= 31 ->
  tb_P wrap src pos inp aout (c_DONE m).
Proof.
  intros K Hmd Hb. pose proof (kc_out _ _ _ _ _ _ K) as Ko.
  unfold c_DONE. apply tb_brk; [apply (tb_Kc wrap src pos inp aout m _ K)|]; tb_side.
Qed.

Lemma tb_bad wrap src pos inp aout m :
  Kc wrap src pos inp aout m -> m_mode m = BAD ->
  tb_P wrap src pos inp aout (c_BAD m).
Proof.
  intros K Hmd. pose proof (kc_out _ _ _ _ _ _ K) as Ko. pose proof (kc_msg _ _ _ _ _ _ K Hmd) as Hm.
  unfold c_BAD. apply tb_brk; [apply (tb_Kc wrap src pos inp aout m _ K)|]; tb_side.
Qed.

Lemma tb_length wrap src pos inp aout m :
  Kc wrap src pos inp aout m -> m_mode m = LENGTH -> m_leave m = 0 -> m_ret m = Z_OK ->
  0 <= m_bits m <= 31 -> 0 <= m_nx m <= Zlength (m_inp m) ->
  tb_P wrap src pos inp aout (c_LENGTH m).
Proof.
  intros K Hmd Hl Hret Hb Hx. pose proof (kc_out _ _ _ _ _ _ K) as Ko.
  unfold c_LENGTH. cbv beta zeta. tb_if.
  - destruct (tb_nb m Hb Hx) as (nx' & h' & b' & lv' & E & R & C). rewrite E. tb_red.
    destruct C as [[-> C]|[-> C]]; [rewrite Z.eqb_refl | rewrite Hl, tb_01].
    + apply tb_brk; [apply (tb_Kc wrap src pos inp aout m _ K)|]; tb_side.
    + tb_if.
      * apply tb_brk; [apply (tb_Kc wrap src pos inp aout m _ K)|]; tb_side.
      * apply tb_done; [apply (tb_Kc wrap src pos inp aout m _ K)| |]; tb_side.
  - apply tb_done; [apply (tb_Kc wrap src pos inp aout m _ K)| |]; tb_side.
Qed.

Lemma tb_check wrap src pos inp aout m :
  Kc wrap src pos inp aout m -> m_mode m = CHECK -> m_leave m = 0 -> m_ret m = Z_OK ->
  0 <= m_bits m <= 31 -> 0 <= m_nx m <= Zlength (m_inp m) ->
  tb_P wrap src pos inp aout (c_CHECK m).
Proof.
  intros K Hmd Hl Hret Hb Hx. pose proof (kc_out _ _ _ _ _ _ K) as Ko.
  unfold c_CHECK. cbv beta zeta. tb_if.
  - destruct (tb_nb m Hb Hx) as (nx' & h' & b' & lv' & E & R & C). rewrite E. tb_red.
    destruct C as [[-> C]|[-> C]]; [rewrite Z.eqb_refl | rewrite Hl, tb_01].
    + apply tb_brk; [apply (tb_Kc wrap src pos inp aout m _ K)|]; tb_side.
    + match goal with |- context [if ?c then set_m_adler _ _ else _] => destruct c end.
      * tb_if.
        -- apply tb_brk; [apply (tb_Kc wrap src pos inp aout m _ K)|]; tb_side.
        -- apply tb_length; [apply (tb_Kc wrap src pos inp aout m _ K)| | | | |]; tb_side.
      * tb_if.
        -- apply tb_brk; [apply (tb_Kc wrap src pos inp aout m _ K)|]; tb_side.
        -- apply tb_length; [apply (tb_Kc wrap src pos inp aout m _ K)| | | | |]; tb_side.
  - apply tb_length; [apply (tb_Kc wrap src pos inp aout m _ K)| | | | |]; tb_side.
Qed.

Lemma tb_copy wrap src pos inp aout m :
  Kc wrap src pos inp aout m -> m_mode m = COPY -> m_leave m = 0 -> m_ret m = Z_OK ->
  0 <= m_bits m <= 31 -> 0 <= m_nx m <= Zlength (m_inp m) -> Zlength (m_ow m) <= m_aout m ->
  0 <= i_length (m_s m) ->
  tb_P wrap src pos inp aout (c_COPY m).
Proof.
  intros K Hmd Hl Hret Hb Hx Ho Hlen. pose proof (kc_out _ _ _ _ _ _ K) as Ko.
  unfold c_COPY. cbv beta zeta. tb_if; [tb_if|].
  - apply tb_brk; [apply (tb_Kc wrap src pos inp aout m _ K)|]; tb_side.
  - apply tb_brk; [apply (tb_Kc wrap src pos inp aout m _ K)|]; tb_side.
  - apply tb_brk; [apply (tb_Kc wrap src pos inp aout m _ K)|]; tb_side.
Qed.

Lemma tb_copy_ wrap src pos inp aout m :
  Kc wrap src pos inp aout m -> m_mode m = COPY_ -> m_leave m = 0 -> m_ret m = Z_OK ->
  0 <= m_bits m <= 31 -> 0 <= m_nx m <= Zlength (m_inp m) -> Zlength (m_ow m) <= m_aout m ->
  0 <= i_length (m_s m) ->
  tb_P wrap src pos inp aout (c_COPY_ m).
Proof.
  intros K Hmd Hl Hret Hb Hx Ho Hlen. pose proof (kc_out _ _ _ _ _ _ K) as Ko.
  unfold c_COPY_. apply tb_copy; [apply (tb_Kc wrap src pos inp aout m _ K)| | | | | | |]; tb_side.
Qed.

Lemma tb_stored wrap src pos inp aout flush m :
  Kc wrap src pos inp aout m -> m_mode m = STORED -> m_leave m = 0 -> m_ret m = Z_OK ->
  0 <= m_bits m <= 31 -> 0 <= m_nx m <= Zlength (m_inp m) -> Zlength (m_ow m) <= m_aout m ->
  tb_P wrap src pos inp aout (c_STORED flush m).
Proof.
  intros K Hmd Hl Hret Hb Hx Ho. pose proof (kc_out _ _ _ _ _ _ K) as Ko.
  assert (Bb : 0 <= m_bits (bytebits m) <= 31).
  { cbn [bytebits m_bits set_m_bits set_m_hold]. pose proof (Z.mod_pos_bound (m_bits m) 8).
    pose proof (Z.mod_le (m_bits m) 8). lia. }
  assert (Bx : 0 <= m_nx (bytebits m) <= Zlength (m_inp (bytebits m))) by (cbn; lia).
  unfold c_STORED. cbv beta zeta.
  destruct (tb_nb (bytebits m) Bb Bx) as (nx' & h' & b' & lv' & E & R & C). rewrite E. tb_red.
  destruct C as [[-> C]|[-> C]]; [rewrite Z.eqb_refl | rewrite Hl, tb_01].
  - apply tb_brk; [apply (tb_Kc wrap src pos inp aout m _ K)|]; tb_side.
  - tb_if; [apply tb_brk; [apply (tb_Kc wrap src pos inp aout m _ K)|]; tb_side|].
    tb_if; [apply tb_brk; [apply (tb_Kc wrap src pos inp aout m _ K)|]; tb_side|].
    apply tb_copy_; [apply (tb_Kc wrap src pos inp aout m _ K)| | | | | | |]; tb_side.
    apply Z.mod_pos_bound; lia.
Qed.

Lemma tb_post wrap src pos inp aout m o :
  tb_P wrap src pos inp aout o -> step_post wrap src pos inp aout m o.
Proof. destruct o; cbn; tauto. Qed.

Lemma th_block : block_stmt.
Proof.
  intros wrap src pos inp aout flush m Hc K Hw Hl Hmd.
  pose proof (proj1 Hw) as W.
  pose proof (Inv.mw_nx _ W) as Hx. pose proof (proj1 (Inv.mw_ow _ W)) as Ho.
  pose proof (Inv.sw_length _ (Inv.mw_s _ W)) as Hlen. unfold urange in Hlen.
  unfold md_block in Hmd.
  assert (Hret : m_mode m <> BAD -> m_mode m <> DONE -> m_ret m = Z_OK) by apply (kc_ret _ _ _ _ _ _ K).
  assert (Hb : m_mode m <> BAD -> m_mode m <> MEM -> 0 <= m_bits m <= 31) by apply (kc_bits _ _ _ _ _ _ K).
  repeat match type of Hmd with _ \/ _ => destruct Hmd as [Hmd|Hmd] end;
  rewrite Hmd in Hret, Hb;
  unfold STORED, COPY_, COPY, CHECK, LENGTH, DONE, BAD, MEM in Hret, Hb;
  try specialize (Hret ltac:(lia) ltac:(lia)); try specialize (Hb ltac:(lia) ltac:(lia)).
  - replace (stepf2 _ _ _ m) with (c_STORED flush m) by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    apply tb_post, tb_stored; auto.
  - replace (stepf2 _ _ _ m) with (c_COPY_ m) by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    apply tb_post, tb_copy_; auto; lia.
  - replace (stepf2 _ _ _ m) with (c_COPY m) by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    apply tb_post, tb_copy; auto; lia.
  - replace (stepf2 _ _ _ m) with (c_CHECK m) by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    apply tb_post, tb_check; auto.
  - replace (stepf2 _ _ _ m) with (c_LENGTH m) by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    apply tb_post, tb_length; auto.
  - replace (stepf2 _ _ _ m) with (c_DONE m) by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    apply tb_post, tb_done; auto.
  - replace (stepf2 _ _ _ m) with (c_BAD m) by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    apply tb_post, tb_bad; auto.
  - replace (stepf2 _ _ _ m) with (IRet Z_MEM_ERROR m) by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    cbn [step_post]. left. auto.
Qed.
