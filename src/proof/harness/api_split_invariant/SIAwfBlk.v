(* The abstract steps of the block modes (TYPE, TYPEDO, STORED, COPY_, COPY, CHECK, LENGTH) keep the
   invariant awfx (SIAwfKit.v).  A fixed block enters the decode modes with inffixed.h's tables (valid,
   replicated, distances up to 32768); the other steps go to plain modes (no table in use). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_split_invariant.SIDefs.
Require Import Zlib.proof.harness.api_split_invariant.SIAwfKit.
Require Zlib.proof.inflate.Step3Header Zlib.proof.inflate.Step3Block.
Import ListNotations.
Local Open Scope Z_scope.

(* a step from a block mode to a plain mode of the data or post phase: the frame of a; the flags and
   the check of a when the new mode is a data mode *)
Lemma go_blk: forall src a n w s O,
  awfx src a -> data_mode (a_mode a) -> a_q a <= n -> swf s ->
  Step3Block.plain_md (i_mode s) -> Model.TYPE <= i_mode s <= BAD ->
  i_wbits s = i_wbits (a_s a) -> i_wrap s = i_wrap (a_s a) -> i_havedict s = i_havedict (a_s a) ->
  i_head s = i_head (a_s a) -> i_back s = i_back (a_s a) ->
  (data_mode (i_mode s) -> i_flags s = i_flags (a_s a) /\ i_check s = i_check (a_s a)) ->
  (O = a_O a \/ (w = true /\ exists b, 0 <= b <= 255 /\ O = a_O a ++ [b])) ->
  go_ok src a (AGo n w (AS s n O)).
Proof.
  intros src a n w s O W D Q S P MR E1 E2 E3 E4 E5 FC EO.
  destruct (ax_frame _ _ W) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
  unfold go_ok. cbn [a_q a_O]. split; [|split; [exact Q | split; [reflexivity|]]].
  2:{ destruct EO as [-> | (Hw & b & _ & ->)]; [left; auto | right; eauto]. }
  apply awfx_plain; auto.
  all: try congruence.
  all: try apply (ax_src _ _ W).
  all: try (rewrite E2; assumption).
  all: try (intros ->; clear -MR; mdc; lia).
  all: try (clear -MR; mdc; lia).
  all: try lia.
  all: try (destruct EO as [-> | (_ & b & B & ->)]; [auto | apply bytes_app1; auto]).
  all: try (intros H; exfalso; clear -MR H; unfold hdr_mode in H; mdc; lia).
  all: try (intros H; exfalso; clear -MR H; mdc; lia).
  intros DS NZ. destruct (FC DS) as [G1 G2]. rewrite G1, G2.
  apply (aw_chk _ _ (ax_w _ _ W) D). congruence.
Qed.

(* the same state at a later bit position *)
Lemma awfx_at: forall src a n, awfx src a -> a_q a <= n -> awfx src (AS (a_s a) n (a_O a)).
Proof. intros src a n [[] ? ?] Q. constructor; [constructor|..]; simpl; auto; lia. Qed.

Ltac bfin :=
  try (apply MwfLemmas.swf_set_mode; [assumption | clear; mdc; lia]);
  try (clear; unfold Step3Block.plain_md, decode_mode; mdc; lia);
  try (clear; mdc; lia);
  try (intros _; split; reflexivity);
  try (left; reflexivity).

Lemma data_TYPE: data_mode Model.TYPE. Proof. unfold data_mode; auto. Qed.

Lemma awf_TYPE : case_ok Model.TYPE.
Proof.
  intros src a W M. rewrite astep_TYPE by exact M. unfold a_TYPE, ago.
  pose proof (ax_swf _ _ W) as S.
  apply go_blk; simpl; auto; try lia; [rewrite M; apply data_TYPE | ..]; bfin.
Qed.

Lemma awf_COPY_ : case_ok COPY_.
Proof.
  intros src a W M. rewrite astep_COPY_ by exact M. unfold a_COPY_, ago.
  pose proof (ax_swf _ _ W) as S.
  apply go_blk; simpl; auto; try lia; [rewrite M; unfold data_mode; mdc; lia | ..]; bfin.
Qed.

Lemma awf_COPY : case_ok COPY.
Proof.
  intros src a W M. rewrite astep_COPY by exact M. unfold a_COPY, ago.
  pose proof (ax_swf _ _ W) as S. pose proof (ax_src _ _ W) as B.
  assert (D: data_mode (a_mode a)) by (rewrite M; unfold data_mode; mdc; lia).
  destruct (i_length (a_s a) =? 0) eqn:L0; cbn [negb].
  - apply go_blk; simpl; auto; try lia; bfin.
  - apply Z.eqb_neq in L0. pose proof (sw_length _ S) as LR.
    apply go_blk; simpl; auto; try lia; bfin.
    all: try (destruct S; constructor; simpl; auto; unfold urange in *; lia).
    all: try (change (i_mode (a_s a)) with (a_mode a); rewrite M; clear; unfold Step3Block.plain_md, decode_mode; mdc; lia).
    all: try (change (i_mode (a_s a)) with (a_mode a); rewrite M; clear; mdc; lia).
    right. split; [reflexivity|]. exists (sbyte src (a_q a)). split; [apply sbyte_range; auto | reflexivity].
Qed.

Lemma awf_STORED : case_ok STORED.
Proof.
  intros src a W M. rewrite astep_STORED by exact M. unfold a_STORED.
  pose proof (ax_swf _ _ W) as S. destruct (ax_frame _ _ W) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
  assert (D: data_mode (a_mode a)) by (rewrite M; unfold data_mode; mdc; lia).
  cbv zeta. destruct (a_q a mod 8 =? 0); cbn [negb].
  - set (h := sbits src (a_q a) 32).
    destruct (Z.land h 65535 =? Z.lxor (Z.shiftr h 16) 65535); cbn [negb].
    + unfold ago. apply go_blk; simpl; auto; try lia; bfin.
      pose proof (Z.mod_pos_bound h 65536 ltac:(lia)).
      destruct S; constructor; simpl; auto; try (clear; mdc; lia). unfold urange. rep_lia.
    + apply go_abad; auto; lia.
  - pose proof (align8_ge (a_q a)). unfold go_ok, ago. cbn [a_q a_O].
    split; [apply awfx_at; auto | split; [auto | split; [reflexivity | left; reflexivity]]].
Qed.

(* the fixed block's state: the decode mode LEN_ with inffixed.h's tables *)
Lemma awf_fixed: forall src a s n,
  awfx src a -> data_mode (a_mode a) -> swf s -> 0 <= n ->
  i_wbits s = i_wbits (a_s a) -> i_wrap s = i_wrap (a_s a) -> i_havedict s = i_havedict (a_s a) ->
  i_head s = i_head (a_s a) -> i_back s = i_back (a_s a) -> i_flags s = i_flags (a_s a) ->
  i_check s = i_check (a_s a) -> tabrep_stmt ->
  awfx src (AS (set_i_mode (set_i_distbits (set_i_distcode (set_i_lenbits (set_i_lencode s TLenfix) 9)
                                             TDistfix) 5) LEN_) n (a_O a)).
Proof.
  intros src a s n W D S N E1 E2 E3 E4 E5 E6 E7 TR.
  destruct (ax_frame _ _ W) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
  set (s' := set_i_mode (set_i_distbits (set_i_distcode (set_i_lenbits (set_i_lencode s TLenfix) 9) TDistfix) 5) LEN_).
  destruct (tvalid_fixed s') as (TL & TD & TLL).
  destruct TR as (_ & RL & RD & _ & DF).
  assert (X1: i_wbits s = 15) by congruence.
  assert (X2: i_wrap s = 0 \/ i_wrap s = 5 \/ i_wrap s = 6 \/ i_wrap s = 7) by (rewrite E2; exact F2).
  assert (X3: i_havedict s = 0) by congruence.
  assert (X4: i_head s = false) by congruence.
  assert (X5: i_back s <= 15) by (rewrite E5; exact F5).
  assert (X6: i_wrap s <> 0 -> (i_flags s = 0 /\ i_check s = 1) \/ (i_flags s <> 0 /\ i_check s = 0)).
  { intros NZ. rewrite E6, E7. apply (aw_chk _ _ (ax_w _ _ W) D). congruence. }
  assert (DO: forall src' q, dist_ok (fst (adecode lenfix_list distfix_list src' s' TDistfix 5 dist_islink q))).
  { intros src' q.
    apply (adecode_prop DISTS lenfix_list distfix_list src' s' TDistfix 5 32 q dist_ok (tvalid_b_distfix s')).
    intros i Hi. simpl. apply (proj1 (Forall_Znth _ _) DF). rewrite FixedValid2.distfix_len. lia. }
  assert (S': swf s') by (destruct S; constructor; simpl; auto; clear; unfold tref_ok; mdc; lia).
  apply awfx_decode; simpl; auto; try (clear; mdc; lia).
  - apply (ax_src _ _ W).
  - unfold decode_mode; auto.
Qed.

Lemma awf_TYPEDO_gen : tabrep_stmt -> forall src a, awfx src a -> data_mode (a_mode a) ->
  go_ok src a (a_TYPEDO src a).
Proof.
  intros TR src a W D. unfold a_TYPEDO.
  pose proof (ax_swf _ _ W) as S. pose proof (ax_src _ _ W) as B.
  destruct (ax_frame _ _ W) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
  cbv zeta. destruct (i_last (a_s a) =? 0); cbn [negb].
  2:{ unfold ago. pose proof (align8_ge (a_q a)). apply go_blk; simpl; auto; try lia; bfin. }
  set (s1 := set_i_last (a_s a) (sbits src (a_q a) 1)).
  assert (S1: swf s1).
  { pose proof (sbits_range src (a_q a) 1 ltac:(lia)). destruct S; constructor; simpl; auto. lia. }
  set (bt := sbits src (a_q a + 1) 2).
  destruct (bt =? 0).
  { unfold ago. apply go_blk; simpl; auto; try lia; bfin. }
  destruct (bt =? 1).
  { unfold ago, go_ok. cbn [a_q a_O]. split; [|split; [lia | split; [reflexivity | left; reflexivity]]].
    apply awf_fixed; auto; lia. }
  destruct (bt =? 2).
  { unfold ago. apply go_blk; simpl; auto; try lia; bfin. }
  unfold abad, go_ok. cbn [a_q a_O a_s]. split; [|split; [lia | split; [reflexivity | left; reflexivity]]].
  apply awfx_bad; simpl; auto; lia.
Qed.

Lemma awf_TYPEDO : tabrep_stmt -> case_ok TYPEDO.
Proof.
  intros TR src a W M. rewrite astep_TYPEDO by exact M.
  apply awf_TYPEDO_gen; auto. rewrite M; unfold data_mode; auto.
Qed.

Lemma awf_CHECK : case_ok CHECK.
Proof.
  intros src a W M. rewrite astep_CHECK by exact M. unfold a_CHECK.
  pose proof (ax_swf _ _ W) as S. destruct (ax_frame _ _ W) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
  assert (D: data_mode (a_mode a)) by (rewrite M; unfold data_mode; mdc; lia).
  cbv zeta. destruct (i_wrap (a_s a) =? 0); cbn [negb].
  - unfold ago. apply go_blk; simpl; auto; try lia; bfin.
  - set (c := update_check (i_flags (a_s a)) (i_check (a_s a)) (a_O a)).
    assert (C: lrange c).
    { unfold c, update_check. destruct (i_flags (a_s a) =? 0).
      - pose proof (adler32_z_val_range (i_check (a_s a)) (a_O a) F7). unfold lrange; rep_lia.
      - apply Step3Header.ref_crc32_lrange; auto. }
    destruct (andb _ _); [apply go_abad; auto; lia|].
    unfold ago. apply go_blk; simpl; auto; try lia; bfin.
    all: try (destruct S; constructor; simpl; auto; clear; mdc; lia).
    all: intros H; exfalso; clear -H; unfold data_mode, decode_mode in H; mdc; lia.
Qed.

Lemma awf_LENGTH : case_ok LENGTH.
Proof.
  intros src a W M. rewrite astep_LENGTH by exact M. unfold a_LENGTH.
  pose proof (ax_swf _ _ W) as S. destruct (ax_frame _ _ W) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
  assert (G: forall n, a_q a <= n -> go_ok src a (ago a n (set_i_mode (a_s a) DONE))).
  { intros n Q. unfold ago, go_ok. cbn [a_q a_O a_s]. split; [|split; [lia | split; [reflexivity | left; reflexivity]]].
    apply awfx_plain; simpl; auto; try lia; bfin.
    all: try apply (ax_src _ _ W).
    all: try (intros H; exfalso; clear -H; unfold hdr_mode in H; mdc; lia).
    all: intros H; exfalso; clear -H; unfold data_mode, decode_mode in H; mdc; lia. }
  cbv zeta. destruct (andb _ _); [|apply G; lia].
  destruct (andb _ _); [apply go_abad; auto; lia | apply G; lia].
Qed.
