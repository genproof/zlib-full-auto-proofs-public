(* The abstract steps of the decode modes (LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT) keep the
   invariant awfx (SIAwfKit.v).  The tables are not changed; a code read with a valid table ends at a
   final entry (a literal, a length base 3..258 with 0..5 extra bits, a distance base 1..32768 with 0..13
   extra bits, the end of the block, or an invalid code), and the distance table's entries reach at most
   32768 (aw_dtab), so a match's distance stays within the window and its length is positive. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_split_invariant.SIDefs.
Require Import Zlib.proof.harness.api_split_invariant.SIAwfKit.
Require Import Zlib.proof.harness.api_split_invariant.SIAwfBlk.
Require Zlib.proof.inflate.Step3Block Zlib.proof.inflate.Step3Decode.
Import ListNotations.
Local Open Scope Z_scope.

(* a step between decode modes: the tables and the frame of a *)
Lemma go_dec: forall src a n w s O,
  awfx src a -> decode_mode (a_mode a) -> a_q a <= n -> swf s -> decode_mode (i_mode s) ->
  i_codes s = i_codes (a_s a) -> i_lencode s = i_lencode (a_s a) -> i_distcode s = i_distcode (a_s a) ->
  i_lenbits s = i_lenbits (a_s a) -> i_distbits s = i_distbits (a_s a) ->
  i_wbits s = i_wbits (a_s a) -> i_wrap s = i_wrap (a_s a) -> i_havedict s = i_havedict (a_s a) ->
  i_head s = i_head (a_s a) -> i_back s = i_back (a_s a) -> i_flags s = i_flags (a_s a) ->
  i_check s = i_check (a_s a) ->
  (i_mode s = LENEXT -> i_extra s <= 5 /\ i_length s <= 258) ->
  (i_mode s = DISTEXT -> i_extra s <= 13) ->
  (i_mode s = MATCH -> 1 <= i_length s) ->
  (i_mode s = LENEXT \/ i_mode s = DIST \/ i_mode s = DISTEXT -> 1 <= i_length s) ->
  (i_mode s = DISTEXT \/ i_mode s = MATCH -> 1 <= i_offset s) ->
  (i_mode s = MATCH -> i_offset s <= 32768) ->
  (i_mode s = DISTEXT -> i_offset s + 2 ^ i_extra s - 1 <= 32768) ->
  (O = a_O a \/ (w = true /\ exists b, 0 <= b <= 255 /\ O = a_O a ++ [b])) ->
  go_ok src a (AGo n w (AS s n O)).
Proof.
  intros src a n w s O W D Q S D' C1 C2 C3 C4 C5 F1 F2 F3 F4 F5 F6 F7 H1 H2 H3 H4 H5 H6 H7 EO.
  destruct (ax_frame _ _ W) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
  unfold go_ok. cbn [a_q a_O]. split; [|split; [exact Q | split; [reflexivity|]]].
  2:{ destruct EO as [-> | (Hw & b & _ & ->)]; [left; auto | right; eauto]. }
  apply awfx_decode_keep with a; auto; try lia.
  destruct EO as [-> | (_ & b & B & ->)]; [auto | apply bytes_app1; auto].
Qed.

Lemma dec_md: forall md, decode_mode md -> md <> HEAD.
Proof. intros md D. unfold decode_mode in D; mdc; lia. Qed.

(* the final entry of a literal/length code *)
Lemma adecode_len: forall src s q,
  tvalid LENS lenfix_list distfix_list s (i_lencode s) (i_lenbits s) ->
  let r := adecode lenfix_list distfix_list src s (i_lencode s) (i_lenbits s) len_islink q in
  entry_ok (fst r) /\ final_ok LENS (fst r) /\ 0 <= snd r <= 15.
Proof.
  intros src s q T. destruct (adecode_final LENS lenfix_list distfix_list src s (i_lencode s) (i_lenbits s) q T)
    as (A & B & _ & C). cbv zeta. auto.
Qed.

Lemma adecode_dist: forall src s q,
  tvalid DISTS lenfix_list distfix_list s (i_distcode s) (i_distbits s) ->
  let r := adecode lenfix_list distfix_list src s (i_distcode s) (i_distbits s) dist_islink q in
  entry_ok (fst r) /\ final_ok DISTS (fst r) /\ 0 <= snd r <= 15.
Proof.
  intros src s q T. destruct (adecode_final DISTS lenfix_list distfix_list src s (i_distcode s) (i_distbits s) q T)
    as (A & B & _ & C). cbv zeta. auto.
Qed.

Lemma land16: forall x, 16 <= x <= 31 -> Z.land x 16 = 16.
Proof.
  intros x H. assert (C: x = 16 \/ x = 17 \/ x = 18 \/ x = 19 \/ x = 20 \/ x = 21 \/ x = 22 \/ x = 23 \/
    x = 24 \/ x = 25 \/ x = 26 \/ x = 27 \/ x = 28 \/ x = 29 \/ x = 30 \/ x = 31) by lia.
  repeat destruct C as [C | C]; subst x; reflexivity.
Qed.

Ltac dfin :=
  try reflexivity;
  try (intros ?HM; exfalso; clear -HM; mdc; lia);
  try (intros [?HM | [?HM | ?HM]]; exfalso; clear -HM; mdc; lia);
  try (intros [?HM | ?HM]; exfalso; clear -HM; mdc; lia);
  try (left; reflexivity);
  try (unfold decode_mode; mdc; lia).

Lemma awf_LEN_ : case_ok LEN_.
Proof.
  intros src a W M. rewrite astep_LEN_ by exact M. unfold a_LEN_, ago.
  pose proof (ax_swf _ _ W) as S.
  assert (D: decode_mode (a_mode a)) by (rewrite M; clear; unfold decode_mode; mdc; lia).
  apply go_dec; simpl; auto; try lia; dfin.
  apply MwfLemmas.swf_set_mode; auto; clear; mdc; lia.
Qed.

Lemma awf_LIT : case_ok LIT.
Proof.
  intros src a W M. rewrite astep_LIT by exact M. unfold a_LIT.
  pose proof (ax_swf _ _ W) as S.
  assert (D: decode_mode (a_mode a)) by (rewrite M; clear; unfold decode_mode; mdc; lia).
  apply go_dec; simpl; auto; try lia; dfin.
  - apply MwfLemmas.swf_set_mode; auto; clear; mdc; lia.
  - right. split; [reflexivity|]. eexists; split; [|reflexivity].
    pose proof (Z.mod_pos_bound (i_length (a_s a)) 256 ltac:(lia)). lia.
Qed.

Lemma awf_LEN : case_ok LEN.
Proof.
  intros src a W M. rewrite astep_LEN by exact M. unfold a_LEN.
  pose proof (ax_swf _ _ W) as S. pose proof (ax_md _ _ W) as MD.
  destruct (ax_frame _ _ W) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
  assert (D: decode_mode (a_mode a)) by (rewrite M; clear; unfold decode_mode; mdc; lia).
  destruct (md_tables _ MD D) as [TL TD].
  destruct (adecode_len src (a_s a) (a_q a) TL) as (EO & FO & L).
  destruct (adecode lenfix_list distfix_list src (a_s a) (i_lencode (a_s a)) (i_lenbits (a_s a)) len_islink (a_q a))
    as [here l]. cbn [fst snd] in EO, FO, L. cbv zeta.
  destruct EO as (EO1 & EO2 & EO3).
  unfold final_ok in FO. cbn [Z.eqb LENS CODES Pos.eqb] in FO.
  destruct (e_op here =? 0) eqn:O0.
  { unfold ago. apply go_dec; simpl; auto; try lia; dfin.
    destruct S; constructor; simpl; auto; [clear; mdc; lia | unfold urange; rep_lia]. }
  destruct (Z.land (e_op here) 32 =? 0) eqn:O32; cbn [negb].
  2:{ unfold ago. apply go_blk; simpl; auto; try lia.
      all: try (unfold data_mode; tauto).
      all: try (destruct S; constructor; simpl; auto; [clear; mdc; lia | unfold urange; rep_lia]).
      all: try (clear; unfold Step3Block.plain_md, decode_mode; mdc; lia).
      all: clear; mdc; lia. }
  destruct (Z.land (e_op here) 64 =? 0) eqn:O64; cbn [negb].
  2:{ apply go_abad; auto; lia. }
  apply Z.eqb_neq in O0. apply Z.eqb_eq in O32. apply Z.eqb_eq in O64.
  assert (OP: 16 <= e_op here <= 21 /\ 3 <= e_val here <= 258).
  { destruct FO as [[A _] | [A | [A | [A _]]]]; auto; try contradiction.
    rewrite A in O32. discriminate. }
  rewrite Step3Decode.land15 by lia.
  unfold ago. apply go_dec; simpl; auto; try lia; dfin.
  destruct S; constructor; simpl; auto; [clear; mdc; lia | unfold urange; rep_lia | lia].
Qed.

Lemma awf_LENEXT : case_ok LENEXT.
Proof.
  intros src a W M. rewrite astep_LENEXT by exact M. unfold a_LENEXT.
  pose proof (ax_swf _ _ W) as S. pose proof (ax_md _ _ W) as MD. pose proof (ax_s3 _ _ W) as S3.
  destruct (ax_frame _ _ W) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
  assert (D: decode_mode (a_mode a)) by (rewrite M; clear; unfold decode_mode; mdc; lia).
  pose proof (md_lenext _ MD M) as HEX. pose proof (s3_lenext _ S3 M) as L258.
  pose proof (md_length _ MD (or_introl M)) as L1. pose proof (sw_extra _ S) as EXR.
  cbv zeta. destruct (i_extra (a_s a) =? 0); cbn [negb]; unfold ago.
  - apply go_dec; simpl; auto; try lia; dfin.
    apply MwfLemmas.swf_set_mode; auto; clear; mdc; lia.
  - pose proof (sbits_range src (a_q a) (i_extra (a_s a)) ltac:(lia)) as SB.
    assert (P: 2 ^ i_extra (a_s a) <= 2 ^ 5) by (apply Z.pow_le_mono_r; lia).
    assert (U: u32 (i_length (a_s a) + sbits src (a_q a) (i_extra (a_s a))) =
               i_length (a_s a) + sbits src (a_q a) (i_extra (a_s a))).
    { unfold u32. rewrite Z.mod_small; auto. change (2 ^ 5) with 32 in P. lia. }
    rewrite U.
    apply go_dec; simpl; auto; try lia; dfin.
    all: try (destruct S; constructor; simpl; auto; [clear; mdc; lia | unfold urange; change (2 ^ 5) with 32 in P; rep_lia]).
    all: try (intros _; lia).
Qed.

Lemma awf_DIST : case_ok DIST.
Proof.
  intros src a W M. rewrite astep_DIST by exact M. unfold a_DIST.
  pose proof (ax_swf _ _ W) as S. pose proof (ax_md _ _ W) as MD.
  destruct (ax_frame _ _ W) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
  assert (D: decode_mode (a_mode a)) by (rewrite M; clear; unfold decode_mode; mdc; lia).
  destruct (md_tables _ MD D) as [TL TD].
  pose proof (aw_dtab _ _ (ax_w _ _ W) D src (a_q a)) as DK.
  pose proof (md_length _ MD (or_intror (or_introl M))) as L1.
  destruct (adecode_dist src (a_s a) (a_q a) TD) as (EO & FO & L).
  destruct (adecode lenfix_list distfix_list src (a_s a) (i_distcode (a_s a)) (i_distbits (a_s a)) dist_islink (a_q a))
    as [here l]. cbn [fst snd] in EO, FO, L, DK. cbv zeta.
  destruct EO as (EO1 & EO2 & EO3).
  unfold final_ok in FO. cbn [Z.eqb LENS CODES DISTS Pos.eqb] in FO.
  destruct (Z.land (e_op here) 64 =? 0) eqn:O64; cbn [negb].
  2:{ apply go_abad; auto; lia. }
  apply Z.eqb_eq in O64.
  assert (OP: 16 <= e_op here <= 29 /\ 1 <= e_val here <= 32768).
  { destruct FO as [A | [A _]]; auto; contradiction. }
  rewrite Step3Decode.land15 by lia.
  assert (DK': e_val here + 2 ^ (e_op here - 16) - 1 <= 32768).
  { unfold dist_ok in DK. rewrite Step3Decode.land15 in DK by lia. apply DK.
    rewrite land16 by lia. discriminate. }
  unfold ago. apply go_dec; simpl; auto; try lia; dfin.
  destruct S; constructor; simpl; auto; [clear; mdc; lia | unfold urange; rep_lia | lia].
Qed.

Lemma awf_DISTEXT : case_ok DISTEXT.
Proof.
  intros src a W M. rewrite astep_DISTEXT by exact M. unfold a_DISTEXT.
  pose proof (ax_swf _ _ W) as S. pose proof (ax_md _ _ W) as MD.
  destruct (ax_frame _ _ W) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
  assert (D: decode_mode (a_mode a)) by (rewrite M; clear; unfold decode_mode; mdc; lia).
  pose proof (aw_distext _ _ (ax_w _ _ W) M) as DE.
  pose proof (md_length _ MD (or_intror (or_intror M))) as L1.
  pose proof (md_offset _ MD (or_introl M)) as O1. pose proof (sw_extra _ S) as EXR.
  cbv zeta. destruct (i_extra (a_s a) =? 0) eqn:E0; cbn [negb]; unfold ago.
  - apply Z.eqb_eq in E0. rewrite E0 in DE. change (2 ^ 0) with 1 in DE.
    apply go_dec; simpl; auto; try lia; dfin.
    apply MwfLemmas.swf_set_mode; auto; clear; mdc; lia.
  - pose proof (sbits_range src (a_q a) (i_extra (a_s a)) ltac:(lia)) as SB.
    assert (U: u32 (i_offset (a_s a) + sbits src (a_q a) (i_extra (a_s a))) =
               i_offset (a_s a) + sbits src (a_q a) (i_extra (a_s a))).
    { unfold u32. rewrite Z.mod_small; auto. lia. }
    rewrite U.
    apply go_dec; simpl; auto; try lia; dfin.
    all: try (destruct S; constructor; simpl; auto; [clear; mdc; lia | unfold urange; rep_lia]).
    all: intros _; lia.
Qed.

Lemma awf_MATCH : case_ok MATCH.
Proof.
  intros src a W M. rewrite astep_MATCH by exact M. unfold a_MATCH.
  pose proof (ax_swf _ _ W) as S. pose proof (ax_md _ _ W) as MD.
  destruct (ax_frame _ _ W) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
  assert (D: decode_mode (a_mode a)) by (rewrite M; clear; unfold decode_mode; mdc; lia).
  pose proof (aw_offset _ _ (ax_w _ _ W) M) as OF.
  pose proof (md_match _ MD M) as L1. pose proof (md_offset _ MD (or_intror M)) as O1.
  cbv zeta. destruct (Zlength (a_O a) <? i_offset (a_s a)).
  - unfold go_ok. cbn [a_q a_O]. split; [|split; [lia | split; [reflexivity | left; reflexivity]]].
    apply awfx_bad; auto; try apply (ax_src _ _ W); lia.
  - assert (B: 0 <= Znth (Zlength (a_O a) - i_offset (a_s a)) (a_O a) <= 255) by (apply Znth_bytes; auto).
    destruct (i_length (a_s a) - 1 =? 0) eqn:E1.
    + apply go_dec; simpl; auto; try lia; dfin.
      * destruct S; constructor; simpl; auto; [clear; mdc; lia | unfold urange in *; lia].
      * right. split; [reflexivity|]. eexists; split; [exact B | reflexivity].
    + apply Z.eqb_neq in E1.
      apply go_dec; simpl; auto; try lia; dfin.
      all: try (destruct S; constructor; simpl; auto; unfold urange in *; lia).
      all: try (change (i_mode (a_s a)) with (a_mode a); rewrite M; clear; unfold decode_mode; mdc; lia).
      all: try (intros HM; exfalso; change (i_mode (a_s a)) with (a_mode a) in HM; rewrite M in HM; clear -HM; mdc; lia).
      all: try (intros _; lia).
      right. split; [reflexivity|]. eexists; split; [exact B | reflexivity].
Qed.

(* all the decode modes *)
Lemma awf_dec_all : case_ok LEN_ /\ case_ok LEN /\ case_ok LENEXT /\ case_ok DIST /\ case_ok DISTEXT /\
  case_ok MATCH /\ case_ok LIT.
Proof.
  split; [exact awf_LEN_|]. split; [exact awf_LEN|]. split; [exact awf_LENEXT|]. split; [exact awf_DIST|].
  split; [exact awf_DISTEXT|]. split; [exact awf_MATCH | exact awf_LIT].
Qed.
