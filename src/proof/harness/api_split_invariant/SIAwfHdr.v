(* The abstract steps of the header modes (HEAD .. DICT) keep the invariant awfx (SIAwfKit.v).  They write
   no output, change only the mode, the check, the flags, dmax and the length, and go to header modes or to
   TYPE/TYPEDO (zlib's check value 1, gzip's 0 after HCRC: the flags set by FLAGS are not zero). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_split_invariant.SIDefs.
Require Import Zlib.proof.harness.api_split_invariant.SIAwfKit.
Require Zlib.proof.inflate.Step3Header Zlib.proof.inflate.Step3Block.
Import ListNotations.
Local Open Scope Z_scope.

(* acrc changes the check only, to a 64-bit value *)
Lemma acrc_eq: forall s d, swf s -> bytes_ok d -> exists c, acrc s d = set_i_check s c /\ lrange c.
Proof.
  intros s d S B. unfold acrc. destruct (andb _ _).
  - eexists; split; [reflexivity|]. apply Step3Header.ref_crc32_lrange; auto.
  - exists (i_check s). split; [destruct s; reflexivity | apply (sw_check _ S)].
Qed.

Lemma hbytes2_ok: forall h, bytes_ok (hbytes2 h).
Proof. intros. apply Step3Header.hbytes2_bytes. Qed.

Lemma hbytes4_ok: forall h, bytes_ok (hbytes4 h).
Proof. intros. apply Step3Header.hbytes4_bytes. Qed.

Lemma byte1_ok: forall src q, bytes_ok src -> bytes_ok [sbyte src q].
Proof. intros. constructor; [pose proof (sbyte_range src q H); rep_lia | constructor]. Qed.

(* a header step to the state s at bit position n: the frame fields of a, no output *)
Lemma go_hdr: forall src a n s,
  awfx src a -> hdr_mode (a_mode a) -> a_q a <= n -> swf s ->
  Step3Block.plain_md (i_mode s) -> i_mode s <> HEAD -> HEAD <= i_mode s <= BAD ->
  i_wbits s = 15 -> i_wrap s = i_wrap (a_s a) -> i_havedict s = 0 -> i_head s = false ->
  i_back s = i_back (a_s a) ->
  (data_mode (i_mode s) -> i_wrap s <> 0 ->
     (i_flags s = 0 /\ i_check s = 1) \/ (i_flags s <> 0 /\ i_check s = 0)) ->
  (TIME <= i_mode s <= HCRC -> i_flags s <> 0) ->
  go_ok src a (ago a n s).
Proof.
  intros src a n s W HM Q S P NH MR WB WR HD HE BK CK GZ.
  destruct (ax_frame _ _ W) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
  apply go_ago; [|exact Q]. apply awfx_plain; auto.
  all: try apply (ax_src _ _ W).
  all: try (rewrite WR; auto).
  all: try lia.
  intros _. apply (aw_hdrO _ _ (ax_w _ _ W) HM).
Qed.

Ltac hdr_mode_tac := unfold hdr_mode; mdc; lia.

(* the side goals of go_hdr / go_gzs about the modes *)
Ltac hfin :=
  try (apply MwfLemmas.swf_set_mode; [assumption | clear; mdc; lia]);
  try (clear; unfold Step3Block.plain_md, decode_mode; mdc; lia);
  try (clear; mdc; lia);
  try (intros _ ?NZ; contradiction);
  try (intros ?D; exfalso; clear -D; unfold data_mode, decode_mode in D; mdc; lia).

Section Cases.

Lemma awf_HEAD : case_ok HEAD.
Proof.
  intros src a W M. rewrite astep_HEAD by exact M.
  destruct (ax_frame _ _ W) as (F1 & F2 & F3 & F4 & F5 & F6 & F7). pose proof (ax_swf _ _ W) as S.
  assert (HM: hdr_mode (a_mode a)) by (rewrite M; hdr_mode_tac).
  assert (WS: i_wsize (a_s a) = 0 \/ (i_win (a_s a) = true /\ i_wsize (a_s a) = 2 ^ 15))
    by (rewrite <- F1; apply (sw_wsize _ S)).
  unfold a_HEAD. rewrite F1. cbv zeta.
  destruct (i_wrap (a_s a) =? 0) eqn:WZ.
  { apply Z.eqb_eq in WZ. apply go_hdr; simpl; auto; try lia. all: hfin. }
  set (h := sbits src (a_q a) 16).
  assert (Hh: 0 <= h < 2 ^ 16) by (apply sbits_range; lia).
  destruct (andb (negb (Z.land (i_wrap (a_s a)) 2 =? 0)) (h =? 35615)) eqn:GZ.
  { apply go_hdr; simpl; auto; try lia. all: hfin.
    destruct S; constructor; simpl; auto; try exact WS; mdc; try lia.
    apply Step3Header.ref_crc32_lrange. apply hbytes2_ok. }
  destruct (orb (Z.land (i_wrap (a_s a)) 1 =? 0) (negb (((h mod 256) * 256 + Z.shiftr h 8) mod 31 =? 0))).
  { apply go_abad; auto; lia. }
  destruct (negb (h mod 16 =? 8)). { apply go_abad; auto; lia. }
  set (len := Z.shiftr h 4 mod 16 + 8).
  destruct (orb (15 <? len) (andb (negb (15 =? 0)) (15 <? len))) eqn:LN.
  { apply go_abad; auto; lia. }
  apply orb_false_iff in LN. destruct LN as [LN _]. apply Z.ltb_ge in LN.
  assert (L8: 8 <= len) by (unfold len; pose proof (Z.mod_pos_bound (Z.shiftr h 4) 16 ltac:(lia)); lia).
  assert (PL: 2 ^ len <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia).
  assert (PL0: 0 < 2 ^ len) by (apply Z.pow_pos_nonneg; lia).
  destruct (Z.land (Z.shiftr h 4) 512 =? 0); apply go_hdr; simpl; auto; try lia.
  all: try (destruct S; constructor; simpl; auto; try exact WS; unfold srange, urange, lrange; mdc; rep_lia).
  all: hfin.
  all: intros _ _; left; auto.
Qed.

Lemma awf_FLAGS : case_ok FLAGS.
Proof.
  intros src a W M. rewrite astep_FLAGS by exact M.
  destruct (ax_frame _ _ W) as (F1 & F2 & F3 & F4 & F5 & F6 & F7). pose proof (ax_swf _ _ W) as S.
  assert (HM: hdr_mode (a_mode a)) by (rewrite M; hdr_mode_tac).
  unfold a_FLAGS. cbv zeta. set (h := sbits src (a_q a) 16).
  destruct (negb (Z.land (s32 h) 255 =? 8)) eqn:F8; [apply go_abad; auto; lia|].
  destruct (negb (Z.land (s32 h) 57344 =? 0)); [apply go_abad; auto; lia|].
  apply negb_false_iff, Z.eqb_eq in F8.
  set (s1 := set_i_flags (a_s a) (s32 h)).
  assert (S1: swf s1) by (destruct S; constructor; simpl; auto; apply Step3Header.s32_range).
  destruct (acrc_eq s1 (hbytes2 h) S1 (hbytes2_ok h)) as (c & E & C). rewrite E.
  apply go_hdr; simpl; auto; try lia. all: hfin.
  - destruct S1; constructor; simpl; auto; mdc; lia.
  - intros _ Z0. rewrite Z0 in F8. discriminate.
Qed.

(* a gzip header step after FLAGS, to a state of the modes TIME .. HCRC with the frame and flags of a *)
Lemma go_gzs: forall src a n s,
  awfx src a -> TIME <= a_mode a <= HCRC -> a_q a <= n -> swf s -> TIME <= i_mode s <= HCRC ->
  i_wbits s = i_wbits (a_s a) -> i_wrap s = i_wrap (a_s a) -> i_havedict s = i_havedict (a_s a) ->
  i_head s = i_head (a_s a) -> i_back s = i_back (a_s a) -> i_flags s = i_flags (a_s a) ->
  go_ok src a (ago a n s).
Proof.
  intros src a n s W M Q S MD E1 E2 E3 E4 E5 E6.
  destruct (ax_frame _ _ W) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
  apply go_hdr; auto; try congruence.
  all: try (clear -M; unfold hdr_mode; mdc; lia).
  all: try (clear -MD; unfold Step3Block.plain_md, decode_mode; mdc; lia).
  all: try (clear -MD; mdc; lia).
  all: try (intros D; exfalso; clear -MD D; unfold data_mode, decode_mode in D; mdc; lia).
  intros _. rewrite E6. apply (ax_gzf _ _ W M).
Qed.

Lemma swf_acrc: forall s d, swf s -> bytes_ok d -> swf (acrc s d) /\ i_mode (acrc s d) = i_mode s /\
  i_wbits (acrc s d) = i_wbits s /\ i_wrap (acrc s d) = i_wrap s /\ i_havedict (acrc s d) = i_havedict s /\
  i_head (acrc s d) = i_head s /\ i_back (acrc s d) = i_back s /\ i_flags (acrc s d) = i_flags s /\
  i_length (acrc s d) = i_length s.
Proof.
  intros s d S B. destruct (acrc_eq s d S B) as (c & -> & C).
  split; [destruct S; constructor; simpl; auto|]. simpl; repeat split; auto.
Qed.

Lemma awf_TIME : case_ok TIME.
Proof.
  intros src a W M. rewrite astep_TIME by exact M. unfold a_TIME.
  pose proof (ax_swf _ _ W) as S. destruct (ax_frame _ _ W) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
  destruct (swf_acrc (a_s a) (hbytes4 (sbits src (a_q a) 32)) S (hbytes4_ok _)) as (S1 & E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7).
  apply go_gzs; simpl; auto; try lia; [rewrite M; mdc; lia | apply MwfLemmas.swf_set_mode; auto; mdc; lia | mdc; lia].
Qed.

Lemma awf_OS : case_ok OS.
Proof.
  intros src a W M. rewrite astep_OS by exact M. unfold a_OS.
  pose proof (ax_swf _ _ W) as S. destruct (ax_frame _ _ W) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
  destruct (swf_acrc (a_s a) (hbytes2 (sbits src (a_q a) 16)) S (hbytes2_ok _)) as (S1 & E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7).
  apply go_gzs; simpl; auto; try lia; [rewrite M; mdc; lia | apply MwfLemmas.swf_set_mode; auto; mdc; lia | mdc; lia].
Qed.

Lemma awf_EXLEN : case_ok EXLEN.
Proof.
  intros src a W M. rewrite astep_EXLEN by exact M. unfold a_EXLEN.
  pose proof (ax_swf _ _ W) as S. destruct (ax_frame _ _ W) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
  assert (MT: TIME <= a_mode a <= HCRC) by (rewrite M; mdc; lia).
  destruct (negb (Z.land (i_flags (a_s a)) 1024 =? 0)); cbv zeta.
  - set (h := sbits src (a_q a) 16).
    assert (S0: swf (set_i_length (a_s a) (u32 h))).
    { destruct S; constructor; simpl; auto. apply Step3Header.u32_range. }
    destruct (swf_acrc _ (hbytes2 h) S0 (hbytes2_ok _)) as (S1 & E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7).
    apply go_gzs; simpl; auto; try lia; [apply MwfLemmas.swf_set_mode; auto; mdc; lia | mdc; lia].
  - apply go_gzs; simpl; auto; try lia; [apply MwfLemmas.swf_set_mode; auto; mdc; lia | mdc; lia].
Qed.

Lemma awf_EXTRA : case_ok EXTRA.
Proof.
  intros src a W M. rewrite astep_EXTRA by exact M. unfold a_EXTRA.
  pose proof (ax_swf _ _ W) as S. destruct (ax_frame _ _ W) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
  assert (MT: TIME <= a_mode a <= HCRC) by (rewrite M; mdc; lia).
  destruct (andb (negb (Z.land (i_flags (a_s a)) 1024 =? 0)) (negb (i_length (a_s a) =? 0))) eqn:C; cbv zeta.
  - apply andb_true_iff in C. destruct C as [_ C]. apply negb_true_iff, Z.eqb_neq in C.
    pose proof (sw_length _ S) as LR.
    destruct (swf_acrc (a_s a) [sbyte src (a_q a)] S (byte1_ok _ _ (ax_src _ _ W))) as (S1 & E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7).
    apply go_gzs; simpl; auto; try lia; [| rewrite E0; exact MT].
    destruct S1; constructor; simpl; auto. unfold urange in *. lia.
  - apply go_gzs; simpl; auto; try lia; [|mdc; lia].
    destruct S; constructor; simpl; auto; unfold urange; mdc; rep_lia.
Qed.

(* NAME and COMMENT: one byte of a zero-terminated string *)
Lemma awf_NAME : case_ok NAME.
Proof.
  intros src a W M. rewrite astep_NAME by exact M. unfold a_NAME.
  pose proof (ax_swf _ _ W) as S. destruct (ax_frame _ _ W) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
  assert (MT: TIME <= a_mode a <= HCRC) by (rewrite M; mdc; lia).
  destruct (negb (Z.land (i_flags (a_s a)) 2048 =? 0)); cbv zeta.
  - destruct (swf_acrc (a_s a) [sbyte src (a_q a)] S (byte1_ok _ _ (ax_src _ _ W))) as (S1 & E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7).
    destruct (sbyte src (a_q a) =? 0); apply go_gzs; simpl; auto; try lia.
    + destruct S1; constructor; simpl; auto; unfold urange; mdc; rep_lia.
    + mdc; lia.
    + rewrite E0; exact MT.
  - apply go_gzs; simpl; auto; try lia; [|mdc; lia].
    destruct S; constructor; simpl; auto; unfold urange; mdc; rep_lia.
Qed.

Lemma awf_COMMENT : case_ok COMMENT.
Proof.
  intros src a W M. rewrite astep_COMMENT by exact M. unfold a_COMMENT.
  pose proof (ax_swf _ _ W) as S. destruct (ax_frame _ _ W) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
  assert (MT: TIME <= a_mode a <= HCRC) by (rewrite M; mdc; lia).
  destruct (negb (Z.land (i_flags (a_s a)) 4096 =? 0)); cbv zeta.
  - destruct (swf_acrc (a_s a) [sbyte src (a_q a)] S (byte1_ok _ _ (ax_src _ _ W))) as (S1 & E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7).
    destruct (sbyte src (a_q a) =? 0); apply go_gzs; simpl; auto; try lia.
    all: try (apply MwfLemmas.swf_set_mode; auto; clear; mdc; lia).
    all: try (clear; mdc; lia).
    all: rewrite E0; exact MT.
  - apply go_gzs; simpl; auto; try lia.
    all: try (apply MwfLemmas.swf_set_mode; auto; clear; mdc; lia).
    all: clear; mdc; lia.
Qed.

Lemma awf_HCRC : case_ok HCRC.
Proof.
  intros src a W M. rewrite astep_HCRC by exact M. unfold a_HCRC.
  pose proof (ax_swf _ _ W) as S. destruct (ax_frame _ _ W) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
  assert (HM: hdr_mode (a_mode a)) by (rewrite M; hdr_mode_tac).
  assert (FL: i_flags (a_s a) <> 0) by (apply (ax_gzf _ _ W); rewrite M; mdc; lia).
  assert (G: forall n, a_q a <= n ->
    go_ok src a (ago a n (set_i_mode (set_i_check (a_s a) 0) Model.TYPE))).
  { intros n Q. apply go_hdr; simpl; auto; try lia. all: hfin.
    destruct S; constructor; simpl; auto; unfold lrange; mdc; rep_lia. }
  cbv zeta. destruct (negb (Z.land (i_flags (a_s a)) 512 =? 0)); [|apply G; lia].
  destruct (andb _ _); [apply go_abad; auto; lia | apply G; lia].
Qed.

Lemma awf_DICTID : case_ok DICTID.
Proof.
  intros src a W M. rewrite astep_DICTID by exact M. unfold a_DICTID.
  pose proof (ax_swf _ _ W) as S. destruct (ax_frame _ _ W) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
  assert (HM: hdr_mode (a_mode a)) by (rewrite M; hdr_mode_tac).
  apply go_hdr; simpl; auto; try lia. all: hfin.
  destruct S; constructor; simpl; auto; mdc; try lia.
  apply Step3Header.swap32_range. apply sbits_range; lia.
Qed.

Lemma awf_DICT : case_ok DICT.
Proof.
  intros src a W M. rewrite astep_DICT by exact M. unfold a_DICT.
  destruct (ax_frame _ _ W) as (F1 & F2 & F3 & F4 & F5 & F6 & F7). rewrite F3. simpl. exact I.
Qed.

End Cases.
