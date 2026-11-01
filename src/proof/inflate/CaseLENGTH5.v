(* inflate(), case LENGTH (index 27) in Delta_cases5: if (wrap && flags) { NEEDBITS(32); if ((wrap & 4) &&
   hold != (total & 0xffffffff)) { strm->msg = "incorrect length check"; mode = BAD; break; } INITBITS(); }
   state->mode = DONE; falls into DONE.  Kit: CKKit5.v. *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.CaseHyps5.
Require Import Zlib.proof.inflate.MwfLemmas.
Require Import Zlib.proof.inflate.Steps2.
Require Import Zlib.proof.inflate.NeedKit5.
Require Import Zlib.proof.inflate.NeedBits3_5.
Require Import Zlib.proof.inflate.CKKit5.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* the length check *)
Definition lg_cond (m: mst) : bool := negb (i_wrap (m_s m) =? 0) && negb (i_flags (m_s m) =? 0).
Definition lg_bad (m: mst) : bool :=
  negb (Z.land (i_wrap (m_s m)) 4 =? 0) && negb (m_hold m =? i_total (m_s m) mod 2 ^ 32).

Lemma c_LENGTH_eq: forall m,
  lg_cond m = true -> m_leave (needbits 32 m) = 0 ->
  c_LENGTH m = (let m1 := needbits 32 m in
                if lg_bad m1 then IBrk (set_bad m1 M_lcheck) else c_DONE (set_mode (initbits m1) DONE)).
Proof.
  intros m C L. unfold c_LENGTH. unfold lg_cond in C. rewrite C. rewrite L. cbv zeta.
  change (0 =? 1) with false. cbv iota. clear L. generalize (needbits 32 m). intro m1.
  unfold lg_bad. reflexivity.
Qed.

Lemma c_LENGTH_eqL: forall m,
  lg_cond m = true -> m_leave (needbits 32 m) = 1 -> c_LENGTH m = IBrk (needbits 32 m).
Proof. intros m C L. unfold c_LENGTH. unfold lg_cond in C. rewrite C. cbv zeta. rewrite L. reflexivity. Qed.

Lemma c_LENGTH_eq0: forall m, lg_cond m = false -> c_LENGTH m = c_DONE (set_mode m DONE).
Proof. intros m C. unfold c_LENGTH. unfold lg_cond in C. rewrite C. reflexivity. Qed.

Lemma lg_swf3_done: forall s, i_mode s = DONE -> swf3 s.
Proof.
  intros s E. constructor; rewrite E; intros; unfold decode_mode, HEAD, DONE, LEN_, LEN, LENEXT, DIST, DISTEXT,
    MATCH, LIT in *; lia.
Qed.

Lemma lg_mwf3_done: forall m, mwf m -> mwf3 (set_mode m DONE).
Proof.
  intros m W. split.
  - apply mwf_set_mode_plain; [exact W | unfold HEAD, DONE, SYNC; lia | unfold LENLENS, DONE; lia
      | unfold CODELENS, DONE; lia | unfold decode_mode, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, DONE; lia
      | right; right; left; reflexivity].
  - apply lg_swf3_done. reflexivity.
Qed.

(* (_Bool) of an int *)
Lemma lg_tbool_s: forall x, Int.min_signed <= x <= Int.max_signed ->
  Vint (if Int.eq (Int.repr x) Int.zero then Int.zero else Int.one) = Vint (Int.repr (if x =? 0 then 0 else 1)).
Proof.
  intros x H. destruct (Z.eqb_spec x 0).
  - subst. reflexivity.
  - rewrite Int.eq_false; [reflexivity | ]. intro E. apply n. apply ck_int_zero; auto.
Qed.

Lemma lg_mask32: forall t, lrange t ->
  Int64.and (Int64.repr t) (Int64.repr (Int.unsigned (Int.repr (-1)))) = Int64.repr (t mod 2 ^ 32).
Proof.
  intros t R. unfold lrange in R. change (Int.unsigned (Int.repr (-1))) with 4294967295.
  unfold Int64.and. rewrite Int64.unsigned_repr by rep_lia.
  change (Int64.unsigned (Int64.repr 4294967295)) with (Z.ones 32). rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma lg_cmp_val: forall x y, lrange x -> lrange y ->
  bool2val (Int64.cmpu Cne (Int64.repr x) (Int64.repr y)) = Vint (Int.repr (if negb (x =? y) then 1 else 0)).
Proof.
  intros x y Rx Ry. unfold Int64.cmpu. destruct (Z.eqb_spec x y).
  - subst. rewrite Int64.eq_true. reflexivity.
  - rewrite Int64.eq_false; [reflexivity | ]. intro E. apply (f_equal Int64.unsigned) in E.
    unfold lrange in *. rewrite !Int64.unsigned_repr in E by rep_lia. contradiction.
Qed.

(* the check block after NEEDBITS(32) *)
Definition lg_cmp_stmt : statement :=
  match case_body 27 with Ssequence (Ssequence _ (Sifthenelse _ (Ssequence _ (Ssequence c _)) _)) _ => c
  | _ => Sskip end.
Definition lg_init_stmt : statement :=
  match case_body 27 with Ssequence (Ssequence _ (Sifthenelse _ (Ssequence _ (Ssequence _ c)) _)) _ => c
  | _ => Sskip end.

Lemma lg_cmp_ok {Espec: OracleKind} (F: frame) (m1 m: mst) (R: ret_assert):
  frame_ok F -> lrange (m_hold m1) -> lrange (i_total (m_s m1)) -> 0 <= i_wrap (m_s m1) <= 15 ->
  RA_break R = RA_normal (case_post2 F m) ->
  (lg_bad m1 = true -> stepf2 (f_flush F) lenfix_list distfix_list m = IBrk (set_bad m1 M_lcheck)) ->
  semax Delta_cases5 (loop_state F m1) lg_cmp_stmt (overridePost (!! (lg_bad m1 = false) && loop_state F m1) R).
Proof.
  intros FOK RH RT RW HR HB. pose proof FOK as (HWS & HWH & HRG & HRT).
  cbv beta iota zeta delta [lg_cmp_stmt case_body inflate_LS find_switch f_inflate fn_body ls_drop].
  rewrite loop_state_ksplit. unfold loop_state_k.
  abbreviate_semax.
  forward.
  forward_if (temp _t'94 (Vint (Int.repr (if lg_bad m1 then 1 else 0)))).
  { forward. forward.
    destruct R as [Rn Rb Rc Rr]. cbn [RA_normal].
    entailer!.
    change (Int.unsigned (Int.repr (-1))) with (Z.ones 32). rewrite Z.land_ones by lia.
    assert (RM: lrange (i_total (m_s m1) mod 2 ^ 32))
      by (unfold lrange; pose proof (Z.mod_pos_bound (i_total (m_s m1)) (2 ^ 32) ltac:(lia)); rep_lia).
    rewrite (lg_cmp_val _ _ RH RM). unfold lg_bad. rewrite (ck_flagbit _ _ H1). reflexivity. }
  { forward.
    destruct R as [Rn Rb Rc Rr]. cbn [RA_normal].
    entailer!.
    unfold lg_bad. rewrite (ck_flagbit0 _ _ H1) by rep_lia. reflexivity. }
  forward_if.
  { assert (Eb: lg_bad m1 = true) by (destruct (lg_bad m1); [reflexivity | exfalso; apply H1; reflexivity]).
    unfold abbreviate in POSTCONDITION, MORE_COMMANDS. subst POSTCONDITION MORE_COMMANDS.
    match goal with |- semax _ _ _ ?P =>
      assert (HR2: RA_break P = RA_normal (case_post2 F m)) by (destruct R; exact HR);
      eapply semax_pre; [ | apply (bad_okk_lcheck F HWS m1 m P HR2 (HB Eb))] end.
    rewrite loop_state_ksplit. unfold loop_state_k. entailer!. }
  { assert (Eb: lg_bad m1 = false) by (destruct (lg_bad m1); [exfalso; exact (Int.one_not_zero H1) | reflexivity]).
    forward.
    destruct R as [Rn Rb Rc Rr]. cbn [RA_normal].
    entailer!. }
Qed.

Lemma case_LENGTH5 {Espec: OracleKind} (F: frame) : frame_ok5 F -> case_ok5 F DONE 28 -> case_ok5 F LENGTH 27.
Proof.
  intros [FOK FL] HY m HM HL [W W3].
  pose proof FOK as (HWS & HWH & HRG & HRT).
  pose proof (sw_wrap_range _ (mw_s _ W)) as RW. pose proof (sw_flags _ (mw_s _ W)) as RF.
  apply (case_fallthrough5 F m DONE 27); [lia | exact HY | ].
  case_body_stmt.
  apply semax_seq with (Q := EX m': mst,
    !! (stepf2 (f_flush F) lenfix_list distfix_list m = c_DONE (set_mode m' DONE) /\ m_leave m' = 0 /\
        mwf3 (set_mode m' DONE)) && loop_state F m').
  2: { apply extract_exists_pre. intro m'. apply semax_extract_prop. intros (E1 & L1 & W1).
       eapply ConseqFacts.semax_post''; [ | apply semax_store_mode5].
       unfold fall_post5. Exists (set_mode m' DONE).
       apply andp_right; [ | apply andp_left2; apply derives_refl].
       apply prop_right. split.
       { rewrite E1. symmetry. exact (stepf2_DONE (f_flush F) lenfix_list distfix_list (set_mode m' DONE) eq_refl). }
       split; [reflexivity | ]. split; [exact L1 | exact W1]. }
  assert (E0: lg_cond m = false -> stepf2 (f_flush F) lenfix_list distfix_list m = c_DONE (set_mode m DONE)).
  { intro C. rewrite (stepf2_LENGTH _ _ _ _ HM). apply c_LENGTH_eq0. exact C. }
  assert (EL: lg_cond m = true -> m_leave (needbits 32 m) = 1 ->
              stepf2 (f_flush F) lenfix_list distfix_list m = IBrk (needbits 32 m)).
  { intros C E. rewrite (stepf2_LENGTH _ _ _ _ HM). apply c_LENGTH_eqL; assumption. }
  assert (EC: lg_cond m = true -> m_leave (needbits 32 m) = 0 ->
     stepf2 (f_flush F) lenfix_list distfix_list m =
       if lg_bad (needbits 32 m) then IBrk (set_bad (needbits 32 m) M_lcheck)
       else c_DONE (set_mode (initbits (needbits 32 m)) DONE)).
  { intros C L0. rewrite (stepf2_LENGTH _ _ _ _ HM). rewrite (c_LENGTH_eq m C L0). reflexivity. }
  rewrite loop_state_ksplit. unfold loop_state_k.
  abbreviate_semax.
  forward.
  forward_if (temp _t'95 (Vint (Int.repr (if lg_cond m then 1 else 0)))).
  { forward. forward. cbv [switch_ret_assert case_post2 RA_normal]. entailer!.
    rewrite lg_tbool_s by exact RF. unfold lg_cond.
    rewrite (proj2 (Z.eqb_neq _ _) H1'). destruct (i_flags (m_s m) =? 0); reflexivity. }
  { forward. cbv [switch_ret_assert case_post2 RA_normal]. entailer!. unfold lg_cond.
    assert (Z0: i_wrap (m_s m) = 0) by (apply ck_int_zero; [rep_lia | assumption]).
    rewrite Z0. reflexivity. }
  forward_if.
  - (* wrap && flags *)
    assert (C: lg_cond m = true) by (destruct (lg_cond m); [reflexivity | exfalso; apply H1; reflexivity]).
    eapply semax_pre; [ | eapply (semax_needbits_seq5 F m m 32)].
    { rewrite loop_state_ksplit. unfold loop_state_k. entailer!. }
    { apply semax_needbits_LENGTH5; auto; lia. }
    { exact W. }
    { lia. }
    { reflexivity. }
    { exact (EL C). }
    apply semax_extract_prop. intros HL0.
    pose proof (EC C HL0) as E. clear EL EC E0.
    pose proof (mwf_needbits 32 m W ltac:(lia)) as W1.
    set (m1 := needbits 32 m) in *. clearbody m1.
    unfold abbreviate in POSTCONDITION. subst POSTCONDITION.
    match goal with |- semax _ _ _ ?P =>
      apply semax_seq with (Q := !! (lg_bad m1 = false) && loop_state F m1);
      [ apply (lg_cmp_ok F m1 m P); auto | ] end.
    { exact (mw_hold _ W1). }
    { exact (sw_total _ (mw_s _ W1)). }
    { exact (sw_wrap_range _ (mw_s _ W1)). }
    { intro Eb. rewrite E, Eb. reflexivity. }
    apply semax_extract_prop. intros Eb.
    eapply ConseqFacts.semax_post''; [ | apply semax_initbits_k].
    cbn [RA_normal overridePost].
    Exists (initbits m1).
    apply andp_right; [apply prop_right | apply andp_left2, derives_refl].
    split; [rewrite E, Eb; reflexivity | ]. split; [exact HL0 | ].
    apply lg_mwf3_done, mwf_initbits, W1.
  - (* no check *)
    assert (C: lg_cond m = false) by (destruct (lg_cond m); [exfalso; exact (Int.one_not_zero H1) | reflexivity]).
    forward.
    Exists m. rewrite loop_state_ksplit. unfold loop_state_k.
    entailer!.
    pose proof (lg_mwf3_done m W) as WM. pose proof (E0 C) as E0'.
    repeat match goal with |- _ /\ _ => split end; first [exact E0' | exact HL | exact WM | exact (proj1 WM) | exact (proj2 WM)].
Qed.
