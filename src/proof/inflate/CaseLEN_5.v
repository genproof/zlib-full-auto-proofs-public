(* inflate(), case LEN_ in Delta_cases5: state->mode = LEN, falls into LEN *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.CaseKit5.
Require Import Zlib.proof.inflate.MwfLemmas.
Require Import Zlib.proof.inflate.Steps2.
Require Import Zlib.proof.inflate.ModeKit5.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Lemma swf3_set_mode_decode5: forall s md,
  swf3 s -> decode_mode (i_mode s) -> md = LEN_ \/ md = LEN \/ md = LIT -> swf3 (set_i_mode s md).
Proof.
  intros s md [A B C D] Hd Hmd.
  constructor; cbn [i_mode i_wbits i_wsize i_wrap i_win i_length i_offset i_lencode i_lenbits set_i_mode].
  - intro E. exfalso. unfold HEAD, LEN_, LEN, LIT in *. lia.
  - intros _. destruct (B Hd) as (sz & S1 & S2 & S3). exists sz. split; [exact S1|]. split; [exact S2|].
    exact S3.
  - intro E. exfalso. unfold LENEXT, LEN_, LEN, LIT in *. lia.
  - intro E. exfalso. unfold DISTEXT, LEN_, LEN, LIT in *. lia.
Qed.

Lemma case_LEN_5 {Espec: OracleKind} (F: frame) : case_ok5 F LEN 20 -> case_ok5 F LEN_ 19.
Proof.
  intros HY m HM HL [W W2].
  assert (E1: stepf2 (f_flush F) lenfix_list distfix_list m =
              stepf2 (f_flush F) lenfix_list distfix_list (set_mode m LEN)).
  { rewrite (stepf2_LEN_ _ _ _ _ HM). unfold c_LEN_. symmetry.
    exact (stepf2_LEN (f_flush F) lenfix_list distfix_list (set_mode m LEN) eq_refl). }
  assert (D: decode_mode (m_mode m)) by (unfold decode_mode; left; exact HM).
  assert (W1: mwf3 (set_mode m LEN)).
  { split.
    - apply mwf_set_mode_tables; [exact W | exact D | right; left; reflexivity].
    - apply swf3_set_mode_decode5; [exact W2 | exact D | right; left; reflexivity]. }
  apply (case_fallthrough5 F m LEN 19); [lia | exact HY | ].
  case_body_stmt.
  eapply ConseqFacts.semax_post''; [ | apply semax_store_mode5].
  unfold fall_post5. Exists (set_mode m LEN).
  apply andp_right; [ | apply andp_left2; apply derives_refl].
  apply prop_right. split; [exact E1 | ]. split; [reflexivity | ]. split; [exact HL | exact W1].
Qed.
