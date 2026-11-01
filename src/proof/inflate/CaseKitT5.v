(* The fallthrough between the header cases (FLAGS .. COMMENT) with the header buffers' tokens framed in
   (CaseHyps5.v case_okT5). *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.inflate.CaseHyps5.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* the end of a header case's body falling into mode Y: the fallthrough machine keeps the header's
   presence and maxima (so the same tokens) *)
Definition fall_postT5 (F: frame) (m: mst) (Y: Z) : environ -> mpred :=
  EX m': mst,
    !! (stepf2 (f_flush F) lenfix_list distfix_list m = stepf2 (f_flush F) lenfix_list distfix_list m' /\
        m_mode m' = Y /\ m_leave m' = 0 /\ mwf3 m' /\ hd_ok F m' /\ hdr_tok F m' = hdr_tok F m) &&
    loop_state F m'.

Lemma case_fallthroughT5 {Espec: OracleKind} (F: frame) (m: mst) (Y: Z) (i: nat):
  (i < 32)%nat ->
  case_okT5 F Y (S i) ->
  semax Delta_cases5 (loop_state F m * (fun _ => hdr_tok F m)) (case_body i)
    (overridePost (fall_postT5 F m Y * (fun _ => hdr_tok F m))
       (frame_ret_assert (switch_ret_assert (case_post2 F m)) (fun _ => hdr_tok F m))) ->
  semax Delta_cases5 (loop_state F m * (fun _ => hdr_tok F m)) (seq_of_labeled_statement (ls_drop i inflate_LS))
    (frame_ret_assert (switch_ret_assert (case_post2 F m)) (fun _ => hdr_tok F m)).
Proof.
  intros Hi HY HB. rewrite seq_split by lia.
  eapply semax_seq; [exact HB | ].
  unfold fall_postT5. rewrite exp_sepcon1. apply extract_exists_pre. intros m'.
  rewrite sepcon_andp_prop'. apply semax_extract_prop. intros (E & HM & HL & W & HD & HT).
  rewrite (case_post2_eq F m m' E). rewrite <- HT.
  apply HY; auto.
Qed.

(* a header case's body proved without the tokens *)
Lemma body_frameT5 {Espec: OracleKind} (F: frame) (m: mst) (Y: Z) (i: nat):
  semax Delta_cases5 (loop_state F m) (case_body i)
    (overridePost (fall_postT5 F m Y) (switch_ret_assert (case_post2 F m))) ->
  semax Delta_cases5 (loop_state F m * (fun _ => hdr_tok F m)) (case_body i)
    (overridePost (fall_postT5 F m Y * (fun _ => hdr_tok F m))
       (frame_ret_assert (switch_ret_assert (case_post2 F m)) (fun _ => hdr_tok F m))).
Proof.
  intros H.
  eapply semax_post; [ | | | | apply semax_frame; [ | exact H]].
  - intros rho. simpl. apply andp_left2. apply derives_refl.
  - intros rho. simpl. apply andp_left2. apply derives_refl.
  - intros rho. simpl. apply andp_left2. apply derives_refl.
  - intros vl rho. simpl. apply andp_left2. apply derives_refl.
  - intros rho te _. reflexivity.
Qed.
