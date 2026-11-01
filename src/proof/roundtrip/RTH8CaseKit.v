(* The header cases with a header that passes in this call (RTH8Defs.case_ok8): the fall-through of a header case
   into the next one (RTHCase.case_fallthrough6 with hpass8 and case_post8) and the statements of the parts, as in
   RTHCase.  The header cases HEAD .. COMMENT are generated from their v6 proofs (docs/port-hl/cfg_rth8.py); only
   HCRC, which leaves the header modes, differs (RTH8CaseHCRC.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTH8Spec.
Require Import Zlib.proof.roundtrip.RTHCase.
Require Import Zlib.proof.roundtrip.RTH8Defs.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Lemma case_post8_eq: forall F m m',
  stepf2 (f_flush F) lenfix_list distfix_list m = stepf2 (f_flush F) lenfix_list distfix_list m' ->
  case_post8 F m = case_post8 F m'.
Proof. intros F m m' E. unfold case_post8. rewrite E. reflexivity. Qed.

(* hpass8 depends on the first pass only through its result *)
Lemma hpass8_same: forall flush n m m',
  hdr_mode (m_mode m) = true -> hdr_mode (m_mode m') = true ->
  stepf2 flush lenfix_list distfix_list m = stepf2 flush lenfix_list distfix_list m' ->
  hpass8 flush (S n) m -> hpass8 flush (S n) m'.
Proof.
  intros flush n m m' H H' E P. cbn [hpass8] in P |- *. rewrite H in P. rewrite H', <- E. exact P.
Qed.

(* a header case whose body falls into the header mode Y (RTHCase.fall_post6) is proved by the case of Y *)
Lemma case_fallthrough8 {Espec: OracleKind} (F: frame) (m: mst) (n: nat) (Y: Z) (i: nat):
  (i < 32)%nat -> hdr_mode Y = true -> hdr_mode (m_mode m) = true -> hpass8 (f_flush F) (S n) m ->
  case_ok8 F Y (S i) ->
  semax Delta_cases5 (loop_stateH F m * (fun _ => hdr_tok F m * hd6 F m)) (case_body i)
    (overridePost (fall_post6 F m Y * (fun _ => hdr_tok F m))
       (frame_ret_assert (switch_ret_assert (case_post8 F m)) (fun _ => hdr_tok F m))) ->
  semax Delta_cases5 (loop_stateH F m * (fun _ => hdr_tok F m * hd6 F m))
    (seq_of_labeled_statement (ls_drop i inflate_LS))
    (frame_ret_assert (switch_ret_assert (case_post8 F m)) (fun _ => hdr_tok F m)).
Proof.
  intros Hi HY Hm HP HC HB. rewrite seq_split by lia.
  eapply semax_seq; [exact HB | ].
  unfold fall_post6. rewrite exp_sepcon1. apply extract_exists_pre. intros m'.
  rewrite sepcon_andp_prop'. apply semax_extract_prop. intros (E & HM & HL & W & HD & HT & HH).
  rewrite (case_post8_eq F m m' E). rewrite <- HT.
  assert (HP': hpass8 (f_flush F) (S n) m') by (apply (hpass8_same _ n m m'); auto; rewrite HM; exact HY).
  eapply semax_pre; [ | apply (HC m' n); auto].
  intros rho. simpl. apply andp_left2. cancel.
Qed.

(* the parts *)
Definition rth_head_stmt8 : Prop :=
  forall {Espec: OracleKind} (F: frame), frame_ok5 F -> case_ok8 F IM.HEAD 0.

Definition rth_fto_stmt8 : Prop :=
  forall {Espec: OracleKind} (F: frame), frame_ok5 F ->
    (case_ok8 F IM.TIME 2 -> case_ok8 F IM.FLAGS 1) /\ (case_ok8 F IM.OS 3 -> case_ok8 F IM.TIME 2) /\
    (case_ok8 F IM.EXLEN 4 -> case_ok8 F IM.OS 3).

Definition rth_ex_stmt8 : Prop :=
  forall {Espec: OracleKind} (F: frame), frame_ok5 F ->
    (case_ok8 F IM.EXTRA 5 -> case_ok8 F IM.EXLEN 4) /\ (case_ok8 F IM.NAME 6 -> case_ok8 F IM.EXTRA 5).

Definition rth_nc_stmt8 : Prop :=
  forall {Espec: OracleKind} (F: frame), frame_ok5 F ->
    (case_ok8 F IM.COMMENT 7 -> case_ok8 F IM.NAME 6) /\ (case_ok8 F IM.HCRC 8 -> case_ok8 F IM.COMMENT 7).

Definition rth_hcrc_stmt8 : Prop :=
  forall {Espec: OracleKind} (F: frame), frame_ok5 F -> case_ok8 F IM.HCRC 8.

Lemma cases8_all_of_parts:
  rth_head_stmt8 -> rth_fto_stmt8 -> rth_ex_stmt8 -> rth_nc_stmt8 -> rth_hcrc_stmt8 -> cases8_all.
Proof.
  intros HH FT XE NC HC Espec F HF.
  pose proof (HC Espec F HF) as C8.
  destruct (NC Espec F HF) as [N6 N7]. pose proof (N7 C8) as C7. pose proof (N6 C7) as C6.
  destruct (XE Espec F HF) as [E4 E5]. pose proof (E5 C6) as C5. pose proof (E4 C5) as C4.
  destruct (FT Espec F HF) as (F1 & F2 & F3). pose proof (F3 C4) as C3. pose proof (F2 C3) as C2.
  pose proof (F1 C2) as C1. pose proof (HH Espec F HF) as C0.
  intros i Hi.
  do 9 (destruct i as [|i]; [ eassumption | ]). exfalso; lia.
Qed.
