(* RT-H: case HEAD (index 0) with a partial gz_header attached (RTHCase.case_ok6): the gzip branch;
   the other branches contradict hpass (they leave the header modes with done <> 1). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTHCase.
Require Import Zlib.proof.roundtrip.RTHHEADKit6.
Require Import Zlib.proof.inflate.HeadDefs5 Zlib.proof.inflate.Steps2.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Lemma rth_head : rth_head_stmt.
Proof.
  intros Espec F HF m n HM HL W3 HD HI HP.
  eapply semax_pre with
    (P' := !! (h_done (m_h m) = 0) && (loop_stateH F m * (fun _ => hdr_tok F m * hd6 F m))).
  { intros rho. simpl. apply andp_left2. apply andp_right; [ | apply derives_refl].
    unfold hd6, head_rep6. rewrite !sepcon_andp_prop. apply andp_left1. apply prop_derives.
    intros [H _]. exact H. }
  apply semax_extract_prop. intros Hd0.
  destruct (rthh_gzip _ _ _ HM HI Hd0 (proj1 W3) HP) as (Hw & HL1 & G).
  pose proof (stepf2_HEAD (f_flush F) lenfix_list distfix_list m HM) as E0.
  assert (E1: stepf2 (f_flush F) lenfix_list distfix_list m = IBrk (head_gzip_m (needbits 16 m))).
  { rewrite E0, (c_HEAD_split m Hw HL1), G. reflexivity. }
  assert (Hh: hd6 F (head_gzip_m (needbits 16 m)) = hd6 F m).
  { destruct (rthh_nb_sh 4 16 m) as [S1 H1]. unfold hd6.
    change (m_h (head_gzip_m (needbits 16 m))) with (m_h (needbits 16 m)). unfold needbits; rewrite H1.
    symmetry. apply head_rep6_HEAD_FLAGS; [exact HM | reflexivity | ].
    change (i_flags (m_s (head_gzip_m (needbits_f 4 16 m)))) with (i_flags (m_s (needbits_f 4 16 m))).
    rewrite S1; reflexivity. }
  eapply semax_post; [ | | | | apply semax_frame with (F := fun _ => hdr_tok F m * hd6 F m);
                                 [ | apply (head_caseH F m HF HM HL W3 Hw HL1 G)]].
  - intros rho. simpl. apply andp_left2. normalize.
  - intros rho. simpl. apply andp_left2. normalize. rewrite E1 in H. inversion H; subst x; clear H.
    apply (exp_right (head_gzip_m (needbits 16 m))). unfold post6.
    replace (hdr_mode (m_mode (head_gzip_m (needbits 16 m)))) with true by reflexivity.
    rewrite Hh. simpl. normalize. cancel.
  - intros rho. simpl. apply andp_left2. normalize.
  - intros vl rho. simpl. apply andp_left2. normalize. rewrite E1 in H. discriminate.
  - intros rho te _. reflexivity.
Qed.
