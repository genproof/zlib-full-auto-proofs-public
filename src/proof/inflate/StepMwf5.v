(* One pass of the switch of the corrected model (Model2.v) preserves mwf3 (Inv3.v) and the header
   pointer facts: the loop invariants of inflate()'s body.  Step3*.v prove stepf_mwf3 for Model.v;
   Model2.v differs only in c_COMMENT (no length reset) and the cases falling into it. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.inflate.Inv3.
Require Import Zlib.proof.inflate.Cover3.
Require Import Zlib.proof.inflate.Model2.
Require Zlib.proof.inflate.Step5Mwf.
Require Import Zlib.proof.inflate.StepHd5.
Local Open Scope Z_scope.

(* the header pointer facts, over the header record and three pointers (CaseHyps5.hd_ok's content) *)
Definition hd_ok_p (head: bool) (h: hstate) (xb nb cb: bool) : Prop :=
  head = true -> (h_xp h = true -> xb = true) /\ (h_np h = true -> nb = true) /\ (h_cp h = true -> cb = true).

(* the header facts: every case keeps i_head and the maxima, and only clears h_xp / h_np / h_cp *)
Lemma stepf2_hd : forall flush m xb nb cb, hd_ok_p (i_head (m_s m)) (m_h m) xb nb cb ->
     match stepf2 flush lenfix_list distfix_list m with
     | IBrk m' => i_head (m_s m') = i_head (m_s m) /\ hd_ok_p (i_head (m_s m')) (m_h m') xb nb cb /\
                  h_extra_max (m_h m') = h_extra_max (m_h m) /\ h_name_max (m_h m') = h_name_max (m_h m) /\
                  h_comm_max (m_h m') = h_comm_max (m_h m)
     | IRet _ m' => i_head (m_s m') = i_head (m_s m) /\ hd_ok_p (i_head (m_s m')) (m_h m') xb nb cb /\
                  h_extra_max (m_h m') = h_extra_max (m_h m) /\ h_name_max (m_h m') = h_name_max (m_h m) /\
                  h_comm_max (m_h m') = h_comm_max (m_h m)
     end.
Proof.
  intros flush m xb nb cb Hok.
  pose proof (stepf2_hrel flush lenfix_list distfix_list m) as H.
  destruct (stepf2 flush lenfix_list distfix_list m) as [m'|r m'];
    unfold hrel, hd_ok_p in *; destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7); rewrite H1;
    (split; [reflexivity|]); (split; [|auto]);
    intros Hh; destruct (Hok Hh) as (A & B & C); auto.
Qed.

Lemma stepf2_inv : cover3_stmt ->
  (forall flush m, mwf3 m -> m_leave m = 0 ->
     match stepf2 flush lenfix_list distfix_list m with IBrk m' => mwf3 m' | IRet _ m' => mwf3 m' end) /\
  (forall flush m xb nb cb, hd_ok_p (i_head (m_s m)) (m_h m) xb nb cb ->
     match stepf2 flush lenfix_list distfix_list m with
     | IBrk m' => i_head (m_s m') = i_head (m_s m) /\ hd_ok_p (i_head (m_s m')) (m_h m') xb nb cb /\
                  h_extra_max (m_h m') = h_extra_max (m_h m) /\ h_name_max (m_h m') = h_name_max (m_h m) /\
                  h_comm_max (m_h m') = h_comm_max (m_h m)
     | IRet _ m' => i_head (m_s m') = i_head (m_s m) /\ hd_ok_p (i_head (m_s m')) (m_h m') xb nb cb /\
                  h_extra_max (m_h m') = h_extra_max (m_h m) /\ h_name_max (m_h m') = h_name_max (m_h m) /\
                  h_comm_max (m_h m') = h_comm_max (m_h m)
     end).
Proof.
  intros C. split; [exact (Step5Mwf.stepf2_mwf3_x C) | exact stepf2_hd].
Qed.
