(* inflate(), the switch case LENLENS (17), version 5: the two loops and inflate_table(CODES), falls through into
   CODELENS; assembled from LLLoop5 / LLZero5 / LLTail5 *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.CaseHyps5.
Require Import Zlib.proof.inflate.NeedKit5.
Require Import Zlib.proof.inflate.Model2 Zlib.proof.inflate.Steps2 Zlib.proof.inflate.MwfLemmas.
Require Import Zlib.proof.inflate.TLFacts Zlib.proof.inflate.LLDefs5.
Require Import Zlib.proof.inflate.LLLoop5 Zlib.proof.inflate.LLZero5 Zlib.proof.inflate.LLTail5.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* the model's pass after the first loop *)
Lemma ll_model_leave: forall fl m m1, lenlens_loop 19 m = m1 -> m_leave m1 = 1 ->
  c_LENLENS fl lenfix_list distfix_list (fast lenfix_list distfix_list) m = IBrk m1.
Proof.
  intros fl m m1 E1 L1. rewrite c_LENLENS_eq. rewrite E1. cbv zeta. rewrite L1. reflexivity.
Qed.

Lemma ll_model_tail: forall fl m m1, lenlens_loop 19 m = m1 -> m_leave m1 = 0 ->
  c_LENLENS fl lenfix_list distfix_list (fast lenfix_list distfix_list) m =
    (let sZ := lenlens_zero 19 (m_s m1) in
     let mm := set_m_ret (set_m_s m1 (tl_s1 sZ)) (tl_r sZ) in
     if negb (tl_r sZ =? 0) then IBrk (set_bad mm M_cl_set) else
     c_CODELENS fl lenfix_list distfix_list (fast lenfix_list distfix_list) (tl_mcl m1)).
Proof.
  intros fl m m1 E1 L1.
  rewrite c_LENLENS_eq. rewrite E1. cbv zeta. rewrite L1. change (0 =? 1) with false. cbv iota.
  assert (Emcl: set_mode (upd_s (set_m_ret (set_m_s m1 (tl_s1 (lenlens_zero 19 (m_s m1))))
                  (tl_r (lenlens_zero 19 (m_s m1)))) (fun s => set_i_have s 0)) CODELENS = tl_mcl m1)
    by reflexivity.
  rewrite Emcl. reflexivity.
Qed.

Lemma ll_after1 {Espec: OracleKind} (F: frame) (m m1: mst) : frame_ok5 F -> cover3_stmt ->
  stepf2 (f_flush F) lenfix_list distfix_list m = c_LENLENS (f_flush F) lenfix_list distfix_list (fast lenfix_list distfix_list) m ->
  ll_exit m m1 ->
  semax Delta_cases5 (loop_state F m1)
    (Ssequence (Sifthenelse (Etempvar _leave tint) Sbreak Sskip) (Ssequence ll_zero ll_tail))
    (overridePost (fall_post5 F m CODELENS) (switch_ret_assert (case_post2 F m))).
Proof.
  intros HF C3 E0 (E1 & W1 & M1 & X1).
  apply semax_seq with (Q := !! (m_leave m1 = 0) && loop_state F m1).
  { apply (semax_ifleave5 F m m1); [exact W1 | reflexivity | ].
    intro L1. rewrite E0. exact (ll_model_leave _ m m1 E1 L1). }
  apply semax_extract_prop; intros L1.
  destruct X1 as [X1 | [_ X1]]; [lia | ].
  eapply semax_seq'; [apply (ll_zero_ok F m1 HF W1 M1 L1 X1) | ].
  apply (ll_tail_ok F m m1 HF C3 W1 M1 L1 X1).
  rewrite E0. exact (ll_model_tail _ m m1 E1 L1).
Qed.

Lemma case_LENLENS5 {Espec: OracleKind} (F: frame) : frame_ok5 F -> cover3_stmt ->
  case_ok5 F CODELENS 18 -> case_ok5 F LENLENS 17.
Proof.
  intros HF C3 HY m HM HL [W W3].
  pose proof (stepf2_LENLENS (f_flush F) lenfix_list distfix_list m HM) as E0.
  apply (case_fallthrough5 F m CODELENS 17); [lia | exact HY | ].
  change (case_body 17) with ll_body. rewrite ll_body_eq.
  eapply semax_seq'; [apply (ll_loop1_ok F m HF W HM HL) | ].
  apply extract_exists_pre; intro m1. apply semax_extract_prop; intros X.
  exact (ll_after1 F m m1 HF C3 E0 X).
Qed.
