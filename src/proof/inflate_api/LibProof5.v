(* The inflate area's library bodies (LibStmt5.inflate_lib5_stmt), assembled from the body proofs:
   the API bodies (Body5_<api>.v), inflate()'s body (Body5_inflate.v) from every switch case
   (CasesAll5.v), the model's invariants (InvQ5.v, StepMwf5.v), inflate_fast (BodyF5.v), updatewindow
   (BodyUw5.v), inflate_fixed and inflateStateCheck (BodySmall.v). *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate_api.LibStmt5.
Require Zlib.proof.inflate.InvQ5.
Require Zlib.proof.inflate.CasesAll5.
Require Zlib.proof.inflate.StepMwf5.
Require Zlib.proof.inflate.BodySmall.
Require Zlib.proof.inflate.BodyUw5.
Require Zlib.proof.inffast.BodyF5.
Require Zlib.proof.inflate_api.Body5_init.
Require Zlib.proof.inflate_api.Body5_reset.
Require Zlib.proof.inflate_api.Body5_dict.
Require Zlib.proof.inflate_api.Body5_misc.
Require Zlib.proof.inflate_api.Body5_sync.
Require Zlib.proof.inflate_api.Body5_inflate.
#[local] Existing Instance Zlib.units.Inflate.CS.

(* a header field marked present has a buffer, as booleans *)
Definition nn (v: val) : bool := if eq_dec v nullval then false else true.

Lemma nn_true: forall v, nn v = true <-> v <> nullval.
Proof.
  intros v. unfold nn. destruct (eq_dec v nullval); split; intros H; try discriminate; auto.
  all: try contradiction.
Qed.

Lemma hd_ok_iff: forall F m,
  hd_ok F m <->
  Zlib.proof.inflate.StepMwf5.hd_ok_p (i_head (m_s m)) (m_h m) (nn (f_xb F)) (nn (f_nb F)) (nn (f_cb F)).
Proof.
  intros F m. unfold hd_ok, Zlib.proof.inflate.StepMwf5.hd_ok_p. rewrite !nn_true. tauto.
Qed.

Lemma stepf2_hd_proof : stepf2_hd_stmt.
Proof.
  intros F flush m H. apply hd_ok_iff in H.
  pose proof (Zlib.proof.inflate.StepMwf5.stepf2_hd flush m _ _ _ H) as Q.
  destruct (stepf2 flush lenfix_list distfix_list m) as [m'|r m'];
    destruct Q as (_ & Q & _); apply hd_ok_iff; exact Q.
Qed.

Lemma inflate_lib5_proof : inflate_lib5_stmt.
Proof.
  split; [exact Zlib.proof.inflate_api.Body5_init.api5_init | ].
  split; [exact Zlib.proof.inflate_api.Body5_reset.api5_reset | ].
  split; [exact Zlib.proof.inflate_api.Body5_dict.api5_dict | ].
  split; [exact Zlib.proof.inflate_api.Body5_misc.api5_misc | ].
  split; [exact Zlib.proof.inflate_api.Body5_sync.api5_sync | ].
  split.
  { exact (Zlib.proof.inflate_api.Body5_inflate.body_inflate_proof5
             Zlib.proof.inflate.CasesAll5.cases_all5_proof
             Zlib.proof.inflate.InvQ5.stepf2_mwf3_proof stepf2_hd_proof). }
  split; [intros Espec; exact Zlib.proof.inffast.BodyF5.body_inflate_fast5 | ].
  split; [intros Espec; exact Zlib.proof.inflate.BodyUw5.body_updatewindow5 | ].
  split; [intros Espec; exact Zlib.proof.inflate.BodySmall.body_inflate_fixed | ].
  intros Espec; exact Zlib.proof.inflate.BodySmall.body_inflateStateCheck.
Qed.
