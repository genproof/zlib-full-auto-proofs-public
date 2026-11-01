(* inflate(), the switch cases CODELENS (18), version 5 (Delta_cases5, case_post2 over Model2.v, mwf3; header cases
   FLAGS .. COMMON with the header buffers' tokens: CaseHyps5.v, CaseKitT5.v) *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.CaseHyps5.
Require Import Zlib.proof.inflate.CLKit5 Zlib.proof.inflate.Steps2.
Require Import Zlib.proof.inflate.CLLookup5 Zlib.proof.inflate.CLSmall5 Zlib.proof.inflate.CLRep5
  Zlib.proof.inflate.CLFill5 Zlib.proof.inflate.CLWhile5 Zlib.proof.inflate.CLLens5 Zlib.proof.inflate.CLDists5
  Zlib.proof.inflate.CLTabFacts5.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* after the loop: if (leave) break; if (state->mode == BAD) break; if (state->lens[256] == 0) { BAD } *)
Definition cl_pre1 : statement := match cl_tail with Ssequence a _ => a | _ => Sskip end.
Definition cl_pre2 : statement := match cl_tail with Ssequence _ (Ssequence b _) => b | _ => Sskip end.
Definition cl_pre3 : statement := match cl_tail with Ssequence _ (Ssequence _ (Ssequence c _)) => c | _ => Sskip end.

Definition t_st := Tstruct _inflate_state noattr.

Lemma cl_pre1_eq: cl_pre1 = Sifthenelse (Etempvar _leave tint) Sbreak Sskip.
Proof. reflexivity. Qed.

Lemma cl_pre2_eq: cl_pre2 =
  Ssequence (Sset _t'289 (Efield (Ederef (Etempvar _state (tptr t_st)) t_st) _mode tint))
    (Sifthenelse (Ebinop Oeq (Etempvar _t'289 tint) (Econst_int (Int.repr 16209) tint) tint) Sbreak Sskip).
Proof. reflexivity. Qed.

Lemma cl_pre3_eq: cl_pre3 =
  Ssequence (Sset _t'288 (Ederef (Ebinop Oadd (Efield (Ederef (Etempvar _state (tptr t_st)) t_st) _lens (tarray tushort 320))
                                  (Econst_int (Int.repr 256) tint) (tptr tushort)) tushort))
    (Sifthenelse (Ebinop Oeq (Etempvar _t'288 tushort) (Econst_int (Int.repr 0) tint) tint)
      (Ssequence
        (Sassign (Efield (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr))) (Tstruct _z_stream_s noattr)) _msg (tptr tschar))
           (Ecast (Evar ___stringlit_inflate_8 (tarray tschar 37)) (tptr tschar)))
        (Ssequence (Sassign (Efield (Ederef (Etempvar _state (tptr t_st)) t_st) _mode tint) (Econst_int (Int.repr 16209) tint))
           Sbreak))
      Sskip).
Proof. reflexivity. Qed.

Lemma cl_tail_eq: cl_tail = Ssequence cl_pre1 (Ssequence cl_pre2 (Ssequence cl_pre3 cl_tables)).
Proof. reflexivity. Qed.

Lemma cases5_CL {Espec: OracleKind} (F: frame) : frame_ok5 F -> cover3_stmt ->
  (case_ok5 F LEN_ 19 -> case_ok5 F CODELENS 18).
Proof.
  intros HF C3 HY m HM HL [W W3].
  pose proof (stepf2_CODELENS (f_flush F) lenfix_list distfix_list m HM) as E0.
  rewrite c_CODELENS_eq in E0.
  apply (case_fallthrough5 F m LEN_ 18); [lia | exact HY | ].
  change (case_body 18) with cl_body. rewrite cl_body_eq.
  eapply semax_seq'.
  { apply (cl_while_ok cl_lookup_ok cl_small_ok cl_rep_ok cl_fill_ok); auto. }
  apply extract_exists_pre; intro m1. apply extract_exists_pre; intro hv.
  apply semax_extract_prop; intros HX.
  rewrite cl_tail_eq.
  destruct HX as [(Lx & W1 & M1 & L1 & H1) | [(Lx & L1) | (Lx & L1 & M1)]]; rewrite Lx in E0.
  - (* the code lengths are complete *)
    rewrite loop_state_h_cl. unfold loop_state_clh, cl_sep, loop_locals. abbreviate_semax.
    rewrite cl_pre1_eq. forward_if.
    { rewrite L1 in H. contradiction. }
    rewrite cl_pre2_eq. forward. forward_if.
    { exfalso. assert (Hmd: i_mode (m_s m1) = CODELENS) by exact M1.
      match goal with Hm: Int.repr (i_mode (m_s m1)) = _ |- _ => rewrite Hmd in Hm;
        apply repr_inj_signed in Hm; [unfold CODELENS in Hm; discriminate | unfold CODELENS; rep_lia | rep_lia] end. }
    rewrite cl_pre3_eq.
    pose proof (sw_lens _ (mw_s _ W1)) as [ZL FL].
    assert (R256: 0 <= Znth 256 (i_lens (m_s m1)) <= 65535)
      by (rewrite Forall_forall in FL; apply FL, Znth_In; lia).
    forward; [entailer!; lia | ].
    forward_if.
    { (* no end-of-block code *)
      assert (E: Znth 256 (i_lens (m_s m1)) = 0).
      { assumption. }
      rewrite E in E0. cbn [Z.eqb] in E0.
      pose proof HF as [[Hshs _] _].
      unfold cl_strm, strm_rep.
      remember (f_gv F _zcalloc) as zca eqn:Hzca. remember (f_gv F _zcfree) as zcf eqn:Hzcf.
      forward. forward. forward.
      change (RA_break _) with (RA_normal (case_post2 F m)). unfold case_post2; cbn [RA_normal].
      Exists (set_bad m1 M_eob).
      assert (MR: mem_rest_cl F (set_bad m1 M_eob) = mem_rest_cl F m1) by reflexivity.
      rewrite loop_state_h_def, loop_state_h_cl. unfold loop_state_clh, cl_sep, loop_locals, cl_strm, strm_rep.
      rewrite MR. unfold set_bad, m_have, m_left. mnorm_goal. cbn [msg_val msg_ident]. rewrite <- Hzca, <- Hzcf.
      entailer!. }
    assert (E: Znth 256 (i_lens (m_s m1)) <> 0).
    { match goal with Hz: Znth 256 _ <> 0 |- _ => exact Hz
        | Hz: Int.repr (Znth 256 _) <> Int.repr 0 |- _ => intro Ez; apply Hz; rewrite Ez; reflexivity end. }
    rewrite (proj2 (Z.eqb_neq _ _) E) in E0.
    unfold abbreviate in POSTCONDITION. subst POSTCONDITION.
    eapply semax_pre; [ | apply (cl_lens_ok Espec F m m1 hv HF W1 M1 L1 H1 E0)].
    + rewrite loop_state_h_cl. unfold loop_state_clh, cl_sep, loop_locals. entailer!.
    + intros mA hv' EA. destruct (cl_tab_facts C3 m1 W1 M1 L1 H1 mA EA) as [P1 P2].
      apply cl_dists_ok; auto.
      rewrite E0. unfold cl_lens_out. rewrite EA. reflexivity.
  - (* out of input *)
    rewrite loop_state_h_cl. unfold loop_state_clh, cl_sep, loop_locals. abbreviate_semax.
    rewrite cl_pre1_eq. forward_if.
    { forward. change (RA_break _) with (RA_normal (case_post2 F m)). unfold case_post2; cbn [RA_normal].
      Exists m1. rewrite loop_state_h_def, loop_state_h_cl. unfold loop_state_clh, cl_sep, loop_locals. entailer!. }
    { rewrite L1 in H. discriminate. }
  - (* BAD *)
    rewrite loop_state_h_cl. unfold loop_state_clh, cl_sep, loop_locals. abbreviate_semax.
    rewrite cl_pre1_eq. forward_if.
    { rewrite L1 in H. contradiction. }
    rewrite cl_pre2_eq. forward. forward_if.
    { forward. change (RA_break _) with (RA_normal (case_post2 F m)). unfold case_post2; cbn [RA_normal].
      Exists m1. rewrite loop_state_h_def, loop_state_h_cl. unfold loop_state_clh, cl_sep, loop_locals. entailer!. }
    { exfalso. assert (Hmd: i_mode (m_s m1) = BAD) by exact M1.
      match goal with Hm: Int.repr (i_mode (m_s m1)) <> _ |- _ => apply Hm; rewrite Hmd; reflexivity end. }
Qed.
