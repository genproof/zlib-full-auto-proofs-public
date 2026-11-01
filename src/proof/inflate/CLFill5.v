(* case CODELENS: the range check of a repeat and the copy loop while (copy--) state->lens[state->have++] = len; (CLKit5.cl_fill; model lens_fill) *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.CLKit5.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* the lens list after k copies of len from position h *)
Fixpoint cl_fill_l (k: nat) (len h: Z) (l: list Z) : list Z :=
  match k with
  | O => l
  | S k' => cl_fill_l k' len (h + 1) (upd_Znth h l len)
  end.

Lemma cl_fill_l_S: forall k len h l,
  cl_fill_l (S k) len h l = upd_Znth (h + Z.of_nat k) (cl_fill_l k len h l) len.
Proof.
  induction k; intros len h l.
  - simpl. rewrite Z.add_0_r. reflexivity.
  - change (cl_fill_l (S (S k)) len h l) with (cl_fill_l (S k) len (h + 1) (upd_Znth h l len)).
    rewrite IHk. f_equal. lia.
Qed.

Lemma cl_fill_l_len: forall k len h l, Zlength (cl_fill_l k len h l) = Zlength l.
Proof.
  induction k; intros len h l; simpl; [reflexivity | ]. rewrite IHk. apply Zlength_upd_Znth.
Qed.

Lemma cl_lens_fill_eq: forall k len s,
  lens_fill k len s = set_i_have (set_i_lens s (cl_fill_l k len (i_have s) (i_lens s))) (i_have s + Z.of_nat k).
Proof.
  induction k; intros len s.
  - simpl. rewrite Z.add_0_r. destruct s; reflexivity.
  - simpl. rewrite IHk. destruct s; unfold set_i_have, set_i_lens; simpl. f_equal. rewrite Zpos_P_of_succ_nat. lia.
Qed.

Definition cl_fill_post (F: frame) (m: mst) (here: entry) (copy len: Z) : ret_assert :=
    {| RA_normal := !! (i_have (m_s m) + copy <= i_nlen (m_s m) + i_ndist (m_s m)) &&
         loop_state_h F (upd_s m (lens_fill (Z.to_nat copy) len)) (ent here);
       RA_break := !! (i_nlen (m_s m) + i_ndist (m_s m) < i_have (m_s m) + copy) &&
         loop_state_h F (set_bad m M_repeat) (ent here);
       RA_continue := FF;
       RA_return := fun _ => FF |}.

Lemma cl_fill_ok : cl_fill_stmt.
Proof.
  intros Espec F m here len copy HF W HM HL HLen HC HH.
  match goal with |- semax _ _ _ ?R => change R with (cl_fill_post F m here copy len) end.
  pose proof (sw_lens _ (mw_s _ W)) as [LL LF]. pose proof (sw_have _ (mw_s _ W)) as HV0.
  pose proof (mw_md _ W) as MD.
  destruct (md_codelens _ MD HM) as (_ & HN & HD & _).
  rewrite loop_state_hc_cl. unfold loop_state_clhc, cl_sep, ent.
  unfold cl_fill; cl_stmt. abbreviate_semax. unfold loop_locals.
  freeze [5;6;7;8;9;10;11;13;14;15;16;17] FR.
  forward. forward. forward.
  forward_if.
  { (* BAD *)
    destruct HF as [(Hshs & _) _]. unfold cl_strm, strm_rep.
    remember (f_gv F _zcalloc) as za eqn:Eza. remember (f_gv F _zcfree) as zf eqn:Ezf.
    forward. forward. forward.
    unfold cl_fill_post. cbn [RA_break].
    apply andp_right; [apply prop_right; lia | ].
    assert (MR: mem_rest_cl F (set_bad m M_repeat) = mem_rest_cl F m) by reflexivity.
    thaw FR. rewrite loop_state_h_cl. unfold loop_state_clh, cl_sep, loop_locals, cl_strm, strm_rep, ent. rewrite MR.
    unfold set_bad, m_have, m_left. mnorm_goal. cbn [msg_val msg_ident]. rewrite <- Eza, <- Ezf.
    entailer!. }
  set (h := i_have (m_s m)). set (l := i_lens (m_s m)). abbreviate_semax.
  forward_loop (@exp (environ -> mpred) _ Z (fun i =>
    PROPx [0 <= i <= copy]
    (LOCALx (temp _len (zv len) :: temp _copy (zv (copy - i)) :: loop_locals F m)
    (SEPx [FRZL FR;
          field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F);
          field_at Ews t_state (DOT _nlen) (zv (i_nlen (m_s m))) (f_sp F);
          field_at Ews t_state (DOT _ndist) (zv (i_ndist (m_s m))) (f_sp F);
          field_at Ews t_state (DOT _have) (zv (h + i)) (f_sp F);
          field_at Ews t_state (DOT _lens) (map (fun z => Vint (Int.repr z)) (cl_fill_l (Z.to_nat i) len h l)) (f_sp F);
          cl_strm F m])))).
  { Exists 0. unfold loop_locals. rewrite Z.add_0_r, Z.sub_0_r. entailer!. }
  Intros i. unfold loop_locals.
  forward. forward. forward_if.
  - forward. forward. forward.
    Exists (i + 1). unfold loop_locals.
    assert (E: cl_fill_l (Z.to_nat (i + 1)) len h l = upd_Znth (h + i) (cl_fill_l (Z.to_nat i) len h l) len).
    { rewrite Z2Nat.inj_add by lia. change (Z.to_nat 1) with 1%nat. rewrite Nat.add_1_r, cl_fill_l_S, Z2Nat.id by lia.
      reflexivity. }
    rewrite E, <- upd_Znth_map, sub_repr, add_repr.
    assert (ZE: Int.zero_ext 16 (Int.repr len) = Int.repr len).
    { apply zero_ext_inrange. rewrite Int.unsigned_repr by rep_lia. simpl. lia. }
    rewrite !ZE.
    replace (h + (i + 1)) with (h + i + 1) by lia. replace (copy - (i + 1)) with (copy - i - 1) by lia.
    entailer!.
  - assert (Ei: i = copy).
    { assert (copy - i = 0); [ | lia]. apply repr_inj_unsigned in H3; rep_lia. }
    subst i. forward.
    unfold cl_fill_post. cbn [RA_normal].
    apply andp_right; [apply prop_right; lia | ].
    unfold upd_s. rewrite cl_lens_fill_eq, Z2Nat.id by lia.
    assert (MR: mem_rest_cl F (set_m_s m (set_i_have (set_i_lens (m_s m) (cl_fill_l (Z.to_nat copy) len h l)) (h + copy))) = mem_rest_cl F m) by reflexivity.
    assert (SR: cl_strm F (set_m_s m (set_i_have (set_i_lens (m_s m) (cl_fill_l (Z.to_nat copy) len h l)) (h + copy))) = cl_strm F m) by reflexivity.
    rewrite loop_state_h_cl. unfold loop_state_clh, cl_sep, ent. fold h l. rewrite MR, SR. thaw FR.
    unfold loop_locals, m_have, m_left. mnorm_goal.
    entailer!.
Qed.
