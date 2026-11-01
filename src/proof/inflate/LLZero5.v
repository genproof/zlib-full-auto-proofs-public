(* case LENLENS, the zero loop: while (state->have < 19) state->lens[order[state->have++]] = 0;
   (LLDefs5.ll_zero; model Model.v lenlens_zero, TLFacts.v lenlens_zero_S / tl_zero_ok) *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.CaseHyps5.
Require Import Zlib.proof.inflate.NeedKit5 Zlib.proof.inflate.NeedBits Zlib.proof.inflate.NeedBits3_5.
Require Import Zlib.proof.inflate.Model2 Zlib.proof.inflate.Steps2 Zlib.proof.inflate.MwfLemmas.
Require Import Zlib.proof.inflate.TLFacts Zlib.proof.inflate.TLKit5 Zlib.proof.inflate.LLDefs5.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* the states of the zero loop: only lens and have differ from the start *)
Definition llz (s: istate) (L: list Z) (h: Z) : istate := set_i_have (set_i_lens s L) h.

Lemma llz_eta: forall s, llz s (i_lens s) (i_have s) = s.
Proof. intros []; reflexivity. Qed.

(* the static tables but order[] *)
Definition tables_rest (gsh: share) (gv: globals) : mpred :=
  data_at gsh (tarray t_code 512) (map ent lenfix_list) (gv g_lenfix) *
  data_at gsh (tarray t_code 32) (map ent distfix_list) (gv g_distfix) *
  Zlib.proof.inftrees.spec.itables gsh gv.

Lemma tables_rep_order: forall gsh gv, tables_rep gsh gv =
  data_at gsh (tarray tushort 19) (map (fun z => Vint (Int.repr z)) order) (gv _order) * tables_rest gsh gv.
Proof. intros. unfold tables_rep, tables_rest. apply pred_ext; cancel. Qed.

Lemma ll_zero_ok {Espec: OracleKind} (F: frame) (m1: mst) :
  frame_ok5 F -> mwf m1 -> m_mode m1 = LENLENS -> m_leave m1 = 0 -> i_ncode (m_s m1) <= i_have (m_s m1) ->
  semax Delta_cases5 (loop_state F m1) ll_zero
    (normal_ret_assert (loop_state F (set_m_s m1 (lenlens_zero 19 (m_s m1))))).
Proof.
  intros HF W HM HL HN.
  ll_stmt.
  assert (Z0: tl_zok (m_s m1)).
  { destruct (md_lenlens _ (mw_md _ W) HM) as (C1 & C2 & C3 & C4 & C5).
    destruct (sw_lens _ (mw_s _ W)) as [ZL FL].
    split; [lia | split; [exact ZL | split; [exact FL | exact C5]]]. }
  set (s1 := m_s m1) in *.
  rewrite loop_state_tl_eq. unfold loop_state_tl, tl_sep. abbreviate_semax.
  freeze [0;1;2;3;6;7;8;9;10;11;12;14;15] FR.
  forward_loop (EX L: list Z, EX h: Z, EX k: nat,
    PROPx [tl_zok (llz s1 L h); lenlens_zero k (llz s1 L h) = lenlens_zero 19 s1; 19 - h <= Z.of_nat k;
          in_ok (f_ib F) (m_inp m1); out_ok (f_ob F) (m_aout m1)]
    (LOCALx (tl_locals F m1)
    (SEPx [FRZL FR; field_at Ews t_state (DOT _have) (zv h) (f_sp F);
         field_at Ews t_state (DOT _lens) (map (fun z => Vint (Int.repr z)) L) (f_sp F);
         tables_rep (f_gsh F) (f_gv F)])))%assert
    break: (EX L: list Z,
    PROPx [llz s1 L 19 = lenlens_zero 19 s1; in_ok (f_ib F) (m_inp m1); out_ok (f_ob F) (m_aout m1)]
    (LOCALx (tl_locals F m1)
    (SEPx [FRZL FR; field_at Ews t_state (DOT _have) (zv 19) (f_sp F);
         field_at Ews t_state (DOT _lens) (map (fun z => Vint (Int.repr z)) L) (f_sp F);
         tables_rep (f_gsh F) (f_gv F)])))%assert.
  - Exists (i_lens s1) (i_have s1) 19%nat. rewrite llz_eta.
    unfold tl_locals. entailer!. destruct Z0 as [Z0 _]. simpl. lia.
  - Intros L h k. unfold tl_locals. forward.
    pose proof H as HZ. unfold llz in HZ. destruct HZ as (Hh & ZL & FL & LE). cbn [i_have i_lens set_i_have set_i_lens] in Hh, ZL, FL, LE.
    forward_if.
    + forward. forward.
      destruct HF as ((Hshs & Hhsh & Hgsh & Htsh) & Hfl).
      rewrite tables_rep_order. Intros. freeze [4] TT.
      pose proof (tl_order_range h ltac:(lia)) as OR. pose proof tl_order_len as OLen.
      forward.
      { entailer!. lia. }
      forward.
      destruct k as [|k]; [simpl in H1; lia | ].
      set (L' := upd_Znth (Znth h order) L 0).
      assert (Z1: tl_zok (llz s1 L' (h + 1))) by exact (tl_zero_step_ok _ H H4).
      assert (E1: lenlens_zero k (llz s1 L' (h + 1)) = lenlens_zero 19 s1).
      { rewrite <- H0, lenlens_zero_S. cbn [i_have llz set_i_have]. destruct (Z.ltb_spec h 19); [ | lia].
        reflexivity. }
      Exists L' (h + 1) k. thaw TT. rewrite tables_rep_order. unfold tl_locals.
      unfold L'. rewrite <- upd_Znth_map. change (Int.zero_ext 16 (Int.repr 0)) with (Int.repr 0).
      rewrite add_repr. entailer!.
    + assert (h = 19) by lia. subst h.
      forward. Exists L. unfold tl_locals. entailer!.
      rewrite <- H0. symmetry. apply lenlens_zero_done. simpl. lia.
  - Intros L. rewrite <- H. rewrite loop_state_tl_eq. unfold loop_state_tl, tl_sep.
    assert (MR: mem_rest_tl F (set_m_s m1 (llz s1 L 19)) = mem_rest_tl F m1) by reflexivity.
    assert (SR: tl_strm F (set_m_s m1 (llz s1 L 19)) = tl_strm F m1) by reflexivity.
    assert (LR: tl_locals F (set_m_s m1 (llz s1 L 19)) = tl_locals F m1) by reflexivity.
    rewrite MR, SR, LR. cbn [m_s set_m_s m_inp m_aout llz set_i_have set_i_lens i_mode i_nlen i_ndist i_ncode
      i_have i_lens i_next i_lencode i_distcode i_lenbits i_codes].
    thaw FR. unfold tl_locals. entailer!.
Qed.
