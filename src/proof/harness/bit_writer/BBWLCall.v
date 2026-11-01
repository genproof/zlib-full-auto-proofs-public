(* Law rj_bad_block, main: the call of the loop's body (BBWLKit.bbl_call_stmt): code = inflate(&strm, flush)
   (SpecW.inflate_specW) offered the clip() pieces, `return 0` on Z_MEM_ERROR; on the other outcomes the theory
   (BBWDefs.bbw_call) gives BBWLKit.bbw_C. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5 Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.bit_writer.BWSpec.
Require Import Zlib.proof.harness.bit_writer.BBWDefs.
Require Import Zlib.proof.harness.bit_writer.BWLawCS Zlib.proof.harness.bit_writer.BWGlobals.
Require Import Zlib.proof.harness.bit_writer.BBWKit.
Require Import Zlib.proof.harness.bit_writer.BBWHelp.
Require Import Zlib.proof.harness.bit_writer.BBWLKit.
Local Open Scope logic.

(* the prologue of inflate() keeps the gz_header flag *)
Lemma bbl_m_init_head z L inp : i_head (m_s (m_init z L inp)) = i_head (l_s L).
Proof. unfold m_init. destruct (_ =? _); reflexivity. Qed.

Lemma bbl_call_ok : bbl_call_stmt.
Proof.
  intros Espec J gv vs vbt vbit S0 kind which lits room flush strp outp F A.
  destruct A as (Hok & Hroom & Hfl & Pstrp & Poutp).
  destruct (bb_bytes_ok _ _ _ _ Hok) as [LS BS].
  assert (H64: Zlength S0 <= Int64.max_signed) by (destruct Hok as (_ & _ & _ & _ & _ & Hz & _); lia).
  unfold bbl_call, bbl_mid, bbl_R, POST_B, bbw_POST. abbreviate_semax.
  Intros pos ob z L oc.
  rename H into HJ, H0 into Hsw, H1 into Hhd, H2 into Hpos, H3 into Hob, H4 into Hoc, H5 into Hz, H6 into HL.
  assert_PROP (isptr vs) as Pvs by entailer!.
  pose proof (Zlength_nonneg ob) as Hob0.
  set (S := bb_bytes S0 kind which lits) in *.
  set (ai := Z.min (Zlength S0 - pos) Int.max_unsigned) in *.
  set (ao := Z.min (room - Zlength ob) Int.max_unsigned) in *.
  assert (Hai: 0 <= ai <= Zlength S0 - pos /\ ai <= Int.max_unsigned) by (unfold ai; rep_lia).
  assert (Hao: 0 <= ao <= room - Zlength ob /\ ao <= Int.max_unsigned) by (unfold ao; rep_lia).
  set (inp := sublist pos (pos + ai) S).
  assert (Hinp: Zlength inp = ai) by (unfold inp; rewrite Zlength_sublist; lia).
  set (ib := bbl_ib strp (Zlength S0) pos S) in *.
  set (o := bbl_ob outp room (Zlength ob) oc) in *.
  set (z0 := bbl_offer_z z (offset_val pos strp) ai (offset_val (Zlength ob) outp) ao) in *.
  assert (INOK: in_ok ib inp) by (unfold ib, inp; apply bbl_in_ok; auto; rep_lia).
  assert (OUTOK: out_ok o ao) by (unfold o; apply bbl_out_ok; auto; rep_lia).
  assert (Z0: zf_ok z0) by (unfold z0, bbl_offer_z, zf_ok in *; simpl; rep_lia).
  forward_call (gv, Tsh, vs, z0, Vundef, Some L, ib, inp, Some o, flush, Ers, Ers, true, true).
  { unfold z0, bbl_offer_z, in_ptr, out_ptr, ib, o, bbl_ib, bbl_ob. simpl. rewrite !Z.add_0_r.
    refine (conj eq_refl (conj (conj INOK _) eq_refl)). lia. }
  Intros vret. destruct vret as [[[r z'] st'] ow]. simpl fst in *; simpl snd in *.
  match goal with Hr: inflate_rel _ _ _ _ _ _ _ _ _ _ _ |- _ => rename Hr into REL end.
  match goal with Hr: match st' with Some _ => _ | None => _ end |- _ => rename Hr into Hsw' end.
  destruct REL as [[Hib _] | [_ [L0 [o0 [res [winp [E1 [E2 [Hrun [Hsnx [Er [Eow [Ez [_ Est]]]]]]]]]]]]]].
  { exfalso. unfold inflate_bad, is_live in Hib.
    rewrite if_false in Hib by (destruct vs; try contradiction; discriminate).
    destruct Hib as [Hib | [Hib | [Hib _]]]; discriminate. }
  injection E1 as <-. injection E2 as <-.
  (* the theory on this call *)
  assert (Einp: inp = sublist pos (pos + Z.min (Zlength S - pos) Int.max_unsigned) S)
    by (unfold inp, ai; rewrite LS; reflexivity).
  pose proof (bbw_call J F S0 kind which lits room pos ob L z0 inp flush res Hok HJ HL Z0
                ltac:(clear -LS Hpos; unfold S in *; lia) ltac:(lia) Hob Einp eq_refl Hfl Hrun) as HP.
  subst r ow z' st'.
  set (L' := Live (l_sp L) winp (m_s (r_m res)) (m_h (r_m res)) (l_headp L) (l_hsh L) (l_xb L) (l_nb L) (l_cb L))
    in *.
  set (z' := z_after z0 ib o res) in *.
  forward_if.
  { (* Z_MEM_ERROR: return 0 *)
    forward. Exists (Int.repr 0). sep_apply (bbl_a_frame_opt gv Tsh vs z' Vundef (Some L')); auto. entailer!. }
  (* the other outcomes: bbw_C *)
  assert (Hr: r_ret res <> Z_MEM_ERROR) by (intro E; rewrite E in H; contradiction).
  clear H.
  forward.
  rewrite bbl_istreamA_opt_ptr by auto.
  unfold ib, o. sep_apply (bbl_bufs_post vs L strp (Zlength S0) pos S outp room (Zlength ob) oc (m_ow (r_m res))); auto.
  set (oc' := bbl_oc room (Zlength ob) oc (m_ow (r_m res))).
  assert_PROP (Zlength oc' = room) as Hoc'.
  { entailer!. }
  assert (Hir: 0 <= Zlength S0 - pos <= Int64.max_unsigned) by rep_lia.
  assert (Hor: 0 <= room - Zlength ob <= Int64.max_unsigned) by rep_lia.
  cbv beta zeta delta [bbw_post] in HP.
  unfold bbw_C.
  destruct HP as [Hd | [Hm | (Hc & Hsnx' & Hsow & Hlow & HJ' & Hnc)]].
  - (* Z_DATA_ERROR *)
    assert (CP: bbw_cpost J strp outp S0 kind which lits room flush (Zlength S0 - pos) (room - Zlength ob)
                  (r_ret res) pos ob z' L') by (left; exact Hd).
    Exists (Zlength S0 - pos) (room - Zlength ob) (r_ret res) pos ob z' L' oc'. entailer!.
  - contradiction.
  - (* Z_OK or Z_BUF_ERROR: the invariant at the new position *)
    destruct (bbl_run2_frame _ _ _ _ _ Hrun Hc) as (Fi & Fa & Fh).
    rewrite bbl_m_init_head, Hhd in Fh.
    change (m_inp (m_init z0 L inp)) with inp in Fi. change (m_aout (m_init z0 L inp)) with ao in Fa.
    change (zf_ao z0) with ao in Hlow.
    set (snx := m_snx (r_m res)) in *. set (ow := m_ow (r_m res)) in *.
    assert (Eni: zf_ni z' = offset_val (pos + snx) strp) by reflexivity.
    assert (Eno: zf_no z' = offset_val (Zlength (ob ++ ow)) outp)
      by (unfold z', z_after; simpl; rewrite Hsow, Zlength_app; reflexivity).
    assert (Eai: zf_ai z' = ai - snx) by (unfold z', z_after; simpl; rewrite Fi, Hinp; reflexivity).
    assert (Eao: zf_ao z' = ao - Zlength ow) by (unfold z', z_after; simpl; rewrite Fa, Hsow; reflexivity).
    assert (CP: bbw_cpost J strp outp S0 kind which lits room flush (Zlength S0 - pos) (room - Zlength ob)
                  (r_ret res) (pos + snx) (ob ++ ow) z' L').
    { right. split; [exact Hc | ]. split; [exact HJ' | ]. split; [exact Hsw' | ]. split; [exact Fh | ].
      split; [lia | ]. split; [rewrite Zlength_app; lia | ]. split; [exact Eni | ]. split; [exact Eno | ].
      intros C1 C2.
      destruct (Hnc ltac:(clear -LS C1; unfold S in *; lia) C2) as (Hok1 & Hft & How & Hx).
      split; [exact Hok1 | ]. split; [exact Hft | ].
      assert (Eai': ai = Zlength S0 - pos) by (unfold ai; lia).
      assert (Eao': ao = room - Zlength ob) by (unfold ao; lia).
      split; [lia | ]. split; [rewrite Eao, Zlength_app, How; simpl; lia | exact Hx]. }
    rewrite (bbl_head_none vs L') by auto.
    Exists (Zlength S0 - pos) (room - Zlength ob) (r_ret res) (pos + snx) (ob ++ ow) z' L' oc'. entailer!.
Qed.
