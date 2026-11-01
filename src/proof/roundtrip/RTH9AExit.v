(* inflate()'s exit inf_leave from the machine after the main loop, in any mode (RTH9AKit.exit9_stmt):
   RTH9Parts.exit_part9_stmt on the machine with the small header RTH8W.mcanon, the header hd9 in the frame. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTH8Spec.
Require Import Zlib.proof.roundtrip.RTH9AKit.
Require Zlib.proof.roundtrip.RTH8SimKit.
Require Zlib.proof.roundtrip.RTH8Pure.
Require Zlib.proof.inflate_api.Body5Fin.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* inf_leave does not read the header model: an outcome from c is one from c with any header model h *)
Lemma exit9_leave_h fl c h res : inf_leave fl c res -> inf_leave fl (set_m_h c h) (res_h res h).
Proof.
  intros IL. destruct IL as [U W|].
  - change (res_h (Res Z_MEM_ERROR (set_mode (restore c) MEM) None) h)
      with (Res Z_MEM_ERROR (set_mode (restore (set_m_h c h)) MEM) None).
    apply il_mem; [exact U | exact W].
  - change (set_m_h c h) with (RTH8SimKit.mh h c).
    change (res_h (leave_fin fl c) h) with (RTH8SimKit.rh h (leave_fin fl c)).
    rewrite <- RTH8SimKit.hr_leave_fin. apply il_ok.
Qed.

(* the window update keeps the fields the partial header's representation reads *)
Lemma exit9_uw_length s d : i_length (updatewindow s d) = i_length s.
Proof. unfold updatewindow; cbv zeta; destruct (i_wsize s =? 0), (_ <=? _); try destruct (negb _); reflexivity. Qed.

Lemma exit9_uw_flags s d : i_flags (updatewindow s d) = i_flags s.
Proof. unfold updatewindow; cbv zeta; destruct (i_wsize s =? 0), (_ <=? _); try destruct (negb _); reflexivity. Qed.

(* the two halves of leave_fin (Body5Fin.leave_fin_eq) keep the mode, the length counter and the flags; the
   second half on a machine m2 left abstract, so that the lets of leave_fin are not expanded into each other *)
Lemma exit9_mid_keep fl m :
  let s := m_s (Zlib.proof.inflate_api.Body5Fin.lf_mid fl m) in
  i_mode s = i_mode (m_s m) /\ i_length s = i_length (m_s m) /\ i_flags s = i_flags (m_s m).
Proof.
  unfold Zlib.proof.inflate_api.Body5Fin.lf_mid. cbv zeta.
  destruct (leave_ok fl m); cbn [m_s set_m_s set_m_sow set_m_snx upd_s restore set_i_win set_i_bits set_i_hold
                                 i_mode i_length i_flags].
  - rewrite RTH8SimKit.hb_updatewindow_md, exit9_uw_length, exit9_uw_flags. auto.
  - auto.
Qed.

Lemma exit9_tail_keep fl m2 :
  let s := m_s (r_m (Zlib.proof.inflate_api.Body5Fin.lf_tail fl m2)) in
  i_mode s = i_mode (m_s m2) /\ i_length s = i_length (m_s m2) /\ i_flags s = i_flags (m_s m2).
Proof.
  unfold Zlib.proof.inflate_api.Body5Fin.lf_tail. cbv zeta. cbn [r_m].
  destruct (andb _ _);
    cbn [r_m m_s set_m_s set_m_tout set_m_tin set_m_adler upd_s set_i_total set_i_check i_mode i_length i_flags];
    auto.
Qed.

Lemma exit9_lf_keep fl m :
  i_mode (m_s (r_m (leave_fin fl m))) = i_mode (m_s m) /\ i_length (m_s (r_m (leave_fin fl m))) = i_length (m_s m) /\
  i_flags (m_s (r_m (leave_fin fl m))) = i_flags (m_s m).
Proof.
  rewrite Zlib.proof.inflate_api.Body5Fin.leave_fin_eq.
  destruct (exit9_tail_keep fl (Zlib.proof.inflate_api.Body5Fin.lf_mid fl m)) as (A1 & B1 & C1).
  destruct (exit9_mid_keep fl m) as (A2 & B2 & C2).
  rewrite A1, B1, C1, A2, B2, C2. auto.
Qed.

(* the partial header's representation reads only the mode, the length counter and the flags of the state *)
Lemma exit9_head_rep6_same hsh hp xb nb cb s s' h :
  i_mode s' = i_mode s -> i_length s' = i_length s -> i_flags s' = i_flags s ->
  head_rep6 hsh hp xb nb cb s' h = head_rep6 hsh hp xb nb cb s h.
Proof. intros A B C. unfold head_rep6, hinv6, hph, fextra, cx6, cn6, cc6. rewrite A, B, C. reflexivity. Qed.

(* a partial header is a raw one, not finished (RTHSpec.hinv6: done is 0) *)
Lemma exit9_hd6_hraw hsh hp xb nb cb s h :
  head_rep6 hsh hp xb nb cb s h |-- !! (h_done h <> 1) && hraw6 hsh hp xb nb cb h.
Proof.
  unfold head_rep6, head_rep6p, hraw6. Intros vt vtm vxf vos vxl vhc lx ln lc.
  match goal with H: hinv6 _ _ |- _ => destruct H as [D _] end.
  match goal with H: bufok6 lx _ _ _ |- _ => destruct H as [X1 _] end.
  match goal with H: bufok6 ln _ _ _ |- _ => destruct H as [N1 _] end.
  match goal with H: bufok6 lc _ _ _ |- _ => destruct H as [C1 _] end.
  apply andp_right; [apply prop_right; lia | ].
  Exists vt vtm vxf vos vxl vhc (zv (h_done h)) lx ln lc.
  rewrite prop_true_andp by (split; [ | split]; assumption). cancel.
Qed.

(* the header frame across the exit: an outcome res of inf_leave from the small machine, the real header
   model put back *)
Lemma exit9_hd F fl m res : inf_leave fl (mcanon m) res -> hd9 F m |-- hd9 F (set_m_h (r_m res) (m_h m)).
Proof.
  intros IL. unfold hd9.
  destruct (hdr_mode (m_mode m)) eqn:HMd.
  - destruct IL as [U W|].
    + (* the window allocation failed: MEM, past the header modes, the header raw *)
      change (hdr_mode (m_mode (set_m_h (r_m (Res Z_MEM_ERROR (set_mode (restore (mcanon m)) MEM) None)) (m_h m))))
        with (hdr_mode MEM).
      replace (hdr_mode MEM) with false by reflexivity.
      unfold hd9a. apply orp_right2. unfold hd6. apply exit9_hd6_hraw.
    + (* leave_fin keeps the mode and the fields of the partial header *)
      assert (E: set_m_h (r_m (leave_fin fl (mcanon m))) (m_h m) = r_m (leave_fin fl m)).
      { pose proof (RTH8SimKit.hr_leave_fin fl (mcanon m) (m_h m)) as E.
        change (RTH8SimKit.mh (m_h m) (mcanon m)) with (set_m_h (mcanon m) (m_h m)) in E.
        rewrite mcanon_back in E. rewrite E. reflexivity. }
      assert (EH: m_h (r_m (leave_fin fl m)) = m_h m) by (rewrite <- E; reflexivity).
      rewrite E. destruct (exit9_lf_keep fl m) as (A & B & C).
      unfold m_mode in *. rewrite A, HMd. unfold hd6. rewrite EH.
      rewrite (exit9_head_rep6_same _ _ _ _ _ _ _ _ A B C). apply derives_refl.
  - (* past the header modes: the mode stays past them, the flags are kept *)
    destruct (RTH8Pure.NH.leave_ngood fl (mcanon m) res IL HMd) as [HM' HF].
    change (m_mode (set_m_h (r_m res) (m_h m))) with (m_mode (r_m res)). rewrite HM'.
    change (m_s (mcanon m)) with (m_s m) in HF.
    unfold hd9a, hd8a, head_rep8a, fextra. cbn [m_s m_h set_m_h]. rewrite HF. apply derives_refl.
Qed.

Lemma exit9 : exit9_stmt.
Proof.
  intros EP Espec F X m R FO [W HW] L O WI HI HEX.
  rewrite <- (lstateH_mcanon F _ m), <- lstate_hl_H.
  apply EP; [exact FO | exact W | exact L | exact O | exact WI | ].
  intros resc winp IL WP.
  pose proof (exit9_leave_h _ _ (m_h m) _ IL) as IL'. rewrite mcanon_back in IL'.
  pose proof (exit9_hd F _ m resc IL) as HE.
  destruct (leave_fin9 (f_flush F) (mcanon m) resc W O WI IL) as (SW & FN & DT & HH & HD & HP).
  (* the small machine after the exit is the real one with the small header *)
  assert (EC: mcanon (r_m (res_h resc (m_h m))) = r_m resc).
  { unfold res_h, mcanon; simpl. rewrite set_m_h_twice. rewrite mcanon_h in HH. rewrite <- HH. apply set_m_h_same. }
  assert (LV: leave9 m (res_h resc (m_h m))).
  { unfold leave9. rewrite EC. exact (conj FN (conj SW (conj DT (conj eq_refl (conj HD HP))))). }
  specialize (HEX (res_h resc (m_h m)) winp IL' LV WP).
  rewrite hdr_tok_mcanon. unfold res_dt.
  unfold res_h, res_dt in HEX; cbn [r_m r_dtype r_ret] in HEX. rewrite mem_rep_hl_set_h in HEX.
  eapply ENTAIL_trans; [ | exact HEX].
  apply andp_left2. apply andp_derives; [apply derives_refl | ].
  apply andp_derives; [apply derives_refl | ].
  unfold SEPx. intros rho. cbn [fold_right_sepcon]. cancel.
Qed.
