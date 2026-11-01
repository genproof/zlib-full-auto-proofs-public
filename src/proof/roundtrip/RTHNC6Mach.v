(* RT-H: the do-while and the crc of NAME / COMMENT on the machine, in the view SL6 (RTHNC6Kit.v)
   with the opened partial header hopen6. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTHCase.
Require Import Zlib.proof.roundtrip.RTHNC6Kit.
Require Import Zlib.proof.roundtrip.RTHNC6Loop.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Lemma semax_frame_PQR_ex:
  forall {A: Type} Q2 R2 Espec {cs: compspecs} Delta R1 P Q (P': A -> list Prop) (Q': A -> list localdef)
    (R1': A -> list mpred) c,
     closed_wrt_modvars c (LOCALx Q2 (SEPx R2)) ->
     @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R1))) c
                     (normal_ret_assert (EX x: A, PROPx (P' x) (LOCALx (Q' x) (SEPx (R1' x))))) ->
     @semax cs Espec Delta (PROPx P (LOCALx (Q++Q2) (SEPx (R1++R2)))) c
                     (normal_ret_assert (EX x: A, PROPx (P' x) (LOCALx (Q' x ++ Q2) (SEPx (R1' x ++ R2))))).
Proof.
intros.
replace (PROPx P (LOCALx (Q++Q2) (SEPx (R1 ++ R2))))
   with (PROPx P (LOCALx Q (SEPx (R1))) * (LOCALx Q2 (SEPx R2))).
eapply semax_pre_post; try (apply semax_frame; try eassumption).
apply andp_left2; auto.
apply andp_left2. intro rho; simpl. rewrite exp_sepcon1. apply exp_left. intros x. apply exp_right with x.
 unfold PROPx, SEPx, LOCALx, local, lift1.
normalize.
rewrite fold_right_sepcon_app.
normalize; autorewrite with norm1 norm2; normalize.
rewrite prop_true_andp; auto.
rewrite map_app. rewrite fold_right_and_app; split; auto.
apply andp_left2; simpl; normalize.
apply andp_left2; simpl; normalize.
intro; apply andp_left2; simpl; normalize.
clear.
extensionality rho.
simpl.
unfold PROPx, LOCALx, local, lift1, SEPx.
rewrite fold_right_sepcon_app.
simpl. normalize.
f_equal.
rewrite map_app. rewrite fold_right_and_app.
apply pred_ext; normalize.
Qed.

Ltac frame_lem_ex Q2 R2 LEM :=
  eapply semax_pre; [ | eapply semax_post_flipped';
    [ eapply (@semax_frame_PQR_ex _ Q2 R2); [ unfold closed_wrt_modvars; try unfold Q2nc; solve [auto 50 with closed] | exact LEM ] | ] ].

Lemma hbuf6_nn: forall b max l, b <> nullval -> hbuf6 b max l = data_at Ews (tarray tuchar max) l b.
Proof. intros. unfold hbuf6. rewrite if_false by auto. reflexivity. Qed.

(* the do-while of NAME on the machine, with a header attached *)
Lemma semax_name_loop6 {Espec: OracleKind} (F: frame) (m: mst) c b ln bf vt vtm vxf vos vxl vhc lx ln0 lc:
  frame_ok F -> mwf m -> hd_ok F m -> i_head (m_s m) = true -> m_have m <> 0 ->
  0 <= i_length (m_s m) <= h_name_max (m_h m) -> Zlength ln0 = h_name_max (m_h m) ->
  sublist 0 (i_length (m_s m)) ln0 = byte_vals (sublist 0 (i_length (m_s m)) (h_nbuf (m_h m))) ->
  zstr_f (Z.to_nat (m_have m)) (name_bytes m) (m_have m) (i_length (m_s m)) (h_name_max (m_h m))
    (andb (i_head (m_s m)) (h_np (m_h m))) (h_nbuf (m_h m)) 0 = (c, b, ln, bf) ->
  semax Delta_cases5
    (PROPx (PP F m) (LOCALx (temp _copy (zv 0) :: LL F m)
      (SEPx (SL6 F m (hopen6 F (m_h m) vt vtm vxf vos vxl vhc lx ln0 lc)))))
    name_loop
    (normal_ret_assert
      (@exp (environ -> mpred) _ (list val) (fun ln1: list val =>
       PROPx ((Zlength ln1 = h_name_max (m_h m) /\ sublist 0 ln ln1 = byte_vals (sublist 0 ln bf)) :: PP F m)
        (LOCALx (temp _copy (zv c) :: temp _len (zv b) :: LL F m)
          (SEPx (SL6 F (nm_loop m ln bf) (hopen6 F (m_h m) vt vtm vxf vos vxl vhc lx ln1 lc))))))).
Proof.
  intros FOK W HD HH HV L0R LN0 S0 ZS. pose proof FOK as (HWS & HWH & HRG & HRT).
  pose proof (mwf_have m W) as HVR. pose proof (mw_nx _ W) as NX. pose proof (mw_inp _ W) as INP.
  pose proof (mw_h _ W) as HW. pose proof (mw_s _ W) as SW.
  unfold PP, LL, SL6. Intros.
  destruct (f_ib F) as [ | ish ip ilo inn icont] eqn:IB.
  { exfalso. match goal with X: in_ok InNull _ |- _ => unfold in_ok in X; unfold m_have in HV; rewrite X, Zlength_nil in HV, NX end. lia. }
  match goal with X: in_ok (InBuf _ _ _ _ _) _ |- _ => pose proof X as HIN; destruct X as (IR & IP & IL0 & IL1 & ILC & ILM & IS & IBY) end.
  pose proof (name_sfx ish ip ilo inn icont (m_inp m) (m_nx m) HIN NX) as SB.
  assert (LB: Zlength (name_bytes m) = m_have m) by (unfold name_bytes, m_have; rewrite Zlength_sublist; lia).
  assert (BB: bytes_ok (name_bytes m)) by (unfold name_bytes; apply Forall_sublist; apply INP).
  change (sublist (m_nx m) (Zlength (m_inp m)) (m_inp m)) with (name_bytes m) in SB.
  change (Zlength (m_inp m) - m_nx m) with (m_have m) in SB.
  cbn [in_ptr in_rep] in *.
  rewrite mem_rep_nc_nm_loop, hdr_tok_nm_loop. nc_simpl.
  pose proof (hw_name_max _ HW) as MXR. pose proof (hw_nbuf _ HW) as [NBL NBB].
  assert (HVR': 0 < m_have m <= Int.max_unsigned) by rep_lia.
  rewrite HH in *. cbn [andb] in ZS.
  unfold hopen6, hstr6.
  destruct (bool_dec3 (h_np (m_h m))) as [NPt | NPf].
  - (* a name buffer: the stores *)
    rewrite NPt in *.
    assert (NN: f_nb F <> nullval) by (apply (proj1 (proj2 (HD HH))); exact NPt).
    rewrite hdr_tok_true by exact HH.
    rewrite !(hbuf6_nn (f_nb F)) by exact NN. rewrite (ncl_btok_nn (f_nb F)) by exact NN.
    frame_lem_ex (Q2nc F m)
      [field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _wrap) (zv (i_wrap (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _flags) (zv (i_flags (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _check) (lv (i_check (m_s m))) (f_sp F);
       hbuf6 (f_xb F) (h_extra_max (m_h m)) lx; hbuf6 (f_cb F) (h_comm_max (m_h m)) lc;
       crc_table_at (f_tsh F) (f_gv F); mem_rep_nc F m; locals_rep F;
       btok (f_xb F) (h_extra_max (m_h m)); btok (f_cb F) (h_comm_max (m_h m))]
      (semax_name_loop_wr6 (f_sp F) (f_headp F) (f_hsh F) vt vtm vxf vos
         (if h_xp (m_h m) then f_xb F else nullval) vxl (zv (h_extra_max (m_h m))) (f_nb F)
         (if h_cp (m_h m) then f_cb F else nullval) (zv (h_comm_max (m_h m))) vhc (zv (h_done (m_h m)))
         (h_name_max (m_h m)) (h_nbuf (m_h m)) ln0 (i_length (m_s m)) (m_have m) (name_bytes m)
         ish ip (ilo + m_nx m) inn icont c b ln bf
         ltac:(auto) IR IP ltac:(lia) ltac:(unfold m_have in *; lia) ILC ILM SB LB BB HVR' L0R ltac:(lia)
         NBL LN0 S0 NN ZS).
    + unfold Q2nc. cbv [app]. entailer!.
    + unfold Q2nc. cbv [app]. Intros lb. Exists lb. entailer!. rewrite hbuf6_nn by exact NN. apply derives_refl.
  - (* no name buffer *)
    rewrite NPf in *.
    destruct (zstr_f_nowr _ _ _ _ _ _ _ _ _ _ _ ZS) as [E1 E2]. subst ln bf. try rewrite set_h_nbuf_id.
    frame_lem (Q2nc F m)
      [field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _wrap) (zv (i_wrap (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _flags) (zv (i_flags (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _check) (lv (i_check (m_s m))) (f_sp F);
       hbuf6 (f_xb F) (h_extra_max (m_h m)) lx; hbuf6 (f_nb F) (h_name_max (m_h m)) ln0;
       hbuf6 (f_cb F) (h_comm_max (m_h m)) lc;
       crc_table_at (f_tsh F) (f_gv F); mem_rep_nc F m; locals_rep F; hdr_tok F m]
      (semax_name_loop_nowr6 (f_sp F) (f_headp F) (f_hsh F) vt vtm vxf vos
         (if h_xp (m_h m) then f_xb F else nullval) vxl (zv (h_extra_max (m_h m))) (zv (h_name_max (m_h m)))
         (if h_cp (m_h m) then f_cb F else nullval) (zv (h_comm_max (m_h m))) vhc (zv (h_done (m_h m)))
         (h_name_max (m_h m)) (h_nbuf (m_h m)) (i_length (m_s m)) (m_have m) (name_bytes m)
         ish ip (ilo + m_nx m) inn icont c b (i_length (m_s m)) (h_nbuf (m_h m))
         ltac:(auto) IR IP ltac:(lia) ltac:(unfold m_have in *; lia) ILC ILM SB LB BB HVR'
         ltac:(apply (sw_length _ SW)) ZS).
    + unfold Q2nc. cbv [app]. entailer!.
    + unfold Q2nc. cbv [app]. Exists ln0. entailer!.
Qed.

(* the crc of the bytes read, on the machine *)
Lemma SL6_crc_if: forall F m d Hd,
  SL6 F (crc_if m d) Hd =
  [field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F);
   field_at Ews t_state (DOT _wrap) (zv (i_wrap (m_s m))) (f_sp F);
   field_at Ews t_state (DOT _flags) (zv (i_flags (m_s m))) (f_sp F);
   field_at Ews t_state (DOT _check) (lv (crc_val (m_s m) d)) (f_sp F);
   field_at Ews t_state (DOT _head) (if i_head (m_s m) then f_headp F else nullval) (f_sp F);
   field_at Ews t_state (DOT _length) (zv (i_length (m_s m))) (f_sp F);
   in_rep (f_ib F); crc_table_at (f_tsh F) (f_gv F); mem_rep_nc F m;
   locals_rep F; hdr_tok F m; Hd].
Proof. intros. rewrite crc_if_eq. reflexivity. Qed.

Lemma semax_name_crc6 {Espec: OracleKind} (F: frame) (m: mst) c b Hd:
  frame_ok F -> mwf m -> m_have m <> 0 -> 0 <= c <= m_have m ->
  semax Delta_cases5
    (PROPx (PP F m) (LOCALx (temp _copy (zv c) :: temp _len (zv b) :: LL F m) (SEPx (SL6 F m Hd))))
    (nc_crcblk _t'372 _t'373 _t'37 _t'371 _t'36)
    (normal_ret_assert
      (PROPx (PP F m) (LOCALx (temp _copy (zv c) :: temp _len (zv b) :: LL F m)
        (SEPx (SL6 F (crc_if m (inbytes m c)) Hd))))).
Proof.
  intros FOK W HV HC. pose proof FOK as (HWS & HWH & HRG & HRT).
  pose proof (mwf_have m W) as HVR. pose proof (mw_nx _ W) as NX. pose proof (mw_inp _ W) as INP.
  pose proof (mw_s _ W) as SW.
  rewrite SL6_crc_if, crc_val_crcv.
  unfold PP, LL, SL6. Intros.
  destruct (f_ib F) as [ | ish ip ilo inn icont] eqn:IB.
  { exfalso. match goal with X: in_ok InNull _ |- _ => unfold in_ok in X; unfold m_have in HV; rewrite X, Zlength_nil in HV, NX end. lia. }
  match goal with X: in_ok (InBuf _ _ _ _ _) _ |- _ => pose proof X as HIN; destruct X as (IR & IP & IL0 & IL1 & ILC & ILM & IS & IBY) end.
  assert (SB: sublist (ilo + m_nx m) (ilo + m_nx m + c) icont = byte_vals (inbytes m c))
    by (apply (inbytes_vals ish ip ilo inn icont m c HIN); unfold m_have in *; lia).
  assert (LD: Zlength (inbytes m c) = c) by (unfold inbytes, m_have in *; rewrite Zlength_sublist; lia).
  assert (BD: bytes_ok (inbytes m c)) by (unfold inbytes; apply Forall_sublist; apply INP).
  cbn [in_ptr in_rep] in *.
  frame_crc (Q2crc F m b)
    [field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F);
     field_at Ews t_state (DOT _head) (if i_head (m_s m) then f_headp F else nullval) (f_sp F);
     field_at Ews t_state (DOT _length) (zv (i_length (m_s m))) (f_sp F);
     mem_rep_nc F m; locals_rep F; hdr_tok F m; Hd]
    (semax_crc_name (f_sp F) c (f_gv F) (f_tsh F) (i_flags (m_s m)) (i_wrap (m_s m)) (i_check (m_s m))
       ish ip (ilo + m_nx m) inn icont (inbytes m c)
       HRT IR IP ltac:(lia) ltac:(unfold m_have in *; lia) ILC ltac:(unfold m_have in *; lia) SB LD BD
       ltac:(rep_lia) (sw_flags _ SW) (sw_wrap_range _ SW) (sw_check _ SW)).
  - unfold Q2crc. cbv [app]. entailer!.
  - unfold Q2crc. cbv [app]. entailer!.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* COMMENT *)

Lemma semax_comm_loop6 {Espec: OracleKind} (F: frame) (m: mst) c b ln bf vt vtm vxf vos vxl vhc lx ln0 lc0:
  frame_ok F -> mwf m -> hd_ok F m -> i_head (m_s m) = true -> m_have m <> 0 ->
  0 <= i_length (m_s m) <= h_comm_max (m_h m) -> Zlength lc0 = h_comm_max (m_h m) ->
  sublist 0 (i_length (m_s m)) lc0 = byte_vals (sublist 0 (i_length (m_s m)) (h_cbuf (m_h m))) ->
  zstr_f (Z.to_nat (m_have m)) (name_bytes m) (m_have m) (i_length (m_s m)) (h_comm_max (m_h m))
    (andb (i_head (m_s m)) (h_cp (m_h m))) (h_cbuf (m_h m)) 0 = (c, b, ln, bf) ->
  semax Delta_cases5
    (PROPx (PP F m) (LOCALx (temp _copy (zv 0) :: LL F m)
      (SEPx (SL6 F m (hopen6 F (m_h m) vt vtm vxf vos vxl vhc lx ln0 lc0)))))
    comm_loop
    (normal_ret_assert
      (@exp (environ -> mpred) _ (list val) (fun lc1: list val =>
       PROPx ((Zlength lc1 = h_comm_max (m_h m) /\ sublist 0 ln lc1 = byte_vals (sublist 0 ln bf)) :: PP F m)
        (LOCALx (temp _copy (zv c) :: temp _len (zv b) :: LL F m)
          (SEPx (SL6 F (cm_loop m ln bf) (hopen6 F (m_h m) vt vtm vxf vos vxl vhc lx ln0 lc1))))))).
Proof.
  intros FOK W HD HH HV L0R LN0 S0 ZS. pose proof FOK as (HWS & HWH & HRG & HRT).
  pose proof (mwf_have m W) as HVR. pose proof (mw_nx _ W) as NX. pose proof (mw_inp _ W) as INP.
  pose proof (mw_h _ W) as HW. pose proof (mw_s _ W) as SW.
  unfold PP, LL, SL6. Intros.
  destruct (f_ib F) as [ | ish ip ilo inn icont] eqn:IB.
  { exfalso. match goal with X: in_ok InNull _ |- _ => unfold in_ok in X; unfold m_have in HV; rewrite X, Zlength_nil in HV, NX end. lia. }
  match goal with X: in_ok (InBuf _ _ _ _ _) _ |- _ => pose proof X as HIN; destruct X as (IR & IP & IL0 & IL1 & ILC & ILM & IS & IBY) end.
  pose proof (name_sfx ish ip ilo inn icont (m_inp m) (m_nx m) HIN NX) as SB.
  assert (LB: Zlength (name_bytes m) = m_have m) by (unfold name_bytes, m_have; rewrite Zlength_sublist; lia).
  assert (BB: bytes_ok (name_bytes m)) by (unfold name_bytes; apply Forall_sublist; apply INP).
  change (sublist (m_nx m) (Zlength (m_inp m)) (m_inp m)) with (name_bytes m) in SB.
  change (Zlength (m_inp m) - m_nx m) with (m_have m) in SB.
  cbn [in_ptr in_rep] in *.
  rewrite mem_rep_nc_cm_loop, hdr_tok_cm_loop. nc_simpl.
  pose proof (hw_comm_max _ HW) as MXR. pose proof (hw_cbuf _ HW) as [NBL NBB].
  assert (HVR': 0 < m_have m <= Int.max_unsigned) by rep_lia.
  rewrite HH in *. cbn [andb] in ZS.
  unfold hopen6, hstr6.
  destruct (bool_dec3 (h_cp (m_h m))) as [NPt | NPf].
  - (* a comment buffer: the stores *)
    rewrite NPt in *.
    assert (NN: f_cb F <> nullval) by (apply (proj2 (proj2 (HD HH))); exact NPt).
    rewrite hdr_tok_true by exact HH.
    rewrite !(hbuf6_nn (f_cb F)) by exact NN. rewrite (ncl_btok_nn (f_cb F)) by exact NN.
    frame_lem_ex (Q2nc F m)
      [field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _wrap) (zv (i_wrap (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _flags) (zv (i_flags (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _check) (lv (i_check (m_s m))) (f_sp F);
       hbuf6 (f_xb F) (h_extra_max (m_h m)) lx; hbuf6 (f_nb F) (h_name_max (m_h m)) ln0;
       crc_table_at (f_tsh F) (f_gv F); mem_rep_nc F m; locals_rep F;
       btok (f_xb F) (h_extra_max (m_h m)); btok (f_nb F) (h_name_max (m_h m))]
      (semax_comm_loop_wr6 (f_sp F) (f_headp F) (f_hsh F) vt vtm vxf vos
         (if h_xp (m_h m) then f_xb F else nullval) vxl (zv (h_extra_max (m_h m)))
         (if h_np (m_h m) then f_nb F else nullval) (zv (h_name_max (m_h m))) (f_cb F)
         vhc (zv (h_done (m_h m)))
         (h_comm_max (m_h m)) (h_cbuf (m_h m)) lc0 (i_length (m_s m)) (m_have m) (name_bytes m)
         ish ip (ilo + m_nx m) inn icont c b ln bf
         ltac:(auto) IR IP ltac:(lia) ltac:(unfold m_have in *; lia) ILC ILM SB LB BB HVR' L0R ltac:(lia)
         NBL LN0 S0 NN ZS).
    + unfold Q2nc. cbv [app]. entailer!.
    + unfold Q2nc. cbv [app]. Intros lb. Exists lb. entailer!. rewrite hbuf6_nn by exact NN. apply derives_refl.
  - (* no comment buffer *)
    rewrite NPf in *.
    destruct (zstr_f_nowr _ _ _ _ _ _ _ _ _ _ _ ZS) as [E1 E2]. subst ln bf. try rewrite set_h_cbuf_id.
    frame_lem (Q2nc F m)
      [field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _wrap) (zv (i_wrap (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _flags) (zv (i_flags (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _check) (lv (i_check (m_s m))) (f_sp F);
       hbuf6 (f_xb F) (h_extra_max (m_h m)) lx; hbuf6 (f_nb F) (h_name_max (m_h m)) ln0;
       hbuf6 (f_cb F) (h_comm_max (m_h m)) lc0;
       crc_table_at (f_tsh F) (f_gv F); mem_rep_nc F m; locals_rep F; hdr_tok F m]
      (semax_comm_loop_nowr6 (f_sp F) (f_headp F) (f_hsh F) vt vtm vxf vos
         (if h_xp (m_h m) then f_xb F else nullval) vxl (zv (h_extra_max (m_h m)))
         (if h_np (m_h m) then f_nb F else nullval) (zv (h_name_max (m_h m)))
         (zv (h_comm_max (m_h m))) vhc (zv (h_done (m_h m)))
         (h_comm_max (m_h m)) (h_cbuf (m_h m)) (i_length (m_s m)) (m_have m) (name_bytes m)
         ish ip (ilo + m_nx m) inn icont c b (i_length (m_s m)) (h_cbuf (m_h m))
         ltac:(auto) IR IP ltac:(lia) ltac:(unfold m_have in *; lia) ILC ILM SB LB BB HVR'
         ltac:(apply (sw_length _ SW)) ZS).
    + unfold Q2nc. cbv [app]. entailer!.
    + unfold Q2nc. cbv [app]. Exists lc0. entailer!.
Qed.

Lemma semax_comm_crc6 {Espec: OracleKind} (F: frame) (m: mst) c b Hd:
  frame_ok F -> mwf m -> m_have m <> 0 -> 0 <= c <= m_have m ->
  semax Delta_cases5
    (PROPx (PP F m) (LOCALx (temp _copy (zv c) :: temp _len (zv b) :: LL F m) (SEPx (SL6 F m Hd))))
    (nc_crcblk _t'357 _t'358 _t'44 _t'356 _t'43)
    (normal_ret_assert
      (PROPx (PP F m) (LOCALx (temp _copy (zv c) :: temp _len (zv b) :: LL F m)
        (SEPx (SL6 F (crc_if m (inbytes m c)) Hd))))).
Proof.
  intros FOK W HV HC. pose proof FOK as (HWS & HWH & HRG & HRT).
  pose proof (mwf_have m W) as HVR. pose proof (mw_nx _ W) as NX. pose proof (mw_inp _ W) as INP.
  pose proof (mw_s _ W) as SW.
  rewrite SL6_crc_if, crc_val_crcv.
  unfold PP, LL, SL6. Intros.
  destruct (f_ib F) as [ | ish ip ilo inn icont] eqn:IB.
  { exfalso. match goal with X: in_ok InNull _ |- _ => unfold in_ok in X; unfold m_have in HV; rewrite X, Zlength_nil in HV, NX end. lia. }
  match goal with X: in_ok (InBuf _ _ _ _ _) _ |- _ => pose proof X as HIN; destruct X as (IR & IP & IL0 & IL1 & ILC & ILM & IS & IBY) end.
  assert (SB: sublist (ilo + m_nx m) (ilo + m_nx m + c) icont = byte_vals (inbytes m c))
    by (apply (inbytes_vals ish ip ilo inn icont m c HIN); unfold m_have in *; lia).
  assert (LD: Zlength (inbytes m c) = c) by (unfold inbytes, m_have in *; rewrite Zlength_sublist; lia).
  assert (BD: bytes_ok (inbytes m c)) by (unfold inbytes; apply Forall_sublist; apply INP).
  cbn [in_ptr in_rep] in *.
  frame_crc (Q2crc F m b)
    [field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F);
     field_at Ews t_state (DOT _head) (if i_head (m_s m) then f_headp F else nullval) (f_sp F);
     field_at Ews t_state (DOT _length) (zv (i_length (m_s m))) (f_sp F);
     mem_rep_nc F m; locals_rep F; hdr_tok F m; Hd]
    (semax_crc_comm (f_sp F) c (f_gv F) (f_tsh F) (i_flags (m_s m)) (i_wrap (m_s m)) (i_check (m_s m))
       ish ip (ilo + m_nx m) inn icont (inbytes m c)
       HRT IR IP ltac:(lia) ltac:(unfold m_have in *; lia) ILC ltac:(unfold m_have in *; lia) SB LD BD
       ltac:(rep_lia) (sw_flags _ SW) (sw_wrap_range _ SW) (sw_check _ SW)).
  - unfold Q2crc. cbv [app]. entailer!.
  - unfold Q2crc. cbv [app]. entailer!.
Qed.
