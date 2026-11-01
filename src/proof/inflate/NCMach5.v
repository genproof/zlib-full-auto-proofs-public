(* inflate(), cases NAME (6) and COMMENT (7): the do-while and the crc of NCLoop5.v / NCCrc5.v lifted to the
   machine (Model.v mst): the view of loop_state with the six state fields the cases touch, the head part, the
   input object, the crc table and the header tokens apart (the rest of the memory opaque: mem_rep_nc). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.NCKit5.
Require Import Zlib.proof.inflate.NCLoop5.
Require Import Zlib.proof.inflate.NCCrc5.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Definition LL (F: frame) (m: mst) : list localdef :=
  [temp _strm (f_strmp F); temp _flush (zv (f_flush F)); temp _state (f_sp F);
   temp _next (in_ptr (f_ib F) (m_nx m)); temp _put (out_ptr (f_ob F) (Zlength (m_ow m)));
   temp _have (zv (m_have m)); temp _left (zv (m_left m)); temp _hold (lv (m_hold m));
   temp _bits (zv (m_bits m)); temp _in (zv (m_in m)); temp _out (zv (m_out m));
   temp _ret (zv (m_ret m)); temp _leave (zv (m_leave m));
   lvar _here t_code (f_vhere F); lvar _last t_code (f_vlast F);
   lvar _hbuf (tarray tuchar 4) (f_vhbuf F); gvars (f_gv F)].

Definition PP (F: frame) (m: mst) : list Prop := [in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m)].

Definition SL (F: frame) (m: mst) : list mpred :=
  [field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F);
   field_at Ews t_state (DOT _wrap) (zv (i_wrap (m_s m))) (f_sp F);
   field_at Ews t_state (DOT _flags) (zv (i_flags (m_s m))) (f_sp F);
   field_at Ews t_state (DOT _check) (lv (i_check (m_s m))) (f_sp F);
   field_at Ews t_state (DOT _head) (if i_head (m_s m) then f_headp F else nullval) (f_sp F);
   field_at Ews t_state (DOT _length) (zv (i_length (m_s m))) (f_sp F);
   hp F (i_head (m_s m)) (m_h m); in_rep (f_ib F); crc_table_at (f_tsh F) (f_gv F); mem_rep_nc F m;
   locals_rep F; hdr_tok F m].

Lemma ls_tok_split: forall F m,
  loop_state F m * (fun _ => hdr_tok F m) = PROPx (PP F m) (LOCALx (LL F m) (SEPx (SL F m))).
Proof.
  intros. unfold loop_state. rewrite sepcon_comm.
  etransitivity; [apply (insert_SEP (hdr_tok F m)) | ].
  unfold PP, LL, SL. f_equal. f_equal. unfold SEPx. extensionality rho. simpl.
  rewrite mem_rep_nc_split. apply pred_ext; cancel.
Qed.

(* the machine after the do-while *)
Definition nm_loop (m: mst) (ln: Z) (bf: list Z) : mst :=
  upd_h (upd_s m (fun s => set_i_length s ln)) (fun h => set_h_nbuf h bf).
Definition cm_loop (m: mst) (ln: Z) (bf: list Z) : mst :=
  upd_h (upd_s m (fun s => set_i_length s ln)) (fun h => set_h_cbuf h bf).

Lemma head_rep_hstruct: forall hsh headp xb nb cb h,
  head_rep hsh headp xb nb cb h =
  hstruct hsh headp xb nb cb h * hbuf_rep xb (h_extra_max h) (h_xbuf h) *
  hbuf_rep nb (h_name_max h) (h_nbuf h) * hbuf_rep cb (h_comm_max h) (h_cbuf h).
Proof. reflexivity. Qed.

Lemma name_sfx: forall sh p lo n c inp nx,
  in_ok (InBuf sh p lo n c) inp -> 0 <= nx <= Zlength inp ->
  sublist (lo + nx) (lo + nx + (Zlength inp - nx)) c = byte_vals (sublist nx (Zlength inp) inp).
Proof.
  intros sh p lo n c inp nx (R & P & L0 & L1 & LC & LM & S & B) N.
  replace (sublist (lo + nx) (lo + nx + (Zlength inp - nx)) c)
    with (sublist nx (Zlength inp) (sublist lo (lo + Zlength inp) c))
    by (rewrite sublist_sublist by lia; f_equal; lia).
  rewrite S. unfold byte_vals. rewrite sublist_map. reflexivity.
Qed.

Lemma hdr_tok_true: forall F m, i_head (m_s m) = true ->
  hdr_tok F m = btok (f_xb F) (h_extra_max (m_h m)) * btok (f_nb F) (h_name_max (m_h m)) *
                btok (f_cb F) (h_comm_max (m_h m)).
Proof. intros F m H. unfold hdr_tok. rewrite H. reflexivity. Qed.

Lemma hdr_tok_nm_loop: forall F m ln bf, hdr_tok F (nm_loop m ln bf) = hdr_tok F m.
Proof. reflexivity. Qed.
Lemma hdr_tok_cm_loop: forall F m ln bf, hdr_tok F (cm_loop m ln bf) = hdr_tok F m.
Proof. reflexivity. Qed.
Lemma mem_rep_nc_nm_loop: forall F m ln bf, mem_rep_nc F (nm_loop m ln bf) = mem_rep_nc F m.
Proof. reflexivity. Qed.
Lemma mem_rep_nc_cm_loop: forall F m ln bf, mem_rep_nc F (cm_loop m ln bf) = mem_rep_nc F m.
Proof. reflexivity. Qed.

Lemma hbuf_rep_nn': forall b max c, b <> nullval ->
  hbuf_rep b max c = data_at Ews (tarray tuchar max) (byte_vals c) b.
Proof. intros. unfold hbuf_rep. rewrite if_false by auto. reflexivity. Qed.

Lemma zstr_f_nowr': forall k bytes have L max wr buf j c b ln bf,
  wr = false -> zstr_f k bytes have L max wr buf j = (c, b, ln, bf) -> ln = L /\ bf = buf.
Proof. intros. subst wr. eapply zstr_f_nowr; eauto. Qed.

Lemma zstr_f_nowr_buf: forall k bytes have L max buf j c b buf',
  zstr_f k bytes have L max false buf j = (c, b, L, buf) -> zstr_f k bytes have L max false buf' j = (c, b, L, buf').
Proof.
  induction k; intros bytes have L max buf j c b buf' Z; simpl in *.
  - inversion Z; subst; reflexivity.
  - destruct (negb (Znth j bytes =? 0) && (j + 1 <? have))%bool.
    + eapply IHk; exact Z.
    + inversion Z; subst; reflexivity.
Qed.

Lemma set_h_nbuf_id: forall h, set_h_nbuf h (h_nbuf h) = h.
Proof. destruct h; reflexivity. Qed.
Lemma set_h_cbuf_id: forall h, set_h_cbuf h (h_cbuf h) = h.
Proof. destruct h; reflexivity. Qed.

Lemma hstruct_nbuf: forall hsh headp xb nb cb h bf,
  hstruct hsh headp xb nb cb (set_h_nbuf h bf) = hstruct hsh headp xb nb cb h.
Proof. reflexivity. Qed.
Lemma hstruct_cbuf: forall hsh headp xb nb cb h bf,
  hstruct hsh headp xb nb cb (set_h_cbuf h bf) = hstruct hsh headp xb nb cb h.
Proof. reflexivity. Qed.

Ltac nc_simpl := cbn [nm_loop cm_loop upd_h upd_s set_m_s set_m_h m_s m_h set_i_length set_h_nbuf set_h_cbuf
  i_mode i_wrap i_flags i_check i_head i_length h_text h_time h_xflags h_os h_xp h_extra_len h_extra_max h_xbuf
  h_np h_name_max h_nbuf h_cp h_comm_max h_cbuf h_hcrc h_done].

Definition Q2nc (F: frame) (m: mst) : list localdef :=
  [temp _strm (f_strmp F); temp _flush (zv (f_flush F));
   temp _put (out_ptr (f_ob F) (Zlength (m_ow m)));
   temp _left (zv (m_left m)); temp _hold (lv (m_hold m));
   temp _bits (zv (m_bits m)); temp _in (zv (m_in m)); temp _out (zv (m_out m));
   temp _ret (zv (m_ret m)); temp _leave (zv (m_leave m));
   lvar _here t_code (f_vhere F); lvar _last t_code (f_vlast F);
   lvar _hbuf (tarray tuchar 4) (f_vhbuf F); gvars (f_gv F)].

(* apply the minimal-context lemma LEM, framing the locals Q2 and the SEP items R2 *)
Ltac frame_lem Q2 R2 LEM :=
  eapply semax_pre; [ | eapply semax_post_flipped';
    [ apply (semax_frame_PQR Q2 R2); [ unfold closed_wrt_modvars; try unfold Q2nc; solve [auto 50 with closed] | exact LEM ] | ] ].

Lemma bool_dec3: forall b: bool, {b = true} + {b = false}.
Proof. intros []; auto. Defined.

(* the do-while of NAME on the machine *)
Lemma semax_name_loop_m {Espec: OracleKind} (F: frame) (m: mst) c b ln bf:
  frame_ok F -> mwf m -> hd_ok F m -> m_have m <> 0 ->
  zstr_f (Z.to_nat (m_have m)) (name_bytes m) (m_have m) (i_length (m_s m)) (h_name_max (m_h m))
    (andb (i_head (m_s m)) (h_np (m_h m))) (h_nbuf (m_h m)) 0 = (c, b, ln, bf) ->
  semax Delta_cases5
    (PROPx (PP F m) (LOCALx (temp _copy (zv 0) :: LL F m) (SEPx (SL F m))))
    name_loop
    (normal_ret_assert
      (PROPx (PP F m) (LOCALx (temp _copy (zv c) :: temp _len (zv b) :: LL F m) (SEPx (SL F (nm_loop m ln bf)))))).
Proof.
  intros FOK W HD HV ZS. pose proof FOK as (HWS & HWH & HRG & HRT).
  pose proof (mwf_have m W) as HVR. pose proof (mw_nx _ W) as NX. pose proof (mw_inp _ W) as INP.
  pose proof (mw_h _ W) as HW. pose proof (mw_s _ W) as SW.
  unfold PP, LL, SL. Intros.
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
  assert (L0R: urange (i_length (m_s m))) by apply (sw_length _ SW).
  pose proof (hw_name_max _ HW) as MXR. pose proof (hw_nbuf _ HW) as [NBL NBB].
  assert (HVR': 0 < m_have m <= Int.max_unsigned) by rep_lia.
  destruct (bool_dec3 (i_head (m_s m))) as [HH | HH]; rewrite HH in *; cbn [andb] in ZS.
  - destruct (bool_dec3 (h_np (m_h m))) as [NPt | NPf].
    + (* a name buffer: the stores *)
      rewrite NPt in ZS.
      assert (NN: f_nb F <> nullval) by (apply (proj1 (proj2 (HD HH))); exact NPt).
      unfold hp. rewrite !head_rep_hstruct, hstruct_nbuf, hdr_tok_true by exact HH. nc_simpl.
      rewrite !(hbuf_rep_nn' (f_nb F)) by exact NN. rewrite (ncl_btok_nn (f_nb F)) by exact NN.
      frame_lem (Q2nc F m)
        [field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F);
         field_at Ews t_state (DOT _wrap) (zv (i_wrap (m_s m))) (f_sp F);
         field_at Ews t_state (DOT _flags) (zv (i_flags (m_s m))) (f_sp F);
         field_at Ews t_state (DOT _check) (lv (i_check (m_s m))) (f_sp F);
         hbuf_rep (f_xb F) (h_extra_max (m_h m)) (h_xbuf (m_h m));
         hbuf_rep (f_cb F) (h_comm_max (m_h m)) (h_cbuf (m_h m));
         crc_table_at (f_tsh F) (f_gv F); mem_rep_nc F m; locals_rep F;
         btok (f_xb F) (h_extra_max (m_h m)); btok (f_cb F) (h_comm_max (m_h m))]
        (semax_name_loop_wr (f_sp F) (f_headp F) (f_hsh F) (f_xb F) (f_nb F) (f_cb F) (m_h m) (h_nbuf (m_h m))
           (i_length (m_s m)) (m_have m) (name_bytes m) ish ip (ilo + m_nx m) inn icont c b ln bf
           ltac:(auto) IR IP ltac:(lia) ltac:(unfold m_have in *; lia) ILC ILM SB LB BB HVR' L0R MXR NBL NBB NPt NN ZS).
      * unfold Q2nc. cbv [app]. entailer!.
      * unfold Q2nc. cbv [app]. entailer!.
    + (* no name buffer *)
      rewrite NPf in ZS.
      destruct (zstr_f_nowr _ _ _ _ _ _ _ _ _ _ _ ZS) as [E1 E2]. subst ln bf. rewrite set_h_nbuf_id.
      unfold hp. rewrite !head_rep_hstruct.
      frame_lem (Q2nc F m)
        [field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F);
         field_at Ews t_state (DOT _wrap) (zv (i_wrap (m_s m))) (f_sp F);
         field_at Ews t_state (DOT _flags) (zv (i_flags (m_s m))) (f_sp F);
         field_at Ews t_state (DOT _check) (lv (i_check (m_s m))) (f_sp F);
         hbuf_rep (f_xb F) (h_extra_max (m_h m)) (h_xbuf (m_h m));
         hbuf_rep (f_cb F) (h_comm_max (m_h m)) (h_cbuf (m_h m));
         crc_table_at (f_tsh F) (f_gv F); mem_rep_nc F m; locals_rep F; hdr_tok F m]
        (semax_name_loop_nowr (f_sp F) true (f_headp F) (f_hsh F) (f_xb F) (f_nb F) (f_cb F) (m_h m)
           (hbuf_rep (f_nb F) (h_name_max (m_h m)) (h_nbuf (m_h m)))
           (i_length (m_s m)) (m_have m) (name_bytes m) ish ip (ilo + m_nx m) inn icont c b (i_length (m_s m)) (h_nbuf (m_h m))
           ltac:(auto) IR IP ltac:(lia) ltac:(unfold m_have in *; lia) ILC ILM SB LB BB HVR' L0R
           ltac:(rewrite NPf; reflexivity) ZS).
      * unfold Q2nc. cbv [app]. entailer!.
      * unfold Q2nc. cbv [app]. entailer!.
  - (* no header *)
    destruct (zstr_f_nowr _ _ _ _ _ _ _ _ _ _ _ ZS) as [E1 E2]. subst ln bf. rewrite set_h_nbuf_id.
    unfold hp.
    frame_lem (Q2nc F m)
      [field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _wrap) (zv (i_wrap (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _flags) (zv (i_flags (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _check) (lv (i_check (m_s m))) (f_sp F);
       crc_table_at (f_tsh F) (f_gv F); mem_rep_nc F m; locals_rep F; hdr_tok F m]
      (semax_name_loop_nowr (f_sp F) false (f_headp F) (f_hsh F) (f_xb F) (f_nb F) (f_cb F) (m_h m) emp
         (i_length (m_s m)) (m_have m) (name_bytes m) ish ip (ilo + m_nx m) inn icont c b (i_length (m_s m)) (h_nbuf (m_h m))
         ltac:(auto) IR IP ltac:(lia) ltac:(unfold m_have in *; lia) ILC ILM SB LB BB HVR' L0R
         ltac:(reflexivity) ZS).
    * unfold Q2nc. cbv [app]. entailer!.
    * unfold Q2nc. cbv [app]. entailer!.
Qed.

(* the crc of the bytes read, on the machine *)
Lemma SL_crc_if: forall F m d,
  SL F (crc_if m d) =
  [field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F);
   field_at Ews t_state (DOT _wrap) (zv (i_wrap (m_s m))) (f_sp F);
   field_at Ews t_state (DOT _flags) (zv (i_flags (m_s m))) (f_sp F);
   field_at Ews t_state (DOT _check) (lv (crc_val (m_s m) d)) (f_sp F);
   field_at Ews t_state (DOT _head) (if i_head (m_s m) then f_headp F else nullval) (f_sp F);
   field_at Ews t_state (DOT _length) (zv (i_length (m_s m))) (f_sp F);
   hp F (i_head (m_s m)) (m_h m); in_rep (f_ib F); crc_table_at (f_tsh F) (f_gv F); mem_rep_nc F m;
   locals_rep F; hdr_tok F m].
Proof. intros. rewrite crc_if_eq. reflexivity. Qed.

Lemma LL_crc_if: forall F m d, LL F (crc_if m d) = LL F m.
Proof. intros. rewrite crc_if_eq. reflexivity. Qed.
Lemma PP_crc_if: forall F m d, PP F (crc_if m d) = PP F m.
Proof. intros. rewrite crc_if_eq. reflexivity. Qed.

Definition Q2crc (F: frame) (m: mst) (b: Z) : list localdef :=
  [temp _len (zv b); temp _strm (f_strmp F); temp _flush (zv (f_flush F));
   temp _put (out_ptr (f_ob F) (Zlength (m_ow m))); temp _have (zv (m_have m));
   temp _left (zv (m_left m)); temp _hold (lv (m_hold m));
   temp _bits (zv (m_bits m)); temp _in (zv (m_in m)); temp _out (zv (m_out m));
   temp _ret (zv (m_ret m)); temp _leave (zv (m_leave m));
   lvar _here t_code (f_vhere F); lvar _last t_code (f_vlast F);
   lvar _hbuf (tarray tuchar 4) (f_vhbuf F)].

Ltac frame_crc Q2 R2 LEM :=
  eapply semax_pre; [ | eapply semax_post_flipped';
    [ apply (semax_frame_PQR Q2 R2); [ unfold closed_wrt_modvars; try unfold Q2crc; solve [auto 50 with closed] | exact LEM ] | ] ].

Lemma inbytes_vals: forall sh p lo n cont m c,
  in_ok (InBuf sh p lo n cont) (m_inp m) -> 0 <= m_nx m -> 0 <= c -> m_nx m + c <= Zlength (m_inp m) ->
  sublist (lo + m_nx m) (lo + m_nx m + c) cont = byte_vals (inbytes m c).
Proof.
  intros sh p lo n cont m c (R & P & L0 & L1 & LC & LM & S & B) N C NC.
  replace (sublist (lo + m_nx m) (lo + m_nx m + c) cont)
    with (sublist (m_nx m) (m_nx m + c) (sublist lo (lo + Zlength (m_inp m)) cont))
    by (rewrite sublist_sublist by lia; f_equal; lia).
  rewrite S. unfold byte_vals, inbytes. rewrite sublist_map. reflexivity.
Qed.

Lemma semax_name_crc_m {Espec: OracleKind} (F: frame) (m: mst) c b:
  frame_ok F -> mwf m -> m_have m <> 0 -> 0 <= c <= m_have m ->
  semax Delta_cases5
    (PROPx (PP F m) (LOCALx (temp _copy (zv c) :: temp _len (zv b) :: LL F m) (SEPx (SL F m))))
    (nc_crcblk _t'372 _t'373 _t'37 _t'371 _t'36)
    (normal_ret_assert
      (PROPx (PP F m) (LOCALx (temp _copy (zv c) :: temp _len (zv b) :: LL F m)
        (SEPx (SL F (crc_if m (inbytes m c))))))).
Proof.
  intros FOK W HV HC. pose proof FOK as (HWS & HWH & HRG & HRT).
  pose proof (mwf_have m W) as HVR. pose proof (mw_nx _ W) as NX. pose proof (mw_inp _ W) as INP.
  pose proof (mw_s _ W) as SW.
  rewrite SL_crc_if, crc_val_crcv.
  unfold PP, LL, SL. Intros.
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
     hp F (i_head (m_s m)) (m_h m); mem_rep_nc F m; locals_rep F; hdr_tok F m]
    (semax_crc_name (f_sp F) c (f_gv F) (f_tsh F) (i_flags (m_s m)) (i_wrap (m_s m)) (i_check (m_s m))
       ish ip (ilo + m_nx m) inn icont (inbytes m c)
       HRT IR IP ltac:(lia) ltac:(unfold m_have in *; lia) ILC ltac:(unfold m_have in *; lia) SB LD BD
       ltac:(rep_lia) (sw_flags _ SW) (sw_wrap_range _ SW) (sw_check _ SW)).
  - unfold Q2crc. cbv [app]. entailer!.
  - unfold Q2crc. cbv [app]. entailer!.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* COMMENT *)

(* the do-while of COMMENT on the machine *)
Lemma semax_comm_loop_m {Espec: OracleKind} (F: frame) (m: mst) c b ln bf:
  frame_ok F -> mwf m -> hd_ok F m -> m_have m <> 0 ->
  zstr_f (Z.to_nat (m_have m)) (name_bytes m) (m_have m) (i_length (m_s m)) (h_comm_max (m_h m))
    (andb (i_head (m_s m)) (h_cp (m_h m))) (h_cbuf (m_h m)) 0 = (c, b, ln, bf) ->
  semax Delta_cases5
    (PROPx (PP F m) (LOCALx (temp _copy (zv 0) :: LL F m) (SEPx (SL F m))))
    comm_loop
    (normal_ret_assert
      (PROPx (PP F m) (LOCALx (temp _copy (zv c) :: temp _len (zv b) :: LL F m) (SEPx (SL F (cm_loop m ln bf)))))).
Proof.
  intros FOK W HD HV ZS. pose proof FOK as (HWS & HWH & HRG & HRT).
  pose proof (mwf_have m W) as HVR. pose proof (mw_nx _ W) as NX. pose proof (mw_inp _ W) as INP.
  pose proof (mw_h _ W) as HW. pose proof (mw_s _ W) as SW.
  unfold PP, LL, SL. Intros.
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
  assert (L0R: urange (i_length (m_s m))) by apply (sw_length _ SW).
  pose proof (hw_comm_max _ HW) as MXR. pose proof (hw_cbuf _ HW) as [NBL NBB].
  assert (HVR': 0 < m_have m <= Int.max_unsigned) by rep_lia.
  destruct (bool_dec3 (i_head (m_s m))) as [HH | HH]; rewrite HH in *; cbn [andb] in ZS.
  - destruct (bool_dec3 (h_cp (m_h m))) as [NPt | NPf].
    + (* a comment buffer: the stores *)
      rewrite NPt in ZS.
      assert (NN: f_cb F <> nullval) by (apply (proj2 (proj2 (HD HH))); exact NPt).
      unfold hp. rewrite !head_rep_hstruct, hstruct_cbuf, hdr_tok_true by exact HH. nc_simpl.
      rewrite !(hbuf_rep_nn' (f_cb F)) by exact NN. rewrite (ncl_btok_nn (f_cb F)) by exact NN.
      frame_lem (Q2nc F m)
        [field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F);
         field_at Ews t_state (DOT _wrap) (zv (i_wrap (m_s m))) (f_sp F);
         field_at Ews t_state (DOT _flags) (zv (i_flags (m_s m))) (f_sp F);
         field_at Ews t_state (DOT _check) (lv (i_check (m_s m))) (f_sp F);
         hbuf_rep (f_xb F) (h_extra_max (m_h m)) (h_xbuf (m_h m));
         hbuf_rep (f_nb F) (h_name_max (m_h m)) (h_nbuf (m_h m));
         crc_table_at (f_tsh F) (f_gv F); mem_rep_nc F m; locals_rep F;
         btok (f_xb F) (h_extra_max (m_h m)); btok (f_nb F) (h_name_max (m_h m))]
        (semax_comm_loop_wr (f_sp F) (f_headp F) (f_hsh F) (f_xb F) (f_nb F) (f_cb F) (m_h m) (h_cbuf (m_h m))
           (i_length (m_s m)) (m_have m) (name_bytes m) ish ip (ilo + m_nx m) inn icont c b ln bf
           ltac:(auto) IR IP ltac:(lia) ltac:(unfold m_have in *; lia) ILC ILM SB LB BB HVR' L0R MXR NBL NBB NPt NN ZS).
      * unfold Q2nc. cbv [app]. entailer!.
      * unfold Q2nc. cbv [app]. entailer!.
    + (* no comment buffer *)
      rewrite NPf in ZS.
      destruct (zstr_f_nowr _ _ _ _ _ _ _ _ _ _ _ ZS) as [E1 E2]. subst ln bf. rewrite set_h_cbuf_id.
      unfold hp. rewrite !head_rep_hstruct.
      frame_lem (Q2nc F m)
        [field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F);
         field_at Ews t_state (DOT _wrap) (zv (i_wrap (m_s m))) (f_sp F);
         field_at Ews t_state (DOT _flags) (zv (i_flags (m_s m))) (f_sp F);
         field_at Ews t_state (DOT _check) (lv (i_check (m_s m))) (f_sp F);
         hbuf_rep (f_xb F) (h_extra_max (m_h m)) (h_xbuf (m_h m));
         hbuf_rep (f_nb F) (h_name_max (m_h m)) (h_nbuf (m_h m));
         crc_table_at (f_tsh F) (f_gv F); mem_rep_nc F m; locals_rep F; hdr_tok F m]
        (semax_comm_loop_nowr (f_sp F) true (f_headp F) (f_hsh F) (f_xb F) (f_nb F) (f_cb F) (m_h m)
           (hbuf_rep (f_cb F) (h_comm_max (m_h m)) (h_cbuf (m_h m)))
           (i_length (m_s m)) (m_have m) (name_bytes m) ish ip (ilo + m_nx m) inn icont c b (i_length (m_s m)) (h_nbuf (m_h m))
           ltac:(auto) IR IP ltac:(lia) ltac:(unfold m_have in *; lia) ILC ILM SB LB BB HVR' L0R
           ltac:(rewrite NPf; reflexivity) (zstr_f_nowr_buf _ _ _ _ _ _ _ _ _ (h_nbuf (m_h m)) ZS)).
      * unfold Q2nc. cbv [app]. entailer!.
      * unfold Q2nc. cbv [app]. entailer!.
  - (* no header *)
    destruct (zstr_f_nowr _ _ _ _ _ _ _ _ _ _ _ ZS) as [E1 E2]. subst ln bf. rewrite set_h_cbuf_id.
    unfold hp.
    frame_lem (Q2nc F m)
      [field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _wrap) (zv (i_wrap (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _flags) (zv (i_flags (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _check) (lv (i_check (m_s m))) (f_sp F);
       crc_table_at (f_tsh F) (f_gv F); mem_rep_nc F m; locals_rep F; hdr_tok F m]
      (semax_comm_loop_nowr (f_sp F) false (f_headp F) (f_hsh F) (f_xb F) (f_nb F) (f_cb F) (m_h m) emp
         (i_length (m_s m)) (m_have m) (name_bytes m) ish ip (ilo + m_nx m) inn icont c b (i_length (m_s m)) (h_nbuf (m_h m))
         ltac:(auto) IR IP ltac:(lia) ltac:(unfold m_have in *; lia) ILC ILM SB LB BB HVR' L0R
         ltac:(reflexivity) (zstr_f_nowr_buf _ _ _ _ _ _ _ _ _ (h_nbuf (m_h m)) ZS)).
    * unfold Q2nc. cbv [app]. entailer!.
    * unfold Q2nc. cbv [app]. entailer!.
Qed.

Lemma semax_comm_crc_m {Espec: OracleKind} (F: frame) (m: mst) c b:
  frame_ok F -> mwf m -> m_have m <> 0 -> 0 <= c <= m_have m ->
  semax Delta_cases5
    (PROPx (PP F m) (LOCALx (temp _copy (zv c) :: temp _len (zv b) :: LL F m) (SEPx (SL F m))))
    (nc_crcblk _t'357 _t'358 _t'44 _t'356 _t'43)
    (normal_ret_assert
      (PROPx (PP F m) (LOCALx (temp _copy (zv c) :: temp _len (zv b) :: LL F m)
        (SEPx (SL F (crc_if m (inbytes m c))))))).
Proof.
  intros FOK W HV HC. pose proof FOK as (HWS & HWH & HRG & HRT).
  pose proof (mwf_have m W) as HVR. pose proof (mw_nx _ W) as NX. pose proof (mw_inp _ W) as INP.
  pose proof (mw_s _ W) as SW.
  rewrite SL_crc_if, crc_val_crcv.
  unfold PP, LL, SL. Intros.
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
     hp F (i_head (m_s m)) (m_h m); mem_rep_nc F m; locals_rep F; hdr_tok F m]
    (semax_crc_comm (f_sp F) c (f_gv F) (f_tsh F) (i_flags (m_s m)) (i_wrap (m_s m)) (i_check (m_s m))
       ish ip (ilo + m_nx m) inn icont (inbytes m c)
       HRT IR IP ltac:(lia) ltac:(unfold m_have in *; lia) ILC ltac:(unfold m_have in *; lia) SB LD BD
       ltac:(rep_lia) (sw_flags _ SW) (sw_wrap_range _ SW) (sw_check _ SW)).
  - unfold Q2crc. cbv [app]. entailer!.
  - unfold Q2crc. cbv [app]. entailer!.
Qed.
