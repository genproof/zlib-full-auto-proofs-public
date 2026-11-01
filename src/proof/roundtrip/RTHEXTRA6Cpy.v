(* RT-H: case EXTRA's copy block `if (copy) { .. }` on the headless loop state with the partial
   header hd6 as a SEP item (the view SLx6). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTHCase.
Require Import Zlib.proof.roundtrip.RTHEx6Kit.
Require Import Zlib.proof.roundtrip.RTHEXTRA6Mb.
Require Import Zlib.proof.inflate.ExtraKit5.
Require Import Zlib.proof.inflate.ExtraBody5.
Require Import Zlib.proof.inflate.Steps2.
Require Import Zlib.proof.inflate.MwfLemmas.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* the view: ExtraBody5's with the head part replaced by the partial header *)
Definition SLx6 (F: frame) (m: mst) (t: mpred) : list mpred :=
  [field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F);
   field_at Ews t_state (DOT _wrap) (zv (i_wrap (m_s m))) (f_sp F);
   field_at Ews t_state (DOT _flags) (zv (i_flags (m_s m))) (f_sp F);
   field_at Ews t_state (DOT _check) (lv (i_check (m_s m))) (f_sp F);
   field_at Ews t_state (DOT _head) (if i_head (m_s m) then f_headp F else nullval) (f_sp F);
   field_at Ews t_state (DOT _length) (zv (i_length (m_s m))) (f_sp F);
   hd6 F m; in_rep (f_ib F); crc_table_at (f_tsh F) (f_gv F); mem_x F m; locals_rep F; t].

Lemma ls_ex_tok6: forall F m t,
  loop_stateH F m * (fun _ => t * hd6 F m) = PROPx (PPx F m) (LOCALx (LLx F m) (SEPx (SLx6 F m t))).
Proof.
  intros. rewrite loop_state_exH. unfold ex_stateH. rewrite PQR_tok.
  unfold PPx, LLx. f_equal. f_equal. unfold SEPx, SLx6, head_partH, hnoneH. extensionality rho. simpl.
  destruct (i_head (m_s m)); apply pred_ext; cancel.
Qed.

Ltac rm_sep_mb6 S := lazymatch S with
  | nil => constr:(@nil mpred)
  | field_at _ _ (DOT _head) _ _ :: ?r => rm_sep_mb6 r
  | field_at _ _ (DOT _length) _ _ :: ?r => rm_sep_mb6 r
  | head_rep6 _ _ _ _ _ _ _ :: ?r => rm_sep_mb6 r
  | data_at _ (tarray tuchar _) _ _ :: ?r => rm_sep_mb6 r
  | hd_tok _ _ _ _ _ :: ?r => rm_sep_mb6 r
  | ?a :: ?r => let r' := rm_sep_mb6 r in constr:(a :: r')
  end.

Lemma semax_extra_cpy6 {Espec: OracleKind} (F: frame) (m: mst) (c: Z):
  frame_ok F -> mwf m -> hd_ok F m -> i_head (m_s m) = true -> m_mode m = IM.EXTRA ->
  c = Z.min (i_length (m_s m)) (m_have m) -> c <> 0 ->
  semax Delta_cases5
    (PROPx (PPx F m) (LOCALx (temp _copy (zv c) :: LLx F m) (SEPx (SLx6 F m (hdr_tok F m)))))
    ex_cpy
    (normal_ret_assert
      (PROPx (PPx F m) (LOCALx (temp _copy (zv c) :: LLx F (extra_upd m)) (SEPx (SLx6 F (extra_upd m) (hdr_tok F m)))))).
Proof.
  intros FOK W HD Hh HM Hc Hn.
  pose proof (mwf_have m W) as HV. pose proof (sw_length _ (mw_s _ W)) as LN.
  pose proof (mw_nx _ W) as NX. pose proof (mw_inp _ W) as INP.
  assert (CP: 0 < c <= m_have m /\ c <= i_length (m_s m)) by (unfold urange in LN; lia).
  assert (XB: h_xp (m_h m) = true -> f_xb F <> nullval) by (intros A; apply (proj1 (HD Hh) A)).
  rewrite (extra_upd_eq m c Hc Hn).
  change ex_cpy with (Ssequence ex_mb (Ssequence ex_crcb ex_upd)).
  unfold PPx, LLx, SLx6.
  rewrite hdr_tok_hd.
  match goal with |- context [mem_x F (set_m_nx ?a ?b)] =>
    replace (mem_x F (set_m_nx a b)) with (mem_x F m) by reflexivity end.
  unfold hd6.
  cbn [set_m_nx set_m_s extra_mc set_m_h m_s m_h m_nx m_inp m_ow m_aout m_hold m_bits m_in m_out m_ret m_leave
       crc_s set_i_length set_i_check i_mode i_wrap i_flags i_check i_head i_length].
  rewrite (head_rep6_ext _ _ _ _ _ (set_i_length (crc_s (m_s m) _) _)
             (set_i_length (m_s m) (i_length (m_s m) - c))) by reflexivity.
  rewrite Hh.
  apply semax_extract_PROP; intro HIN. apply semax_extract_PROP; intro HOUT.
  assert (HMs: i_mode (m_s m) = IM.EXTRA) by exact HM.
  destruct F as [gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush].
  destruct ib as [ | ish ip ilo inn icont].
  { exfalso. cbn in HIN. unfold m_have in CP. rewrite HIN, Zlength_nil in CP, NX. lia. }
  cbn [f_gv f_shs f_strmp f_sp f_headp f_winp f_hsh f_xb f_nb f_cb f_ib f_ob f_gsh f_tsh f_dt f_vres
       f_vhere f_vlast f_vhbuf f_flush in_ptr in_rep] in *.
  set (MX := mem_x _ m). set (LR := locals_rep _). clearbody MX LR.
  pose proof FOK as (_ & HSH & _ & HTS). cbn [f_hsh f_tsh] in HSH, HTS.
  clear FOK HD.
  unfold m_have in *.
  eapply semax_seq'.
  { match goal with |- semax _ (PROPx _ (LOCALx ?L (SEPx ?S))) _ _ =>
      let Q2 := rm_loc_mb L in let R2 := rm_sep_mb6 S in
      eapply semax_pre; [ | apply (semax_frame_PQR Q2 R2);
        [ unfold closed_wrt_modvars; auto 50 with closed
        | apply (semax_extra_mb6 sp headp hsh xb nb cb (m_s m) (m_h m) (i_length (m_s m)) c ish ip ilo inn icont
                   (m_inp m) (m_nx m)) ] ]
    end.
    { cbn [app]. entailer!. }
    all: try assumption; try lia; try rep_lia; try reflexivity; apply (mw_h _ W). }
  cbn [app].
  pose proof HIN as (HIS & HIP & HILO & HINN & HIC & HIMAX & HISUB & HIB).
  pose proof (mw_s _ W) as SW.
  eapply semax_seq'.
  { match goal with |- semax _ (PROPx _ (LOCALx ?L (SEPx ?S))) _ _ =>
      let Q2 := rm_loc_crc L in let R2 := rm_sep_crc S in
      eapply semax_pre; [ | apply (semax_frame_PQR Q2 R2);
        [ unfold closed_wrt_modvars; auto 50 with closed
        | apply (semax_crc_extra sp c gv tsh (i_flags (m_s m)) (i_wrap (m_s m)) (i_check (m_s m)) ish ip
                   (ilo + m_nx m) inn icont (sublist (m_nx m) (m_nx m + c) (m_inp m))) ] ]
    end.
    { cbn [app]. entailer!. }
    all: try assumption; try lia; try rep_lia.
    { apply (ex_in_sub ish ip ilo inn icont); auto; lia. }
    { rewrite Zlength_sublist by lia. lia. }
    { unfold bytes_ok in *. apply Forall_sublist. exact HIB. }
    { apply (sw_flags _ SW). }
    { apply (sw_wrap_range _ SW). }
    { apply (sw_check _ SW). } }
  cbn [app].
  unfold ex_upd. abbreviate_semax.
  forward. forward. forward. forward.
  entailer!.
  split; [f_equal; lia | ].
  cbn [m_inp m_nx set_m_nx set_m_s extra_mc set_m_h]. f_equal. f_equal. lia.
Qed.
