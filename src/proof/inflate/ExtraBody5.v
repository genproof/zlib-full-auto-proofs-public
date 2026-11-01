(* inflate(), case EXTRA: the copy block `if (copy) { ... }` on the machine (extra_upd of ExKit5.v), the view
   of loop_state with the header tokens as a SEP item, and the model facts of the case. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.ExKit5.
Require Import Zlib.proof.inflate.ExtraKit5.
Require Import Zlib.proof.inflate.Steps2.
Require Import Zlib.proof.inflate.MwfLemmas.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* the view                                                                                       *)

Definition PPx (F: frame) (m: mst) : list Prop := [in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m)].

Definition LLx (F: frame) (m: mst) : list localdef :=
  [temp _strm (f_strmp F); temp _flush (zv (f_flush F)); temp _state (f_sp F);
   temp _next (in_ptr (f_ib F) (m_nx m)); temp _put (out_ptr (f_ob F) (Zlength (m_ow m)));
   temp _have (zv (m_have m)); temp _left (zv (m_left m)); temp _hold (lv (m_hold m));
   temp _bits (zv (m_bits m)); temp _in (zv (m_in m)); temp _out (zv (m_out m));
   temp _ret (zv (m_ret m)); temp _leave (zv (m_leave m));
   lvar _here t_code (f_vhere F); lvar _last t_code (f_vlast F);
   lvar _hbuf (tarray tuchar 4) (f_vhbuf F); gvars (f_gv F)].

Definition SLx (F: frame) (m: mst) (t: mpred) : list mpred :=
  [field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F);
   field_at Ews t_state (DOT _wrap) (zv (i_wrap (m_s m))) (f_sp F);
   field_at Ews t_state (DOT _flags) (zv (i_flags (m_s m))) (f_sp F);
   field_at Ews t_state (DOT _check) (lv (i_check (m_s m))) (f_sp F);
   field_at Ews t_state (DOT _head) (if i_head (m_s m) then f_headp F else nullval) (f_sp F);
   field_at Ews t_state (DOT _length) (zv (i_length (m_s m))) (f_sp F);
   head_part F m; in_rep (f_ib F); crc_table_at (f_tsh F) (f_gv F); mem_x F m; locals_rep F; t].

Lemma ls_ex_tok: forall F m t,
  loop_state F m * (fun _ => t) = PROPx (PPx F m) (LOCALx (LLx F m) (SEPx (SLx F m t))).
Proof.
  intros. rewrite loop_state_ex. unfold ex_state. rewrite sepcon_comm.
  etransitivity; [apply (insert_SEP t) | ].
  unfold PPx, LLx, SLx. f_equal. f_equal. unfold SEPx. extensionality rho. simpl.
  apply pred_ext; cancel.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the model                                                                                      *)

Definition extra_mc (m: mst) (c: Z) : mst :=
  set_m_h m (xb_upd (i_head (m_s m)) (m_h m) (i_length (m_s m)) c (m_inp m) (m_nx m)).

Definition crc_s (s: istate) (d: list Z) : istate := set_i_check s (crcv (i_flags s) (i_wrap s) (i_check s) d).

Lemma extra_upd_eq: forall m c, c = Z.min (i_length (m_s m)) (m_have m) -> c <> 0 ->
  extra_upd m =
  set_m_nx (set_m_s (extra_mc m c)
              (set_i_length (crc_s (m_s m) (sublist (m_nx m) (m_nx m + c) (m_inp m))) (i_length (m_s m) - c)))
           (m_nx m + c).
Proof.
  intros m c Hc Hn. unfold extra_upd. rewrite <- Hc. rewrite (proj2 (Z.eqb_neq c 0) Hn). cbv zeta. cbn [negb].
  rewrite crc_if_eq.
  unfold extra_mc, xb_upd, extra_n, crc_s, crc_val, crcv, inbytes, upd_h, upd_s.
  destruct (andb (andb _ _) _); destruct m; reflexivity.
Qed.

Lemma extra_upd_zero: forall m, Z.min (i_length (m_s m)) (m_have m) = 0 -> extra_upd m = m.
Proof. intros m H. unfold extra_upd. rewrite H. reflexivity. Qed.

Lemma hkey_extra_upd: forall m, hkey (extra_upd m) = hkey m.
Proof.
  intros m. unfold extra_upd. destruct (negb _); [ | reflexivity]. cbv zeta.
  unfold crc_if. destruct (andb (andb _ _) _); destruct (andb (negb _) (negb _)); reflexivity.
Qed.

Lemma hkey_extra_fin: forall m, hkey (extra_fin m) = hkey m.
Proof. reflexivity. Qed.

Lemma mem_x_extra_upd: forall F m, mem_x F (extra_upd m) = mem_x F m.
Proof.
  intros F m. unfold extra_upd. destruct (negb _); [ | reflexivity]. cbv zeta.
  unfold crc_if. destruct (andb (andb _ _) _); destruct (andb (negb _) (negb _)); reflexivity.
Qed.

Lemma extra_upd_io: forall m, m_inp (extra_upd m) = m_inp m /\ m_aout (extra_upd m) = m_aout m.
Proof.
  intros m. unfold extra_upd. destruct (negb _); [ | auto]. cbv zeta.
  unfold crc_if. destruct (andb (andb _ _) _); destruct (andb (negb _) (negb _)); auto.
Qed.

Lemma head_part_hd: forall F m,
  head_part F m = hd_part (i_head (m_s m)) (f_hsh F) (f_headp F) (f_xb F) (f_nb F) (f_cb F) (m_h m).
Proof. reflexivity. Qed.

Lemma hdr_tok_hd: forall F m, hdr_tok F m = hd_tok (i_head (m_s m)) (f_xb F) (f_nb F) (f_cb F) (m_h m).
Proof. reflexivity. Qed.

Lemma ex_in_sub: forall sh p lo n c inp nx k,
  in_ok (InBuf sh p lo n c) inp -> 0 <= nx -> 0 <= k -> nx + k <= Zlength inp ->
  sublist (lo + nx) (lo + nx + k) c = byte_vals (sublist nx (nx + k) inp).
Proof.
  intros sh p lo n c inp nx k (R & P & L0 & L1 & LC & LM & S & B) N K NK.
  replace (sublist (lo + nx) (lo + nx + k) c)
    with (sublist nx (nx + k) (sublist lo (lo + Zlength inp) c))
    by (rewrite sublist_sublist by lia; f_equal; lia).
  rewrite S. unfold byte_vals. rewrite sublist_map. reflexivity.
Qed.

Ltac rm_loc_mb L := lazymatch L with
  | nil => constr:(@nil localdef)
  | temp _state _ :: ?r => rm_loc_mb r
  | temp _copy _ :: ?r => rm_loc_mb r
  | temp _next _ :: ?r => rm_loc_mb r
  | ?a :: ?r => let r' := rm_loc_mb r in constr:(a :: r')
  end.
Ltac rm_sep_mb S := lazymatch S with
  | nil => constr:(@nil mpred)
  | field_at _ _ (DOT _head) _ _ :: ?r => rm_sep_mb r
  | field_at _ _ (DOT _length) _ _ :: ?r => rm_sep_mb r
  | hd_part _ _ _ _ _ _ _ :: ?r => rm_sep_mb r
  | data_at _ (tarray tuchar _) _ _ :: ?r => rm_sep_mb r
  | hd_tok _ _ _ _ _ :: ?r => rm_sep_mb r
  | ?a :: ?r => let r' := rm_sep_mb r in constr:(a :: r')
  end.
Ltac rm_loc_crc L := lazymatch L with
  | nil => constr:(@nil localdef)
  | temp _state _ :: ?r => rm_loc_crc r
  | temp _copy _ :: ?r => rm_loc_crc r
  | temp _next _ :: ?r => rm_loc_crc r
  | gvars _ :: ?r => rm_loc_crc r
  | ?a :: ?r => let r' := rm_loc_crc r in constr:(a :: r')
  end.
Ltac rm_sep_crc S := lazymatch S with
  | nil => constr:(@nil mpred)
  | field_at _ _ (DOT _flags) _ _ :: ?r => rm_sep_crc r
  | field_at _ _ (DOT _wrap) _ _ :: ?r => rm_sep_crc r
  | field_at _ _ (DOT _check) _ _ :: ?r => rm_sep_crc r
  | crc_table_at _ _ :: ?r => rm_sep_crc r
  | data_at _ (tarray tuchar _) _ _ :: ?r => rm_sep_crc r
  | ?a :: ?r => let r' := rm_sep_crc r in constr:(a :: r')
  end.

(* ---------------------------------------------------------------------------------------------- *)
(* the copy block                                                                                 *)

Lemma semax_extra_cpy {Espec: OracleKind} (F: frame) (m: mst) (c: Z):
  frame_ok F -> mwf m -> hd_ok F m -> c = Z.min (i_length (m_s m)) (m_have m) -> c <> 0 ->
  semax Delta_cases5
    (PROPx (PPx F m) (LOCALx (temp _copy (zv c) :: LLx F m) (SEPx (SLx F m (hdr_tok F m)))))
    ex_cpy
    (normal_ret_assert
      (PROPx (PPx F m) (LOCALx (temp _copy (zv c) :: LLx F (extra_upd m)) (SEPx (SLx F (extra_upd m) (hdr_tok F m)))))).
Proof.
  intros FOK W HD Hc Hn.
  pose proof (mwf_have m W) as HV. pose proof (sw_length _ (mw_s _ W)) as LN.
  pose proof (mw_nx _ W) as NX. pose proof (mw_inp _ W) as INP.
  assert (CP: 0 < c <= m_have m /\ c <= i_length (m_s m)) by (unfold urange in LN; lia).
  rewrite (extra_upd_eq m c Hc Hn).
  change ex_cpy with (Ssequence ex_mb (Ssequence ex_crcb ex_upd)).
  unfold PPx, LLx, SLx.
  rewrite head_part_hd, hdr_tok_hd.
  match goal with |- context [mem_x F (set_m_nx ?a ?b)] =>
    replace (mem_x F (set_m_nx a b)) with (mem_x F m) by reflexivity end.
  match goal with |- context [head_part F (set_m_nx ?a ?b)] =>
    replace (head_part F (set_m_nx a b)) with
      (hd_part (i_head (m_s m)) (f_hsh F) (f_headp F) (f_xb F) (f_nb F) (f_cb F)
         (xb_upd (i_head (m_s m)) (m_h m) (i_length (m_s m)) c (m_inp m) (m_nx m))) by reflexivity end.
  cbn [set_m_nx set_m_s extra_mc set_m_h m_s m_h m_nx m_inp m_ow m_aout m_hold m_bits m_in m_out m_ret m_leave
       crc_s set_i_length set_i_check i_mode i_wrap i_flags i_check i_head i_length].
  apply semax_extract_PROP; intro HIN. apply semax_extract_PROP; intro HOUT.
  destruct F as [gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush].
  destruct ib as [ | ish ip ilo inn icont].
  { exfalso. cbn in HIN. unfold m_have in CP. rewrite HIN, Zlength_nil in CP, NX. lia. }
  cbn [f_gv f_shs f_strmp f_sp f_headp f_winp f_hsh f_xb f_nb f_cb f_ib f_ob f_gsh f_tsh f_dt f_vres
       f_vhere f_vlast f_vhbuf f_flush in_ptr in_rep] in *.
  set (MX := mem_x _ m). set (LR := locals_rep _). clearbody MX LR.
  pose proof FOK as (_ & HSH & _ & HTS). cbn [f_hsh f_tsh] in HSH, HTS.
  assert (XB: i_head (m_s m) = true -> h_xp (m_h m) = true -> xb <> nullval) by (intros A; apply (HD A)).
  clear FOK HD.
  unfold m_have in *.
  eapply semax_seq'.
  { match goal with |- semax _ (PROPx _ (LOCALx ?L (SEPx ?S))) _ _ =>
      let Q2 := rm_loc_mb L in let R2 := rm_sep_mb S in
      eapply semax_pre; [ | apply (semax_frame_PQR Q2 R2);
        [ unfold closed_wrt_modvars; auto 50 with closed
        | apply (semax_extra_mb sp headp hsh xb nb cb (m_h m) (i_head (m_s m)) (i_length (m_s m)) c ish ip ilo inn icont
                   (m_inp m) (m_nx m)) ] ]
    end.
    { cbn [app]. entailer!. }
    all: try assumption; try lia; try rep_lia; apply (mw_h _ W). }
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

(* ---------------------------------------------------------------------------------------------- *)
(* the exits of the case                                                                          *)

Lemma ex_fall_ok: forall F m mf,
  stepf2 (f_flush F) lenfix_list distfix_list m = stepf2 (f_flush F) lenfix_list distfix_list mf ->
  m_mode mf = NAME -> m_leave mf = 0 -> mwf3 mf -> hd_ok F mf -> hdr_tok F mf = hdr_tok F m ->
  PROPx (PPx F mf) (LOCALx (LLx F mf) (SEPx (SLx F mf (hdr_tok F m))))
  |-- fall_postT5 F m NAME * lift0 (hdr_tok F m).
Proof.
  intros F m mf E HM HL W HD HT. unfold fall_postT5. rewrite exp_sepcon1. Exists mf.
  rewrite sepcon_andp_prop'. apply andp_right; [apply prop_right; tauto | ].
  change (lift0 (hdr_tok F m)) with (fun _ : environ => hdr_tok F m). rewrite ls_ex_tok. apply derives_refl.
Qed.

Lemma ex_brk_ok: forall F m m1,
  stepf2 (f_flush F) lenfix_list distfix_list m = IBrk (set_leave m1) ->
  PROPx (PPx F m1) (LOCALx (LLx F (set_leave m1)) (SEPx (SLx F m1 (hdr_tok F m))))
  |-- RA_normal (case_post2 F m) * lift0 (hdr_tok F m).
Proof.
  intros F m m1 E. unfold case_post2. cbn [RA_normal]. rewrite exp_sepcon1. Exists (set_leave m1).
  rewrite sepcon_andp_prop'. apply andp_right; [apply prop_right; exact E | ].
  change (lift0 (hdr_tok F m)) with (fun _ : environ => hdr_tok F m). rewrite ls_ex_tok. apply derives_refl.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the body of case EXTRA                                                                         *)

Ltac fix_post :=
  match goal with |- context [RA_normal (match ?R with _ => _ end)] =>
    destruct R as [r1 r2 r3 r4]; cbn [RA_normal] end.

Lemma extra_body5 {Espec: OracleKind} (F: frame) (m: mst):
  frame_ok5 F -> m_mode m = EXTRA -> m_leave m = 0 -> mwf3 m -> hd_ok F m ->
  semax Delta_cases5 (loop_state F m * (fun _ => hdr_tok F m)) (case_body 5)
    (overridePost (fall_postT5 F m NAME * (fun _ => hdr_tok F m))
       (frame_ret_assert (switch_ret_assert (case_post2 F m)) (fun _ => hdr_tok F m))).
Proof.
  intros [FOK FR] HM HL [W W3] HD.
  pose proof (step_extra (f_flush F) m HM) as [SB SF]. cbv zeta in SB, SF.
  pose proof (mwf_extra_upd m W HM) as (WU & HMU & HLU).
  pose proof (sw_flags _ (mw_s _ W)) as RF.
  rewrite ls_ex_tok.
  change (fun _ : environ => hdr_tok F m) with (lift0 (hdr_tok F m)).
  case_body_stmt.
  unfold PPx, LLx, SLx.
  abbreviate_semax.
  forward.
  unfold abbreviate in MORE_COMMANDS. subst MORE_COMMANDS. apply semax_if_seq.
  forward_if.
  - assert (Hf: Z.land (i_flags (m_s m)) 1024 <> 0).
    { match goal with H: Int.and _ _ <> Int.zero |- _ => apply Z.eqb_neq; apply (exc_flagbit _ _ H) end. }
    rewrite (proj2 (Z.eqb_neq _ _) Hf) in SB, SF.
    pose proof (sw_length _ (mw_s _ W)) as LN. pose proof (mwf_have m W) as HV.
    unfold urange in LN.
    forward.
    match goal with |- semax _ (PROPx ?P (LOCALx (temp _copy _ :: ?Q) (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp _copy (Vint (Int.repr (Z.min (i_length (m_s m)) (m_have m)))) :: Q) (SEPx R))) end.
    + forward. fix_post. entailer!. rewrite Z.min_r by lia. reflexivity.
    + forward. fix_post. entailer!. rewrite Z.min_l by lia. reflexivity.
    + remember (Z.min (i_length (m_s m)) (m_have m)) as c eqn:Hc.
      destruct (extra_upd_io m) as [EI EA].
      forward_if (PROPx (PPx F (extra_upd m)) (LOCALx (temp _copy (Vint (Int.repr c)) :: LLx F (extra_upd m))
                    (SEPx (SLx F (extra_upd m) (hdr_tok F m))))).
      * assert (Hn: c <> 0) by (intro E; subst c; rewrite E in *; contradiction).
        unfold abbreviate in MORE_COMMANDS. subst MORE_COMMANDS.
        eapply semax_pre; [ | eapply ConseqFacts.semax_post''; [ | apply (semax_extra_cpy F m c FOK W HD Hc Hn)]].
        { unfold PPx, LLx, SLx. entailer!. }
        unfold abbreviate in POSTCONDITION. subst POSTCONDITION. unfold overridePost. fix_post.
        unfold PPx. rewrite EI, EA. apply andp_left2. apply derives_refl.
      * assert (Hz: c = 0).
        { match goal with H: Int.repr c = Int.zero |- _ =>
            apply (f_equal Int.unsigned) in H; rewrite Int.unsigned_repr in H by rep_lia; exact H end. }
        forward.
        try (unfold abbreviate in POSTCONDITION; subst POSTCONDITION).
        try unfold overridePost. try fix_post.
        rewrite (extra_upd_zero m) by congruence.
        unfold PPx, LLx, SLx. entailer!.
      * assert (HK: hkey (extra_fin (extra_upd m)) = hkey m) by (rewrite hkey_extra_fin; apply hkey_extra_upd).
        pose proof (mwf3_extra_fin (extra_upd m) WU HMU) as [WF LF].
        pose proof (sw_length _ (mw_s _ WU)) as LN1. unfold urange in LN1.
        set (m1 := extra_upd m) in *. clearbody m1.
        unfold PPx, LLx, SLx.
        forward.
        unfold abbreviate in MORE_COMMANDS. subst MORE_COMMANDS. apply semax_if_seq.
        forward_if.
        -- assert (LNZ: i_length (m_s m1) <> 0) by (intro E; rewrite E in *; contradiction).
           forward. forward.
           try (unfold abbreviate in POSTCONDITION; subst POSTCONDITION).
           match goal with |- context [RA_break ?X] =>
             replace (RA_break X) with (RA_normal (case_post2 F m) * lift0 (hdr_tok F m)) by reflexivity end.
           eapply derives_trans; [ | apply (ex_brk_ok F m m1 (SB LNZ Hf)) ].
           unfold PPx, LLx, SLx.
           change (m_have (set_leave m1)) with (m_have m1). change (m_left (set_leave m1)) with (m_left m1).
           cbn [set_leave set_m_leave m_leave m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret].
           entailer!.
        -- assert (LZ: i_length (m_s m1) = 0).
           { match goal with H: Int.repr _ = Int.zero |- _ =>
               apply (f_equal Int.unsigned) in H; rewrite Int.unsigned_repr in H by rep_lia; exact H end. }
           specialize (SF (or_introl LZ)).
           forward. forward.
           try (unfold abbreviate in POSTCONDITION; subst POSTCONDITION).
           try unfold overridePost. repeat fix_post.
           eapply derives_trans; [ | apply (ex_fall_ok F m (extra_fin m1) SF eq_refl
               ltac:(rewrite LF, HLU; exact HL) WF (hkey_hd_ok F m _ HK HD) (hkey_hdr_tok F m _ HK))].
           unfold PPx, LLx, SLx.
           change (head_part F (extra_fin m1)) with (head_part F m1).
           change (mem_x F (extra_fin m1)) with (mem_x F m1).
           change (m_have (extra_fin m1)) with (m_have m1). change (m_left (extra_fin m1)) with (m_left m1).
           cbn [extra_fin set_mode upd_s set_m_s m_s m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave
                set_i_mode set_i_length i_mode i_wrap i_flags i_check i_head i_length].
           unfold NAME.
           entailer!.
  - assert (Hf: Z.land (i_flags (m_s m)) 1024 = 0).
    { match goal with H: Int.and _ _ = Int.zero |- _ => apply Z.eqb_eq; apply (exc_flagbit0 _ _ H); rep_lia end. }
    rewrite (proj2 (Z.eqb_eq _ _) Hf) in SF.
    specialize (SF (or_intror Hf)).
    pose proof (mwf3_extra_fin m W HM) as [WF LF].
    forward. forward.
    destruct (frame_ret_assert (switch_ret_assert (case_post2 F m)) (lift0 (hdr_tok F m))) as [r1 r2 r3 r4].
    cbn [RA_normal].
    eapply derives_trans; [ | apply (ex_fall_ok F m (extra_fin m) SF eq_refl ltac:(rewrite LF; exact HL) WF
        (hkey_hd_ok F m _ (hkey_extra_fin m) HD) (hkey_hdr_tok F m _ (hkey_extra_fin m)))].
    unfold PPx, LLx, SLx.
    change (head_part F (extra_fin m)) with (head_part F m).
    change (mem_x F (extra_fin m)) with (mem_x F m).
    change (m_have (extra_fin m)) with (m_have m). change (m_left (extra_fin m)) with (m_left m).
    cbn [extra_fin set_mode upd_s set_m_s m_s m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave
         set_i_mode set_i_length i_mode i_wrap i_flags i_check i_head i_length].
    unfold NAME.
    entailer!.
Qed.
