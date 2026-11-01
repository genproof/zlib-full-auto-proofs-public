(* RT-H: cases FLAGS, TIME, OS of inflate() with the partial header hd6 (RTHCase.case_ok6).
   The header is framed through the headless kit lemmas (RTH*5H); the stores into the header are done against
   head_rep6 and fold into the header of the next mode.  The branches that leave (short NEEDBITS) or go to BAD
   (FLAGS) contradict hpass. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTHCase.
Require Import Zlib.proof.inflate.HdrSame5.
Require Import Zlib.proof.inflate.MwfLemmas.
Require Import Zlib.proof.inflate.Steps2.
Require Import Zlib.proof.roundtrip.RTHNeedKit5.
Require Import Zlib.proof.roundtrip.RTHNeedBits_5.
Require Import Zlib.proof.roundtrip.RTHNeedBits1_5.
Require Import Zlib.proof.roundtrip.RTHHdrKit5.
Require Import Zlib.proof.roundtrip.RTHHdrCrc5.
Require Import Zlib.proof.inflate.CaseFLAGS5.
Require Import Zlib.proof.inflate.CaseTIME5.
Require Import Zlib.proof.inflate.CaseOS5.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* framing a closed header through the headless kit                                               *)

Lemma closed_const: forall c (P: mpred), closed_wrt_modvars c (fun _: environ => P).
Proof. intros. unfold closed_wrt_modvars, closed_wrt_vars. intros. reflexivity. Qed.

Lemma semax_seq_frame6 {Espec: OracleKind} (Delta: tycontext) (P Q: environ -> mpred) (Hd: mpred)
    (c1 c2: statement) (R: ret_assert):
  semax Delta P c1 (normal_ret_assert Q) ->
  semax Delta (Q * (fun _ => Hd)) c2 R ->
  semax Delta (P * (fun _ => Hd)) (Ssequence c1 c2) R.
Proof.
  intros H1 H2. eapply semax_seq'; [ | exact H2].
  eapply semax_post; [ | | | | apply semax_frame; [apply closed_const | exact H1]].
  - intros rho. simpl. apply andp_left2. apply derives_refl.
  - intros rho. simpl. apply andp_left2. normalize.
  - intros rho. simpl. apply andp_left2. normalize.
  - intros vl rho. simpl. apply andp_left2. normalize.
Qed.

Lemma semax_last_frame6 {Espec: OracleKind} (Delta: tycontext) (P Q: environ -> mpred) (Hd: mpred)
    (c: statement) (R: ret_assert):
  semax Delta P c (normal_ret_assert Q) ->
  (Q * (fun _ => Hd) |-- RA_normal R) ->
  semax Delta (P * (fun _ => Hd)) c R.
Proof.
  intros H1 HQ.
  eapply semax_post; [ | | | | apply semax_frame; [apply closed_const | exact H1]].
  - intros rho. simpl. apply andp_left2. apply HQ.
  - intros rho. simpl. apply andp_left2. normalize.
  - intros rho. simpl. apply andp_left2. normalize.
  - intros vl rho. simpl. apply andp_left2. normalize.
Qed.

(* the header cases' bodies proved without the tokens *)
Lemma body_frame6 {Espec: OracleKind} (F: frame) (m: mst) (Y: Z) (i: nat):
  semax Delta_cases5 (loop_stateH F m * (fun _ => hd6 F m)) (case_body i)
    (overridePost (fall_post6 F m Y) (switch_ret_assert (case_post6 F m))) ->
  semax Delta_cases5 (loop_stateH F m * (fun _ => hdr_tok F m * hd6 F m)) (case_body i)
    (overridePost (fall_post6 F m Y * (fun _ => hdr_tok F m))
       (frame_ret_assert (switch_ret_assert (case_post6 F m)) (fun _ => hdr_tok F m))).
Proof.
  intros H.
  eapply semax_pre; [ | eapply semax_post; [ | | | | apply semax_frame with (F := fun _ => hdr_tok F m);
                                                       [apply closed_const | exact H]]].
  - intros rho. simpl. apply andp_left2. cancel.
  - intros rho. simpl. apply andp_left2. apply derives_refl.
  - intros rho. simpl. apply andp_left2. apply derives_refl.
  - intros rho. simpl. apply andp_left2. apply derives_refl.
  - intros vl rho. simpl. apply andp_left2. apply derives_refl.
Qed.

(* if (leave) break; with leave = 0 *)
Lemma semax_ifleave0H {Espec: OracleKind} (F: frame) (m: mst):
  m_leave m = 0 ->
  semax Delta_cases5 (loop_stateH F m) (Sifthenelse (Etempvar _leave tint) Sbreak Sskip)
    (normal_ret_assert (loop_stateH F m)).
Proof.
  intros HL. unfold loop_stateH. rewrite HL. abbreviate_semax.
  forward_if.
  - exfalso. apply H. reflexivity.
  - forward. entailer!.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the header of a machine                                                                        *)

Lemma needbits_f_sh: forall k n m, m_s (needbits_f k n m) = m_s m /\ m_h (needbits_f k n m) = m_h m.
Proof.
  induction k; intros n m; simpl; auto.
  destruct (m_bits m <? n); auto. destruct (m_have m =? 0); auto.
  destruct (IHk n (pull m)) as [A B]. rewrite A, B. auto.
Qed.

Lemma hd6_needbits: forall F n m, hd6 F (needbits n m) = hd6 F m.
Proof.
  intros. unfold hd6, needbits. destruct (needbits_f_sh 4 n m) as [A B]. rewrite A, B. reflexivity.
Qed.

Lemma head_rep6_ext: forall hsh headp xb nb cb s s' h,
  i_mode s = i_mode s' -> i_flags s = i_flags s' -> i_length s = i_length s' ->
  head_rep6 hsh headp xb nb cb s h = head_rep6 hsh headp xb nb cb s' h.
Proof.
  intros hsh headp xb nb cb s s' h E1 E2 E3.
  unfold head_rep6, hinv6, hph, fextra, cx6, cn6, cc6. rewrite E1, E2, E3. reflexivity.
Qed.

Lemma crc_if_h: forall m d, m_h (crc_if m d) = m_h m.
Proof. intros. unfold crc_if. destruct (andb _ _); reflexivity. Qed.
Lemma crc_if_flags: forall m d, i_flags (m_s (crc_if m d)) = i_flags (m_s m).
Proof. intros. unfold crc_if. destruct (andb _ _); reflexivity. Qed.
Lemma crc_if_length: forall m d, i_length (m_s (crc_if m d)) = i_length (m_s m).
Proof. intros. unfold crc_if. destruct (andb _ _); reflexivity. Qed.

(* the header of the machine at the end of a header case: set_mode (initbits (crc_if m2 d)) md *)
Lemma hd6_fold6: forall F m2 d md s,
  md = i_mode s -> i_flags (m_s (crc_if m2 d)) = i_flags s -> i_length (m_s (crc_if m2 d)) = i_length s ->
  loop_stateH F (set_mode (initbits (crc_if m2 d)) md) *
    (fun _ => head_rep6 (f_hsh F) (f_headp F) (f_xb F) (f_nb F) (f_cb F) s (m_h m2)) =
  loop_stateH F (set_mode (initbits (crc_if m2 d)) md) * (fun _ => hd6 F (set_mode (initbits (crc_if m2 d)) md)).
Proof.
  intros F m2 d md s E1 E2 E3. unfold hd6.
  change (m_h (set_mode (initbits (crc_if m2 d)) md)) with (m_h (crc_if m2 d)). rewrite crc_if_h.
  rewrite (head_rep6_ext _ _ _ _ _ s (m_s (set_mode (initbits (crc_if m2 d)) md))); [reflexivity | | | ].
  - rewrite E1. reflexivity.
  - rewrite <- E2. reflexivity.
  - rewrite <- E3. reflexivity.
Qed.

Lemma hkey_head: forall m' m, hkey m' = hkey m -> i_head (m_s m) = true -> i_head (m_s m') = true.
Proof. intros m' m K H. unfold hkey in K. injection K as K. congruence. Qed.

Lemma hd6_hinv: forall F m, hd6 F m |-- !! hinv6 (m_s m) (m_h m).
Proof. intros. unfold hd6, head_rep6. apply andp_left1. apply derives_refl. Qed.

(* the loop state and a header as one PROP/LOCAL/SEP *)
Lemma lsH_hd: forall F m Hd,
  loop_stateH F m * (fun _ => Hd) =
  PROP (in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m))
  LOCAL (temp _strm (f_strmp F); temp _flush (zv (f_flush F)); temp _state (f_sp F);
         temp _next (in_ptr (f_ib F) (m_nx m)); temp _put (out_ptr (f_ob F) (Zlength (m_ow m)));
         temp _have (zv (m_have m)); temp _left (zv (m_left m)); temp _hold (lv (m_hold m));
         temp _bits (zv (m_bits m)); temp _in (zv (m_in m)); temp _out (zv (m_out m));
         temp _ret (zv (m_ret m)); temp _leave (zv (m_leave m));
         lvar _here t_code (f_vhere F); lvar _last t_code (f_vlast F);
         lvar _hbuf (tarray tuchar 4) (f_vhbuf F); gvars (f_gv F))
  SEP (Hd; field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _wrap) (zv (i_wrap (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _flags) (zv (i_flags (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _check) (lv (i_check (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _head) (if i_head (m_s m) then f_headp F else nullval) (f_sp F);
       head_partH F m; strm_part F m; crc_table_at (f_tsh F) (f_gv F);
       data_at_ Tsh (tarray tuchar 4) (f_vhbuf F);
       data_at_ Tsh t_code (f_vhere F); data_at_ Tsh t_code (f_vlast F); mem_rep_h F m).
Proof.
  intros. rewrite loop_state_hsplitH. unfold loop_state_hH. rewrite sepcon_comm. apply insert_SEP.
Qed.

Lemma hpass_step: forall flush n m, hdr_mode (m_mode m) = true -> hpass flush (S n) m ->
  exists m', stepf2 flush lenfix_list distfix_list m = IBrk m' /\ m_leave m' = 0 /\ hpass flush n m'.
Proof.
  intros flush n m H P. cbn [hpass] in P. rewrite H in P.
  destruct (stepf2 flush lenfix_list distfix_list m) as [m' | r m']; [ | contradiction].
  exists m'. destruct P. auto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* case TIME                                                                                       *)

Lemma case_TIME6 {Espec: OracleKind} (F: frame) : frame_ok5 F -> case_ok6 F IM.OS 3 -> case_ok6 F IM.TIME 2.
Proof.
  intros [FOK _] HY m n HM HL [W W2] HD HH HP. pose proof FOK as (HWS & HWH & HRG & HRT).
  apply (case_fallthrough6 F m n IM.OS 2); [lia | reflexivity | rewrite HM; reflexivity | exact HP | exact HY | ].
  apply body_frame6.
  pose proof (mwf_needbits 32 m W ltac:(lia)) as W1.
  assert (HL0: m_leave (needbits 32 m) = 0).
  { pose proof (mw_leave _ W1) as RL.
    destruct (Z.eq_dec (m_leave (needbits 32 m)) 1) as [E1 | E1]; [ | lia].
    exfalso. destruct (hpass_step _ _ _ ltac:(rewrite HM; reflexivity) HP) as (m' & Es & Hl' & _).
    rewrite (stepf2_TIME _ _ _ m HM) in Es. unfold c_TIME2 in Es. rewrite E1, Z.eqb_refl in Es.
    injection Es as Es. subst m'. lia. }
  assert (E: stepf2 (f_flush F) lenfix_list distfix_list m =
             c_OS2 (set_mode (initbits (crc_if (time_h (needbits 32 m)) (hbytes4 (m_hold (needbits 32 m))))) OS)).
  { rewrite (stepf2_TIME _ _ _ m HM). unfold c_TIME2. rewrite HL0. cbv zeta.
    unfold time_h. destruct (i_head (m_s (needbits 32 m))); reflexivity. }
  assert (HM1: m_mode (needbits 32 m) = TIME) by (rewrite hk_needbits_mode; exact HM).
  pose proof (hkey_needbits 32 m) as K1.
  destruct (needbits_f_sh 4 32 m) as [S1 H1]. change (needbits_f 4 32 m) with (needbits 32 m) in S1, H1.
  case_body_stmt.
  eapply semax_seq_frame6; [apply semax_needbits_TIME5H; auto; lia | ].
  rewrite <- (hd6_needbits F 32 m).
  eapply semax_seq_frame6; [apply semax_ifleave0H; exact HL0 | ].
  assert (Hh1: i_head (m_s (needbits 32 m)) = true) by (rewrite S1; exact HH).
  unfold time_h in E. rewrite Hh1 in E.
  set (m1 := needbits 32 m) in *. clearbody m1.
  set (m2 := upd_h m1 (fun h => set_h_time h (m_hold m1))).
  apply semax_seq' with
    (P' := loop_stateH F m2 * (fun _ => head_rep6 (f_hsh F) (f_headp F) (f_xb F) (f_nb F) (f_cb F)
                                          (set_i_mode (m_s m1) IM.OS) (m_h m2))).
  { clear E HY. rewrite !lsH_hd. unfold hd6, head_rep6, head_rep6p, head_partH, hnoneH.
    rewrite Hh1. subst m2. cbn [upd_h set_m_h m_s m_h].
    abbreviate_semax. Intros vt vtm vxf vos vxl vhc lx ln lc.
    forward.
    assert_PROP (isptr (f_headp F)) by entailer!.
    forward_if.
    { forward. forward. Exists vt (Vlong (Int64.repr (m_hold m1))) vxf vos vxl vhc lx ln lc. entailer!.
      2: { rewrite Hh1. cancel. apply derives_refl. }
      assert (HMs: i_mode (m_s m1) = IM.TIME) by exact HM1.
      unfold hinv6, hph, cx6, cn6, cc6 in *.
      cbn [i_mode set_i_mode h_done set_h_time h_text h_extra_max h_name_max h_comm_max h_xbuf h_nbuf h_cbuf] in *.
      rewrite HMs in *. cbn in H3, H8, H9, H10 |- *.
      refine (conj (conj (proj1 H2) (conj _ (conj _ (conj _ _)))) (conj (fun _ => H3 ltac:(lia)) (conj H8 (conj H9 H10))));
        intros E; first [discriminate E | compute in E; discriminate E]. }
    { exfalso. destruct (f_headp F); try contradiction; discriminate. } }
  assert (HM2: m_mode m2 = TIME) by exact HM1.
  assert (HL2: m_leave m2 = 0) by exact HL0.
  assert (K2: hkey m2 = hkey m) by exact K1.
  assert (W2': mwf m2).
  { apply mwf_upd_h; [exact W1 | ]. apply hwf_set_time; [apply (mw_h _ W1) | apply (mw_hold _ W1)]. }
  assert (Ehold: m_hold m2 = m_hold m1) by reflexivity.
  fold m2 in E. rewrite <- Ehold in E.
  assert (S2: i_mode (set_i_mode (m_s m1) IM.OS) = IM.OS /\ i_flags (set_i_mode (m_s m1) IM.OS) = i_flags (m_s m2) /\
              i_length (set_i_mode (m_s m1) IM.OS) = i_length (m_s m2)) by (split; [ | split]; reflexivity).
  set (HdOS := head_rep6 (f_hsh F) (f_headp F) (f_xb F) (f_nb F) (f_cb F) (set_i_mode (m_s m1) IM.OS) (m_h m2)).
  clearbody m2. clear Ehold.
  eapply semax_seq_frame6; [exact (semax_crcblock_TIMEH F m2 FOK W2') | ].
  eapply semax_seq_frame6; [apply semax_initbits5H | ].
  assert (W3: mwf3 (set_mode (initbits (crc_if m2 (hbytes4 (m_hold m2)))) OS)).
  { apply mwf3_set_mode_hdr.
    - apply mwf_initbits, mwf_crc_if; [exact W2' | apply hk_hbytes4_bytes].
    - change (m_mode (initbits (crc_if m2 (hbytes4 (m_hold m2))))) with (m_mode (crc_if m2 (hbytes4 (m_hold m2)))).
      rewrite hk_crc_if_mode, HM2. unfold HEAD, TIME, TYPEDO; lia.
    - unfold FLAGS, OS, TYPEDO; lia. }
  assert (HL3: m_leave (set_mode (initbits (crc_if m2 (hbytes4 (m_hold m2)))) OS) = 0).
  { change (m_leave (set_mode (initbits (crc_if m2 (hbytes4 (m_hold m2)))) OS))
      with (m_leave (crc_if m2 (hbytes4 (m_hold m2)))). rewrite hk_crc_if_leave. exact HL2. }
  assert (K3: hkey (set_mode (initbits (crc_if m2 (hbytes4 (m_hold m2)))) OS) = hkey m).
  { rewrite hkey_set_mode, hkey_initbits, hkey_crc_if. exact K2. }
  eapply semax_last_frame6; [apply semax_store_mode5H | ].
  cbn [RA_normal overridePost]. unfold fall_post6.
  apply exp_right with (set_mode (initbits (crc_if m2 (hbytes4 (m_hold m2)))) OS).
  apply andp_right.
  { apply prop_right. split.
    { etransitivity; [exact E | symmetry; exact (stepf2_OS (f_flush F) lenfix_list distfix_list (set_mode (initbits (crc_if m2 (hbytes4 (m_hold m2)))) OS) eq_refl)]. }
    split; [reflexivity | ]. split; [exact HL3 | ]. split; [exact W3 | ].
    split; [exact (hkey_hd_ok F m _ K3 HD) | ]. split; [exact (hkey_hdr_tok F m _ K3) | ].
    exact (hkey_head _ _ K3 HH). }
  rewrite hd6_fold6 with (s := set_i_mode (m_s m1) IM.OS); [apply derives_refl | exact (proj1 S2) | | ].
  - rewrite crc_if_flags. symmetry; exact (proj1 (proj2 S2)).
  - rewrite crc_if_length. symmetry; exact (proj2 (proj2 S2)).
Qed.


(* ---------------------------------------------------------------------------------------------- *)
(* case OS                                                                                         *)

Lemma case_OS6 {Espec: OracleKind} (F: frame) : frame_ok5 F -> case_ok6 F IM.EXLEN 4 -> case_ok6 F IM.OS 3.
Proof.
  intros [FOK _] HY m n HM HL [W W2] HD HH HP. pose proof FOK as (HWS & HWH & HRG & HRT).
  apply (case_fallthrough6 F m n IM.EXLEN 3); [lia | reflexivity | rewrite HM; reflexivity | exact HP | exact HY | ].
  apply body_frame6.
  pose proof (mwf_needbits 16 m W ltac:(lia)) as W1.
  assert (HL0: m_leave (needbits 16 m) = 0).
  { pose proof (mw_leave _ W1) as RL.
    destruct (Z.eq_dec (m_leave (needbits 16 m)) 1) as [E1 | E1]; [ | lia].
    exfalso. destruct (hpass_step _ _ _ ltac:(rewrite HM; reflexivity) HP) as (m' & Es & Hl' & _).
    rewrite (stepf2_OS _ _ _ m HM) in Es. unfold c_OS2 in Es. rewrite E1, Z.eqb_refl in Es.
    injection Es as Es. subst m'. lia. }
  assert (E: stepf2 (f_flush F) lenfix_list distfix_list m =
             c_EXLEN2 (set_mode (initbits (crc_if (os_h (needbits 16 m)) (hbytes2 (m_hold (needbits 16 m))))) EXLEN)).
  { rewrite (stepf2_OS _ _ _ m HM). unfold c_OS2. rewrite HL0. cbv zeta.
    unfold os_h. destruct (i_head (m_s (needbits 16 m))); reflexivity. }
  assert (HM1: m_mode (needbits 16 m) = OS) by (rewrite hk_needbits_mode; exact HM).
  pose proof (hkey_needbits 16 m) as K1.
  destruct (needbits_f_sh 4 16 m) as [S1 H1]. change (needbits_f 4 16 m) with (needbits 16 m) in S1, H1.
  case_body_stmt.
  eapply semax_seq_frame6; [apply semax_needbits_OS5H; auto; lia | ].
  rewrite <- (hd6_needbits F 16 m).
  eapply semax_seq_frame6; [apply semax_ifleave0H; exact HL0 | ].
  assert (Hh1: i_head (m_s (needbits 16 m)) = true) by (rewrite S1; exact HH).
  unfold os_h in E. rewrite Hh1 in E.
  set (m1 := needbits 16 m) in *. clearbody m1.
  set (m2 := upd_h m1 (fun h => set_h_os (set_h_xflags h (Z.land (m_hold m1) 255)) (s32 (Z.shiftr (m_hold m1) 8)))).
  apply semax_seq' with
    (P' := loop_stateH F m2 * (fun _ => head_rep6 (f_hsh F) (f_headp F) (f_xb F) (f_nb F) (f_cb F)
                                          (set_i_mode (m_s m1) IM.EXLEN) (m_h m2))).
  { clear E HY. rewrite !lsH_hd. unfold hd6, head_rep6, head_rep6p, head_partH, hnoneH.
    rewrite Hh1. subst m2. cbn [upd_h set_m_h m_s m_h].
    abbreviate_semax. Intros vt vtm vxf vos vxl vhc lx ln lc.
    forward.
    assert_PROP (isptr (f_headp F)) by entailer!.
    forward_if.
    { forward. forward. forward. forward.
      Exists vt vtm (Vint (Int.repr (Int64.Z_mod_modulus (Z.land (Int64.Z_mod_modulus (m_hold m1)) 255))))
        (Vint (Int.repr (Int64.Z_mod_modulus (Z.shiftr (Int64.Z_mod_modulus (m_hold m1)) 8)))) vxl vhc lx ln lc.
      entailer!.
      2: { rewrite Hh1. cancel. apply derives_refl. }
      pose proof (mw_hold _ W1) as RH.
      rewrite hk_land255, hk_shr8 by exact RH.
      assert (HMs: i_mode (m_s m1) = IM.OS) by exact HM1.
      unfold hinv6, hph, cx6, cn6, cc6 in *.
      cbn [i_mode set_i_mode h_done set_h_os set_h_xflags h_text h_time h_xflags h_os h_extra_max h_name_max h_comm_max h_xbuf h_nbuf h_cbuf] in *.
      rewrite HMs in *. cbn in H3, H4, H8, H9, H10 |- *.
      refine (conj (conj (proj1 H2) (conj _ (conj _ (conj _ _))))
        (conj (fun _ => H3 ltac:(lia)) (conj (fun _ => H4 ltac:(lia)) (conj (fun _ => conj eq_refl eq_refl)
          (conj H8 (conj H9 H10))))));
        intros E; first [discriminate E | compute in E; discriminate E]. }
    { exfalso. destruct (f_headp F); try contradiction; discriminate. } }
  assert (HM2: m_mode m2 = OS) by exact HM1.
  assert (HL2: m_leave m2 = 0) by exact HL0.
  assert (K2: hkey m2 = hkey m) by exact K1.
  assert (W2': mwf m2).
  { apply mwf_upd_h; [exact W1 | ]. apply hwf_set_xflags_os; [apply (mw_h _ W1) | | apply hk_s32_range].
    pose proof (hk_land_range (m_hold m1) 255 ltac:(lia)). unfold srange; rep_lia. }
  assert (Ehold: m_hold m2 = m_hold m1) by reflexivity.
  fold m2 in E. rewrite <- Ehold in E.
  assert (S2: i_mode (set_i_mode (m_s m1) IM.EXLEN) = IM.EXLEN /\ i_flags (set_i_mode (m_s m1) IM.EXLEN) = i_flags (m_s m2) /\
              i_length (set_i_mode (m_s m1) IM.EXLEN) = i_length (m_s m2)) by (split; [ | split]; reflexivity).
  set (HdEX := head_rep6 (f_hsh F) (f_headp F) (f_xb F) (f_nb F) (f_cb F) (set_i_mode (m_s m1) IM.EXLEN) (m_h m2)).
  clearbody m2. clear Ehold.
  eapply semax_seq_frame6; [exact (semax_crcblock_OSH F m2 FOK W2') | ].
  eapply semax_seq_frame6; [apply semax_initbits5H | ].
  assert (W3: mwf3 (set_mode (initbits (crc_if m2 (hbytes2 (m_hold m2)))) EXLEN)).
  { apply mwf3_set_mode_hdr.
    - apply mwf_initbits, mwf_crc_if; [exact W2' | apply hk_hbytes2_bytes].
    - change (m_mode (initbits (crc_if m2 (hbytes2 (m_hold m2))))) with (m_mode (crc_if m2 (hbytes2 (m_hold m2)))).
      rewrite hk_crc_if_mode, HM2. unfold HEAD, OS, TYPEDO; lia.
    - unfold FLAGS, EXLEN, TYPEDO; lia. }
  assert (HL3: m_leave (set_mode (initbits (crc_if m2 (hbytes2 (m_hold m2)))) EXLEN) = 0).
  { change (m_leave (set_mode (initbits (crc_if m2 (hbytes2 (m_hold m2)))) EXLEN))
      with (m_leave (crc_if m2 (hbytes2 (m_hold m2)))). rewrite hk_crc_if_leave. exact HL2. }
  assert (K3: hkey (set_mode (initbits (crc_if m2 (hbytes2 (m_hold m2)))) EXLEN) = hkey m).
  { rewrite hkey_set_mode, hkey_initbits, hkey_crc_if. exact K2. }
  eapply semax_last_frame6; [apply semax_store_mode5H | ].
  cbn [RA_normal overridePost]. unfold fall_post6.
  apply exp_right with (set_mode (initbits (crc_if m2 (hbytes2 (m_hold m2)))) EXLEN).
  apply andp_right.
  { apply prop_right. split.
    { etransitivity; [exact E | symmetry; exact (stepf2_EXLEN (f_flush F) lenfix_list distfix_list (set_mode (initbits (crc_if m2 (hbytes2 (m_hold m2)))) EXLEN) eq_refl)]. }
    split; [reflexivity | ]. split; [exact HL3 | ]. split; [exact W3 | ].
    split; [exact (hkey_hd_ok F m _ K3 HD) | ]. split; [exact (hkey_hdr_tok F m _ K3) | ].
    exact (hkey_head _ _ K3 HH). }
  rewrite hd6_fold6 with (s := set_i_mode (m_s m1) IM.EXLEN); [apply derives_refl | exact (proj1 S2) | | ].
  - rewrite crc_if_flags. symmetry; exact (proj1 (proj2 S2)).
  - rewrite crc_if_length. symmetry; exact (proj2 (proj2 S2)).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* case FLAGS                                                                                      *)

Lemma hpass_bad: forall flush n m e, h_done (m_h m) = 0 -> ~ hpass flush n (set_bad m e).
Proof.
  intros flush n m e D P. destruct n as [ | n]; [exact P | ]. cbn [hpass] in P.
  change (m_mode (set_bad m e)) with BAD in P. change (hdr_mode BAD) with false in P.
  destruct P as [D1 _]. change (m_h (set_bad m e)) with (m_h m) in D1. lia.
Qed.

(* the header's done field, from hd6 *)
Lemma hd6_done_pre {Espec: OracleKind} (Delta: tycontext) (F: frame) (m: mst) (P: environ -> mpred) c R:
  (h_done (m_h m) = 0 -> semax Delta (P * (fun _ => hd6 F m)) c R) ->
  semax Delta (P * (fun _ => hd6 F m)) c R.
Proof.
  intros H.
  apply semax_pre with (P' := !! (h_done (m_h m) = 0) && (P * (fun _ => hd6 F m))).
  - intros rho. simpl. apply andp_left2. apply andp_right; [ | apply derives_refl].
    eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply hd6_hinv] | ].
    rewrite sepcon_comm. rewrite prop_sepcon. apply andp_left1. apply prop_derives. intros [D _]. exact D.
  - apply semax_extract_prop. exact H.
Qed.

Lemma case_FLAGS6 {Espec: OracleKind} (F: frame) : frame_ok5 F -> case_ok6 F IM.TIME 2 -> case_ok6 F IM.FLAGS 1.
Proof.
  intros [FOK _] HY m n HM HL [W W2] HD HH HP. pose proof FOK as (HWS & HWH & HRG & HRT).
  apply (case_fallthrough6 F m n IM.TIME 1); [lia | reflexivity | rewrite HM; reflexivity | exact HP | exact HY | ].
  apply body_frame6.
  apply hd6_done_pre. intros D0.
  pose proof (mwf_needbits 16 m W ltac:(lia)) as W1.
  destruct (hpass_step _ _ _ ltac:(rewrite HM; reflexivity) HP) as (m' & Es & Hl' & Hp').
  rewrite (stepf2_FLAGS _ _ _ m HM) in Es. unfold c_FLAGS2 in Es.
  destruct (needbits_f_sh 4 16 m) as [S1 H1]. change (needbits_f 4 16 m) with (needbits 16 m) in S1, H1.
  assert (HL0: m_leave (needbits 16 m) = 0).
  { pose proof (mw_leave _ W1) as RL.
    destruct (Z.eq_dec (m_leave (needbits 16 m)) 1) as [E1 | E1]; [ | lia].
    exfalso. rewrite E1, Z.eqb_refl in Es. injection Es as Es. subst m'. lia. }
  rewrite HL0 in Es. cbv zeta in Es. change (0 =? 1) with false in Es.
  assert (C1: Z.land (s32 (m_hold (needbits 16 m))) 255 = 8).
  { destruct (Z.eq_dec (Z.land (s32 (m_hold (needbits 16 m))) 255) 8) as [C | C]; [exact C | exfalso].
    rewrite (proj2 (Z.eqb_neq _ _) C) in Es. cbn [negb] in Es. injection Es as Es. subst m'.
    refine (hpass_bad _ _ _ _ _ Hp'). change (h_done (m_h (needbits 16 m)) = 0). rewrite H1. exact D0. }
  rewrite (proj2 (Z.eqb_eq _ _) C1) in Es. cbn [negb] in Es.
  assert (C2: Z.land (s32 (m_hold (needbits 16 m))) 57344 = 0).
  { destruct (Z.eq_dec (Z.land (s32 (m_hold (needbits 16 m))) 57344) 0) as [C | C]; [exact C | exfalso].
    rewrite (proj2 (Z.eqb_neq _ _) C) in Es. cbn [negb] in Es. injection Es as Es. subst m'.
    refine (hpass_bad _ _ _ _ _ Hp'). change (h_done (m_h (needbits 16 m)) = 0). rewrite H1. exact D0. }
  clear Es Hl' Hp' m'.
  assert (E: stepf2 (f_flush F) lenfix_list distfix_list m =
    c_TIME2 (set_mode (initbits (crc_if
      (text_h (upd_s (needbits 16 m) (fun s => set_i_flags s (s32 (m_hold (needbits 16 m))))))
      (hbytes2 (m_hold (needbits 16 m))))) TIME)).
  { rewrite (stepf2_FLAGS _ _ _ m HM). unfold c_FLAGS2. rewrite HL0. cbv zeta.
    rewrite (proj2 (Z.eqb_eq _ _) C1), (proj2 (Z.eqb_eq _ _) C2). cbn [negb].
    unfold text_h. destruct (i_head (m_s (upd_s (needbits 16 m) (fun s => set_i_flags s (s32 (m_hold (needbits 16 m)))))));
      reflexivity. }
  assert (HM1: m_mode (needbits 16 m) = FLAGS) by (rewrite hk_needbits_mode; exact HM).
  pose proof (hkey_needbits 16 m) as K1.
  assert (Hh1: i_head (m_s (needbits 16 m)) = true) by (rewrite S1; exact HH).
  case_body_stmt.
  eapply semax_seq_frame6; [apply semax_needbits_FLAGS5H; auto; lia | ].
  rewrite <- (hd6_needbits F 16 m).
  eapply semax_seq_frame6; [apply semax_ifleave0H; exact HL0 | ].
  set (m1 := needbits 16 m) in *. clearbody m1.
  pose proof (mw_hold _ W1) as RH.
  eapply semax_seq_frame6 with (Q := loop_stateH F (upd_s m1 (fun s => set_i_flags s (s32 (m_hold m1))))).
  { rewrite !loop_state_hsplitH. unfold loop_state_hH.
    abbreviate_semax.
    forward.
    entailer!.
    change (i_flags (m_s (upd_s m1 (fun s : istate => set_i_flags s (s32 (m_hold m1)))))) with (s32 (m_hold m1)).
    rewrite hkf_repr_s32, hkf_repr_mod64. apply derives_refl. }
  assert (W2': mwf (upd_s m1 (fun s => set_i_flags s (s32 (m_hold m1))))).
  { destruct W1 as [MD S H]; constructor; auto; cbn [upd_s set_m_s m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits
      m_in m_out m_ret m_leave m_adler m_tin m_tout m_snx m_sow m_mode] in *; auto.
    - destruct MD; constructor; auto.
    - destruct S; constructor; auto. apply hk_s32_range. }
  pose proof (hk_s32_range (m_hold m1)) as RF.
  set (fl := s32 (m_hold m1)) in *.
  set (m2 := upd_s m1 (fun s => set_i_flags s fl)) in *.
  assert (Hfl: i_flags (m_s m2) = fl) by reflexivity.
  assert (Hh2: m_hold m2 = m_hold m1) by reflexivity.
  assert (HM2: m_mode m2 = FLAGS) by exact HM1.
  assert (HL2: m_leave m2 = 0) by exact HL0.
  assert (K2: hkey m2 = hkey m) by exact K1.
  assert (Hh2': i_head (m_s m2) = true) by exact Hh1.
  assert (S2: i_mode (m_s m2) = i_mode (m_s m1)) by reflexivity.
  assert (Hmh2: m_h m2 = m_h m1) by reflexivity.
  clearbody m2. clear HY.
  eapply semax_seq_frame6 with (Q := loop_stateH F m2).
  { rewrite !loop_state_hsplitH. unfold loop_state_hH. rewrite Hfl.
    abbreviate_semax.
    forward.
    forward_if.
    - exfalso. apply H2. rewrite hk_and_repr, C1. reflexivity.
    - forward. entailer!. }
  eapply semax_seq_frame6 with (Q := loop_stateH F m2).
  { rewrite !loop_state_hsplitH. unfold loop_state_hH. rewrite Hfl.
    abbreviate_semax.
    forward.
    forward_if.
    - exfalso. match goal with H: Int.and _ _ <> _ |- _ => apply H end. rewrite hk_and_repr, C2. reflexivity.
    - forward. entailer!. }
  set (m3 := upd_h m2 (fun h => set_h_text h (Z.land (Z.shiftr (m_hold m2) 8) 1))).
  apply semax_seq' with
    (P' := loop_stateH F m3 * (fun _ => head_rep6 (f_hsh F) (f_headp F) (f_xb F) (f_nb F) (f_cb F)
                                          (set_i_mode (m_s m2) IM.TIME) (m_h m3))).
  { clear E. rewrite !lsH_hd. unfold hd6, head_rep6, head_rep6p, head_partH, hnoneH.
    rewrite Hh2'. subst m3. cbn [upd_h set_m_h m_s m_h].
    abbreviate_semax. Intros vt vtm vxf vos vxl vhc lx ln lc.
    forward.
    assert_PROP (isptr (f_headp F)) by entailer!.
    forward_if.
    { forward. forward. rewrite Hmh2.
      Exists (Vint (Int.repr (Int64.Z_mod_modulus (Z.land (Int64.Z_mod_modulus (Z.shiftr (Int64.Z_mod_modulus (m_hold m2)) 8)) 1))))
        vtm vxf vos vxl vhc lx ln lc.
      entailer!.
      2: { rewrite Hh2'. cancel. apply derives_refl. }
      rewrite hkf_text by exact (mw_hold _ W2').
      assert (HMs: i_mode (m_s m1) = IM.FLAGS) by exact HM1.
      unfold hinv6, hph, cx6, cn6, cc6 in *.
      cbn [i_mode set_i_mode h_done set_h_text h_text h_extra_max h_name_max h_comm_max h_xbuf h_nbuf h_cbuf] in *.
      rewrite HMs in *. cbn in H8, H9, H10 |- *.
      refine (conj (conj (proj1 H2) (conj _ (conj _ (conj _ _)))) (conj (fun _ => eq_refl) (conj H8 (conj H9 H10))));
        intros E; first [discriminate E | compute in E; discriminate E]. }
    { exfalso. destruct (f_headp F); try contradiction; discriminate. } }
  unfold text_h in E. rewrite Hh2' in E. fold m3 in E.
  assert (Ehold: m_hold m3 = m_hold m1) by exact Hh2.
  rewrite <- Ehold in E.
  assert (HM3: m_mode m3 = FLAGS) by exact HM2.
  assert (HL3: m_leave m3 = 0) by exact HL2.
  assert (K3: hkey m3 = hkey m) by exact K2.
  assert (W3: mwf m3).
  { apply mwf_upd_h; [exact W2' | ]. apply hwf_set_text; [apply (mw_h _ W2') | ].
    pose proof (hk_land_range (Z.shiftr (m_hold m2) 8) 1 ltac:(lia)). unfold srange; rep_lia. }
  assert (S3: i_mode (set_i_mode (m_s m2) IM.TIME) = IM.TIME /\ i_flags (set_i_mode (m_s m2) IM.TIME) = i_flags (m_s m3) /\
              i_length (set_i_mode (m_s m2) IM.TIME) = i_length (m_s m3)) by (split; [ | split]; reflexivity).
  set (HdT := head_rep6 (f_hsh F) (f_headp F) (f_xb F) (f_nb F) (f_cb F) (set_i_mode (m_s m2) IM.TIME) (m_h m3)).
  clearbody m3. clear Ehold.
  eapply semax_seq_frame6; [exact (semax_crcblock_FLAGSH F m3 FOK W3) | ].
  eapply semax_seq_frame6; [apply semax_initbits5H | ].
  assert (W4: mwf3 (set_mode (initbits (crc_if m3 (hbytes2 (m_hold m3)))) TIME)).
  { apply mwf3_set_mode_hdr.
    - apply mwf_initbits, mwf_crc_if; [exact W3 | apply hk_hbytes2_bytes].
    - change (m_mode (initbits (crc_if m3 (hbytes2 (m_hold m3))))) with (m_mode (crc_if m3 (hbytes2 (m_hold m3)))).
      rewrite hk_crc_if_mode, HM3. unfold HEAD, FLAGS, TYPEDO; lia.
    - unfold FLAGS, TIME, TYPEDO; lia. }
  assert (HL4: m_leave (set_mode (initbits (crc_if m3 (hbytes2 (m_hold m3)))) TIME) = 0).
  { change (m_leave (set_mode (initbits (crc_if m3 (hbytes2 (m_hold m3)))) TIME))
      with (m_leave (crc_if m3 (hbytes2 (m_hold m3)))). rewrite hk_crc_if_leave. exact HL3. }
  assert (K4: hkey (set_mode (initbits (crc_if m3 (hbytes2 (m_hold m3)))) TIME) = hkey m).
  { rewrite hkey_set_mode, hkey_initbits, hkey_crc_if. exact K3. }
  eapply semax_last_frame6; [apply semax_store_mode5H | ].
  cbn [RA_normal overridePost]. unfold fall_post6.
  apply exp_right with (set_mode (initbits (crc_if m3 (hbytes2 (m_hold m3)))) TIME).
  apply andp_right.
  { apply prop_right. split.
    { etransitivity; [exact E | symmetry;
        exact (stepf2_TIME (f_flush F) lenfix_list distfix_list (set_mode (initbits (crc_if m3 (hbytes2 (m_hold m3)))) TIME) eq_refl)]. }
    split; [reflexivity | ]. split; [exact HL4 | ]. split; [exact W4 | ].
    split; [exact (hkey_hd_ok F m _ K4 HD) | ]. split; [exact (hkey_hdr_tok F m _ K4) | ].
    exact (hkey_head _ _ K4 HH). }
  rewrite hd6_fold6 with (s := set_i_mode (m_s m2) IM.TIME); [apply derives_refl | exact (proj1 S3) | | ].
  - rewrite crc_if_flags. symmetry; exact (proj1 (proj2 S3)).
  - rewrite crc_if_length. symmetry; exact (proj2 (proj2 S3)).
Qed.

(* the three cases *)
Lemma rth_fto_proof : rth_fto_stmt.
Proof.
  intros Espec F FOK. split; [ | split].
  - apply case_FLAGS6; exact FOK.
  - apply case_TIME6; exact FOK.
  - apply case_OS6; exact FOK.
Qed.
