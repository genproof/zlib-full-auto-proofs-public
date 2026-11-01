(* inflate(), case FLAGS (index 1) in Delta_cases5: NEEDBITS(16); state->flags = (int)hold; the two header
   checks (BAD, with strm->msg = the string literal: in Delta_cases5's globals); head->text; CRC2; INITBITS;
   state->mode = TIME; falls into TIME. *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.HdrSame5.
Require Import Zlib.proof.inflate.MwfLemmas.
Require Import Zlib.proof.inflate.Steps2.
Require Import Zlib.proof.inflate.NeedKit5.
Require Import Zlib.proof.inflate.NeedBits_5.
Require Import Zlib.proof.inflate.HdrKit5.
Require Import Zlib.proof.inflate.HdrCrc5.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* strm->msg = (char * )<msg>; state->mode = BAD; break;  (the literal <msg> is an array of n chars) *)
Definition bad_block (id: ident) (n: Z) : statement :=
  (Ssequence (Sassign (Efield (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr))) (Tstruct _z_stream_s noattr)) _msg (tptr tschar)) (Ecast (Evar id (tarray tschar n)) (tptr tschar))) (Ssequence (Sassign (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr))) (Tstruct _inflate_state noattr)) _mode tint) (Econst_int (Int.repr 16209) tint)) Sbreak)).

(* the error block of the cases: the break leaves the switch with the machine set_bad m e *)
Definition bad_ok5 {Espec: OracleKind} (F: frame) (e: msgid) (n: Z) : Prop :=
  forall (m m0: mst) (R: ret_assert),
    RA_break R = RA_normal (case_post2 F m0) ->
    stepf2 (f_flush F) lenfix_list distfix_list m0 = IBrk (set_bad m e) ->
    semax Delta_cases5 (loop_state F m) (bad_block (msg_ident e) n) R.

Lemma mem_rep_h_bad: forall F m e, mem_rep_h F (set_bad m e) = mem_rep_h F m.
Proof. reflexivity. Qed.
Lemma head_part_bad: forall F m e, head_part F (set_bad m e) = head_part F m.
Proof. reflexivity. Qed.

Lemma bad_ok5_method {Espec: OracleKind} (F: frame) : frame_ok F -> bad_ok5 F M_method 27.
Proof.
  intros FOK m m0 R HR HS. pose proof FOK as (HWS & HWH & HRG & HRT).
  unfold bad_block. cbn [msg_ident].
  rewrite loop_state_hsplit. unfold loop_state_h, strm_part, strm_rep.
  abbreviate_semax.
  remember (f_gv F _zcalloc) as zca eqn:Hzca. remember (f_gv F _zcfree) as zcf eqn:Hzcf.
  forward. forward. forward.
  rewrite HR. unfold case_post2, RA_normal. Exists (set_bad m M_method).
  rewrite loop_state_hsplit. unfold loop_state_h, strm_part, strm_rep.
  rewrite (mem_rep_h_bad F m M_method), (head_part_bad F m M_method).
  cbn [set_bad set_mode upd_s set_m_s set_m_msg m_s m_msg i_mode set_i_mode i_wrap i_flags i_check i_head
       m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_snx m_sow m_tin m_tout m_adler m_have m_left].
  rewrite <- Hzca, <- Hzcf. entailer!.
Qed.

Lemma bad_ok5_hflags {Espec: OracleKind} (F: frame) : frame_ok F -> bad_ok5 F M_hflags 25.
Proof.
  intros FOK m m0 R HR HS. pose proof FOK as (HWS & HWH & HRG & HRT).
  unfold bad_block. cbn [msg_ident].
  rewrite loop_state_hsplit. unfold loop_state_h, strm_part, strm_rep.
  abbreviate_semax.
  remember (f_gv F _zcalloc) as zca eqn:Hzca. remember (f_gv F _zcfree) as zcf eqn:Hzcf.
  forward. forward. forward.
  rewrite HR. unfold case_post2, RA_normal. Exists (set_bad m M_hflags).
  rewrite loop_state_hsplit. unfold loop_state_h, strm_part, strm_rep.
  rewrite (mem_rep_h_bad F m M_hflags), (head_part_bad F m M_hflags).
  cbn [set_bad set_mode upd_s set_m_s set_m_msg m_s m_msg i_mode set_i_mode i_wrap i_flags i_check i_head
       m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_snx m_sow m_tin m_tout m_adler m_have m_left].
  rewrite <- Hzca, <- Hzcf. entailer!.
Qed.

Lemma hkf_repr_s32: forall x, Int.repr (s32 x) = Int.repr x.
Proof.
  intros x. apply Int.eqm_samerepr. unfold Int.eqm, s32.
  change Int.modulus with (2 ^ 32).
  pose proof (Z.mod_pos_bound x (2 ^ 32) ltac:(lia)).
  destruct (Z.ltb_spec (x mod 2 ^ 32) (2 ^ 31)).
  - exists (- (x / 2 ^ 32)). pose proof (Z.div_mod x (2 ^ 32) ltac:(lia)). lia.
  - exists (- (x / 2 ^ 32) - 1). pose proof (Z.div_mod x (2 ^ 32) ltac:(lia)). lia.
Qed.

Lemma hkf_repr_mod64: forall x, Int.repr (Int64.Z_mod_modulus x) = Int.repr x.
Proof.
  intros x. rewrite Int64.Z_mod_modulus_eq. apply Int.eqm_samerepr. unfold Int.eqm.
  change Int.modulus with (2 ^ 32). change Int64.modulus with ((2 ^ 32 * 2 ^ 32)%Z).
  exists ((- (x / (2 ^ 32 * 2 ^ 32)) * 2 ^ 32)%Z).
  pose proof (Z.div_mod x (2 ^ 32 * 2 ^ 32)%Z ltac:(lia)). lia.
Qed.

Lemma hkf_and_eq: forall a b c, 0 <= b <= Int.max_signed -> 0 <= c <= Int.max_signed ->
  Int.and (Int.repr a) (Int.repr b) = Int.repr c -> Z.land a b = c.
Proof.
  intros a b c Hb Hc H. rewrite hk_and_repr in H. pose proof (hk_land_range a b ltac:(lia)).
  apply (f_equal Int.unsigned) in H. rewrite !Int.unsigned_repr in H by rep_lia. exact H.
Qed.

Lemma hkf_text: forall h, lrange h ->
  Int64.Z_mod_modulus (Z.land (Int64.Z_mod_modulus (Z.shiftr (Int64.Z_mod_modulus h) 8)) 1) =
  Z.land (Z.shiftr h 8) 1.
Proof.
  intros h R. unfold lrange in R.
  assert (M: Int64.modulus = Int64.max_unsigned + 1) by reflexivity.
  pose proof (Zshiftr_range h 8 R ltac:(lia)) as R8.
  pose proof (hk_land_range (Z.shiftr h 8) 1 ltac:(lia)) as R1.
  rewrite !Int64.Z_mod_modulus_eq, M.
  rewrite (Z.mod_small h) by rep_lia. rewrite (Z.mod_small (Z.shiftr h 8)) by rep_lia.
  rewrite Z.mod_small by rep_lia. reflexivity.
Qed.

Definition text_h (m: mst) : mst :=
  if i_head (m_s m) then upd_h m (fun h => set_h_text h (Z.land (Z.shiftr (m_hold m) 8) 1)) else m.

Lemma case_FLAGS5 {Espec: OracleKind} (F: frame) : frame_ok5 F -> case_okT5 F TIME 2 -> case_okT5 F FLAGS 1.
Proof.
  intros [FOK _] HY m HM HL [W W2] HD. pose proof FOK as (HWS & HWH & HRG & HRT).
  pose proof (bad_ok5_method F FOK) as HB1. pose proof (bad_ok5_hflags F FOK) as HB2.
  apply (case_fallthroughT5 F m TIME 1); [lia | exact HY | ].
  apply body_frameT5.
  case_body_stmt.
  eapply (semax_needbits_seq_r5 F m m 16);
    [ apply semax_needbits_FLAGS5; auto; lia | auto | lia | reflexivity
    | intro E; rewrite (stepf2_FLAGS _ _ _ m HM); unfold c_FLAGS2; rewrite E; reflexivity | ].
  apply semax_extract_prop; intros HL0.
  pose proof (mwf_needbits 16 m W ltac:(lia)) as W1.
  assert (HM1: m_mode (needbits 16 m) = FLAGS) by (rewrite hk_needbits_mode; exact HM).
  pose proof (hkey_needbits 16 m) as K1.
  assert (EB1: Z.land (s32 (m_hold (needbits 16 m))) 255 <> 8 ->
    stepf2 (f_flush F) lenfix_list distfix_list m =
    IBrk (set_bad (upd_s (needbits 16 m) (fun s => set_i_flags s (s32 (m_hold (needbits 16 m))))) M_method)).
  { intro N. rewrite (stepf2_FLAGS _ _ _ m HM). unfold c_FLAGS2. rewrite HL0. cbv zeta.
    rewrite (proj2 (Z.eqb_neq _ _) N). reflexivity. }
  assert (EB2: Z.land (s32 (m_hold (needbits 16 m))) 255 = 8 ->
    Z.land (s32 (m_hold (needbits 16 m))) 57344 <> 0 ->
    stepf2 (f_flush F) lenfix_list distfix_list m =
    IBrk (set_bad (upd_s (needbits 16 m) (fun s => set_i_flags s (s32 (m_hold (needbits 16 m))))) M_hflags)).
  { intros N1 N2. rewrite (stepf2_FLAGS _ _ _ m HM). unfold c_FLAGS2. rewrite HL0. cbv zeta.
    rewrite (proj2 (Z.eqb_eq _ _) N1), (proj2 (Z.eqb_neq _ _) N2). reflexivity. }
  assert (EOK: Z.land (s32 (m_hold (needbits 16 m))) 255 = 8 ->
    Z.land (s32 (m_hold (needbits 16 m))) 57344 = 0 ->
    stepf2 (f_flush F) lenfix_list distfix_list m =
    c_TIME2 (set_mode (initbits (crc_if
      (text_h (upd_s (needbits 16 m) (fun s => set_i_flags s (s32 (m_hold (needbits 16 m))))))
      (hbytes2 (m_hold (needbits 16 m))))) TIME)).
  { intros N1 N2. rewrite (stepf2_FLAGS _ _ _ m HM). unfold c_FLAGS2. rewrite HL0. cbv zeta.
    rewrite (proj2 (Z.eqb_eq _ _) N1), (proj2 (Z.eqb_eq _ _) N2). cbn [negb].
    unfold text_h. destruct (i_head (m_s (upd_s (needbits 16 m) (fun s => set_i_flags s (s32 (m_hold (needbits 16 m)))))));
      reflexivity. }
  set (m1 := needbits 16 m) in *. clearbody m1.
  pose proof (mw_hold _ W1) as RH.
  apply semax_seq' with (P' := loop_state F (upd_s m1 (fun s => set_i_flags s (s32 (m_hold m1))))).
  { clear EB1 EB2 EOK HY HB1 HB2. rewrite !loop_state_hsplit. unfold loop_state_h.
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
  clearbody m2. clear HY.
  destruct (Z.eq_dec (Z.land fl 255) 8) as [C1 | C1].
  2: { apply semax_seq with (Q := FF); [ | apply semax_ff].
       rewrite !loop_state_hsplit. unfold loop_state_h. rewrite Hfl.
       abbreviate_semax.
       forward.
       forward_if.
       - unfold abbreviate in POSTCONDITION. subst POSTCONDITION.
         eapply semax_pre; [ | apply (HB1 m2 m); [reflexivity | exact (EB1 C1)]].
         rewrite loop_state_hsplit. unfold loop_state_h. rewrite Hfl. entailer!.
       - exfalso. apply C1.
         match goal with H: Int.and _ _ = _ |- _ => eapply hkf_and_eq; [rep_lia | rep_lia | exact H] end. }
  apply semax_seq with (Q := loop_state F m2).
  { rewrite !loop_state_hsplit. unfold loop_state_h. rewrite Hfl.
    abbreviate_semax.
    forward.
    forward_if.
    - exfalso. apply H1. rewrite hk_and_repr, C1. reflexivity.
    - cbv [switch_ret_assert case_post2 RA_normal]. forward. entailer!. }
  destruct (Z.eq_dec (Z.land fl 57344) 0) as [C2 | C2].
  2: { apply semax_seq with (Q := FF); [ | apply semax_ff].
       rewrite !loop_state_hsplit. unfold loop_state_h. rewrite Hfl.
       abbreviate_semax.
       forward.
       forward_if.
       - unfold abbreviate in POSTCONDITION. subst POSTCONDITION.
         eapply semax_pre; [ | apply (HB2 m2 m); [reflexivity | exact (EB2 C1 C2)]].
         rewrite loop_state_hsplit. unfold loop_state_h. rewrite Hfl. entailer!.
       - exfalso. apply C2.
         match goal with H: Int.and _ _ = _ |- _ => apply Z.eqb_eq; apply (hk_flagbit0 _ _ H); rep_lia end. }
  apply semax_seq with (Q := loop_state F m2).
  { rewrite !loop_state_hsplit. unfold loop_state_h. rewrite Hfl.
    abbreviate_semax.
    forward.
    forward_if.
    - exfalso. match goal with H: Int.and _ _ <> _ |- _ => apply H end. rewrite hk_and_repr, C2. reflexivity.
    - cbv [switch_ret_assert case_post2 RA_normal]. forward. entailer!. }
  apply semax_seq' with (P' := loop_state F (text_h m2)).
  { clear EB1 EB2 EOK HB1 HB2. rewrite !loop_state_hsplit. unfold text_h.
    destruct (i_head (m_s m2)) eqn:Hh.
    - unfold loop_state_h, head_part. mnorm_goal. rewrite Hh. unfold head_rep.
      abbreviate_semax. Intros.
      forward.
      assert_PROP (isptr (f_headp F)) by entailer!.
      forward_if.
      { forward. forward. entailer!. rewrite hkf_text by exact (mw_hold _ W2'). apply derives_refl. }
      { exfalso. destruct (f_headp F); try contradiction; discriminate. }
    - unfold loop_state_h, head_part. rewrite Hh.
      abbreviate_semax.
      forward.
      forward_if.
      { discriminate. }
      { forward. entailer!. } }
  pose proof (EOK C1 C2) as E. clear EOK EB1 EB2 HB1 HB2.
  assert (Ehold: m_hold (text_h m2) = m_hold m1) by (unfold text_h; destruct (i_head (m_s m2)); exact Hh2).
  assert (HM3: m_mode (text_h m2) = FLAGS) by (unfold text_h; destruct (i_head (m_s m2)); exact HM2).
  assert (HL3: m_leave (text_h m2) = 0) by (unfold text_h; destruct (i_head (m_s m2)); exact HL2).
  assert (K3: hkey (text_h m2) = hkey m) by (unfold text_h; destruct (i_head (m_s m2)); exact K2).
  assert (W3: mwf (text_h m2)).
  { unfold text_h. destruct (i_head (m_s m2)); [ | exact W2'].
    apply mwf_upd_h; [exact W2' | ]. apply hwf_set_text; [apply (mw_h _ W2') | ].
    pose proof (hk_land_range (Z.shiftr (m_hold m2) 8) 1 ltac:(lia)). unfold srange; rep_lia. }
  rewrite <- Ehold in E.
  set (m3 := text_h m2) in *. clearbody m3. clear Ehold.
  apply semax_seq' with (P' := loop_state F (crc_if m3 (hbytes2 (m_hold m3)))).
  { exact (semax_crcblock_FLAGS F m3 FOK W3). }
  apply semax_seq' with (P' := loop_state F (initbits (crc_if m3 (hbytes2 (m_hold m3))))).
  { apply semax_initbits5. }
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
  eapply ConseqFacts.semax_post''; [ | apply semax_store_mode5].
  unfold fall_postT5. Exists (set_mode (initbits (crc_if m3 (hbytes2 (m_hold m3)))) TIME).
  apply andp_right; [ | apply andp_left2; apply derives_refl].
  apply prop_right. split.
  { etransitivity; [exact E | symmetry;
      exact (stepf2_TIME (f_flush F) lenfix_list distfix_list (set_mode (initbits (crc_if m3 (hbytes2 (m_hold m3)))) TIME) eq_refl)]. }
  split; [reflexivity | ]. split; [exact HL4 | ]. split; [exact W4 | ].
  split; [exact (hkey_hd_ok F m _ K4 HD) | exact (hkey_hdr_tok F m _ K4)].
Qed.
