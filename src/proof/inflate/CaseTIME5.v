(* inflate(), case TIME (index 2) in Delta_cases5: NEEDBITS(32); head->time = hold; CRC4; INITBITS;
   state->mode = OS; falls into OS *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.HdrSame5.
Require Import Zlib.proof.inflate.MwfLemmas.
Require Import Zlib.proof.inflate.Steps2.
Require Import Zlib.proof.inflate.NeedKit5.
Require Import Zlib.proof.inflate.NeedBits1_5.
Require Import Zlib.proof.inflate.HdrKit5.
Require Import Zlib.proof.inflate.HdrCrc5.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Definition time_h (m: mst) : mst :=
  if i_head (m_s m) then upd_h m (fun h => set_h_time h (m_hold m)) else m.

Lemma case_TIME5 {Espec: OracleKind} (F: frame) : frame_ok5 F -> case_okT5 F OS 3 -> case_okT5 F TIME 2.
Proof.
  intros [FOK _] HY m HM HL [W W2] HD. pose proof FOK as (HWS & HWH & HRG & HRT).
  apply (case_fallthroughT5 F m OS 2); [lia | exact HY | ].
  apply body_frameT5.
  case_body_stmt.
  eapply (semax_needbits_seq_r5 F m m 32);
    [ apply semax_needbits_TIME5; auto; lia | auto | lia | reflexivity
    | intro E; rewrite (stepf2_TIME _ _ _ m HM); unfold c_TIME2; rewrite E; reflexivity | ].
  apply semax_extract_prop; intros HL0.
  pose proof (mwf_needbits 32 m W ltac:(lia)) as W1.
  assert (E: stepf2 (f_flush F) lenfix_list distfix_list m =
             c_OS2 (set_mode (initbits (crc_if (time_h (needbits 32 m)) (hbytes4 (m_hold (needbits 32 m))))) OS)).
  { rewrite (stepf2_TIME _ _ _ m HM). unfold c_TIME2. rewrite HL0. cbv zeta.
    unfold time_h. destruct (i_head (m_s (needbits 32 m))); reflexivity. }
  assert (HM1: m_mode (needbits 32 m) = TIME) by (rewrite hk_needbits_mode; exact HM).
  pose proof (hkey_needbits 32 m) as K1.
  set (m1 := needbits 32 m) in *. clearbody m1.
  apply semax_seq' with (P' := loop_state F (time_h m1)).
  { clear E HY. rewrite !loop_state_hsplit. unfold time_h.
    destruct (i_head (m_s m1)) eqn:Hh.
    - unfold loop_state_h, head_part. mnorm_goal. rewrite Hh. unfold head_rep.
      abbreviate_semax. Intros.
      forward.
      assert_PROP (isptr (f_headp F)) by entailer!.
      forward_if.
      { forward. forward. entailer!. apply derives_refl. }
      { exfalso. destruct (f_headp F); try contradiction; discriminate. }
    - unfold loop_state_h, head_part. rewrite Hh.
      abbreviate_semax.
      forward.
      forward_if.
      { discriminate. }
      { forward. entailer!. } }
  assert (Ehold: m_hold (time_h m1) = m_hold m1) by (unfold time_h; destruct (i_head (m_s m1)); reflexivity).
  assert (HM2: m_mode (time_h m1) = TIME) by (unfold time_h; destruct (i_head (m_s m1)); exact HM1).
  assert (HL2: m_leave (time_h m1) = 0) by (unfold time_h; destruct (i_head (m_s m1)); exact HL0).
  assert (K2: hkey (time_h m1) = hkey m) by (unfold time_h; destruct (i_head (m_s m1)); exact K1).
  assert (W2': mwf (time_h m1)).
  { unfold time_h. destruct (i_head (m_s m1)); [ | exact W1].
    apply mwf_upd_h; [exact W1 | ]. apply hwf_set_time; [apply (mw_h _ W1) | apply (mw_hold _ W1)]. }
  rewrite <- Ehold in E.
  set (m2 := time_h m1) in *. clearbody m2. clear Ehold.
  apply semax_seq' with (P' := loop_state F (crc_if m2 (hbytes4 (m_hold m2)))).
  { exact (semax_crcblock_TIME F m2 FOK W2'). }
  apply semax_seq' with (P' := loop_state F (initbits (crc_if m2 (hbytes4 (m_hold m2))))).
  { apply semax_initbits5. }
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
  eapply ConseqFacts.semax_post''; [ | apply semax_store_mode5].
  unfold fall_postT5. Exists (set_mode (initbits (crc_if m2 (hbytes4 (m_hold m2)))) OS).
  apply andp_right; [ | apply andp_left2; apply derives_refl].
  apply prop_right. split.
  { etransitivity; [exact E | symmetry; exact (stepf2_OS (f_flush F) lenfix_list distfix_list (set_mode (initbits (crc_if m2 (hbytes4 (m_hold m2)))) OS) eq_refl)]. }
  split; [reflexivity | ]. split; [exact HL3 | ]. split; [exact W3 | ].
  split; [exact (hkey_hd_ok F m _ K3 HD) | exact (hkey_hdr_tok F m _ K3)].
Qed.
