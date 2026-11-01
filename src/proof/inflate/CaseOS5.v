(* inflate(), case OS (index 3) in Delta_cases5: NEEDBITS(16); head->xflags = hold & 0xff, head->os = hold >> 8;
   CRC2; INITBITS; state->mode = EXLEN; falls into EXLEN *)
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

Definition os_h (m: mst) : mst :=
  if i_head (m_s m) then
    upd_h m (fun h => set_h_os (set_h_xflags h (Z.land (m_hold m) 255)) (s32 (Z.shiftr (m_hold m) 8)))
  else m.

Lemma hk_repr_s32: forall x, Int.repr (s32 x) = Int.repr x.
Proof.
  intros x. apply Int.eqm_samerepr. unfold Int.eqm, s32.
  change Int.modulus with (2 ^ 32).
  pose proof (Z.mod_pos_bound x (2 ^ 32) ltac:(lia)).
  destruct (Z.ltb_spec (x mod 2 ^ 32) (2 ^ 31)).
  - exists (- (x / 2 ^ 32)). pose proof (Z.div_mod x (2 ^ 32) ltac:(lia)). lia.
  - exists (- (x / 2 ^ 32) - 1). pose proof (Z.div_mod x (2 ^ 32) ltac:(lia)). lia.
Qed.

Lemma hk_land255: forall h, lrange h ->
  Int.repr (Int64.Z_mod_modulus (Z.land (Int64.Z_mod_modulus h) 255)) = Int.repr (Z.land h 255).
Proof.
  intros h R. change (Int64.Z_mod_modulus h) with (Int64.unsigned (Int64.repr h)). unfold lrange in R. rewrite Int64.unsigned_repr by rep_lia.
  rewrite Int64.Z_mod_modulus_eq. pose proof (hk_land_range h 255 ltac:(lia)).
  rewrite Z.mod_small; [reflexivity | ]. unfold Int64.modulus, Int64.wordsize, Wordsize_64.wordsize.
  change (two_power_nat 64) with (Int64.max_unsigned + 1). rep_lia.
Qed.

Lemma hk_shr8: forall h, lrange h ->
  Int.repr (Int64.Z_mod_modulus (Z.shiftr (Int64.Z_mod_modulus h) 8)) = Int.repr (s32 (Z.shiftr h 8)).
Proof.
  intros h R. change (Int64.Z_mod_modulus h) with (Int64.unsigned (Int64.repr h)). unfold lrange in R. rewrite Int64.unsigned_repr by rep_lia.
  rewrite Int64.Z_mod_modulus_eq. rewrite hk_repr_s32.
  pose proof (Zshiftr_range h 8 R ltac:(lia)).
  rewrite Z.mod_small; [reflexivity | ]. unfold Int64.modulus, Int64.wordsize, Wordsize_64.wordsize.
  change (two_power_nat 64) with (Int64.max_unsigned + 1). rep_lia.
Qed.

Lemma case_OS5 {Espec: OracleKind} (F: frame) : frame_ok5 F -> case_okT5 F EXLEN 4 -> case_okT5 F OS 3.
Proof.
  intros [FOK _] HY m HM HL [W W2] HD. pose proof FOK as (HWS & HWH & HRG & HRT).
  apply (case_fallthroughT5 F m EXLEN 3); [lia | exact HY | ].
  apply body_frameT5.
  case_body_stmt.
  eapply (semax_needbits_seq_r5 F m m 16);
    [ apply semax_needbits_OS5; auto; lia | auto | lia | reflexivity
    | intro E; rewrite (stepf2_OS _ _ _ m HM); unfold c_OS2; rewrite E; reflexivity | ].
  apply semax_extract_prop; intros HL0.
  pose proof (mwf_needbits 16 m W ltac:(lia)) as W1.
  assert (E: stepf2 (f_flush F) lenfix_list distfix_list m =
             c_EXLEN2 (set_mode (initbits (crc_if (os_h (needbits 16 m)) (hbytes2 (m_hold (needbits 16 m))))) EXLEN)).
  { rewrite (stepf2_OS _ _ _ m HM). unfold c_OS2. rewrite HL0. cbv zeta.
    unfold os_h. destruct (i_head (m_s (needbits 16 m))); reflexivity. }
  assert (HM1: m_mode (needbits 16 m) = OS) by (rewrite hk_needbits_mode; exact HM).
  pose proof (hkey_needbits 16 m) as K1.
  set (m1 := needbits 16 m) in *. clearbody m1.
  apply semax_seq' with (P' := loop_state F (os_h m1)).
  { clear E HY. pose proof (mw_hold _ W1) as RH. rewrite !loop_state_hsplit. unfold os_h.
    destruct (i_head (m_s m1)) eqn:Hh.
    - unfold loop_state_h, head_part. mnorm_goal. rewrite Hh. unfold head_rep.
      abbreviate_semax. Intros.
      forward.
      assert_PROP (isptr (f_headp F)) by entailer!.
      forward_if.
      { forward. forward. forward. forward. entailer!.
        rewrite hk_land255, hk_shr8 by exact RH. apply derives_refl. }
      { exfalso. destruct (f_headp F); try contradiction; discriminate. }
    - unfold loop_state_h, head_part. rewrite Hh.
      abbreviate_semax.
      forward.
      forward_if.
      { discriminate. }
      { forward. entailer!. } }
  assert (Ehold: m_hold (os_h m1) = m_hold m1) by (unfold os_h; destruct (i_head (m_s m1)); reflexivity).
  assert (HM2: m_mode (os_h m1) = OS) by (unfold os_h; destruct (i_head (m_s m1)); exact HM1).
  assert (HL2: m_leave (os_h m1) = 0) by (unfold os_h; destruct (i_head (m_s m1)); exact HL0).
  assert (K2: hkey (os_h m1) = hkey m) by (unfold os_h; destruct (i_head (m_s m1)); exact K1).
  assert (W2': mwf (os_h m1)).
  { unfold os_h. destruct (i_head (m_s m1)); [ | exact W1].
    apply mwf_upd_h; [exact W1 | ]. apply hwf_set_xflags_os; [apply (mw_h _ W1) | | apply hk_s32_range].
    pose proof (hk_land_range (m_hold m1) 255 ltac:(lia)). unfold srange; rep_lia. }
  rewrite <- Ehold in E.
  set (m2 := os_h m1) in *. clearbody m2. clear Ehold.
  apply semax_seq' with (P' := loop_state F (crc_if m2 (hbytes2 (m_hold m2)))).
  { exact (semax_crcblock_OS F m2 FOK W2'). }
  apply semax_seq' with (P' := loop_state F (initbits (crc_if m2 (hbytes2 (m_hold m2))))).
  { apply semax_initbits5. }
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
  eapply ConseqFacts.semax_post''; [ | apply semax_store_mode5].
  unfold fall_postT5. Exists (set_mode (initbits (crc_if m2 (hbytes2 (m_hold m2)))) EXLEN).
  apply andp_right; [ | apply andp_left2; apply derives_refl].
  apply prop_right. split.
  { etransitivity; [exact E | symmetry; exact (stepf2_EXLEN (f_flush F) lenfix_list distfix_list (set_mode (initbits (crc_if m2 (hbytes2 (m_hold m2)))) EXLEN) eq_refl)]. }
  split; [reflexivity | ]. split; [exact HL3 | ]. split; [exact W3 | ].
  split; [exact (hkey_hd_ok F m _ K3 HD) | exact (hkey_hdr_tok F m _ K3)].
Qed.
