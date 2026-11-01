(* inflate(), case EXLEN (index 4) in Delta_cases5: NEEDBITS(16), state->length, head->extra_len, CRC2, INITBITS
   (or head->extra = Z_NULL without FEXTRA); falls into EXTRA (port of the v3 proof) *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.ExKit5.
Require Import Zlib.proof.inflate.MwfLemmas.
Require Import Zlib.proof.inflate.Steps2.
Require Import Zlib.proof.inflate.NeedKit5.
Require Import Zlib.proof.inflate.NeedBits1_5.
Require Import Zlib.proof.inflate.ExHdrCrc5.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Definition exlen_mid (F: frame) (m: mst) : environ -> mpred :=
  EX m4: mst,
    !! (stepf2 (f_flush F) lenfix_list distfix_list m =
        stepf2 (f_flush F) lenfix_list distfix_list (set_mode m4 EXTRA) /\
        mwf3 (set_mode m4 EXTRA) /\ m_leave m4 = 0 /\ hd_ok F m4 /\ hdr_tok F m4 = hdr_tok F m) && loop_state F m4.

Lemma and_repr_zero: forall x c, 0 <= c <= Int.max_unsigned ->
  Int.and (Int.repr x) (Int.repr c) = Int.zero -> Z.land x c = 0.
Proof.
  intros x c Hc H. apply (f_equal Int.unsigned) in H. unfold Int.and in H.
  rewrite (Int.unsigned_repr c) in H by lia.
  rewrite land_repr in H by rep_lia.
  rewrite Int.unsigned_repr_eq in H. change Int.modulus with (2 ^ 32) in H.
  assert (R: Z.land x c = Z.land x c mod 2 ^ 32).
  { rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc. rewrite (Z.land_ones c 32) by lia.
    rewrite Z.mod_small by rep_lia. reflexivity. }
  rewrite <- R in H. exact H.
Qed.

Lemma land4: forall x, Z.land x 4 = 0 \/ Z.land x 4 = 4.
Proof.
  intros x. assert (E: Z.land x 4 = Z.land (x mod 8) 4).
  { change 8 with (2 ^ 3). rewrite <- (Z.land_ones x 3) by lia. rewrite <- Z.land_assoc. reflexivity. }
  rewrite E. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as B.
  destruct (x mod 8) as [ | k | k]; try lia; [left; reflexivity | ].
  assert (Zpos k = 1 \/ Zpos k = 2 \/ Zpos k = 3 \/ Zpos k = 4 \/ Zpos k = 5 \/ Zpos k = 6 \/ Zpos k = 7) as K by lia.
  destruct K as [K|[K|[K|[K|[K|[K|K]]]]]]; rewrite K; [left|left|left|right|right|right|right]; reflexivity.
Qed.

Lemma and_repr_nz: forall x c, 0 <= c <= Int.max_unsigned ->
  Int.and (Int.repr x) (Int.repr c) <> Int.zero -> Z.land x c <> 0.
Proof.
  intros x c Hc H E. apply H. unfold Int.and. rewrite (Int.unsigned_repr c) by lia.
  rewrite land_repr by rep_lia. rewrite E. reflexivity.
Qed.

(* the statements of EXLEN after NEEDBITS(16) *)
Definition exlen_rest : statement := ltac:(
  let c := eval cbv beta iota zeta delta [case_body inflate_LS find_switch f_inflate fn_body ls_drop] in (case_body 4) in
  match c with Ssequence (Ssequence _ (Sifthenelse _ (Ssequence _ ?r) _)) _ => exact r end).

Definition exlen_A : statement := ltac:(let c := eval cbv delta [exlen_rest] in exlen_rest in
  match c with Ssequence ?a (Ssequence _ (Ssequence _ _)) => exact a end).
Definition exlen_B : statement := ltac:(let c := eval cbv delta [exlen_rest] in exlen_rest in
  match c with Ssequence _ (Ssequence ?b (Ssequence _ _)) => exact b end).
Definition exlen_C : statement := ltac:(let c := eval cbv delta [exlen_rest] in exlen_rest in
  match c with Ssequence _ (Ssequence _ (Ssequence ?c _)) => exact c end).
Definition exlen_D : statement := ltac:(let c := eval cbv delta [exlen_rest] in exlen_rest in
  match c with Ssequence _ (Ssequence _ (Ssequence _ ?d)) => exact d end).

Lemma exlen_rest_eq: exlen_rest = Ssequence exlen_A (Ssequence exlen_B (Ssequence exlen_C exlen_D)).
Proof. reflexivity. Qed.

Definition ex_m2 (m1: mst) : mst := upd_s m1 (fun s => set_i_length s (u32 (m_hold m1))).
Definition ex_m3 (m1: mst) : mst :=
  if i_head (m_s m1) then upd_h (ex_m2 m1) (fun h => set_h_extra_len h (u32 (m_hold m1))) else ex_m2 m1.

Lemma exlen_A_ok {Espec: OracleKind} (F: frame) (m1: mst) : mwf m1 ->
  semax Delta_cases5 (loop_state F m1) exlen_A (normal_ret_assert (loop_state F (ex_m2 m1))).
Proof.
  intros W1. unfold exlen_A, ex_m2.
  rewrite loop_state_ex. unfold ex_state. abbreviate_semax.
  forward.
  rewrite loop_state_ex. unfold ex_state. x_simpl.
  entailer!. cbn [i_length m_s upd_s set_m_s set_i_length].
  pose proof (mw_hold _ W1) as HH. unfold lrange in HH.
  rewrite repr_u32, Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia. cancel.
Qed.

Lemma exlen_B_ok {Espec: OracleKind} (F: frame) (m1: mst) : frame_ok F -> mwf m1 ->
  semax Delta_cases5 (loop_state F (ex_m2 m1)) exlen_B (normal_ret_assert (loop_state F (ex_m3 m1))).
Proof.
  intros Hok W1. pose proof Hok as (HS1 & HS2 & HS3 & HS4).
  pose proof (mw_hold _ W1) as HH. unfold lrange in HH.
  unfold exlen_B, ex_m3, ex_m2.
  rewrite loop_state_ex. unfold ex_state. x_simpl. xp_simpl.
  destruct (i_head (m_s m1)) eqn:Eh.
  - rewrite (head_part_on F m1 Eh). unfold head_rep. Intros.
    abbreviate_semax.
    forward.
    forward_if.
    { forward. forward.
      rewrite loop_state_ex. unfold ex_state.
      rewrite (head_part_upd_h F (upd_s m1 (fun s => set_i_length s (u32 (m_hold m1)))) _ Eh). x_simpl. xp_simpl.
      rewrite ?Eh. unfold head_rep.
      xp_simpl. rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia. rewrite !repr_u32. rewrite Eh.
      entailer!. }
    { assert_PROP (field_compatible t_head [] (f_headp F)) as FC by entailer!.
      exfalso. destruct FC as [P _]. match goal with E: _ = nullval |- _ => rewrite E in P end. exact P. }
  - abbreviate_semax.
    forward.
    forward_if.
    { exfalso. match goal with E: false = true |- _ => discriminate E end. }
    { forward. rewrite loop_state_ex. unfold ex_state. x_simpl. xp_simpl. rewrite Eh.
      entailer!. }
Qed.

Lemma exlen_C_eq: exlen_C = crcblock _t'407 _t'408 _t'24 (crc2_stmt _t'406 _t'23).
Proof. reflexivity. Qed.

Lemma exlen_C_ok {Espec: OracleKind} (F: frame) (m3: mst) : frame_ok F -> mwf m3 ->
  semax Delta_cases5 (loop_state F m3) exlen_C
    (normal_ret_assert (loop_state F (crc_if m3 (hbytes2 (m_hold m3))))).
Proof. intros FOK W. rewrite exlen_C_eq. apply semax_crcblock_EXLEN; auto. Qed.

Lemma mwf_ex_m2: forall m1, mwf m1 -> m_mode m1 = EXLEN -> mwf (ex_m2 m1).
Proof.
  intros m1 W HM. pose proof (u32_range (m_hold m1)) as U. unfold ex_m2.
  destruct W as [MD S H]; constructor; auto; cbn [upd_s set_m_s m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits
    m_in m_out m_ret m_leave m_adler m_tin m_tout m_snx m_sow m_mode] in *; auto.
  - apply modewf_hdr. left. exact HM.
  - destruct S; constructor; auto.
Qed.

Lemma mwf_ex_m3: forall m1, mwf m1 -> m_mode m1 = EXLEN -> mwf (ex_m3 m1).
Proof.
  intros m1 W HM. pose proof (u32_range (m_hold m1)) as U. pose proof (mwf_ex_m2 m1 W HM) as W2.
  unfold ex_m3. destruct (i_head (m_s m1)); [ | exact W2].
  apply mwf_upd_h; [exact W2 | ]. cbn. destruct (mw_h _ W); constructor; auto.
Qed.

Lemma exlen_D_ok {Espec: OracleKind} (F: frame) (m: mst) :
  semax Delta_cases5 (loop_state F m) exlen_D (normal_ret_assert (loop_state F (initbits m))).
Proof.
  unfold exlen_D. apply semax_dowhile0. unfold loop_state. abbreviate_semax.
  change (mem_rep F (initbits m)) with (mem_rep F m).
  forward. forward. entailer!. apply derives_refl.
Qed.

Lemma exlen_rest_ok {Espec: OracleKind} (F: frame) (m1: mst) :
  frame_ok F -> mwf m1 -> m_mode m1 = EXLEN -> m_leave m1 = 0 ->
  semax Delta_cases5 (loop_state F m1) exlen_rest (normal_ret_assert (loop_state F (exlen_fin m1))).
Proof.
  intros Hok W1 HM1 HL1.
  rewrite exlen_rest_eq.
  eapply semax_seq'; [apply exlen_A_ok; exact W1 | ].
  eapply semax_seq'; [apply exlen_B_ok; auto | ].
  assert (E: exlen_fin m1 = initbits (crc_if (ex_m3 m1) (hbytes2 (m_hold (ex_m3 m1))))).
  { unfold exlen_fin, ex_m3, ex_m2. cbv zeta.
    change (i_head (m_s (upd_s m1 (fun s => set_i_length s (u32 (m_hold m1)))))) with (i_head (m_s m1)).
    destruct (i_head (m_s m1)); reflexivity. }
  rewrite E.
  eapply semax_seq'; [apply exlen_C_ok; auto; apply mwf_ex_m3; auto | apply exlen_D_ok].
Qed.

Lemma exlen_skip_hd: forall F m, hd_ok F m -> hd_ok F (exlen_skip m) /\ hdr_tok F (exlen_skip m) = hdr_tok F m.
Proof.
  intros F m HD. unfold exlen_skip. destruct (i_head (m_s m)) eqn:Eh; [ | split; [exact HD | reflexivity]].
  split; [ | reflexivity].
  unfold hd_ok in *. cbn [upd_h set_m_h m_s m_h set_h_xp h_xp h_np h_cp]. intros E.
  destruct (HD E) as (A & B & C). split; [discriminate | split; auto].
Qed.

Lemma exlen_fin_hkey: forall m1, hkey (exlen_fin m1) = hkey m1.
Proof.
  intros m1. unfold exlen_fin. cbv zeta. rewrite hkey_initbits, hkey_crc_if.
  change (i_head (m_s (upd_s m1 (fun s => set_i_length s (u32 (m_hold m1)))))) with (i_head (m_s m1)).
  destruct (i_head (m_s m1)); reflexivity.
Qed.

Lemma case_EXLEN5 {Espec: OracleKind} (F: frame) : frame_ok5 F -> case_okT5 F EXTRA 5 -> case_okT5 F EXLEN 4.
Proof.
  intros [Hok _] HY m HM HL [W W2] HD.
  pose proof Hok as (HS1 & HS2 & HS3 & HS4).
  apply (case_fallthroughT5 F m EXTRA 4); [lia | exact HY | ].
  apply body_frameT5.
  case_body_stmt.
  apply semax_seq with (Q := exlen_mid F m).
  2: { unfold exlen_mid. Intros m4. apply semax_extract_prop. intros (E & W4 & L4 & HD4 & HT4).
       eapply ConseqFacts.semax_post''; [ | apply semax_store_mode5].
       unfold fall_postT5. Exists (set_mode m4 EXTRA).
       apply andp_right; [ | apply andp_left2; apply derives_refl].
       apply prop_right. split; [exact E | ]. split; [reflexivity | ]. split; [exact L4 | ].
       split; [exact W4 | ]. split; [exact HD4 | exact HT4]. }
  destruct (Z.eqb_spec (Z.land (i_flags (m_s m)) 1024) 0) as [Hf | Hf].
  - (* no FEXTRA *)
    pose proof (step_exlen_skip (f_flush F) m HM Hf) as E.
    destruct (mwf3_exlen_skip m W HM) as [W4 L4].
    destruct (exlen_skip_hd F m HD) as [HD4 HT4].
    rewrite loop_state_ex. unfold ex_state.
    abbreviate_semax.
    forward.
    forward_if.
    { exfalso. apply H1'. rewrite (Int.unsigned_repr 1024) by rep_lia. rewrite land_repr by lia. exact Hf. }
    destruct (i_head (m_s m)) eqn:Eh.
    + assert (X: exlen_skip m = upd_h m (fun h => set_h_xp h false)) by (unfold exlen_skip; rewrite Eh; reflexivity).
      rewrite (head_part_on F m Eh). unfold head_rep. Intros.
      forward.
      forward_if.
      { forward. forward.
        unfold exlen_mid. Exists (exlen_skip m).
        apply andp_right; [apply prop_right; split; [exact E | split; [exact W4 | split; [exact (eq_trans L4 HL) | split; [exact HD4 | exact HT4]]]] | ].
        rewrite X, loop_state_ex. unfold ex_state.
        x_simpl. rewrite (head_part_upd_h F m _ Eh). unfold head_rep.
        entailer!. cbn. rewrite Eh. cancel. }
      { assert_PROP (field_compatible t_head [] (f_headp F)) by entailer!.
        exfalso. destruct H3 as [P _]. rewrite H2 in P. exact P. }
    + rewrite (head_part_off F m Eh).
      forward.
      forward_if.
      { exfalso. discriminate H2. }
      { forward. unfold exlen_mid. Exists (exlen_skip m).
        apply andp_right; [apply prop_right; split; [exact E | split; [exact W4 | split; [exact (eq_trans L4 HL) | split; [exact HD4 | exact HT4]]]] | ].
        rewrite loop_state_ex. unfold ex_state. unfold exlen_skip. rewrite Eh.
        rewrite (head_part_off F m Eh).
        entailer!. rewrite Eh. cancel. }
  - (* FEXTRA *)
    destruct (step_exlen_set (f_flush F) m HM Hf) as [EL E0].
    rewrite loop_state_ex. unfold ex_state.
    abbreviate_semax.
    forward.
    forward_if.
    2: { exfalso. apply Hf. apply and_repr_zero; [rep_lia | exact H1]. }
    apply semax_pre with (P' := loop_state F m).
    { rewrite loop_state_ex. unfold ex_state. entailer!. }
    eapply (semax_needbits_seq5 F m m 16).
    + apply semax_needbits_EXLEN5; auto; lia.
    + exact W.
    + lia.
    + reflexivity.
    + exact EL.
    + apply semax_extract_prop. intros HL1.
      specialize (E0 HL1).
      pose proof (mwf_needbits 16 m W ltac:(lia)) as W1.
      destruct (needbits_sh 16 m) as [S1 H1s].
      assert (HM1: m_mode (needbits 16 m) = EXLEN) by (unfold m_mode; rewrite S1; exact HM).
      destruct (mwf3_exlen_fin _ W1 HM1) as [W4 L4].
      assert (K4: hkey (exlen_fin (needbits 16 m)) = hkey m) by (rewrite exlen_fin_hkey; apply hkey_needbits).
      pose proof (hkey_hd_ok F m _ K4 HD) as HD4. pose proof (hkey_hdr_tok F m _ K4) as HT4.
      set (m1 := needbits 16 m) in *. clearbody m1.
      eapply ConseqFacts.semax_post''; [ | apply (exlen_rest_ok F m1 Hok W1 HM1 HL1) ].
      unfold POSTCONDITION, abbreviate. simpl RA_normal.
      unfold exlen_mid. Exists (exlen_fin m1).
      apply andp_right; [apply prop_right; split; [exact E0 | split; [exact W4 | split; [exact (eq_trans L4 HL1) | split; [exact HD4 | exact HT4]]]] | ].
      apply andp_left2. apply derives_refl.
Qed.
