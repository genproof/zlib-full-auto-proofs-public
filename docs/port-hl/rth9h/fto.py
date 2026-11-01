"""Patches of docs/port-hl/cfg_rth9h.py, group fto (the cases FLAGS, TIME, OS): see the configuration's header.

Round 1's cases assumed a call that passes the header (hpass); here every branch is proved, with the lemmas of
src/proof/roundtrip/RTH9HFtoKit.v:
- NEEDBITS out of input (FLAGS 16 bits, TIME 32, OS 16): RTH9HFtoKit.semax_leave9, the break in the same header
  mode with the partial header (needbits leaves the header alone);
- FLAGS's errors (method <> 8, flags & 0xe000): RTH9HFtoKit.semax_seq_bad9 with bad_brk9_method / bad_brk9_hflags,
  the break in mode BAD with the raw header (done = 0, from hd6's hinv6, and the buffer lengths, from bufok6);
- the fall-throughs FLAGS -> TIME -> OS -> EXLEN keep InvW.hdrW (RTH9HFtoKit.hdrW_initbits9: they end with
  INITBITS, at EXLEN bits = hold = 0)."""

M = 'Zlib.proof.roundtrip.RTHFTO6'


def _intro(md, i):
    """the case's statement without the header pass: case_fallthrough9v has no hpass premise"""
    return (M,
            '  intros [FOK _] HY m n HM HL [W W2] HD HH HP. pose proof FOK as (HWS & HWH & HRG & HRT).\n'
            '  apply (case_fallthrough9v F m n IM.%s %d); [lia | reflexivity | rewrite HM; reflexivity | exact HP '
            '| exact HY | ].' % (md, i),
            '  intros [FOK _] HY m HM HL [W W2] HD HH. pose proof FOK as (HWS & HWH & HRG & HRT).\n'
            '  apply (case_fallthrough9v F m IM.%s %d); [lia | exact HY | ].' % (md, i))


def _leave(n, md, c):
    """NEEDBITS(n) out of input: the case breaks (RTH9HFtoKit.semax_leave9); otherwise leave = 0"""
    old = ('  assert (HL0: m_leave (needbits %d m) = 0).\n'
           '  { pose proof (mw9_leave _ W1) as RL.\n'
           '    destruct (Z.eq_dec (m_leave (needbits %d m)) 1) as [E1 | E1]; [ | lia].\n'
           '    exfalso. destruct (hpass_step _ _ _ ltac:(rewrite HM; reflexivity) HP) as (m\' & Es & Hl\' & _).\n'
           '    rewrite (stepf2_%s _ _ _ m HM) in Es. unfold c_%s2 in Es. rewrite E1, Z.eqb_refl in Es.\n'
           '    injection Es as Es. subst m\'. lia. }' % (n, n, md, md))
    new = ('  destruct (Z.eq_dec (m_leave (needbits %d m)) 1) as [E1 | E1].\n'
           '  { case_body_stmt.\n'
           '    apply (semax_leave9 F m %d);\n'
           '      [apply semax_needbits_%s5H; auto; lia | exact E1 | rewrite HM; reflexivity | | reflexivity].\n'
           '    rewrite (stepf2_%s _ _ _ m HM). unfold c_%s2. rewrite E1, Z.eqb_refl. reflexivity. }\n'
           '  assert (HL0: m_leave (needbits %d m) = 0) by (pose proof (mw9_leave _ W1) as RL; lia).'
           % (n, n, c, md, md, n))
    return (M, old, new)


def _hdrw(md):
    """the fall-through into md keeps InvW.hdrW (it ends with INITBITS)"""
    return (M, '    - unfold FLAGS, %s, TYPEDO; lia. }' % md,
            '    - unfold FLAGS, %s, TYPEDO; lia.\n'
            '    - apply hdrW_initbits9. unfold %s, EXTRA; lia. }' % (md, md))


# FLAGS: the leave and the two errors are cases of the proof; the model's step in each of them
_FLAGS_STEP = (
    M,
    '''  destruct (hpass_step _ _ _ ltac:(rewrite HM; reflexivity) HP) as (m' & Es & Hl' & Hp').
  rewrite (stepf2_FLAGS _ _ _ m HM) in Es. unfold c_FLAGS2 in Es.
  destruct (needbits_f_sh 4 16 m) as [S1 H1]. change (needbits_f 4 16 m) with (needbits 16 m) in S1, H1.
  assert (HL0: m_leave (needbits 16 m) = 0).
  { pose proof (mw9_leave _ W1) as RL.
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
''',
    '''  destruct (needbits_f_sh 4 16 m) as [S1 H1]. change (needbits_f 4 16 m) with (needbits 16 m) in S1, H1.
  destruct (Z.eq_dec (m_leave (needbits 16 m)) 1) as [E1 | E1].
  { case_body_stmt.
    apply (semax_leave9 F m 16);
      [apply semax_needbits_FLAGS5H; auto; lia | exact E1 | rewrite HM; reflexivity | | reflexivity].
    rewrite (stepf2_FLAGS _ _ _ m HM). unfold c_FLAGS2. rewrite E1, Z.eqb_refl. reflexivity. }
  assert (HL0: m_leave (needbits 16 m) = 0) by (pose proof (mw9_leave _ W1) as RL; lia).
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
  assert (E: Z.land (s32 (m_hold (needbits 16 m))) 255 = 8 ->
    Z.land (s32 (m_hold (needbits 16 m))) 57344 = 0 ->
    stepf2 (f_flush F) lenfix_list distfix_list m =
    c_TIME2 (set_mode (initbits (crc_if
      (text_h (upd_s (needbits 16 m) (fun s => set_i_flags s (s32 (m_hold (needbits 16 m))))))
      (hbytes2 (m_hold (needbits 16 m))))) TIME)).
  { intros C1 C2. rewrite (stepf2_FLAGS _ _ _ m HM). unfold c_FLAGS2. rewrite HL0. cbv zeta.
''')

# the method check: BAD when the method is not 8
_FLAGS_C1 = (
    M,
    '''  clearbody m2. clear HY.
  eapply semax_seq_frame6 with (Q := loop_stateH F m2).
''',
    '''  clearbody m2. clear HY.
  destruct (Z.eq_dec (Z.land fl 255) 8) as [C1 | C1].
  2: { eapply (semax_seq_bad9 F m m2 M_method);
         [ | reflexivity | exact (EB1 C1) | apply hd6_hd9_raw; [exact Hmh2 | reflexivity]].
       rewrite (loop_state_hsplitH F m2). unfold loop_state_hH. rewrite Hfl.
       abbreviate_semax.
       forward.
       forward_if.
       - unfold abbreviate in POSTCONDITION. subst POSTCONDITION.
         eapply semax_pre; [ | apply (bad_brk9_method F m2 FOK)].
         rewrite loop_state_hsplitH. unfold loop_state_hH. rewrite Hfl. entailer!.
       - exfalso. apply C1.
         match goal with H: Int.and _ _ = _ |- _ => eapply hkf_and_eq; [rep_lia | rep_lia | exact H] end. }
  eapply semax_seq_frame6 with (Q := loop_stateH F m2).
''')

# the flags check: BAD when a reserved flag is set
_FLAGS_C2 = (
    M,
    '''    - forward. entailer!. }
  eapply semax_seq_frame6 with (Q := loop_stateH F m2).
''',
    '''    - forward. entailer!. }
  destruct (Z.eq_dec (Z.land fl 57344) 0) as [C2 | C2].
  2: { eapply (semax_seq_bad9 F m m2 M_hflags);
         [ | reflexivity | exact (EB2 C1 C2) | apply hd6_hd9_raw; [exact Hmh2 | reflexivity]].
       rewrite (loop_state_hsplitH F m2). unfold loop_state_hH. rewrite Hfl.
       abbreviate_semax.
       forward.
       forward_if.
       - unfold abbreviate in POSTCONDITION. subst POSTCONDITION.
         eapply semax_pre; [ | apply (bad_brk9_hflags F m2 FOK)].
         rewrite loop_state_hsplitH. unfold loop_state_hH. rewrite Hfl. entailer!.
       - exfalso. apply C2.
         match goal with H: Int.and _ _ = _ |- _ => apply Z.eqb_eq; apply (hk_flagbit0 _ _ H); rep_lia end. }
  specialize (E C1 C2).
  eapply semax_seq_frame6 with (Q := loop_stateH F m2).
''')

# the kit of these branches
_REQ = (M, 'Require Import Zlib.proof.crc32.Spec.',
        'Require Import Zlib.proof.crc32.Spec.\nRequire Import Zlib.proof.roundtrip.RTH9HFtoKit.')

# the source's comment: these branches are now proved
_DOC = (M, '''   head_rep6 and fold into the header of the next mode.  The branches that leave (short NEEDBITS) or go to BAD
   (FLAGS) contradict hpass. *)''', '''   head_rep6 and fold into the header of the next mode.  The branches that leave (short NEEDBITS) or go to BAD
   (FLAGS) break the switch: RTH9HFtoKit.v. *)''')

PATCHES = [
    _DOC, _REQ,
    _intro('OS', 2), _intro('EXLEN', 3), _intro('TIME', 1),
    _leave(32, 'TIME', 'TIME'), _leave(16, 'OS', 'OS'),
    _FLAGS_STEP, _FLAGS_C1, _FLAGS_C2,
    _hdrw('TIME'), _hdrw('OS'), _hdrw('EXLEN'),
]
