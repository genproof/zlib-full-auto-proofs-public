"""Patches of docs/port-hl/cfg_rth9h.py, group ex (the cases EXLEN and EXTRA): see the configuration's header.

Without the header pass, the branches that leave are proved (src/proof/roundtrip/RTH9HExKit.v): EXLEN's
NEEDBITS(16) out of input, and EXTRA's copy that stops before the end of the extra field; both return in their
header mode with the partial header.  With calls of any uInt size the extra length read by EXLEN must be below
2^31 - 1 (InvW.hdrW in EXTRA): NEEDBITS(16) from a bit buffer of fewer than 16 bits leaves hold < 2^24
(za.inflate.ExHoldZ, as docs/port-za/inflate/cases_ex.py); EXTRA's copy count is bounded by that length."""

R = 'Zlib.proof.roundtrip.'

PATCHES = [
    # ---------------------------------------------------------------------------------------------------
    # EXLEN
    (R + 'RTHEXLEN6',
     'Require Import Zlib.proof.inflate.CaseEXLEN5.',
     'Require Import Zlib.proof.inflate.CaseEXLEN5.\n'
     'Require Import Zlib.proof.za.inflate.ExHoldZ.\n'
     'Require Import Zlib.proof.roundtrip.RTH9HExKit.'),
    (R + 'RTHEXLEN6',
     '  intros [Hok HF] HY m n HM HL [W W2] HD Eh HP.\n',
     '  intros [Hok HF] HY m HM HL [W W2] HD Eh.\n'),
    (R + 'RTHEXLEN6',
     'apply (case_fallthrough9v F m n IM.EXTRA 4); [lia | reflexivity | exact Hhm | exact HP | exact HY | ].',
     'apply (case_fallthrough9v F m IM.EXTRA 4); [lia | exact HY | ].'),
    # NEEDBITS(16) out of input: the switch is left in mode EXLEN with the header as it was
    (R + 'RTHEXLEN6',
     '    eapply (semax_needbits_seq6 F m 16 (hd6 F m)).\n'
     '    + apply semax_needbits_EXLEN5H; auto; lia.\n'
     '    + exact W.\n'
     '    + lia.\n'
     '    + intros L1. pose proof (hpass_brk _ _ _ _ Hhm HP (EL L1)) as L0. lia.\n',
     '    eapply (semax_needbits_seq9 F m m 16 (hd6 F m)).\n'
     '    + apply semax_needbits_EXLEN5H; auto; lia.\n'
     '    + exact W.\n'
     '    + lia.\n'
     '    + reflexivity.\n'
     '    + exact EL.\n'
     '    + apply hd6_hd9_needbits; exact Hhm.\n'),
    # the extra length read by NEEDBITS(16) from a bit buffer of hdrW is below 2^24
    (R + 'RTHEXLEN6',
     '      destruct (mwf39_exlen_fin _ W1 HM1) as [W4 L4].\n',
     '      assert (HB1: m_hold (needbits 16 m) < 2 ^ 24).\n'
     '      { destruct W2 as [_ [HX _]]. destruct (HX HM) as [HB0 HH0].\n'
     '        pose proof (mw9_hold _ W) as HO. pose proof (mw9_bits _ W) as B0.\n'
     '        pose proof (mw9_inp _ W) as I0. pose proof (mw9_nx _ W) as N0. unfold lrange in HO.\n'
     '        refine (proj2 (needbits16_hold_lt m _ _ _ _ _)); try lia; tauto. }\n'
     '      destruct (mwf39_exlen_fin _ W1 HM1 HB1) as [W4 L4].\n'),
    # without an extra field: the flag test is the reason why EXTRA does not need the length
    (R + 'RTHEXLEN6',
     '    destruct (mwf39_exlen_skip m W HM) as [W4 L4].\n',
     '    destruct (mwf39_exlen_skip m W HM Hf) as [W4 L4].\n'),

    # ---------------------------------------------------------------------------------------------------
    # EXTRA: the memcpy block (as round 1's docs/port-hl/cfg_rth8w.py)
    # EXTRA's copy count: len + copy <= extra_len (header invariant hinv6) does not wrap
    (R + 'RTHEXTRA6Mb',
     "pose proof (extra_n_range lv0 c (h_extra_max h) ltac:(lia) ltac:(lia) ltac:(rep_lia)) as [N1 N2].",
     "pose proof (extra_n_range8 lv0 c (h_extra_max h) ltac:(lia) ltac:(lia) ltac:(unfold urange in UXL; rep_lia))\n"
     "      as [N1 N2]."),
    # the test len + copy > extra_max on the unwrapped sum (lv0 + c <= extra_len <= Int.max_unsigned)
    (R + 'RTHEXTRA6Mb',
     "{ forward. forward. forward. rewrite (NE1 H0). entailer!. }\n    { forward. rewrite (NE2 ltac:(lia)). entailer!. }",
     "{ forward. forward. forward. unfold urange in UXL. rewrite Int.unsigned_repr in H0 by rep_lia.\n"
     "      rewrite (NE1 H0). entailer!. }\n"
     "    { forward. unfold urange in UXL.\n"
     "      match goal with Hq: context [Int.unsigned (Int.repr (lv0 + c))] |- _ =>\n"
     "        rewrite Int.unsigned_repr in Hq by rep_lia end.\n"
     "      rewrite (NE2 ltac:(lia)). entailer!. }"),
    # the copy: with an input of up to 2^32 - 1 bytes, copy = min(length, have) <= 2^31 - 1 comes from the length
    (R + 'RTHEXTRA6Cpy',
     '  c = Z.min (i_length (m_s m)) (m_have m) -> c <> 0 ->\n',
     '  c = Z.min (i_length (m_s m)) (m_have m) -> c <> 0 -> i_length (m_s m) <= Int.max_signed ->\n'),
    (R + 'RTHEXTRA6Cpy',
     '  intros FOK W HD Hh HM Hc Hn.\n',
     '  intros FOK W HD Hh HM Hc Hn HLM.\n'),

    # EXTRA's body
    (R + 'RTHEXTRA6',
     'Require Import Zlib.proof.roundtrip.RTHEXTRA6Cpy.',
     'Require Import Zlib.proof.roundtrip.RTHEXTRA6Cpy.\n'
     'Require Import Zlib.proof.roundtrip.RTH9HExKit.'),
    (R + 'RTHEXTRA6',
     'Lemma extra_body6 {Espec: OracleKind} (F: frame) (m: mst) (n: nat):\n',
     'Lemma extra_body6 {Espec: OracleKind} (F: frame) (m: mst):\n'),
    (R + 'RTHEXTRA6',
     '  hpass (f_flush F) (S n) m ->\n',
     ''),
    (R + 'RTHEXTRA6',
     '  intros [FOK FR] HM HL [W W3] HD Hh HP.\n',
     '  intros [FOK FR] HM HL [W W3] HD Hh.\n'),
    # the header invariant's bound on length (from hd6's hinv6) for mwf9_extra_upd (as round 1's docs/port-hl/cfg_rth8w.py)
    (R + 'RTHEXTRA6',
     '  pose proof (mwf9_extra_upd m W HM) as (WU & HMU & HLU).\n',
     '  apply (semax_pre (!! hinv6 (m_s m) (m_h m) && (loop_stateH F m * (fun _ => hdr_tok F m * hd6 F m)))).\n'
     '  { intros rho. simpl. apply andp_left2. apply andp_right; [ | apply derives_refl]. unfold hd6, head_rep6.\n'
     '    normalize. }\n'
     '  apply semax_extract_prop. intros HI6.\n'),
    # with an extra field the length is below 2^31 (hdrW)
    (R + 'RTHEXTRA6',
     '    rewrite (proj2 (Z.eqb_neq _ _) Hf) in SB, SF.\n',
     '    rewrite (proj2 (Z.eqb_neq _ _) Hf) in SB, SF.\n'
     '    assert (HLM: i_length (m_s m) <= Int.max_signed) by (destruct W3 as [_ [_ HX]]; exact (HX HM Hf)).\n'
     '    pose proof (mwf9_extra_upd m W HM HLM (fun _ X => proj1 (proj2 (proj2 HI6)) HM X)) as (WU & HMU & HLU).\n'),
    (R + 'RTHEXTRA6',
     'apply (semax_extra_cpy6 F m c FOK W HD Hh HM Hc Hn)',
     'apply (semax_extra_cpy6 F m c FOK W HD Hh HM Hc Hn HLM)'),
    # the copy stopped before the end of the field (state->length <> 0): the switch is left in mode EXTRA
    (R + 'RTHEXTRA6',
     '        assert (LZ: i_length (m_s (extra_upd m)) = 0).\n'
     '        { destruct (Z.eq_dec (i_length (m_s (extra_upd m))) 0) as [E | E]; [exact E | exfalso].\n'
     '          pose proof (hpass_brk _ n m _ HDM HP (SB E Hf)) as B. discriminate B. }\n'
     '        specialize (SF (or_introl LZ)).\n',
     ''),
    (R + 'RTHEXTRA6',
     '        -- exfalso. match goal with H: Int.repr _ <> Int.zero |- _ => apply H end. rewrite LZ. reflexivity.\n'
     '        -- forward. forward.\n',
     '        -- assert (LNZ: i_length (m_s m1) <> 0) by (intro E; rewrite E in *; contradiction).\n'
     '           forward. forward.\n'
     '           try (unfold abbreviate in POSTCONDITION; subst POSTCONDITION).\n'
     '           match goal with |- context [RA_break ?X] =>\n'
     '             replace (RA_break X) with (RA_normal (case_post9 F m) * lift0 (hdr_tok F m)) by reflexivity end.\n'
     '           eapply derives_trans; [ | apply (ex_brk_ok9 F m m1 (SB LNZ Hf) ltac:(rewrite HMU; reflexivity)) ].\n'
     '           unfold PPx, LLx, SLx6.\n'
     '           change (m_have (set_leave m1)) with (m_have m1). change (m_left (set_leave m1)) with (m_left m1).\n'
     '           cbn [set_leave set_m_leave m_leave m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret].\n'
     '           entailer!.\n'
     '        -- assert (LZ: i_length (m_s m1) = 0).\n'
     '           { match goal with H: Int.repr _ = Int.zero |- _ =>\n'
     '               apply (f_equal Int.unsigned) in H; rewrite Int.unsigned_repr in H by rep_lia; exact H end. }\n'
     '           specialize (SF (or_introl LZ)).\n'
     '           forward. forward.\n'),
    (R + 'RTHEXTRA6',
     '  intros FOK HY m n HM HL W HD Hh HP.\n'
     '  apply (case_fallthrough9v F m n IM.NAME 5); [lia | reflexivity | rewrite HM; reflexivity | exact HP | exact HY | ].\n'
     '  apply (extra_body6 F m n); auto.',
     '  intros FOK HY m HM HL W HD Hh.\n'
     '  apply (case_fallthrough9v F m IM.NAME 5); [lia | exact HY | ].\n'
     '  apply (extra_body6 F m); auto.'),
]
