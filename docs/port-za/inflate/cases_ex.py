"""Patches of the inflate port, part cases, group ex: see docs/port-za/inflate/cases.py."""

PATCHES = [
    # mwf3 is now mwf /\ swf3 /\ hdrW: a header mode set from a header mode keeps hdrW only when the bit
    # buffer (EXLEN) or the extra length (EXTRA) is in range, a hypothesis (the lemma is not used by EXLEN
    # and EXTRA, which have their own lemmas in ExKit5)
    ('Zlib.proof.inflate.ExHdrKit5',
     '  mwf m -> HEAD <= m_mode m <= TYPEDO -> FLAGS <= md <= TYPEDO -> mwf3 (set_mode m md).\n'
     'Proof.\n'
     '  intros m md W HM Hmd. split.',
     '  mwf m -> HEAD <= m_mode m <= TYPEDO -> FLAGS <= md <= TYPEDO ->\n'
     '  Zlib.proof.inflate.InvW.hdrW (set_mode m md) -> mwf3 (set_mode m md).\n'
     'Proof.\n'
     '  intros m md W HM Hmd HW. split.'),
    ('Zlib.proof.inflate.ExHdrKit5',
     '  - constructor; cbn [set_mode upd_s set_m_s m_s set_i_mode i_mode];\n'
     '      unfold decode_mode, HEAD, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, FLAGS, TYPEDO in *; intros; lia.\n'
     'Qed.',
     '  - split; [ | exact HW]. constructor; cbn [set_mode upd_s set_m_s m_s set_i_mode i_mode];\n'
     '      unfold decode_mode, HEAD, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, FLAGS, TYPEDO in *; intros; lia.\n'
     'Qed.'),
]

# hdrW of the EXTRA machine after EXLEN read the extra length: u32 hold with hold < 2^24 (ExHoldZ)
_FIN_HDRW = ('unfold Zlib.proof.inflate.InvW.hdrW; cbn -[crc_val]; split; intros X; '
             '[exfalso; unfold EXLEN, EXTRA in X; lia | '
             'intros _; unfold u32; rewrite Z.mod_small by (unfold lrange in HO; lia); rep_lia]')
# hdrW of the EXTRA machine after EXLEN without an extra field: the length is not bounded, nor read
_SKIP_HDRW = ('unfold Zlib.proof.inflate.InvW.hdrW; cbn; split; intros X; '
              '[exfalso; unfold EXLEN, EXTRA in X; lia | intros Y; exfalso; apply Y; exact HF]')

PATCHES += [
    ('Zlib.proof.inflate.ExKit5',
     'Lemma mwf3_exlen_fin: forall m1, mwf m1 -> m_mode m1 = EXLEN ->\n'
     '  mwf3 (set_mode (exlen_fin m1) EXTRA) /\\ m_leave (set_mode (exlen_fin m1) EXTRA) = m_leave m1.\n'
     'Proof.\n'
     '  intros m1 W HM.',
     'Lemma mwf3_exlen_fin: forall m1, mwf m1 -> m_mode m1 = EXLEN -> m_hold m1 < 2 ^ 24 ->\n'
     '  mwf3 (set_mode (exlen_fin m1) EXTRA) /\\ m_leave (set_mode (exlen_fin m1) EXTRA) = m_leave m1.\n'
     'Proof.\n'
     '  intros m1 W HM HB.'),
    ('Zlib.proof.inflate.ExKit5',
     '    [ | apply swf3_hdr; right; left; reflexivity | | apply swf3_hdr; right; left; reflexivity];\n'
     '    (constructor; cbn -[crc_val]; auto;\n'
     '     [ apply modewf_hdr; right; left; reflexivity\n'
     '     | destruct S; constructor; cbn -[crc_val]; auto;',
     '    [ | split; [apply swf3_hdr; right; left; reflexivity | ' + _FIN_HDRW + ']\n'
     '      | | split; [apply swf3_hdr; right; left; reflexivity | ' + _FIN_HDRW + ']];\n'
     '    (constructor; cbn -[crc_val Int.max_unsigned]; auto;\n'
     '     [ apply modewf_hdr; right; left; reflexivity\n'
     '     | destruct S; constructor; cbn -[crc_val Int.max_unsigned]; auto;'),
    ('Zlib.proof.inflate.ExKit5',
     'Lemma mwf3_exlen_skip: forall m, mwf m -> m_mode m = EXLEN ->\n'
     '  mwf3 (set_mode (exlen_skip m) EXTRA) /\\ m_leave (set_mode (exlen_skip m) EXTRA) = m_leave m.\n'
     'Proof.\n'
     '  intros m W HM.',
     'Lemma mwf3_exlen_skip: forall m, mwf m -> m_mode m = EXLEN -> Z.land (i_flags (m_s m)) 1024 = 0 ->\n'
     '  mwf3 (set_mode (exlen_skip m) EXTRA) /\\ m_leave (set_mode (exlen_skip m) EXTRA) = m_leave m.\n'
     'Proof.\n'
     '  intros m W HM HF.'),
    ('Zlib.proof.inflate.ExKit5',
     '    [ | apply swf3_hdr; right; left; reflexivity | | apply swf3_hdr; right; left; reflexivity];\n'
     '    (constructor; cbn; auto;',
     '    [ | split; [apply swf3_hdr; right; left; reflexivity | ' + _SKIP_HDRW + ']\n'
     '      | | split; [apply swf3_hdr; right; left; reflexivity | ' + _SKIP_HDRW + ']];\n'
     '    (constructor; cbn -[Int.max_unsigned]; auto;'),
    # extra_fin ends in NAME: hdrW vacuous
    ('Zlib.proof.inflate.ExKit5',
     '  split; [split | reflexivity]; [ | apply swf3_hdr; right; right; reflexivity].\n'
     '  constructor; cbn; auto.',
     '  split; [split | reflexivity]; [ | split; [apply swf3_hdr; right; right; reflexivity | ]].\n'
     '  2: { unfold Zlib.proof.inflate.InvW.hdrW, m_mode; cbn [set_mode upd_s set_m_s m_s i_mode set_i_mode];\n'
     '       unfold NAME, EXLEN, EXTRA; split; intro X; exfalso; lia. }\n'
     '  constructor; cbn -[Int.max_unsigned]; auto.'),
]

PATCHES += [
    ('Zlib.proof.inflate.CaseEXLEN5',
     'Require Import Zlib.proof.inflate.NeedBits1_5.',
     'Require Import Zlib.proof.inflate.NeedBits1_5.\nRequire Import Zlib.proof.za.inflate.ExHoldZ.'),
    # without an extra field: the flag test is the reason why EXTRA does not need the length
    ('Zlib.proof.inflate.CaseEXLEN5',
     '    destruct (mwf3_exlen_skip m W HM) as [W4 L4].',
     '    destruct (mwf3_exlen_skip m W HM Hf) as [W4 L4].'),
    # with an extra field: the length read by NEEDBITS(16) from a buffer of hdrW is below 2^24
    ('Zlib.proof.inflate.CaseEXLEN5',
     '      destruct (mwf3_exlen_fin _ W1 HM1) as [W4 L4].',
     '      assert (HB1: m_hold (needbits 16 m) < 2 ^ 24).\n'
     '      { destruct W2 as [_ [HX _]]. destruct (HX HM) as [HB0 HH0].\n'
     '        pose proof (mw_hold _ W) as HO. pose proof (mw_bits _ W) as B0.\n'
     '        pose proof (mw_inp _ W) as I0. pose proof (mw_nx _ W) as N0. unfold lrange in HO.\n'
     '        apply (needbits16_hold_lt m); try lia; tauto. }\n'
     '      destruct (mwf3_exlen_fin _ W1 HM1 HB1) as [W4 L4].'),
]

# EXTRA with an extra field copies copy = min(length, have) bytes; with inputs of up to 2^32 - 1 bytes the
# bound copy <= 2^31 - 1 of the 32-bit test `len + copy > extra_max` comes from the length (hdrW), no longer
# from the input
PATCHES += [
    ('Zlib.proof.inflate.ExKit5',
     'Lemma mwf_extra_upd: forall m, mwf m -> m_mode m = EXTRA ->\n'
     '  mwf (extra_upd m) /\\ m_mode (extra_upd m) = EXTRA /\\ m_leave (extra_upd m) = m_leave m.\n'
     'Proof.\n'
     '  intros m W HM.',
     'Lemma mwf_extra_upd: forall m, mwf m -> m_mode m = EXTRA -> i_length (m_s m) <= Int.max_signed ->\n'
     '  mwf (extra_upd m) /\\ m_mode (extra_upd m) = EXTRA /\\ m_leave (extra_upd m) = m_leave m.\n'
     'Proof.\n'
     '  intros m W HM HLM.'),
    ('Zlib.proof.inflate.ExtraBody5',
     '  frame_ok F -> mwf m -> hd_ok F m -> c = Z.min (i_length (m_s m)) (m_have m) -> c <> 0 ->\n',
     '  frame_ok F -> mwf m -> hd_ok F m -> c = Z.min (i_length (m_s m)) (m_have m) -> c <> 0 ->\n'
     '  i_length (m_s m) <= Int.max_signed ->\n'),
    ('Zlib.proof.inflate.ExtraBody5',
     '  intros FOK W HD Hc Hn.',
     '  intros FOK W HD Hc Hn HLM.'),
    ('Zlib.proof.inflate.ExtraBody5',
     '  pose proof (mwf_extra_upd m W HM) as (WU & HMU & HLU).\n',
     ''),
    ('Zlib.proof.inflate.ExtraBody5',
     '    rewrite (proj2 (Z.eqb_neq _ _) Hf) in SB, SF.',
     '    rewrite (proj2 (Z.eqb_neq _ _) Hf) in SB, SF.\n'
     '    assert (HLM: i_length (m_s m) <= Int.max_signed) by (destruct W3 as [_ [_ HX]]; exact (HX HM Hf)).\n'
     '    pose proof (mwf_extra_upd m W HM HLM) as (WU & HMU & HLU).'),
    ('Zlib.proof.inflate.ExtraBody5',
     'apply (semax_extra_cpy F m c FOK W HD Hc Hn)',
     'apply (semax_extra_cpy (ZA:=ZA) (ZAV:=ZAV) F m c FOK W HD Hc Hn HLM)'),
]

# mwf of the machine after the copy: `cbn` must keep Int.max_unsigned folded (else `auto` runs for minutes)
PATCHES += [
    ('Zlib.proof.inflate.ExKit5',
     '    constructor; cbn -[put_bytes inbytes]; auto.\n'
     '    destruct H; constructor; cbn -[put_bytes inbytes]; auto.',
     '    constructor; cbn -[put_bytes inbytes Int.max_unsigned]; auto.\n'
     '    destruct H; constructor; cbn -[put_bytes inbytes Int.max_unsigned]; auto.'),
    ('Zlib.proof.inflate.ExKit5',
     '  constructor; cbn; rewrite ?E1, ?E2, ?E3; auto;',
     '  constructor; cbn -[Int.max_unsigned]; rewrite ?E1, ?E2, ?E3; auto;'),
]

# lemmas of other generated modules with the section's allocator named (as evars, the unification takes minutes)
PATCHES += [
    ('Zlib.proof.inflate.CaseEXLEN5',
     '    eapply (semax_needbits_seq5 F m m 16).\n'
     '    + apply semax_needbits_EXLEN5; auto; lia.',
     '    eapply (semax_needbits_seq5 (ZA:=ZA) (ZAV:=ZAV) F m m 16).\n'
     '    + apply (semax_needbits_EXLEN5 (ZA:=ZA) (ZAV:=ZAV)); auto; lia.'),
]

# mem_x (ExKit5) in change / replace: with implicit allocator evars the conversion unfolds everything
PATCHES += [
    ('Zlib.proof.inflate.ExtraBody5',
     '  match goal with |- context [mem_x F (set_m_nx ?a ?b)] =>\n'
     '    replace (mem_x F (set_m_nx a b)) with (mem_x F m) by reflexivity end.',
     '  match goal with |- context [@mem_x ZA ZAV F (set_m_nx ?a ?b)] =>\n'
     '    replace (@mem_x ZA ZAV F (set_m_nx a b)) with (@mem_x ZA ZAV F m) by reflexivity end.'),
    ('Zlib.proof.inflate.ExtraBody5',
     '           change (mem_x F (extra_fin m1)) with (mem_x F m1).',
     '           change (@mem_x ZA ZAV F (extra_fin m1)) with (@mem_x ZA ZAV F m1).'),
    ('Zlib.proof.inflate.ExtraBody5',
     '    change (mem_x F (extra_fin m)) with (mem_x F m).',
     '    change (@mem_x ZA ZAV F (extra_fin m)) with (@mem_x ZA ZAV F m).'),
]

PATCHES += [
    ('Zlib.proof.inflate.ExtraBody5',
     '        | apply (semax_extra_mb sp ',
     '        | apply (semax_extra_mb (ZA:=ZA) (ZAV:=ZAV) sp '),
    ('Zlib.proof.inflate.ExtraBody5',
     '        | apply (semax_crc_extra sp ',
     '        | apply (semax_crc_extra (ZA:=ZA) (ZAV:=ZAV) sp '),
    ('Zlib.proof.inflate.ExtraBody5',
     'rewrite ls_ex_tok. apply derives_refl.',
     'rewrite (ls_ex_tok (ZA:=ZA) (ZAV:=ZAV)). apply derives_refl.'),
    ('Zlib.proof.inflate.ExtraBody5',
     '  rewrite ls_ex_tok.\n',
     '  rewrite (ls_ex_tok (ZA:=ZA) (ZAV:=ZAV)).\n'),
    ('Zlib.proof.inflate.ExtraBody5',
     'apply (ex_brk_ok F m m1 (SB LNZ Hf))',
     'apply (ex_brk_ok (ZA:=ZA) (ZAV:=ZAV) F m m1 (SB LNZ Hf))'),
    ('Zlib.proof.inflate.ExtraBody5',
     'apply (ex_fall_ok F m (extra_fin m1) SF eq_refl',
     'apply (ex_fall_ok (ZA:=ZA) (ZAV:=ZAV) F m (extra_fin m1) SF eq_refl'),
    ('Zlib.proof.inflate.ExtraBody5',
     'apply (ex_fall_ok F m (extra_fin m) SF eq_refl',
     'apply (ex_fall_ok (ZA:=ZA) (ZAV:=ZAV) F m (extra_fin m) SF eq_refl'),
]
