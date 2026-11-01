"""Patches of the inflate port, part cases, group fto: see docs/port-za/inflate/cases.py."""

# mwf3_za of the successor of a header case also asks InvW.hdrW of it: at EXLEN the bit buffer holds only its
# bits (bits < 16, hold < 2^bits), at EXTRA the extra length is bounded.  The mode change at the end of FLAGS,
# TIME, OS takes the EXLEN fact as a hypothesis (OS ends with INITBITS: hold = bits = 0) and excludes EXTRA
# (reached only from EXLEN, whose group has its own copy of this lemma).
_HDR_STMT = (
    '  mwf m -> HEAD <= m_mode m <= TYPEDO -> FLAGS <= md <= TYPEDO -> mwf3 (set_mode m md).\n'
    'Proof.\n'
    '  intros m md W HM Hmd. split.',
    '  mwf m -> HEAD <= m_mode m <= TYPEDO -> FLAGS <= md <= TYPEDO ->\n'
    '  (md = EXLEN -> m_bits m < 16 /\\ m_hold m < 2 ^ m_bits m) -> md <> EXTRA -> mwf3 (set_mode m md).\n'
    'Proof.\n'
    '  intros m md W HM Hmd HB HX. split.')
_HDR_PROOF = (
    '  - constructor; cbn [set_mode upd_s set_m_s m_s set_i_mode i_mode];\n'
    '      unfold decode_mode, HEAD, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, FLAGS, TYPEDO in *; intros; lia.\n'
    'Qed.',
    '  - split.\n'
    '    + constructor; cbn [set_mode upd_s set_m_s m_s set_i_mode i_mode];\n'
    '        unfold decode_mode, HEAD, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, FLAGS, TYPEDO in *; intros; lia.\n'
    '    + unfold Zlib.proof.inflate.InvW.hdrW, m_mode; cbn [set_mode upd_s set_m_s m_s set_i_mode i_mode m_bits m_hold].\n'
    '      split; [exact HB | intros HE; exfalso; exact (HX HE)].\n'
    'Qed.')


def _caller(md):
    """the two new side conditions of mwf3_set_mode_hdr at the end of the case whose successor mode is md"""
    old = '    - unfold FLAGS, %s, TYPEDO; lia. }' % md
    if md == 'EXLEN':
        exlen = ('    - intros _. unfold initbits; cbn [set_m_bits set_m_hold m_bits m_hold].\n'
                 '      split; [lia | cbv; reflexivity].\n')
    else:
        exlen = '    - unfold %s, EXLEN; intros; lia.\n' % md
    return (old, '    - unfold FLAGS, %s, TYPEDO; lia.\n' % md + exlen + '    - unfold %s, EXTRA; lia. }' % md)


# the stream's zalloc / zfree are the allocator's values, no longer zcalloc's / zcfree's addresses
_ZFUNCS = ('  remember (f_gv F _zcalloc) as zca eqn:Hzca. remember (f_gv F _zcfree) as zcf eqn:Hzcf.',
           '  remember (@za_alloc ZA) as zca eqn:Hzca. remember (@za_free ZA) as zcf eqn:Hzcf.')

PATCHES = [
    ('Zlib.proof.inflate.CaseFLAGS5',) + _ZFUNCS,
    ('Zlib.proof.inflate.HdrKit5',) + _HDR_STMT,
    ('Zlib.proof.inflate.HdrKit5',) + _HDR_PROOF,
    ('Zlib.proof.inflate.CaseFLAGS5',) + _caller('TIME'),
    ('Zlib.proof.inflate.CaseTIME5',) + _caller('OS'),
    ('Zlib.proof.inflate.CaseOS5',) + _caller('EXLEN'),
]
