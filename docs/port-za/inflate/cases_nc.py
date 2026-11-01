"""Patches of the inflate port, part cases, group nc: see docs/port-za/inflate/cases.py."""


# mwf3 of the wide machine also states InvW.hdrW, which constrains only the modes EXLEN and EXTRA: after the swf3
# part, it is vacuous for the successor machine of NAME (mode COMMENT) and of COMMENT (mode HCRC)
def _fin_mwf3(mode):
    return ('  - apply swf3_hdr. cbn. unfold FLAGS, %s, TYPEDO; lia.\n' % mode,
            '  - split; [apply swf3_hdr; cbn; unfold FLAGS, %s, TYPEDO; lia | ].\n'
            '    unfold Zlib.proof.inflate.InvW.hdrW, m_mode;\n'
            '    cbn [set_mode upd_s set_m_s m_s i_mode set_i_mode set_i_length]; split; intros Hm;\n'
            '    cbv [%s EXLEN EXTRA] in Hm; lia.\n' % (mode, mode))


# a lemma of another generated module applied with the section variables named: left as evars, the unification
# with the goal ran for more than 300 s
def _named(module, lemma):
    return ('Zlib.proof.inflate.' + module, 'apply (%s F' % lemma, 'apply (%s (ZA:=ZA) (ZAV:=ZAV) F' % lemma)


PATCHES = [
    _named('CaseNAME5', 'semax_name_loop_m'),
    _named('CaseNAME5', 'semax_name_crc_m'),
    _named('CaseCOMMENT5', 'semax_comm_loop_m'),
    _named('CaseCOMMENT5', 'semax_comm_crc_m'),
    ('Zlib.proof.inflate.Cases5_NC', 'apply case_NAME5;', 'apply (case_NAME5 (ZA:=ZA) (ZAV:=ZAV));'),
    ('Zlib.proof.inflate.Cases5_NC', 'apply case_COMMENT5;', 'apply (case_COMMENT5 (ZA:=ZA) (ZAV:=ZAV));'),
    ('Zlib.proof.inflate.CaseNAME5',) + _fin_mwf3('COMMENT'),
    ('Zlib.proof.inflate.CaseCOMMENT5',) + _fin_mwf3('HCRC'),
]
