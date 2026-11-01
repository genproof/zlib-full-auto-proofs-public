"""Patches of the inflate port, part cases, group tl: see docs/port-za/inflate/cases.py."""


# mwf3 of the wide machine also states InvW.hdrW, which constrains only the modes EXLEN and EXTRA: vacuous for a
# machine in mode LENLENS or CODELENS (`unfolds`: the local definitions to unfold to see the mode)
def _hdrw_vacuous(unfolds=''):
    return ('    unfold Zlib.proof.inflate.InvW.hdrW, m_mode%s; cbn [m_s set_m_s i_mode set_i_mode]; split; intros HM;\n'
            '    cbv [LENLENS CODELENS EXLEN EXTRA] in HM; lia.\n' % unfolds)


# the stream's zalloc / zfree fields are now the allocator's za_alloc / za_free (strm_rep_za), no longer the global
# zcalloc / zcfree: name those values so that entailer! keeps them folded
_ZFUNCS = ('remember (f_gv F _zcalloc) as za eqn:Eza. remember (f_gv F _zcfree) as zf eqn:Ezf.',
           'remember (@za_alloc ZA) as za eqn:Eza. remember (@za_free ZA) as zf eqn:Ezf.')

PATCHES = [
    # lemmas of other generated modules with the section variables named: with them left as evars, apply's
    # unification ran for minutes
    ('Zlib.proof.inflate.LLLoop5', 'apply semax_needbits_LENLENS5;',
     'apply (semax_needbits_LENLENS5 (ZA:=ZA) (ZAV:=ZAV));'),
    ('Zlib.proof.inflate.LLTail5',) + _ZFUNCS,
    ('Zlib.proof.inflate.CaseTABLE5',) + _ZFUNCS,
    ('Zlib.proof.inflate.TLFacts',
     '    apply tl_swf3_plain; cbn [i_mode set_i_mode]; [md_neq | unfold decode_mode; md_neq | md_neq | md_neq].\n',
     '    split; [apply tl_swf3_plain; cbn [i_mode set_i_mode]; [md_neq | unfold decode_mode; md_neq | md_neq | md_neq] | ].\n'
     + _hdrw_vacuous()),
    ('Zlib.proof.inflate.TLFacts',
     "  - simpl. apply tl_swf3_plain; unfold s'; cbn [i_mode set_i_mode]; [md_neq | unfold decode_mode; md_neq | md_neq | md_neq].\n",
     "  - simpl. split; [apply tl_swf3_plain; unfold s'; cbn [i_mode set_i_mode];\n"
     "      [md_neq | unfold decode_mode; md_neq | md_neq | md_neq] | ].\n"
     + _hdrw_vacuous(", s'")),
]
