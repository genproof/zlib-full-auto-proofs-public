"""Patches of the inflate port, part cases, group dm: see docs/port-za/inflate/cases.py."""

# the input count of the wide machine invariant is bounded by Int.max_unsigned (mwf_za), no longer by
# Int.max_signed
_HAVE = ('      assert (HH: 0 <= m_have (pullk k m) <= Int.max_signed) by (unfold m_have; rewrite P3, P10; lia).',
         '      assert (HH: 0 <= m_have (pullk k m) <= Int.max_unsigned) by (unfold m_have; rewrite P3, P10; lia).')

PATCHES = [
    ('Zlib.proof.inflate.DxNb5',) + _HAVE,
    # mwf3_za = mwf_za /\ swf3 /\ hdrW: the machine after DISTEXT is in mode MATCH, where hdrW says nothing
    ('Zlib.proof.inflate.DxCase5',
     '  split.\n  - apply mwf_dropbits',
     '  split; [ | split].\n  - apply mwf_dropbits'),
    ('Zlib.proof.inflate.DxCase5',
     '    exact TL3.\nQed.',
     '    exact TL3.\n'
     '  - unfold Zlib.proof.inflate.InvW.hdrW, m_mode; cbn [dropbits upd_s set_m_s set_m_hold set_m_bits m_s\n'
     '      set_i_mode set_i_offset set_i_back i_mode].\n'
     '    unfold EXLEN, EXTRA, MATCH; split; intro; exfalso; lia.\nQed.'),
    ('Zlib.proof.inflate.DxCase5',
     '  pose proof W3 as [W X].',
     '  pose proof W3 as [W [X _]].'),
    # lemmas of other generated modules with their section arguments named: with ZA / ZAV left as evars the
    # application unifies by unfolding (sentence timeout)
    ('Zlib.proof.inflate.DxCase5',
     '  apply (case_fallthrough5 F m MATCH 23);',
     '  apply (case_fallthrough5 (ZA:=ZA) (ZAV:=ZAV) F m MATCH 23);'),
    ('Zlib.proof.inflate.DxCase5',
     '      apply (semax_needbits_seq5 F m m (i_extra (m_s m)) dx_nb dx_rest);',
     '      apply (semax_needbits_seq5 (ZA:=ZA) (ZAV:=ZAV) F m m (i_extra (m_s m)) dx_nb dx_rest);'),
    ('Zlib.proof.inflate.DxCase5',
     '[apply dx_rest_ok; auto;',
     '[apply (dx_rest_ok (ZA:=ZA) (ZAV:=ZAV)); auto;'),
    ('Zlib.proof.inflate.DxCase5',
     '    eapply dx_post_over; [apply semax_store_mode5 | ].',
     '    eapply dx_post_over; [apply (semax_store_mode5 (ZA:=ZA) (ZAV:=ZAV)) | ].'),
]
