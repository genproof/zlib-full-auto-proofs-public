"""Patches of the inflate port, part cases, group st: see docs/port-za/inflate/cases.py."""

_COPY5 = 'Zlib.proof.inflate.CaseCOPY5'
_STORED5 = 'Zlib.proof.inflate.CaseSTORED5'

PATCHES = [
    # mwf3_za = mwf_za /\ swf3 /\ hdrW: the stored-block modes are neither EXLEN nor EXTRA, so hdrW holds
    (_COPY5, '  intros m md [W [A B C D]] H1 H2 H3 Hmd.',
     '  intros m md [W [[A B C D] _]] H1 H2 H3 Hmd.'),
    (_COPY5, '  split.\n  - apply mwf_set_mode_plain',
     '  split; [ | split].\n  - apply mwf_set_mode_plain'),
    (_COPY5, '    + intro X. apply Hne. tauto.\n    + intro X. apply Hne. tauto.\n    + intro X. apply Hne. tauto.\n'
             '    + intro X. apply Hne. tauto.\nQed.',
     '    + intro X. apply Hne. tauto.\n    + intro X. apply Hne. tauto.\n    + intro X. apply Hne. tauto.\n'
     '    + intro X. apply Hne. tauto.\n'
     '  - unfold Zlib.proof.inflate.InvW.hdrW. cbn [set_mode upd_s set_m_s m_s m_mode i_mode set_i_mode].\n'
     '    unfold EXLEN, EXTRA, COPY_, COPY, Model.TYPE in *. split; intro X; exfalso; lia.\nQed.'),
    # the evar pitfall: an implicit allocator in the replaced term is unified by unfolding (> 300 s)
    (_COPY5, 'replace (mem_rep_io F (upd_s m1 f)) with (mem_rep_io F m) by reflexivity end.',
     'replace (@mem_rep_io ZA ZAV F (upd_s m1 f)) with (@mem_rep_io ZA ZAV F m) by reflexivity end.'),
    # mwf3_za of the machine entering COPY_: its mode STORED is neither EXLEN nor EXTRA (hdrW)
    (_STORED5, '  split.\n  - apply mwf_initbits.', '  split; [ | split].\n  - apply mwf_initbits.'),
    (_STORED5, '      unfold STORED, HEAD, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT in *; lia.\nQed.',
     '      unfold STORED, HEAD, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT in *; lia.\n'
     '  - unfold Zlib.proof.inflate.InvW.hdrW, m_mode in *.\n'
     '    cbn [initbits upd_s set_m_s set_m_hold set_m_bits m_s set_i_length i_mode]; rewrite HM.\n'
     '    unfold STORED, EXLEN, EXTRA. split; intro X; exfalso; lia.\nQed.'),
    # the evar pitfall in `change`: name the section's allocator and adler cell
    (_STORED5, 'change (mem_rep F (bytebits m)) with (mem_rep F m).',
     'change (@mem_rep ZA ZAV F (bytebits m)) with (@mem_rep ZA ZAV F m).'),
    (_STORED5, '\n    change (mem_rep_io F (initbits (upd_s m1 (fun s => set_i_length s (m_hold m1 mod 65536)))))\n'
               '      with (mem_rep_io F m1).',
     '\n    change (@mem_rep_io ZA ZAV F (initbits (upd_s m1 (fun s => set_i_length s (m_hold m1 mod 65536)))))\n'
     '      with (@mem_rep_io ZA ZAV F m1).'),
    (_STORED5, '\n  change (mem_rep_io F (initbits (upd_s m1 (fun s => set_i_length s (m_hold m1 mod 65536)))))\n'
               '    with (mem_rep_io F m1).',
     '\n  change (@mem_rep_io ZA ZAV F (initbits (upd_s m1 (fun s => set_i_length s (m_hold m1 mod 65536)))))\n'
     '    with (@mem_rep_io ZA ZAV F m1).'),
    (_STORED5, 'change (mem_rep_io F (set_leave (st_m2 m1))) with (mem_rep_io F m1).',
     'change (@mem_rep_io ZA ZAV F (set_leave (st_m2 m1))) with (@mem_rep_io ZA ZAV F m1).'),
    (_STORED5, 'change (mem_rep_io F (st_m2 m1)) with (mem_rep_io F m1).',
     'change (@mem_rep_io ZA ZAV F (st_m2 m1)) with (@mem_rep_io ZA ZAV F m1).'),
]
