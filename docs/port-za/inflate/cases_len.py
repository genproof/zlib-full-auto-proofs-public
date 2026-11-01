"""Patches of the inflate port, part cases, group len: see docs/port-za/inflate/cases.py."""

PATCHES = [
    # mwf3_za = mwf_za /\ swf3 /\ hdrW: the second component is a pair; hdrW of the machine with i_back set
    # is the one of the old machine (hdrW does not read i_back)
    ('Zlib.proof.inflate.LnCase5',
     '  - destruct X; constructor; cbn [set_i_back',
     '  - destruct X as [X X3]; split; [destruct X; constructor | ]; cbn [set_i_back'),
    # hdrW of a machine with the same saved state: it reads the bit buffer in mode EXLEN, so the lemma now
    # takes the mode (LEN in every use)
    ('Zlib.proof.inflate.LnCase5',
     'Lemma mwf3_intro: forall m m\', mwf3 m -> mwf m\' -> m_s m\' = m_s m -> mwf3 m\'.\n'
     'Proof. intros m m\' [W X] W\' E. split; [exact W\'|]. rewrite E. exact X. Qed.',
     'Lemma mwf3_intro: forall m m\', mwf3 m -> mwf m\' -> m_s m\' = m_s m -> m_mode m = LEN -> mwf3 m\'.\n'
     'Proof.\n'
     '  intros m m\' [W [X H]] W\' E HM. split; [exact W\'|]. rewrite E. split; [exact X|].\n'
     '  unfold Zlib.proof.inflate.InvW.hdrW, m_mode in *. rewrite E, HM. unfold LEN, EXLEN, EXTRA.\n'
     '  split; intro Y; exfalso; lia.\n'
     'Qed.'),
    ('Zlib.proof.inflate.LnCase5',
     '  - apply (mwf3_intro _ _ W4); [ | reflexivity].',
     '  - apply (mwf3_intro _ _ W4); [ | reflexivity | exact HM2].'),
    # the swf3 part of mwf3 is now the first half of a pair (the second is hdrW)
    ('Zlib.proof.inflate.LnFast5',
     '  intros m [W S] HM. split;',
     '  intros m [W [S _]] HM. split;'),
    ('Zlib.proof.inflate.LnTail5',
     '  intros h m [W W3] HM EO B0 B1 B2 OP VL.',
     '  intros h m [W [W3 HW]] HM EO B0 B1 B2 OP VL.'),
    # hdrW of the machine in mode LENEXT: it constrains only the modes EXLEN and EXTRA
    ('Zlib.proof.inflate.LnTail5',
     '  - constructor; cbn [upd_s set_m_s m_s dropbits set_m_hold set_m_bits set_mode\n',
     '  - split; [ | unfold Zlib.proof.inflate.InvW.hdrW, m_mode; cbn [upd_s set_m_s m_s dropbits set_m_hold\n'
     '      set_m_bits set_mode set_i_mode set_i_extra set_i_length set_i_back i_mode];\n'
     '      unfold EXLEN, EXTRA, LENEXT; split; intro X; exfalso; lia].\n'
     '    constructor; cbn [upd_s set_m_s m_s dropbits set_m_hold set_m_bits set_mode\n'),
    # the stream's zalloc / zfree are the caller's allocator functions
    ('Zlib.proof.inflate.LnTail5',
     'remember (f_gv F _zcalloc) as zca eqn:Hzca. remember (f_gv F _zcfree) as zcf eqn:Hzcf.',
     'remember (@za_alloc ZA) as zca eqn:Hzca. remember (@za_free ZA) as zcf eqn:Hzcf.'),
] + [
    # the input count of the wide machine invariant is bounded by Int.max_unsigned (mwf_za)
    ('Zlib.proof.inflate.' + m,
     '    + assert (HH: 0 <= m_have mk <= Int.max_signed) by (unfold m_have; rewrite P3, P10; lia).',
     '    + assert (HH: 0 <= m_have mk <= Int.max_unsigned) by (unfold m_have; rewrite P3, P10; lia).')
    for m in ['LnLoop1_5', 'LnLoop2_5']
]
