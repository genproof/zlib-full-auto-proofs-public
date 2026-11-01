"""Patches of the inflate port, part cases, group cl: see docs/port-za/inflate/cases.py."""

# the stream's zalloc / zfree are the allocator's functions (strm_rep_za), no longer zcalloc / zcfree
_REM = ('remember (f_gv F _zcalloc) as za eqn:Eza. remember (f_gv F _zcfree) as zf eqn:Ezf.',
        'remember (@za_alloc ZA) as za eqn:Eza. remember (@za_free ZA) as zf eqn:Ezf.')

# the input count of the wide machine invariant is bounded by Int.max_unsigned (mwf_za), no longer by
# Int.max_signed
_HAVE_J = ('assert (HH: 0 <= m_have (pullk j m) <= Int.max_signed) by (unfold m_have; rewrite P3, P10; lia).',
           'assert (HH: 0 <= m_have (pullk j m) <= Int.max_unsigned) by (unfold m_have; rewrite P3, P10; lia).')

PATCHES = [
    ('Zlib.proof.inflate.' + m,) + _REM for m in ['CLFill5', 'CLLens5', 'CLRepBr5']
] + [
    ('Zlib.proof.inflate.CLRepNB5',) + _HAVE_J,
    ('Zlib.proof.inflate.CLLookup5',
     'assert (HH: 0 <= m_have mk <= Int.max_signed) by (unfold m_have; rewrite P3, P10; lia).',
     'assert (HH: 0 <= m_have mk <= Int.max_unsigned) by (unfold m_have; rewrite P3, P10; lia).'),
    ('Zlib.proof.inflate.Cases5_CL',
     'remember (f_gv F _zcalloc) as zca eqn:Hzca. remember (f_gv F _zcfree) as zcf eqn:Hzcf.',
     'remember (@za_alloc ZA) as zca eqn:Hzca. remember (@za_free ZA) as zcf eqn:Hzcf.'),
    # mwf3_za also holds InvW.hdrW, which only concerns the modes EXLEN and EXTRA: the tables end in LEN_
    ('Zlib.proof.inflate.CLTabFacts5',
     '- unfold s4. constructor; simpl; intros; try ctf_md_neq.',
     '- split; [|unfold InvW.hdrW; split; intros Hm; cbn in Hm; exfalso; cbv [LEN_ EXLEN EXTRA] in Hm; discriminate Hm].\n'
     '    unfold s4. constructor; simpl; intros; try ctf_md_neq.'),
    # the lemmas of another generated module take the section's allocator explicitly (else their ZA / ZAV are
    # evars while apply unifies the triple: minutes)
] + [
    ('Zlib.proof.inflate.CLRep5', 'apply %s; auto' % l, 'apply (%s (ZA:=ZA) (ZAV:=ZAV)); auto' % l)
    for l in ['cl_r16_ok', 'cl_r17_ok', 'cl_r18_ok']
] + [
    ('Zlib.proof.inflate.Cases5_CL', 'apply (case_fallthrough5 F m LEN_ 18)',
     'apply (case_fallthrough5 (ZA:=ZA) (ZAV:=ZAV) F m LEN_ 18)'),
    ('Zlib.proof.inflate.Cases5_CL', 'apply (cl_while_ok cl_lookup_ok cl_small_ok cl_rep_ok cl_fill_ok)',
     'apply (cl_while_ok (ZA:=ZA) (ZAV:=ZAV) (cl_lookup_ok (ZA:=ZA) (ZAV:=ZAV)) (cl_small_ok (ZA:=ZA) (ZAV:=ZAV))\n'
     '                (cl_rep_ok (ZA:=ZA) (ZAV:=ZAV)) (cl_fill_ok (ZA:=ZA) (ZAV:=ZAV)))'),
    ('Zlib.proof.inflate.Cases5_CL', 'apply (cl_lens_ok Espec', 'apply (cl_lens_ok (ZA:=ZA) (ZAV:=ZAV) Espec'),
    ('Zlib.proof.inflate.Cases5_CL', 'apply cl_dists_ok; auto.', 'apply (cl_dists_ok (ZA:=ZA) (ZAV:=ZAV)); auto.'),
]
