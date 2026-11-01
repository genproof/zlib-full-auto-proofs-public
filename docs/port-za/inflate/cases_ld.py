"""Patches of the inflate port, part cases, group ld: see docs/port-za/inflate/cases.py."""

_TAIL5 = 'Zlib.proof.inflate.DsTail5'
_LENEXT5 = 'Zlib.proof.inflate.LdLenext5'
_LD5 = 'Zlib.proof.inflate.Cases5_LD'

# the input count of the wide machine invariant is bounded by Int.max_unsigned (mwf_za), no longer by
# Int.max_signed
_HAVE = ('    + assert (HH: 0 <= m_have mk <= Int.max_signed) by (unfold m_have; rewrite P3, P10; lia).',
         '    + assert (HH: 0 <= m_have mk <= Int.max_unsigned) by (unfold m_have; rewrite P3, P10; lia).')

PATCHES = [
    ('Zlib.proof.inflate.DsLoop1_5',) + _HAVE,
    ('Zlib.proof.inflate.DsLoop2_5',) + _HAVE,
    ('Zlib.proof.inflate.LdNb5',
     '      assert (HH: 0 <= m_have (pullk k m) <= Int.max_signed) by (unfold m_have; rewrite P3, P10; lia).',
     '      assert (HH: 0 <= m_have (pullk k m) <= Int.max_unsigned) by (unfold m_have; rewrite P3, P10; lia).'),
    # mwf3_za = mwf_za /\ swf3 /\ hdrW: the machine entering DISTEXT is in mode DISTEXT, neither EXLEN nor
    # EXTRA, so hdrW holds
    (_TAIL5, '  intros m x y z [W W3] HM Hx Hy Hz.', '  intros m x y z [W [W3 _]] HM Hx Hy Hz.'),
    (_TAIL5, '  split.\n  - constructor; cbn [upd_s set_mode set_m_s m_s m_h',
     '  split; [ | split].\n  - constructor; cbn [upd_s set_mode set_m_s m_s m_h'),
    (_TAIL5, '    + intros X; unfold DISTEXT, LENEXT in X; lia.\n    + intros _. lia.\nQed.',
     '    + intros X; unfold DISTEXT, LENEXT in X; lia.\n    + intros _. lia.\n'
     '  - unfold Zlib.proof.inflate.InvW.hdrW, m_mode. cbn [set_mode upd_s set_m_s m_s i_mode set_i_mode].\n'
     '    unfold DISTEXT, EXLEN, EXTRA. split; intro X; exfalso; lia.\nQed.'),
    # the dropped bits keep the mode DIST, neither EXLEN nor EXTRA: hdrW holds
    (_TAIL5, '  - split; [exact W2 | exact W3].',
     '  - split; [exact W2 | split; [exact (proj1 W3) | ]].\n'
     '    unfold Zlib.proof.inflate.InvW.hdrW. change (m_mode (dropbits (e_bits h) (dropbits b1 M))) with (m_mode M).\n'
     '    rewrite HM. unfold DIST, EXLEN, EXTRA. split; intro X; exfalso; lia.'),
    # the stream's zalloc / zfree are the allocator's functions
    (_TAIL5, 'remember (f_gv F _zcalloc) as zca eqn:Hzca. remember (f_gv F _zcfree) as zcf eqn:Hzcf.',
     'remember (@za_alloc ZA) as zca eqn:Hzca. remember (@za_free ZA) as zcf eqn:Hzcf.'),
    # the evar pitfall in `change`: name the section's allocator
    (_TAIL5, 'change (mem_rep_d F (set_bad (dt_m1 h m) M_d_code)) with (mem_rep_d F m).',
     'change (@mem_rep_d ZA F (set_bad (dt_m1 h m) M_d_code)) with (@mem_rep_d ZA F m).'),
    (_TAIL5, 'change (mem_rep_d F (dt_distext h m)) with (mem_rep_d F m).',
     'change (@mem_rep_d ZA F (dt_distext h m)) with (@mem_rep_d ZA F m).'),
    # mwf3_za of the machine entering DIST: its mode DIST is neither EXLEN nor EXTRA (hdrW)
    (_LENEXT5, '  intros m [W W3] HM.\n', '  intros m [W [W3 _]] HM.\n'),
    (_LENEXT5, '  intros m [W W3] HM HL0 E0 L0.', '  intros m [W [W3 _]] HM HL0 E0 L0.'),
    (_LENEXT5, '  split.\n  - constructor; cbn [le_fin_m set_mode', '  split; [ | split].\n  - constructor; cbn [le_fin_m set_mode'),
    (_LENEXT5, '  split.\n  - constructor; cbn [set_mode upd_s set_m_s m_s m_h',
     '  split; [ | split].\n  - constructor; cbn [set_mode upd_s set_m_s m_s m_h'),
    (_LENEXT5, '    + intros X; unfold DIST, DISTEXT in X; lia.\nQed.',
     '    + intros X; unfold DIST, DISTEXT in X; lia.\n'
     '  - unfold Zlib.proof.inflate.InvW.hdrW, m_mode. cbn [le_fin_m set_mode upd_s set_m_s m_s i_mode set_i_mode].\n'
     '    unfold DIST, EXLEN, EXTRA. split; intro X; exfalso; lia.\nQed.'),
    (_LENEXT5, '  pose proof (s3_lenext _ (proj2 W3) HM) as LN2.', '  pose proof (s3_lenext _ (proj1 (proj2 W3)) HM) as LN2.'),
    # the table lookups keep the mode DIST, neither EXLEN nor EXTRA: hdrW holds
    (_LD5, '  assert (W31: mwf3 m1) by (split; [exact W1 | rewrite S1; exact S3]).',
     '  assert (W31: mwf3 m1).\n'
     '  { split; [exact W1 | split; [rewrite S1; exact (proj1 S3) | ]].\n'
     '    unfold Zlib.proof.inflate.InvW.hdrW. rewrite M1. unfold DIST, EXLEN, EXTRA. split; intro X; exfalso; lia. }'),
    (_LD5, '      * split; [exact W2 | rewrite S2, S1; exact S3].',
     '      * split; [exact W2 | split; [rewrite S2, S1; exact (proj1 S3) | ]].\n'
     '        unfold Zlib.proof.inflate.InvW.hdrW.\n'
     '        replace (m_mode m2) with DIST by (unfold m_mode in *; rewrite S2; exact (eq_sym M1)).\n'
     '        unfold DIST, EXLEN, EXTRA. split; intro X; exfalso; lia.'),
    # lemmas of other generated modules applied with the section's allocator and adler cell named (as evars,
    # their unification unfolds the specifications: > 300 s)
    (_LENEXT5, '    apply (semax_needbits_seq5 F m m (i_extra (m_s m))).',
     '    apply (semax_needbits_seq5 (ZA:=ZA) (ZAV:=ZAV) F m m (i_extra (m_s m))).'),
    (_LENEXT5, '  apply (case_fallthrough5 F m DIST 21); [lia | exact HD | ].',
     '  apply (case_fallthrough5 (ZA:=ZA) (ZAV:=ZAV) F m DIST 21); [lia | exact HD | ].'),
    (_LD5, '    apply (semax_ifleave5 F m0 m R W HR). intros _. exact E.',
     '    apply (semax_ifleave5 (ZA:=ZA) (ZAV:=ZAV) F m0 m R W HR). intros _. exact E.'),
    (_LD5, '      apply (ds_link_ok (ds_loop2_ok ds_tab_ok) _ F m0 m1 here lv sz R HF W1 M1 L1 SZ LINK EOh B1 HR) ].',
     '      apply (ds_link_ok (ZA:=ZA) (ZAV:=ZAV) (ds_loop2_ok (ZA:=ZA) (ZAV:=ZAV) (ds_tab_ok (ZA:=ZA) (ZAV:=ZAV)))\n'
     '               _ F m0 m1 here lv sz R HF W1 M1 L1 SZ LINK EOh B1 HR) ].'),
    (_LD5, '  apply (case_fallthrough5 F m DISTEXT 22); [lia | exact HY | ].',
     '  apply (case_fallthrough5 (ZA:=ZA) (ZAV:=ZAV) F m DISTEXT 22); [lia | exact HY | ].'),
    (_LD5, "  eapply semax_seq'; [ apply (ds_loop1_ok ds_tab_ok _ F m _ _ HF W HM HL) | ].",
     "  eapply semax_seq'; [ apply (ds_loop1_ok (ZA:=ZA) (ZAV:=ZAV) (ds_tab_ok (ZA:=ZA) (ZAV:=ZAV)) _ F m _ _ HF W HM HL) | ]."),
    (_LD5, '    apply (ds_tail_ok _ F m M b1 h lv _ HF WM MM LM B0 EOK FOK BB1 BB2 ET); reflexivity.',
     '    apply (ds_tail_ok (ZA:=ZA) (ZAV:=ZAV) _ F m M b1 h lv _ HF WM MM LM B0 EOK FOK BB1 BB2 ET); reflexivity.'),
    (_LD5, '  - exact (ld_lenext_ok ld_nb_ok _ F HF).',
     '  - exact (ld_lenext_ok (ZA:=ZA) (ZAV:=ZAV) (ld_nb_ok (ZA:=ZA) (ZAV:=ZAV)) _ F HF).'),
]
