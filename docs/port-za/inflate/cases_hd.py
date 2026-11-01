"""Patches of the inflate port, part cases, group hd: see docs/port-za/inflate/cases.py."""

_M = 'Zlib.proof.inflate.Cases5_HD'

# the z_stream's zalloc / zfree are the allocator's values (no longer gv of _zcalloc / _zcfree)
_REM = ('remember (f_gv F _zcalloc) as za eqn:Eza. remember (f_gv F _zcfree) as zf eqn:Ezf.',
        'remember (@za_alloc ZA) as za eqn:Eza. remember (@za_free ZA) as zf eqn:Ezf.')

# the cases store a Vlong into strm->adler, which the port's z_stream holds as the adler cell (any contents when
# av_undef): weaken the stored member before the final entailment
_AW = ('match goal with |- context [data_at ?sh t_strm (?a1, (?a2, (?a3, (?a4, (?a5, (?a6, (?a7, (?a8, (?a9, (?a10, '
       '(?a11, (?a12, (Vlong (Int64.repr ?y), ?a14))))))))))))) ?p] => sep_apply (@data_at_adler_val ZAV sh p a1 a2 a3 '
       'a4 a5 a6 a7 a8 a9 a10 a11 a12 a14 (Vlong (Int64.repr y)) y (fun _ => eq_refl)) end.')

PATCHES = [
    (_M, 'rest_simpl. thaw FB. thaw FR. unfold win_rep. entailer!.',
     'rest_simpl. thaw FB. thaw FR. unfold win_rep.\n        ' + _AW + '\n        entailer!.'),
    (_M, 'rest_simpl. thaw FR. unfold win_rep. entailer!.',
     'rest_simpl. thaw FR. unfold win_rep.\n        ' + _AW + '\n        entailer!.'),
    (_M, 'change (Int.signed (Int.repr 0)) with 0.\n    entailer!.',
     'change (Int.signed (Int.repr 0)) with 0.\n    ' + _AW + '\n    entailer!.'),
    (_M, 'rest_simpl. rewrite strm_rep_unfold. rewrite <- Eza, <- Ezf.\n    entailer!.',
     'rest_simpl. rewrite strm_rep_unfold. rewrite <- Eza, <- Ezf.\n    ' + _AW + '\n    entailer!.'),
    # lemmas of the other generated modules with their allocator and adler cell given: as evars, the
    # unification of their conclusions runs for minutes
    (_M, 'eapply (semax_needbits_seq5 F m m 16).', 'eapply (@semax_needbits_seq5 ZA ZAV _ F m m 16).'),
    (_M, 'apply semax_needbits_HCRC5;', 'apply (@semax_needbits_HCRC5 ZA ZAV _ F m 16);'),
    (_M, 'eapply (semax_needbits_seq_r5 F m m 32).', 'eapply (@semax_needbits_seq_r5 ZA ZAV _ F m m 32).'),
    (_M, 'apply semax_needbits_DICTID5;', 'apply (@semax_needbits_DICTID5 ZA ZAV _ F m 32);'),
    (_M, 'apply (case_fallthrough5 F m DICT 9);', 'apply (@case_fallthrough5 ZA ZAV _ F m DICT 9);'),
    (_M, 'apply (case_fallthrough5 F m Zlib.proof.inflate.Model.TYPE 10);',
     'apply (@case_fallthrough5 ZA ZAV _ F m Zlib.proof.inflate.Model.TYPE 10);'),
    # strm->adler written by the cases: src/proof/za/inflate/AdlerZ.v
    (_M, 'Require Import Zlib.proof.inflate.CaseRet5.',
     'Require Import Zlib.proof.inflate.CaseRet5.\nRequire Import Zlib.proof.za.inflate.AdlerZ.'),
    # the z_stream as the port represents it: the allocator's opaque, the adler cell
    (_M, '(nullval, (zv dt, (lv adler, vres))))))))))))) strmp.',
     '(za_opaque, (zv dt, (adler_val adler, vres))))))))))))) strmp.'),
    # case DICT has two of them (the second one before the two stores)
    (_M, '  - unfold strm_rep. ' + _REM[0], '  - unfold strm_rep. ' + _REM[1]),
    (_M, '    unfold strm_rep. ' + _REM[0] + '\n    forward. forward.',
     '    unfold strm_rep. ' + _REM[1] + '\n    forward. forward.'),
    (_M,) + _REM,
    # mwf3 now also holds InvW.hdrW, which only constrains the modes EXLEN and EXTRA
    (_M, '  - apply swf3_plain; unfold decode_mode, DICT, HEAD, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT; lia.',
     '  - split; [apply swf3_plain; unfold decode_mode, DICT, HEAD, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT; lia | ].\n'
     '    unfold Zlib.proof.inflate.InvW.hdrW. change (m_mode (set_mode ?x DICT)) with DICT.\n'
     '    unfold DICT, EXLEN, EXTRA; split; intro; lia.'),
    (_M, '  - apply swf3_plain; unfold decode_mode, Zlib.proof.inflate.Model.TYPE, HEAD, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT; lia.',
     '  - split; [apply swf3_plain; unfold decode_mode, Zlib.proof.inflate.Model.TYPE, HEAD, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT; lia | ].\n'
     '    unfold Zlib.proof.inflate.InvW.hdrW. change (m_mode (set_mode ?x Zlib.proof.inflate.Model.TYPE)) with Zlib.proof.inflate.Model.TYPE.\n'
     '    unfold Zlib.proof.inflate.Model.TYPE, EXLEN, EXTRA; split; intro; lia.'),
]
