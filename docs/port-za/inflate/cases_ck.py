"""Patches of the inflate port, part cases, group ck: see docs/port-za/inflate/cases.py."""

PATCHES = [
    # the stream's zalloc / zfree members are the allocator's values za_alloc / za_free (strm_rep_za), no longer
    # the global zcalloc / zcfree: name those values so that entailer! keeps them folded
    ('Zlib.proof.inflate.CKKit5',
     '  remember (f_gv F _zcalloc) as zca eqn:Hzca; remember (f_gv F _zcfree) as zcf eqn:Hzcf;',
     '  remember za_alloc as zca eqn:Hzca; remember za_free as zcf eqn:Hzcf;'),
    # mwf3_za = mwf_za /\ swf3 /\ InvW.hdrW: InvW.hdrW only constrains the modes EXLEN and EXTRA, vacuous in mode LENGTH
    ('Zlib.proof.inflate.CaseCHECK5',
     '  - apply ck_swf3_plain. reflexivity.\n',
     '  - split; [apply ck_swf3_plain; reflexivity | ].\n'
     '    unfold Zlib.proof.inflate.InvW.hdrW, m_mode; cbn [set_mode set_m_out initbits upd_s m_s set_m_s i_mode set_i_mode];\n'
     '    unfold EXLEN, EXTRA, LENGTH; split; intro X; exfalso; lia.\n'),
    # the output count is bounded by m_aout <= Int.max_unsigned in the wide invariant
    ('Zlib.proof.inflate.CaseCHECK5',
     'bytes_ok (m_ow mt) -> 0 <= o <= Int.max_signed ->',
     'bytes_ok (m_ow mt) -> 0 <= o <= Int.max_unsigned ->'),
    ('Zlib.proof.inflate.CaseCHECK5',
     'assert (Ho0: 0 <= o <= Int.max_signed)',
     'assert (Ho0: 0 <= o <= Int.max_unsigned)'),
    # the same in mode DONE (case LENGTH); the conjunction is one level deeper
    ('Zlib.proof.inflate.CaseLENGTH5',
     '  - apply lg_swf3_done. reflexivity.\n',
     '  - split; [apply lg_swf3_done; reflexivity | ].\n'
     '    unfold Zlib.proof.inflate.InvW.hdrW, m_mode; cbn [set_mode upd_s m_s set_m_s i_mode set_i_mode];\n'
     '    unfold EXLEN, EXTRA, DONE; split; intro X; exfalso; lia.\n'),
    ('Zlib.proof.inflate.CaseLENGTH5',
     'first [exact E0\' | exact HL | exact WM | exact (proj1 WM) | exact (proj2 WM)].',
     'first [exact E0\' | exact HL | exact WM | exact (proj1 WM) | exact (proj2 WM)\n'
     '      | exact (proj1 (proj2 WM)) | exact (proj2 (proj2 WM))].'),
    # case CHECK stores the new check value into strm->adler, which the representation holds as the adler cell
    # (adler_val): weaken the stored Vlong with AdlerZ.data_at_adler_val
    ('Zlib.proof.inflate.CaseCHECK5',
     'Require Import Zlib.proof.crc32.Combine.',
     'Require Import Zlib.proof.crc32.Combine.\nRequire Import Zlib.proof.za.inflate.AdlerZ.'),
    ('Zlib.proof.inflate.CaseCHECK5',
     '  clearbody c. entailer!.\n  unfold out_ok.',
     """  clearbody c.
  match goal with |- context [data_at ?sh t_strm (?a1, (?a2, (?a3, (?a4, (?a5, (?a6, (?a7, (?a8, (?a9, (?a10,
      (?a11, (?a12, (Vlong (Int64.repr ?y), ?a14))))))))))))) ?p] =>
    sep_apply (data_at_adler_val sh p a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a14
      (Vlong (Int64.repr y)) y (fun _ => eq_refl)) end.
  entailer!.
  unfold out_ok."""),
    # lemmas of other generated modules applied with their allocator and adler cell named (else they are evars
    # during the unification and the sentence runs for minutes)
    ('Zlib.proof.inflate.CaseCHECK5',
     'eapply semax_pre; [ | eapply (semax_needbits_seq5 F m m 32)].',
     'eapply semax_pre; [ | eapply (semax_needbits_seq5 (ZA:=ZA) (ZAV:=ZAV) F m m 32)].'),
    ('Zlib.proof.inflate.CaseCHECK5',
     '{ apply semax_needbits_CHECK5; auto; lia. }',
     '{ apply (semax_needbits_CHECK5 (ZA:=ZA) (ZAV:=ZAV)); auto; lia. }'),
    ('Zlib.proof.inflate.CaseLENGTH5',
     'eapply semax_pre; [ | eapply (semax_needbits_seq5 F m m 32)].',
     'eapply semax_pre; [ | eapply (semax_needbits_seq5 (ZA:=ZA) (ZAV:=ZAV) F m m 32)].'),
    ('Zlib.proof.inflate.CaseLENGTH5',
     '{ apply semax_needbits_LENGTH5; auto; lia. }',
     '{ apply (semax_needbits_LENGTH5 (ZA:=ZA) (ZAV:=ZAV)); auto; lia. }'),
]
