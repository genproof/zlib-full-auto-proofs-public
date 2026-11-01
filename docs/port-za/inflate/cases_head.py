"""Patches of the inflate port, part cases, group head: see docs/port-za/inflate/cases.py."""

PATCHES = [
    # mwf3_za = mwf_za /\ swf3 /\ InvW.hdrW: the swf3 conjunct is one level deeper
    ('Zlib.proof.inflate.HeadGzipW5',
     '  intros m [_ S3] HM Hw Hb.',
     '  intros m [_ [S3 _]] HM Hw Hb.'),
    # the stream's zalloc / zfree members are the allocator's values za_alloc / za_free
    ('Zlib.proof.inflate.HeadZlib7',
     '  remember (f_gv F _zcalloc) as zca eqn:Hzca; remember (f_gv F _zcfree) as zcf eqn:Hzcf;',
     '  remember za_alloc as zca eqn:Hzca; remember za_free as zcf eqn:Hzcf;'),
    ('Zlib.proof.inflate.HeadZlib7',
     '  remember (f_gv F _zcalloc) as zca eqn:Hzca. remember (f_gv F _zcfree) as zcf eqn:Hzcf.',
     '  remember (@za_alloc ZA) as zca eqn:Hzca. remember (@za_free ZA) as zcf eqn:Hzcf.'),
    # case HEAD's zlib branch stores the check value into strm->adler, which the representation holds as the
    # adler cell (adler_val): weaken the stored Vlong with AdlerZ.data_at_adler_val
    ('Zlib.proof.inflate.HeadZlib7',
     'Require Import Zlib.proof.crc32.Spec Zlib.proof.adler32.Spec.',
     'Require Import Zlib.proof.crc32.Spec Zlib.proof.adler32.Spec.\nRequire Import Zlib.proof.za.inflate.AdlerZ.'),
    ('Zlib.proof.inflate.HeadZlib7',
     '  rewrite Em; rewrite (zl_shl1 len) by lia;\n  rewrite <- Hzca, <- Hzcf; entailer!.',
     """  rewrite Em; rewrite (zl_shl1 len) by lia;
  rewrite <- Hzca, <- Hzcf;
  match goal with |- context [data_at ?sh t_strm (?a1, (?a2, (?a3, (?a4, (?a5, (?a6, (?a7, (?a8, (?a9, (?a10,
      (?a11, (?a12, (Vlong (Int64.repr ?y), ?a14))))))))))))) ?p] =>
    sep_apply (data_at_adler_val sh p a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a14
      (Vlong (Int64.repr y)) y (fun _ => eq_refl)) end;
  entailer!."""),
    # lemmas of other generated modules applied with their allocator and adler cell given (else they are
    # evars during the unification and the sentence runs for minutes)
    ('Zlib.proof.inflate.Cases5_HEAD',
     'apply (head_gzip5_w F m0 m1 _ HF W HL HN)',
     'apply (head_gzip5_w (ZA:=ZA) (ZAV:=ZAV) F m0 m1 _ HF W HL HN)'),
    ('Zlib.proof.inflate.Cases5_HEAD',
     'reflexivity. }\n      rewrite G in E.\n      eapply semax_pre; [ | apply (head_zlib7_w F m0 m1 R HF W HL HN HR E)].',
     'reflexivity. }\n      rewrite G in E.\n      eapply semax_pre; [ | apply (head_zlib7_w (ZA:=ZA) (ZAV:=ZAV) F m0 m1 R HF W HL HN HR E)].'),
    ('Zlib.proof.inflate.Cases5_HEAD',
     'discriminate]. }\n      rewrite G in E.\n      eapply semax_pre; [ | apply (head_zlib7_w F m0 m1 R HF W HL HN HR E)].',
     'discriminate]. }\n      rewrite G in E.\n      eapply semax_pre; [ | apply (head_zlib7_w (ZA:=ZA) (ZAV:=ZAV) F m0 m1 R HF W HL HN HR E)].'),
    ('Zlib.proof.inflate.Cases5_HEAD',
     'eapply (semax_needbits_seq_r5 F m m 16).\n  - apply semax_needbits_HEAD5;',
     'eapply (semax_needbits_seq_r5 (ZA:=ZA) (ZAV:=ZAV) F m m 16).\n  - apply (semax_needbits_HEAD5 (ZA:=ZA) (ZAV:=ZAV));'),
]
