"""Patches of docs/port-hl/cfg_rth9h.py, group nc (the cases NAME and COMMENT): see the configuration's header.

Round 1 excluded the two leave branches of NAME and COMMENT with the header pass (RTHSpec.hpass_noleave_set):
`if (have == 0) goto inf_leave;` before the do-while and `if (len) goto inf_leave;` after a do-while that read all
the input without meeting the zero byte.  Here they are proved (src/proof/roundtrip/RTH9HNcKit.v): the model
breaks with leave = 1 in the same header mode, the header stays partial (hd6), after the do-while with the bytes
stored so far (RTH9HNcKit.hd6_name_leave / hd6_comm_leave)."""

R = 'Zlib.proof.roundtrip.'


# the statement RTH9WKit.case_ok9v has no header pass (no n, no hpass premise)
def _intro(mod, nxt, idx):
    return [
        (R + mod,
         'intros [FOK FR] HY m n HM HL [W W2] HD HH HP.',
         'intros [FOK FR] HY m HM HL [W W2] HD HH.'),
        (R + mod,
         'apply (case_fallthrough9v F m n IM.%s %d); [lia | reflexivity | rewrite HM; reflexivity | exact HP | exact HY | ].'
         % (nxt, idx),
         'apply (case_fallthrough9v F m IM.%s %d); [lia | exact HY | ].' % (nxt, idx)),
    ]


def _leaves(mod, mode, stepf2, have0, fin, leave_lem, eq, eqdef, mode_lem, buf, hdr_args):
    return [
        (R + mod,
         'Require Import Zlib.proof.crc32.Spec.',
         'Require Import Zlib.proof.crc32.Spec.\nRequire Import Zlib.proof.roundtrip.RTH9HNcKit.'),
        # no input: `goto inf_leave` with the machine and its header unchanged but leave = 1
        (R + mod,
         '    - exfalso. apply (hpass_noleave_set _ n m m HP); [rewrite HM; reflexivity | ].\n'
         '      rewrite (%s _ _ _ m HM). apply %s; auto.\n' % (stepf2, have0),
         '    - forward. forward.\n'
         '      apply (brk9_hdr F m (set_leave m));\n'
         '        [rewrite (%s _ _ _ m HM); apply %s; auto\n'
         '        | change (hdr_mode (m_mode m) = true); rewrite HM; reflexivity | reflexivity | ].\n'
         '      change (hd6 F (set_leave m)) with (hd6 F m). change (hdr_tok F (set_leave m)) with (hdr_tok F m).\n'
         '      unfold PP, LL, SL6. cbn [set_leave set_m_leave m_s m_h m_leave m_inp m_aout m_nx m_ow].\n'
         '      entailer!; apply derives_refl.\n' % (stepf2, have0)),
        # the do-while read all the input without a zero byte: `goto inf_leave` after the bytes stored so far
        (R + mod,
         '        exfalso. apply (hpass_noleave_set _ n m m3 HP); [rewrite HM; reflexivity | ].\n'
         '        rewrite (%s _ _ _ m HM), Ecase. rewrite (proj2 (Z.eqb_neq _ _) Hb). reflexivity.\n' % stepf2,
         '        forward. forward.\n'
         '        sep_apply (%s F m c b ln bf %s HM HH HI HPR (proj1 (%s _ HW)) ltac:(lia) ZS Hb\n'
         '                     HL1 H3).\n'
         '        apply (brk9_hdr F m (set_leave m3)).\n'
         '        { rewrite (%s _ _ _ m HM), Ecase. rewrite (proj2 (Z.eqb_neq _ _) Hb). reflexivity. }\n'
         '        { change (m_mode (set_leave m3)) with (m_mode m3). unfold m3. rewrite %s, HM. reflexivity. }\n'
         '        { change (hdr_tok F (set_leave m3)) with (hdr_tok F m3). exact T3. }\n'
         '        unfold PP, LL, SL6, m3. rewrite %s. unfold %s. rewrite IB.\n'
         '        mnorm_goal.\n'
         '        fin_tac.\n' % (leave_lem, hdr_args, buf, stepf2, mode_lem, eq, eqdef)),
    ]


PATCHES = [
    # the do-while of NAME / COMMENT with a buffer of any uInt size (length < max <= Int.max_unsigned), as
    # round 1's docs/port-hl/cfg_rth8w.py
    (R + 'RTHNC6Loop',
     "0 < have <= Int.max_unsigned -> 0 <= L0 <= max -> max <= 65536 ->",
     "0 < have <= Int.max_unsigned -> 0 <= L0 <= max -> max <= Int.max_unsigned ->"),
    (R + 'RTHCaseNAME6',
     'The leave branches\n   contradict hpass. *)',
     'The leave branches\n   return in mode NAME with the name stored so far (RTH9HNcKit). *)'),
    (R + 'RTHCaseCOMMENT6',
     'The leave branches contradict hpass. *)',
     'The leave branches return in mode COMMENT with the comment stored so far (RTH9HNcKit). *)'),
] + _intro('RTHCaseNAME6', 'COMMENT', 6) + _intro('RTHCaseCOMMENT6', 'HCRC', 7) \
  + _leaves('RTHCaseNAME6', 'NAME', 'stepf2_NAME', 'c_NAME2_have0', None, 'hd6_name_leave', 'nm_name_eq', 'nm3',
            'nm_name_mode', 'h8_nbuf', 'vt vtm vxf vos vxl vhc lx ln0 ln1 lc') \
  + _leaves('RTHCaseCOMMENT6', 'COMMENT', 'stepf2_COMMENT', 'c_COMMENT2_have0', None, 'hd6_comm_leave',
            'cm_comment_eq', 'cm3', 'cm_comment_mode', 'h8_cbuf', 'vt vtm vxf vos vxl vhc lx ln0 lc lc1')
