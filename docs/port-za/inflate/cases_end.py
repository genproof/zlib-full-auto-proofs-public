"""Patches of the inflate port, part cases, group end: see docs/port-za/inflate/cases.py."""

PATCHES = [
    # mwf3_za of the machine after `state->mode = LEN`: the swf3 part as before; hdrW is vacuous since LEN is
    # neither EXLEN nor EXTRA
    ('Zlib.proof.inflate.CaseLEN_5',
     '    - apply swf3_set_mode_decode5; [exact W2 | exact D | right; left; reflexivity]. }',
     '    - split; [apply swf3_set_mode_decode5; [exact (proj1 W2) | exact D | right; left; reflexivity] |\n'
     '        unfold Zlib.proof.inflate.InvW.hdrW; split; intros Hm; cbn in Hm; exfalso;\n'
     '        cbv [LEN EXLEN EXTRA] in Hm; discriminate Hm]. }'),
]
