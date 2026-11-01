"""Configuration of docs/port-hl/port.py: the zlib branch of inflate()'s case HEAD (src/proof/inflate/HeadZlib7.v)
on the loop state WITHOUT the application's gz_header (RTHLoop.loop_stateH).

Round 1 proved case HEAD of the header world only for a call that passes the header (the gzip branch); the zlib
branch (head->done = -1, then the zlib header's checks) was excluded.  Its steps after `head->done = -1` do not touch
the header, so HeadZlib7.v's lemmas hold of the headless loop state as they are: the port renames Loop.loop_state,
Loop.mem_rep, Loop.head_part and Loop2.case_post2 to RTHLoop's / RTHLoop2's loop_stateH, mem_repH, head_partH and
case_post2H.  The write `head->done = -1` needs the header itself (held next to the loop state by the header cases):
its lemma zl_hd_ok and the whole branch head_zlib7_w, which uses it, are left out; the header case
(src/proof/roundtrip/RTH9HHeadKit.v) proves that write with the header's memory and composes the rest from the ported
lemmas.
Run from the repository root:  python3 docs/port-hl/port.py rth9hz  (--check: compare with the file)."""

PREFIXES = ['Zlib.proof.inflate.HeadZlib7']

TARGETS = ['Zlib.proof.inflate.HeadZlib7']

SUFFIX = '_h9z'
OUT = 'hl9h'
STEM = 'H9Z'
SECTION = None
REQUIRES = ('Require Import Zlib.proof.roundtrip.RTHLoop.\n'
            'Require Import Zlib.proof.roundtrip.RTHLoop2.\n')
WHAT = ('the\n   application\'s gz_header (Loop.head_part in Loop.loop_state), with the headless loop state '
        'RTHLoop.loop_stateH\n   (RTHLoop2.case_post2H) in its place')

SUBST = [
    (r'\bloop_state\b', 'loop_stateH'),
    (r'\bmem_rep\b', 'mem_repH'),
    (r'\bhead_part\b', 'head_partH'),
    (r'\bcase_post2\b', 'case_post2H'),
]

PATCHES = []

DROP = {'Zlib.proof.inflate.HeadZlib7': ['zl_hd_ok', 'head_zlib7_w']}
