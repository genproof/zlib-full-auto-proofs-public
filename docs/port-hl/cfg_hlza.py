"""Configuration of docs/port-hl/port.py: the HEADLESS port of the allocator-generic, wide switch cases of inflate().

The allocator-generic port src/proof/za/ (docs/port-za/) proves the switch cases of inflate() and the body of
inflate_fast for calls of any uInt size (its machine invariant mwf3_za is InvW.mwf3W) with a caller-supplied
allocator.  Its memory, like Loop.mem_rep, holds the application's gz_header as Spec5's DEFINED head_rep
(Loop.head_part).  This port replaces Loop.head_part by the headless port's HlLoop.head_part_hl, whose header is
the atom RTHLoop.hnoneH = emp (docs/port-hl/cfg_inflate.py, src/proof/hl/): the header is then a frame
held by the caller, which the modes after the header (DICTID .. SYNC) and inflate_fast never touch.  The case
HCRC writes the header (head->hcrc, head->done): it is left out.  The ported files are src/proof/hlza/<dir>/Hz<stem>.v,
the ported names carry the suffix _hz; at zlib's allocator (SpecWLib.zc_alloc) the memory is the narrow headless
one of src/proof/hl (roundtrip/RTH9Fast.v)."""
import os as _os
import re as _re

PREFIXES = ['Zlib.proof.za.']
HL = 'Zlib.proof.hl.'

Z = 'Zlib.proof.za.inflate.'
# the case groups of the modes after the header (the statements Cases<Group>Z.v) and the body of inflate_fast
TARGETS = [Z + m for m in ['CasesHdZ', 'CasesTyZ', 'CasesStZ', 'CasesTlZ', 'CasesClZ', 'CasesLenZ', 'CasesLdZ',
                           'CasesDmZ', 'CasesCkZ', 'CasesEndZ']] + ['Zlib.proof.za.inffast.BodyF5']

SUFFIX = '_hz'
OUT = 'hlza'
STEM = 'Hz'
SECTION = None
REQUIRES = ''.join('Require %s.\n' % (HL + m) for m in
                   ['inflate.HlLoop', 'inflate.HlMtKit5', 'inflate.HlMtTail5', 'inffast.HlF5Len', 'inffast.HlF5Iter',
                    'inffast.HlF5Main', 'inffast.HlF5Copy'])
WHAT = ('the\n   application\'s gz_header (Loop.head_part), with the header replaced by RTHLoop.hnoneH = emp '
        '(HlLoop.head_part_hl)')

# the header of the memory: the headless port's (HlLoop.head_part_hl, whose header is RTHLoop.hnoneH = emp); the
# few definitions of the original proofs that hold the header and that the allocator-generic port uses unchanged
# (with their lemmas) are the headless port's too
_HLNAMES = [('inflate.HlLoop', 'head_part'), ('inffast.HlF5Len', 'lb_rest_nm'), ('inflate.HlMtKit5', 'mem_rep_mt'),
            ('inflate.HlMtTail5', 'mt_fin_rest'), ('inffast.HlF5Iter', 'rest_ms'), ('inffast.HlF5Iter', 'rest_ms_mode'),
            ('inffast.HlF5Main', 'rest_pro'), ('inffast.HlF5Copy', 'rest_x'), ('inffast.HlF5Copy', 'rest_x_bad')]
SUBST = [(r'(?<![.\w\'])%s\b' % n, HL + m + '.' + n + '_hl') for m, n in _HLNAMES]


def _hcrc_lemma():
    """The text of the case HCRC in the allocator-generic port (from its statement to its Qed), after SUBST."""
    src = open(_os.path.join(_os.path.dirname(_os.path.abspath(__file__)), '..', '..',
                             'src', 'proof', 'za', 'inflate', 'Cases5_HD.v')).read()
    i = src.index('Lemma case_HCRC5_za ')
    j = src.index('\nQed.\n', i) + len('\nQed.\n')
    txt = src[i:j]
    for pat, rep in SUBST:
        txt = _re.sub(pat, rep, txt)
    return txt


PATCHES = [
    # the case HCRC belongs to the header world: no lemma, no conjunct
    (Z + 'Cases5_HD', _hcrc_lemma(), ''),
    (Z + 'Cases5_HD',
     "  case_ok5_za F HCRC 8 /\\ (case_ok5_za F DICT 10 -> case_ok5_za F DICTID 9) /\\",
     "  (case_ok5_za F DICT 10 -> case_ok5_za F DICTID 9) /\\"),
    (Z + 'Cases5_HD',
     "  intros HF. split; [ | split].\n  - apply case_HCRC5_za; exact HF.\n",
     "  intros HF. split.\n"),
    (Z + 'CasesHdZ',
     "  case_ok5_za F HCRC 8 /\\ (case_ok5_za F DICT 10 -> case_ok5_za F DICTID 9) /\\",
     "  (case_ok5_za F DICT 10 -> case_ok5_za F DICTID 9) /\\"),
]
