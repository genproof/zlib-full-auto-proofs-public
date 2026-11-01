"""Configuration of docs/port-hl/port.py: the header cases HEAD .. HCRC of inflate() for calls of any uInt size
with an application header of any uInt buffer sizes, every branch (RTH9HDefs.cases9h_all).

The sources are those of round 1's cfg_rth8w.py (round 1's header cases with the partial header RTHSpec.head_rep6 and their
kits).  Two things change:
- the machine invariant: Inv.mwf / Inv3.mwf3 become RTH9WKit.mwf9 / mwf39 (avail_in and avail_out up to 2^32 - 1
  as InvW.mwfW, header buffers of any uInt size as RTH8WKit.hwf8r, and InvW.hdrW in mwf39 as in InvW.mwf3W); the
  proofs read the invariant through its projections, so the port renames mwf / hwf and their projections and
  lemmas to RTH9WKit's (mwf9, hwf8r, mw9_*, h8_*, mwf9_*, mwf39_*);
- the statement: round 1's cases assumed a call that passes the header (RTHSpec.hpass / RTH8Spec.hpass8), which
  excluded the branches that leave (NEEDBITS or a copy loop out of input) or leave the header modes without
  passing the header (bad method, flags or header CRC; HEAD's zlib branch; wrap 0).  Here (RTH9WKit.case_ok9v)
  there is no such premise and the post is RTH9HDefs.case_post9 (the header RTH9HDefs.hd9): those branches are
  proved by the patches.
The ported files sit under src/proof/hl9h/ with the stem prefix H9H and the suffix _h9h; RTH9Hdr.v assembles
RTH9HDefs.cases9h_all from the parts (RTH9WKit.cases9h_all_of_parts).

The patches are split by group, one file docs/port-hl/rth9h/<group>.py each (PATCHES, DROP):
  kit:  RTHNeedKit, RTHNeedKit5, RTHNeedBits, RTHNeedBits_5, RTHNeedBits1_5, RTHNeedBits2_5, RTHHeadGzipW5,
        RTHHdrKit5, RTHHdrCrc5, RTHExHdrKit5, RTHEx6Base, RTHExHdrCrc5
  head: RTHHEADKit6, RTHCaseHEAD6
  fto:  RTHFTO6, RTHCasesFTO6
  ex:   RTHEx6Kit, RTHEXLEN6, RTHEXTRA6Mb, RTHEXTRA6Cpy, RTHEXTRA6, RTHCasesEX6
  nc:   RTHNC6Kit, RTHNC6Facts, RTHNC6Loop, RTHNC6Mach, RTHCaseCOMMENT6, RTHCaseNAME6, RTHCasesNC6
  hcrc: RTHCaseHCRC6, RTH8CaseHCRC
Run from the repository root:  python3 docs/port-hl/port.py rth9h  (--check: compare with the files)."""
import importlib.util as _ilu
import os as _os

R = 'Zlib.proof.roundtrip.'

PREFIXES = [R + m for m in [
    'RTHNeedKit', 'RTHNeedKit5', 'RTHNeedBits', 'RTHNeedBits_5', 'RTHNeedBits1_5', 'RTHNeedBits2_5',
    'RTHHeadGzipW5', 'RTHHdrKit5', 'RTHHdrCrc5', 'RTHExHdrKit5', 'RTHEx6Base', 'RTHExHdrCrc5',
    'RTHHEADKit6', 'RTHCaseHEAD6', 'RTHFTO6', 'RTHCasesFTO6', 'RTHEx6Kit', 'RTHEXLEN6', 'RTHEXTRA6Mb',
    'RTHEXTRA6Cpy', 'RTHEXTRA6', 'RTHCasesEX6', 'RTHNC6Kit', 'RTHNC6Facts', 'RTHNC6Loop', 'RTHNC6Mach',
    'RTHCaseCOMMENT6', 'RTHCaseNAME6', 'RTHCasesNC6', 'RTHCaseHCRC6', 'RTH8CaseHCRC']]

TARGETS = [R + 'RTHCaseHEAD6', R + 'RTHCasesFTO6', R + 'RTHCasesEX6', R + 'RTHCasesNC6', R + 'RTH8CaseHCRC']

SUFFIX = '_h9h'
OUT = 'hl9h'
STEM = 'H9H'
SECTION = None
REQUIRES = ('Require Import Zlib.proof.roundtrip.RTH8Spec.\n'
            'Require Import Zlib.proof.roundtrip.RTH8Defs.\n'
            'Require Import Zlib.proof.roundtrip.RTH8WKit.\n'
            'Require Import Zlib.proof.roundtrip.RTH9HDefs.\n'
            'Require Import Zlib.proof.roundtrip.RTH9WKit.\n')
WHAT = ('the\n   machine invariant (Inv3.mwf3 with the header cap of Inv.hwf and the narrow input), with RTH9WKit.mwf39 '
        '(calls and\n   header buffers of any uInt size) in its place, and the header pass (RTHSpec.hpass, '
        'RTHCase.case_ok6), with\n   RTH9WKit.case_ok9v (every branch, RTH9HDefs.case_post9) in its place')

SUBST = [
    # the statement: every branch, the header hd9
    (r'\bRTHCase\.case_ok6\b', 'case_ok9v'),
    (r'\bunfold post6\b', 'unfold post9, hd9'),
    (r'\bunfold post8, hd8\b', 'unfold post9, hd9'),
    (r'\bpost[68]\b', 'post9'),
    (r'\bcase_post[68]\b', 'case_post9'),
    (r'\bcase_post[68]_eq\b', 'case_post9_eq'),
    (r'\bcase_ok[68]\b', 'case_ok9v'),
    (r'\bcase_fallthrough[68]\b', 'case_fallthrough9v'),
    (r'\bfall_post6\b', 'fall_post9v'),
    (r'\brth_(head|fto|ex|nc|hcrc)_stmt8?\b', r'rth_\1_stmt9v'),
    # the machine invariant for calls and header buffers of any uInt size
    (r'\bmwf3\b', 'mwf39'),
    (r'\bmwf3_(\w+)', r'mwf39_\1'),
    (r'\bmwf\b', 'mwf9'),
    (r'\bmwf_(\w+)', r'mwf9_\1'),
    (r'\bhwf\b', 'hwf8r'),
    (r'\bhwf_(\w+)', r'hwf8_\1'),
    (r'\bmw_(\w+)', r'mw9_\1'),
    (r'\bhw_(\w+)', r'h8_\1'),
    (r'\bhead_gzip_nowin\b', 'head_gzip_nowin9'),
]

GROUPS = ['kit', 'head', 'fto', 'ex', 'nc', 'hcrc']


def _group(name):
    """the patches of one group (docs/port-hl/rth9h/<name>.py: PATCHES, optional DROP), None when the group has no
    file yet"""
    path = _os.path.join(_os.path.dirname(_os.path.abspath(__file__)), 'rth9h', name + '.py')
    if not _os.path.exists(path):
        return None
    spec = _ilu.spec_from_file_location('cfg_rth9h_' + name, path)
    mod = _ilu.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


PATCHES = []
DROP = {}
for _g in GROUPS:
    _m = _group(_g)
    if _m is None:
        continue
    PATCHES += _m.PATCHES
    DROP.update(getattr(_m, 'DROP', {}))
