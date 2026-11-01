"""Patches of the inflate port (docs/port-za/cfg_inflate.py), part cases: see docs/port-za/inflate/README.md.

The case modules are split into groups, one patch file docs/port-za/inflate/cases_<group>.py each (PATCHES),
so that each group's patches sit next to each other:
  head: HeadGzipKit5, HeadGzipW5, HeadZlib7, Cases5_HEAD
  fto:  HdrKit5, HdrCrc5, HdrSame5, CaseFLAGS5, CaseOS5, CaseTIME5, Cases5_FTO
  ex:   ExHdrKit5, ExHdrCrc5, ExHdrSame5, ExKit5, CaseEXLEN5, ExtraKit5, ExtraBody5, CaseEXTRA5, Cases5_EX
  nc:   NCKit5, NCCrc5, NCLoop5, NCMach5, CaseNAME5, CaseCOMMENT5, Cases5_NC
  hd:   Cases5_HD
  ty:   Cases5_TY
  st:   STKit5, CaseCOPY5, CaseSTORED5, Cases5_ST
  tl:   LLDefs5, TLFacts, TLKit5, LLLoop5, LLTail5, LLZero5, CaseLENLENS5, CaseTABLE5, Cases5_TL
  cl:   CLKit5, CLDists5, CLFill5, CLLens5, CLLookup5, CLRepNB5, CLRepBr5, CLRep5, CLSmall5, CLTabFacts5,
        CLWhile5, Cases5_CL
  dm:   DmKit5, MtKit5, MtSel5, MtTail5, CaseMATCH5, DxNb5, DxRest5, DxCase5, MtLoopO5, MtLoopW5, Cases5_DM
  ld:   LdKit5, DsLink5, DsLoop1_5, DsLoop2_5, DsTab5, DsTail5, LdLenext5, LdNb5, Cases5_LD
  len:  LnKit5, LnCase5, LnFast5, LnLoop1_5, LnLoop2_5, LnTab5, LnTail5 (the LEN case's parts: their assembly
        is src/proof/za/inflate/CasesLenZ.v, by hand)
  ck:   CKKit5, CaseCHECK5, CaseLENGTH5, Cases5_CK
  end:  CaseLIT5, CaseEnd, CaseEnd5, CaseLEN_5
The modules below them that several groups share are the part kit (docs/port-za/inflate/kit.py)."""
import importlib.util as _ilu
import os as _os

GROUPS = ['head', 'fto', 'ex', 'nc', 'hd', 'ty', 'st', 'tl', 'cl', 'dm', 'ld', 'len', 'ck', 'end']


def _group(name):
    path = _os.path.join(_os.path.dirname(_os.path.abspath(__file__)), 'cases_' + name + '.py')
    spec = _ilu.spec_from_file_location('cfg_inflate_cases_' + name, path)
    mod = _ilu.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod.PATCHES


PATCHES = []
for _g in GROUPS:
    PATCHES += _group(_g)
