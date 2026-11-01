"""Configuration of docs/port-za/port.py for deflate() with next_in = Z_NULL (src/proof/deflate/DSpecN.v).

DSpec's representation of the z_stream puts `offset_val (z_next_in z) pin` in the next_in field and the input object
`data_at ish ... pin` in every specification that carries the input (read_buf, flush_pending, fill_window, the five
compressors, deflate): both are meaningless at pin = Z_NULL.  The port replaces them by DSpecN.in_ptrN (Z_NULL at
pin = Z_NULL) and DSpecN.in_objN (no object, no input bytes at pin = Z_NULL), which are the old ones when pin is not
Z_NULL; deflate's specification becomes DSpecN.deflate_specN.  Output: src/proof/dnull/ (modules
Zlib.proof.dnull.*), suffix _N.

The patches of the proofs (where a proof reads next_in or the input object: read_buf, deflate_stored's direct
copies, deflate's NULL test) are in docs/port-za/dnull/*.py, one file per group of modules, appended in the order
of their names.

Usage (from the repository root):  python3 docs/port-za/port_dnull.py (port.py with module names <X>_N)"""
import glob
import importlib.util
import os

SUFFIX = '_N'
OUT = 'dnull'
SECTION = None
REQUIRES = 'Require Import Zlib.proof.deflate.DSpecN.\n'
WHAT = 'next_in and the input object (DSpecN.in_ptrN, DSpecN.in_objN: Z_NULL and no object allowed),'

PREFIXES = ['Zlib.proof.deflate.']

TARGETS = [
    'Zlib.proof.deflate.Body_read_buf',
    'Zlib.proof.deflate.Body_flush_pending',
    'Zlib.proof.deflate.Body_fill_window',
    'Zlib.proof.deflate.Body_stored',
    'Zlib.proof.deflate.Body_fast',
    'Zlib.proof.deflate.Body_slow',
    'Zlib.proof.deflate.Body_rle',
    'Zlib.proof.deflate.Body_huff',
    'Zlib.proof.deflate.MainDeflate',
]

_NI = r'\((z_next_in [^()]*|z_next_in \([^()]*\))\)'
SUBST = [
    # the next_in field of the z_stream: Z_NULL when there is no input object
    (r'\(DOT _next_in\) \(offset_val ' + _NI + r' (pin|p_in)\)', r'(DOT _next_in) (in_ptrN \2 (\1))'),
]

PATCHES = [
    # the input object
    ('Zlib.proof.deflate.DRep',
     "(@data_at DCS.CS ish (tarray tuchar (Zlength (z_in z))) (map vi (z_in z)) p_in)%logic.",
     "in_objN ish (z_in z) p_in."),
    # deflate(): DSpecN.deflate_specN (the same text applies to deflateParams' specification)
    ('Zlib.proof.deflate.DSpec',
     "api_fields strmp (offset_val nin pin) ain tin pout (Zlength rest) tout msgv adler;\n"
     "       @data_at DCS.CS ish (tarray tuchar (Zlength inb)) (map vi inb) pin;",
     "api_fields strmp (in_ptrN pin nin) ain tin pout (Zlength rest) tout msgv adler;\n"
     "       in_objN ish inb pin;"),
    ('Zlib.proof.deflate.DSpec',
     "api_fields strmp (offset_val (z_next_in (snd (fst r))) pin) (z_avail_in (snd (fst r)))\n"
     "         (z_total_in (snd (fst r))) (offset_val (Zlength (z_out (snd (fst r)))) pout)\n"
     "         (z_avail_out (snd (fst r))) (z_total_out (snd (fst r))) msgv' (z_adler (snd (fst r)));\n"
     "       @data_at DCS.CS ish (tarray tuchar (Zlength inb)) (map vi inb) pin;",
     "api_fields strmp (in_ptrN pin (z_next_in (snd (fst r)))) (z_avail_in (snd (fst r)))\n"
     "         (z_total_in (snd (fst r))) (offset_val (Zlength (z_out (snd (fst r)))) pout)\n"
     "         (z_avail_out (snd (fst r))) (z_total_out (snd (fst r))) msgv' (z_adler (snd (fst r)));\n"
     "       in_objN ish inb pin;"),
]

_here = os.path.dirname(os.path.abspath(__file__))
for _f in sorted(glob.glob(os.path.join(_here, 'dnull', '*.py'))):
    _spec = importlib.util.spec_from_file_location('dnull_' + os.path.basename(_f)[:-3], _f)
    _mod = importlib.util.module_from_spec(_spec)
    _spec.loader.exec_module(_mod)
    SUBST = SUBST + list(getattr(_mod, 'SUBST', []))
    PATCHES = PATCHES + list(getattr(_mod, 'PATCHES', []))
