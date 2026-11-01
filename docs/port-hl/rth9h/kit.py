"""Patches of docs/port-hl/cfg_rth9h.py, group kit (the NEEDBITS loops, the header kits): see the configuration's
header."""

# the input count of the wide machine invariant is bounded by Int.max_unsigned (RTH9WKit.mwf9), no longer by
# Int.max_signed (as docs/port-za/inflate/kit.py)
_HAVE = ('      assert (HH: 0 <= m_have (pullk k m) <= Int.max_signed) by (unfold m_have; rewrite P3, P10; lia).',
         '      assert (HH: 0 <= m_have (pullk k m) <= Int.max_unsigned) by (unfold m_have; rewrite P3, P10; lia).')

PATCHES = [
    ('Zlib.proof.roundtrip.' + m,) + _HAVE
    for m in ['RTHNeedBits', 'RTHNeedBits_5', 'RTHNeedBits1_5', 'RTHNeedBits2_5']
]
