"""Patches of the inflate port (docs/port-za/cfg_inflate.py), part kit: see docs/port-za/inflate/README.md.

The kit is the layer below the case groups that several groups share (the NEEDBITS loops, the return and
mode lemmas, the case kits)."""

# the input count of the wide machine invariant is bounded by Int.max_unsigned (mwf_za), no longer by
# Int.max_signed
_HAVE = ('      assert (HH: 0 <= m_have (pullk k m) <= Int.max_signed) by (unfold m_have; rewrite P3, P10; lia).',
         '      assert (HH: 0 <= m_have (pullk k m) <= Int.max_unsigned) by (unfold m_have; rewrite P3, P10; lia).')

PATCHES = [
    ('Zlib.proof.inflate.' + m,) + _HAVE
    for m in ['NeedBits', 'NeedBits_5', 'NeedBits1_5', 'NeedBits2_5', 'NeedBits3_5']
] + [
    # rewriting with a lemma of another generated module: its allocator arguments given explicitly (as evars
    # the rewrite's matching takes minutes)
    ('Zlib.proof.inflate.CaseKitT5',
     "  rewrite (case_post2_eq F m m' E). rewrite <- HT.",
     "  rewrite (@case_post2_eq ZA ZAV F m m' E). rewrite <- HT."),
]
