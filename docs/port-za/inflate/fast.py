"""Patches of the inflate port (docs/port-za/cfg_inflate.py), part fast: see docs/port-za/inflate/README.md."""

# strm->zalloc / strm->zfree are the allocator's values za_alloc / za_free (no longer the globals zcalloc /
# zcfree): the proofs name them before the stream's representation is unfolded
_RA = "remember (f_gv F inflate.code._zcalloc) as zca eqn:EZA."
_RF = "remember (f_gv F inflate.code._zcfree) as zcf eqn:EZF."
_NA = "remember (@za_alloc ZA) as zca eqn:EZA."
_NF = "remember (@za_free ZA) as zcf eqn:EZF."

PATCHES = [
    ('Zlib.proof.inffast.%s' % m, old, new)
    for m in ['F5Iter', 'F5Copy', 'F5Main', 'F5Len']
    for old, new in [(_RA, _NA), (_RF, _NF)]
] + [
    # the wide machine invariant: a plain cbn unfolds Int.max_unsigned to a literal and auto then searches
    # for minutes; keep it folded so that auto closes the bound from the hypothesis
    ('Zlib.proof.inffast.F5Iter', "destruct W; constructor; cbn; auto. Qed.",
     "destruct W; constructor; cbn -[Int.max_unsigned]; auto. Qed."),
    ('Zlib.proof.inffast.F5Iter', "destruct W; constructor; cbn; auto; try lia.",
     "destruct W; constructor; cbn -[Int.max_unsigned]; auto; try lia."),
    # the epilogue (avail_in / avail_out from the pointer differences, computed in 64 bits) for the wide
    # bounds |input|, avail_out <= 2^32-1
    ('Zlib.proof.inffast.F5Main',
     "Zlength (m_inp m0) <= Int.max_signed -> m_aout m0 <= Int.max_signed ->",
     "Zlength (m_inp m0) <= Int.max_unsigned -> m_aout m0 <= Int.max_unsigned ->"),
    ('Zlib.proof.inffast.F5Main',
     "assert (INR': Zlength (m_inp m') <= Int.max_signed)",
     "assert (INR': Zlength (m_inp m') <= Int.max_unsigned)"),
    ('Zlib.proof.inffast.F5Main',
     "assert (AOR': m_aout m' <= Int.max_signed)",
     "assert (AOR': m_aout m' <= Int.max_unsigned)"),
]
