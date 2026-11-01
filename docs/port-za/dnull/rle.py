"""deflate_rle: in the ported RleScan the name MAX_MATCH resolves to DState.MAX_MATCH (the port's imports come in
another order), while rs_tail is stated with Rep.MAX_MATCH; both are 258, but the rewrite with the match-length
equation needs the same constant, so the proof names Rep.MAX_MATCH explicitly."""

M = 'Zlib.proof.deflate.RleScan'
PATCHES = [
    (M, "unfold MAX_MATCH in Hl.", "unfold Rep.MAX_MATCH in Hl."),
    (M, "assert (Em : u32 (MAX_MATCH - u32 (d_strstart s + MAX_MATCH - sf)) = sf - d_strstart s).\n"
        "      { unfold MAX_MATCH.",
     "assert (Em : u32 (Rep.MAX_MATCH - u32 (d_strstart s + Rep.MAX_MATCH - sf)) = sf - d_strstart s).\n"
     "      { unfold Rep.MAX_MATCH."),
]
