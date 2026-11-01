"""deflate_huff: in the port's scope (DSpecN imported last) the short name Z_NO_FLUSH no longer denotes the flush
constant of the model, so the unfold is written with the qualified name Rep.Z_NO_FLUSH."""

M = 'Zlib.proof.deflate.Body_huff'
PATCHES = [
    (M, "        unfold Z_NO_FLUSH in Hrf.", "        unfold Rep.Z_NO_FLUSH in Hrf."),
]
