"""read_buf: with len > 0 there is input (avail_in > 0), so next_in is not Z_NULL and the input object exists."""

M = 'Zlib.proof.deflate.Body_read_buf'
PATCHES = [
    (M, "    unfold in_obj.\n",
     "    unfold in_obj, in_objN, in_ptrN.\n"
     "    destruct (eq_dec pin nullval) as [Pnull | Pnn].\n"
     "    { (* no input object: no input bytes, against len > 0 *)\n"
     "      Intros. exfalso. match goal with Hz : z_in z = [] |- _ => rewrite Hz, Zlength_nil in Hend end. lia. }\n"),
    (M, "field_at Ews t_strm (DOT _next_in) (in_ptrN pin (z_next_in z)) strmp;",
     "field_at Ews t_strm (DOT _next_in) (offset_val (z_next_in z) pin) strmp;"),
    (M, "    unfold strm_in_at, in_obj. simpl.\n",
     "    unfold strm_in_at, in_obj, in_objN, in_ptrN. destruct (eq_dec pin nullval); [contradiction |]. simpl.\n"),
]
