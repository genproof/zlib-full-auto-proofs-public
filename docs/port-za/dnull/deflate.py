"""deflate(): its stages (Stage*.v) and the body (MainDeflate.v) with next_in = Z_NULL allowed.

Name resolution: a ported module requires DSpecN last, which re-exports DSpec and with it DModel2, whose
[df_body] (the model's loop body) then hides DeflateKit's [df_body] (the statement list of deflate's body) that
the stage proofs unfold.  The first ported declaration of each such module is preceded by a re-import of
DeflateKit, which restores the order of names of the original module (likewise Rep's flush constants, hidden
behind DState's).

The NULL test (StageEntry): `strm->avail_in != 0 && strm->next_in == Z_NULL` short-circuits at avail_in = 0;
with avail_in <> 0 there are input bytes (strm_ranges), so the input object exists and pin is a pointer
(in_objN at Z_NULL has no input bytes): the old argument applies.

The API's view of the stream (MainDeflate): next_in is in_ptrN pin nin and the input object in_objN, as in
DSpecN.deflate_specN."""

REIMPORT = ("(* DSpecN, required last, hides DeflateKit's df_body (deflate's statements) behind DModel2's *)\n"
            "Import Zlib.proof.deflate.DeflateKit.\n\n")

# the first ported declaration of each module that unfolds df_body or names a flush constant (Z_PARTIAL_FLUSH, ...)
FIRST = [
    ('Zlib.proof.deflate.StageEntry', "Lemma in_isptr ish z pin :"),
    ('Zlib.proof.deflate.StageZlib', "Lemma zlib_close s om z z3 ob3 m3 po3 lf p pin pout ish R msgv gv :"),
    ('Zlib.proof.deflate.StageGzip', "Lemma dfull_close_gen s z0 z ob m po gi st lf p pin pout ish R msgv gv :"),
    ('Zlib.proof.deflate.StageExtra', "Lemma ff_close s z0 z3 st g lf ob m po p pin pout ish R msgv gv :"),
    ('Zlib.proof.deflate.StageName', "Definition fr_nogz (s : dstate)"),
    ('Zlib.proof.deflate.StageCompress', "Definition dfull_nolvl (s : dstate)"),
    ('Zlib.proof.deflate.StageHcrc', "Lemma dfull_close_gen s z0 z ob m po gi st lf p pin pout ish R msgv gv :"),
    ('Zlib.proof.deflate.StageTrailer', "Lemma semax_ret_const {Espec: OracleKind}"),
    ('Zlib.proof.deflate.MainDeflate', "Lemma dfull_build s p gv pin ish inb nin ain tin pout rest tout msgv msg adler :"),
]

E = 'Zlib.proof.deflate.StageEntry'
M = 'Zlib.proof.deflate.MainDeflate'

PATCHES = [(m, old, REIMPORT + old) for (m, old) in FIRST] + [
    # next_in's NULL test: pin is a pointer when there are input bytes
    (E, "Lemma in_isptr ish z pin : in_obj ish z pin |-- !! isptr pin && in_obj ish z pin.\n"
        "Proof. unfold in_obj. entailer!. Qed.",
        "Lemma in_isptr ish z pin : in_obj ish z pin |-- !! (z_in z <> [] -> isptr pin) && in_obj ish z pin.\n"
        "Proof.\n"
        "  unfold in_obj, in_objN. destruct (eq_dec pin nullval) as [Pnull | Pnn].\n"
        "  - Intros. entailer!.\n"
        "  - entailer!.\n"
        "Qed."),
    (E, "  intros Hsh Hz Ha. open_zranges Hz. unfold in_obj.\n",
        "  intros Hsh Hz Ha. open_zranges Hz. unfold in_obj, in_objN.\n"
        "  destruct (eq_dec pin nullval) as [Pnull | Pnn].\n"
        "  { (* no input object: no input bytes, against avail_in <> 0 *)\n"
        "    Intros. exfalso. match goal with Hi : z_in z = [] |- _ => rewrite Hi, Zlength_nil in * end. lia. }\n"),
    (E, "    forward_if.\n    - forward.\n",
        "    forward_if.\n"
        "    - assert (Pp : isptr pin).\n"
        "      { match goal with Hi : z_in z <> [] -> isptr pin |- _ => apply Hi end.\n"
        "        intro Ei. open_zranges H. rewrite Ei, Zlength_nil in *.\n"
        "        assert (z_avail_in z <> 0) by (intro E0; rewrite E0 in *; contradiction). lia. }\n"
        "      assert (Ep : in_ptrN pin (z_next_in z) = offset_val (z_next_in z) pin).\n"
        "      { unfold in_ptrN. destruct (eq_dec pin nullval); [subst; contradiction | reflexivity]. }\n"
        "      rewrite Ep.\n"
        "      forward.\n"),
    # the join point keeps next_in as in_ptrN
    (E, "      forward. entailer!. destruct pin; try contradiction. reflexivity.\n",
        "      forward. entailer!.\n"
        "      + destruct pin; try contradiction. reflexivity.\n"
        "      + rewrite Ep. apply derives_refl.\n"),
]

# the API's next_in and input object (dfull_build, dfull_close, the body)
_ON = "(offset_val nin pin)"
_IN = "(in_ptrN pin nin)"
PATCHES += [
    (M, "api_fields (p_strm p) (offset_val nin pin) ain tin pout (Zlength rest) tout msgv adler *\n"
        "  @data_at DCS.CS ish (tarray tuchar (Zlength inb)) (map vi inb) pin *",
        "api_fields (p_strm p) (in_ptrN pin nin) ain tin pout (Zlength rest) tout msgv adler *\n"
        "  in_objN ish inb pin *"),
    (M, "api_fields (p_strm p) (offset_val (z_next_in z1) pin)", "api_fields (p_strm p) (in_ptrN pin (z_next_in z1))"),
    (M, "      @data_at DCS.CS ish (tarray tuchar (Zlength inb)) (map vi inb) pin *", "      in_objN ish inb pin *"),
    (M, "api_fields_split strmp " + _ON, "api_fields_split strmp " + _IN),
    (M, "za, zf, offset_val nin pin, gv)", "za, zf, in_ptrN pin nin, gv)"),
    (M, "api_fields_join strmp " + _ON, "api_fields_join strmp " + _IN),
    (M, "api_fields_split (p_strm p) " + _ON, "api_fields_split (p_strm p) " + _IN),
    (M, "zcf gv, offset_val nin pin, gv)", "zcf gv, in_ptrN pin nin, gv)"),
    (M, "api_fields_join (p_strm p) " + _ON, "api_fields_join (p_strm p) " + _IN),
    (M, "           api_fields (p_strm p) " + _ON + " ain", "           api_fields (p_strm p) " + _IN + " ain"),
    (M, "           data_at ish (tarray tuchar (Zlength inb)) (map vi inb) pin;", "           in_objN ish inb pin;"),
]
