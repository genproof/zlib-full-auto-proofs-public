"""Configuration of docs/port-za/port.py for deflate.c: the bodies that the laws with a caller-supplied
allocator need under the allocator-generic representation (deflate(), the compressors, the leaves,
deflateStateCheck, deflateResetKeep, deflateReset).  deflateInit2_ and deflateEnd, which call the allocator,
are proved by hand next to the generated files (src/proof/za/deflate/)."""

# modules whose declarations may be ported
PREFIXES = ['Zlib.proof.deflate.']

# what the laws need
TARGETS = [
    'Zlib.proof.deflate.MainDeflate',
    'Zlib.proof.deflate.Body_stored',
    'Zlib.proof.deflate.Body_compress',
    'Zlib.proof.deflate.Body_window',
    'Zlib.proof.deflate.Body_leaf',
    'Zlib.proof.deflate.Api_resetkeep9',
    'Zlib.proof.deflate.Api_reset9',
    'Zlib.proof.deflate.Obligations9',
    'Zlib.proof.deflate.Api_toend',
]

# the allocator's values in the z_stream (DRep.strm_at / strm_in_at, DSpec.dstream*, the frames of the kits)
SUBST = [
    (r'\(gv _zcalloc\)', 'za_alloc'),
    (r'\(gv _zcfree\)', 'za_free'),
    (r'\bgv _zcalloc\b', 'za_alloc'),
    (r'\bgv _zcfree\b', 'za_free'),
    (r'\(DOT _opaque\) nullval', '(DOT _opaque) za_opaque'),
    # deflateStateCheck compares strm->zalloc / zfree with 0: the function pointers inside za_funcs
    (r'\bunfold dcheck_at, zfuncs\.', 'unfold dcheck_at, zfuncs, za_funcs.'),
    # A ported Delta abbreviation is an application [@Delta_x_za ZA], which VST's simplify_Delta (forward,
    # abbreviate_semax) cannot unfold (it loops); the proofs that do not unfold it themselves get its body.
    # (the Deltas of deflate_slow, deflate_rle, deflate_huff are unfolded by some proofs: dropped there first)
    (r'\bunfold Delta_(?:sl|rle|hf)\.\s*', ''),
    (r'(\bunfold\b[^.;]*?), Delta_(?:sl|rle|hf)\b', r'\1'),
    (r'(?<!Definition )(?<!\[)\bDelta_fw\b', '(func_tycontext f_fill_window DSpec.Vprog Gprog_fill_window nil)'),
    (r'(?<!Definition )(?<!\[)\bDelta_ds\b', '(func_tycontext f_deflate_stored DSpec.Vprog Gprog_compress nil)'),
    (r'(?<!Definition )(?<!\[)\bDelta_df\b', '(func_tycontext f_deflate DSpec.Vprog Gprog_deflate nil)'),
    (r'(?<!Definition )(?<!\[)\bDelta_sl\b', '(func_tycontext f_deflate_slow DSpec.Vprog Gprog_compress nil)'),
    (r'(?<!Definition )(?<!\[)\bDelta_rle\b', '(func_tycontext f_deflate_rle DSpec.Vprog Gprog_compress nil)'),
    (r'(?<!Definition )(?<!\[)\bDelta_hf\b', '(func_tycontext f_deflate_huff DSpec.Vprog Gprog_compress nil)'),
]

# (module, old text after SUBST, new text)
PATCHES = [
    # the function pointers strm->zalloc / strm->zfree
    ('Zlib.proof.deflate.DSpec',
     "(func_ptr' (snd zcalloc_spec) za_alloc * func_ptr' (snd zcfree_spec) za_free)%logic.",
     "(@za_funcs DCS.CS ZA)%logic."),
    # the tokens of deflateInit2_'s five allocations
    ('Zlib.proof.deflate.DRep',
     """  (malloc_token Ews t_ds (p_s p) *
  malloc_token Ews (tarray tuchar (2 * d_w_size s)) (p_window p) *
  malloc_token Ews (tarray tushort (d_w_size s)) (p_prev p) *
  malloc_token Ews (tarray tushort (d_hash_size s)) (p_head p) *
  malloc_token Ews (tarray tuchar (4 * tr_lit_bufsize (d_tr s))) (p_pbuf p) *""",
     """  (za_tok t_ds (p_s p) *
  za_tok (tarray tuchar (2 * d_w_size s)) (p_window p) *
  za_tok (tarray tushort (d_w_size s)) (p_prev p) *
  za_tok (tarray tushort (d_hash_size s)) (p_head p) *
  za_tok (tarray tuchar (4 * tr_lit_bufsize (d_tr s))) (p_pbuf p) *"""),
    ('Zlib.proof.deflate.DSpec',
     "(if eq_dec q nullval then emp else @malloc_token DCS.CS Ews t q * @data_at_ DCS.CS Ews t q)%logic.",
     "(if eq_dec q nullval then emp else za_tok t q * @data_at_ DCS.CS Ews t q)%logic."),
    ('Zlib.proof.deflate.DSpec',
     "   @malloc_token DCS.CS Ews t_ds (p_s p) *",
     "   za_tok t_ds (p_s p) *"),
    # the name [dsame] is also a tactic of ApiKit, which the port renames (it mentions dtokens): the definition is
    # ported with it, so that the renamed uses in DeflateFacts' tactics find it
    ('Zlib.proof.deflate.DeflateFacts',
     "(** ** What the stages keep: [dkeep] with equal buffer lengths *)",
     "(** ** What the stages keep: [dkeep] with equal buffer lengths (ported with the tactic [dsame] of ApiKit) *)"),
    # the allocator of a ported lemma is implicit: given before the ltac:(assumption) arguments are elaborated
    ('Zlib.proof.deflate.MainDeflate',
     "sep_apply (dcheck_none_fold strmp za zf gv ltac:(assumption) ltac:(assumption)).",
     "sep_apply (@dcheck_none_fold ZA strmp za zf gv ltac:(assumption) ltac:(assumption))."),
    # the conversion to deflateEnd's representation: the blocks come with the allocator's tokens
    ('Zlib.proof.deflate.Api_toend',
     "(@malloc_token DCS.CS Ews t q * @data_at_ DCS.CS Ews t q)%logic |-- opt_alloc t q.",
     "(za_tok t q * @data_at_ DCS.CS Ews t q)%logic |-- opt_alloc t q."),
    ('Zlib.proof.deflate.Api_toend',
     "  - subst. entailer!.\n  - cancel.",
     "  - subst. entailer!. destruct H as [[] _].\n  - cancel."),
]
