"""Patches of the inflate port, part cases, group ty: see docs/port-za/inflate/cases.py."""

PATCHES = [
    # the stream's zalloc / zfree fields are now the allocator's za_alloc / za_free (strm_rep_za), no longer the
    # global zcalloc / zcfree: name those values so that entailer! keeps them folded
    ('Zlib.proof.inflate.Cases5_TY',
     'remember (f_gv F _zcalloc) as za eqn:Eza. remember (f_gv F _zcfree) as zf eqn:Ezf.',
     'remember (@za_alloc ZA) as za eqn:Eza. remember (@za_free ZA) as zf eqn:Ezf.'),
]
