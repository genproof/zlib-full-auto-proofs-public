"""Configuration of docs/port-hl/port.py: the HEADLESS port of inflate()'s non-header world.

Loop.mem_rep, the memory of every switch case of inflate()'s body proof (and of inflate_fast_spec3), holds the
application's gz_header as Spec5's DEFINED head_rep (Loop.head_part).  An application header whose absent fields
stay undefined (harness/rt_gzip_header.c) fits none of these lemmas.  The port replaces the header in head_part by
the atom RTHLoop.hnoneH (= emp): the header is then held by the caller as a frame, which the non-header cases and
inflate_fast never touch.  The ported names carry the suffix _hl; mem_rep_hl is convertible to RTHLoop.mem_repH."""

PREFIXES = ['Zlib.proof.inflate.', 'Zlib.proof.inflate_api.', 'Zlib.proof.inffast.']

# the loop and the exit of inflate()'s body, and the parts of inflate_fast and the kits that the port of
# cfg_hlza.py requires (the switch cases themselves are ported there, from the allocator-generic proofs)
TARGETS = [
    'Zlib.proof.inflate_api.Body5Loop',
    'Zlib.proof.inflate_api.Body5Exit',
    'Zlib.proof.inffast.F5Main',
    'Zlib.proof.inffast.F5Copy',
    'Zlib.proof.inffast.F5Iter',
    'Zlib.proof.inffast.F5Len',
    'Zlib.proof.inflate.DmKit5',
    'Zlib.proof.inflate.MtKit5',
    'Zlib.proof.inflate.MtTail5',
]

SUFFIX = '_hl'
OUT = 'hl'
# the ported files are src/proof/hl/<dir>/Hl<stem>.v (no stem shared with another module)
STEM = 'Hl'
SECTION = None
REQUIRES = 'Require Zlib.proof.roundtrip.RTHLoop.\n'
WHAT = 'the\n   application\'s gz_header (Loop.head_part), with the header replaced by RTHLoop.hnoneH = emp'

SUBST = []

PATCHES = [
    ('Zlib.proof.inflate.Loop',
     "if i_head (m_s m) then head_rep (f_hsh F) (f_headp F) (f_xb F) (f_nb F) (f_cb F) (m_h m) else emp.",
     "if i_head (m_s m) then Zlib.proof.roundtrip.RTHLoop.hnoneH (f_hsh F) (f_headp F) (f_xb F) (f_nb F) (f_cb F) (m_h m)\n  else emp."),
]
