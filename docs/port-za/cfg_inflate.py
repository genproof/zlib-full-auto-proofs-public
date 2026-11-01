"""Configuration of docs/port-za/port.py for inflate.c: the proofs of the functions inflate() reaches
(inflate, inflate_fast, updatewindow, inflate_fixed, inflateStateCheck), of inflateSetDictionary and of the
reset functions, re-run

- with a CALLER-SUPPLIED allocator (src/proof/zutil/ZAlloc.v): strm->zalloc / zfree / opaque are the
  allocator's values, the state and the window are its blocks (za_tok), its state za_res records the events;
- WIDE: the machine invariant Inv.mwf with avail_in / avail_out up to 2^32 - 1 (the two bounds raised from
  Int.max_signed to Int.max_unsigned, as InvW.mwfW) and Inv3.mwf3 with InvW.hdrW (the gzip extra field's
  length and the bit buffer before it, what the wide input needs in case EXTRA): mwf3 = InvW.mwf3W;
- with strm->adler as `adler_val adler` (src/proof/za/inflate/ZAV.v): the model's value, or any contents on
  a raw stream whose application never set it.

Output: src/proof/za/inflate/, src/proof/za/inflate_api/, src/proof/za/inffast/ (modules Zlib.proof.za.*),
suffix _za, the tainted declarations in a section with the allocator ZA and the adler cell ZAV.
Run from the repository root:  python3 docs/port-za/port.py inflate  (--check: compare with the files)."""

SECTION = ('\nSection ZAlloc.\nContext {ZA : Zlib.proof.zutil.ZAlloc.zallocator} '
           '{ZAV : Zlib.proof.za.inflate.ZAV.adler_cell}.\n',
           '\nEnd ZAlloc.\n')
REQUIRES = ('Require Import Zlib.proof.zutil.ZAlloc.\nRequire Import Zlib.proof.za.inflate.ZAV.\n'
            'Require Import Zlib.proof.za.inflate.ZEvents.\nRequire Import Zlib.proof.za.inflate.ZTac.\n'
            'Require Zlib.proof.inflate.InvW.\n')
WHAT = ('the\n   allocator values, the bounds of the machine invariant and strm->adler, with a caller-supplied '
        'allocator,\n   calls of up to 2^32 - 1 bytes and the adler cell (docs/port-za/cfg_inflate.py)')

PREFIXES = ['Zlib.proof.inflate.', 'Zlib.proof.inflate_api.', 'Zlib.proof.inffast.']

TARGETS = [
    'Zlib.proof.inflate_api.Body5_inflate',
    # the switch cases (CasesAll5's assembly, which also takes the pure lemmas of InvQ5, is redone by hand
    # in src/proof/za/inflate/CasesAllZ.v: the wide step lemma is InvW's, not a port of StepMwf5)
    'Zlib.proof.inflate.Cases5_HEAD', 'Zlib.proof.inflate.Cases5_FTO', 'Zlib.proof.inflate.Cases5_EX',
    'Zlib.proof.inflate.Cases5_NC', 'Zlib.proof.inflate.Cases5_HD', 'Zlib.proof.inflate.Cases5_TY',
    'Zlib.proof.inflate.Cases5_ST', 'Zlib.proof.inflate.Cases5_TL', 'Zlib.proof.inflate.Cases5_CL',
    'Zlib.proof.inflate.Cases5_LD', 'Zlib.proof.inflate.Cases5_DM',
    'Zlib.proof.inflate.Cases5_CK', 'Zlib.proof.inflate.CaseLIT5', 'Zlib.proof.inflate.CaseEnd5',
    'Zlib.proof.inflate.CaseLEN_5',
    # the LEN case's parts (their assembly is src/proof/za/inflate/CasesLenZ.v, by hand)
    'Zlib.proof.inflate.LnKit5', 'Zlib.proof.inflate.LnCase5', 'Zlib.proof.inflate.LnFast5',
    'Zlib.proof.inflate.LnLoop1_5', 'Zlib.proof.inflate.LnLoop2_5', 'Zlib.proof.inflate.LnTab5',
    'Zlib.proof.inflate.LnTail5',
    'Zlib.proof.inffast.BodyF5',
    'Zlib.proof.inflate.BodyUw5',
    'Zlib.proof.inflate.BodySmall',
    'Zlib.proof.inflate_api.Body5_init',
    'Zlib.proof.inflate_api.Body5_reset',
    'Zlib.proof.inflate_api.Body5_end',
    'Zlib.proof.inflate_api.Body5_dict',
]

SUBST = [
    # the allocator's values in the z_stream
    (r'\(gv _zcalloc\) \(gv _zcfree\) nullval', 'za_alloc za_free za_opaque'),
    (r'\(gv _zcalloc\)', 'za_alloc'),
    (r'\(gv _zcfree\)', 'za_free'),
    (r'\bgv _zcalloc\b', 'za_alloc'),
    (r'\bgv _zcfree\b', 'za_free'),
    # the allocator's blocks: the state and the window
    (r'\bmalloc_token Ews t_state\b', 'za_tok t_state'),
    (r'\bmalloc_token Ews \(tarray tuchar \(2 \^ ', 'za_tok (tarray tuchar (2 ^ '),
]

import importlib.util as _ilu
import os as _os


def _area(name):
    """The patches of one part of the port (docs/port-za/inflate/<name>.py: PATCHES)."""
    path = _os.path.join(_os.path.dirname(_os.path.abspath(__file__)), 'inflate', name + '.py')
    spec = _ilu.spec_from_file_location('cfg_inflate_' + name, path)
    mod = _ilu.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod.PATCHES


# (module, old text after SUBST, new text): the interface (representations and specifications) here, the
# proofs' patches in docs/port-za/inflate/*.py
PATCHES = [
    # struct z_stream: opaque is the allocator's, adler the adler cell
    ('Zlib.proof.inflate.Rep',
     "(nullval, (zv dt, (lv adler, vres))))))))))))) strmp.",
     "(za_opaque, (zv dt, (adler_val adler, vres))))))))))))) strmp."),
    # the function pointers strm->zalloc / strm->zfree
    ('Zlib.proof.inflate.Callees',
     """  func_ptr' (snd (@Zlib.proof.zutil.Spec.zcalloc_spec Zlib.units.Inflate.CS)) za_alloc *
  func_ptr' (snd (@Zlib.proof.zutil.Spec.zcfree_spec Zlib.units.Inflate.CS)) za_free.""",
     "  @za_funcs Zlib.units.Inflate.CS ZA."),
    # the wide machine invariant (InvW.mwfW)
    ('Zlib.proof.inflate.Inv',
     "  mw_inp : Zlength (m_inp m) <= Int.max_signed /\\ bytes_ok (m_inp m);\n"
     "  mw_aout : 0 <= m_aout m <= Int.max_signed;",
     "  mw_inp : Zlength (m_inp m) <= Int.max_unsigned /\\ bytes_ok (m_inp m);\n"
     "  mw_aout : 0 <= m_aout m <= Int.max_unsigned;"),
    ('Zlib.proof.inflate.Inv',
     "Lemma mwf_left: forall m, mwf m -> 0 <= m_left m <= Int.max_signed.",
     "Lemma mwf_left: forall m, mwf m -> 0 <= m_left m <= Int.max_unsigned."),
    ('Zlib.proof.inflate.Inv',
     "Lemma mwf_have: forall m, mwf m -> 0 <= m_have m <= Int.max_signed.",
     "Lemma mwf_have: forall m, mwf m -> 0 <= m_have m <= Int.max_unsigned."),
    ('Zlib.proof.inflate.Inv3',
     "Definition mwf3 (m: mst) : Prop := mwf m /\\ swf3 (m_s m).",
     "Definition mwf3 (m: mst) : Prop := mwf m /\\ swf3 (m_s m) /\\ Zlib.proof.inflate.InvW.hdrW m."),
    # the raw stream fields of a live stream: strm->adler is the adler cell
    ('Zlib.proof.inflate_api.Spec5',
     "        (Vlong (Int64.repr (zf_adler z))) (zf_res z)) L\n  = istream gv shs strmp z (Some L).",
     "        (adler_val (zf_adler z)) (zf_res z)) L\n  = istream gv shs strmp z (Some L)."),
    # updatewindow: the window allocation is the allocator's (ZALLOC of 2^wbits bytes, event uw_ev)
    ('Zlib.proof.inflate.Callees3',
     "st' = st /\\ za = za_alloc /\\ zf = za_free /\\ op = nullval.",
     "st' = st /\\ za = za_alloc /\\ zf = za_free /\\ op = za_opaque."),
    ('Zlib.proof.inflate.Callees3',
     "s: istate, ssh: share, p: val, n: Z, c: list val, e: Z, data: list Z\n",
     "s: istate, ssh: share, p: val, n: Z, c: list val, e: Z, data: list Z, tr: list zev\n"),
    ('Zlib.proof.inflate.Callees3',
     "          i_win s = false -> winp = nullval)",
     "          i_win s = false -> winp = nullval; i_win s = false -> za_now tr + 2 ^ i_wbits s <= za_cap;\n"
     "          is_pointer_or_null za_opaque)"),
    ('Zlib.proof.inflate.Callees3',
     "         data_at ssh (tarray tuchar n) c p; mem_mgr gv; zfuncs gv)\n  POST",
     "         data_at ssh (tarray tuchar n) c p; za_res gv tr; zfuncs gv)\n  POST"),
    ('Zlib.proof.inflate.Callees3',
     "         data_at ssh (tarray tuchar n) c p; mem_mgr gv; zfuncs gv).",
     "         data_at ssh (tarray tuchar n) c p; za_res gv (tr ++ uw_ev s r); zfuncs gv)."),
    # inflate(): wide (no 2^31 - 1 bounds), InvW.swfW of the saved state, the window allocation's event
    ('Zlib.proof.inflate_api.Spec5',
     "       ob: option outbuf, flush: Z, gsh: share, tsh: share, itok: bool, otok: bool\n  PRE [ tptr t_strm, tint ]",
     "       ob: option outbuf, flush: Z, gsh: share, tsh: share, itok: bool, otok: bool, tr: list zev\n"
     "  PRE [ tptr t_strm, tint ]"),
    ('Zlib.proof.inflate_api.Spec5',
     """          zf_ai z <= Int.max_signed; zf_ao z <= Int.max_signed)
    PARAMS (strmp; Vint (Int.repr flush)) GLOBALS (gv)
    SEP (istream_opt gv shs strmp z st; head_opt (is_live strmp st); bufs_opt (is_live strmp st) ib ob [] itok otok;
         tables_rep gsh gv; crc_table_at tsh gv; mem_mgr gv; zfuncs gv)
  POST [ tint ]
    EX r: Z, EX z': zfields, EX st': option live, EX ow: list Z,
    PROP (inflate_rel flush strmp z st ib inp ob r z' st' ow)
    RETURN (Vint (Int.repr r))
    SEP (istream_opt gv shs strmp z' st'; head_opt (is_live strmp st'); bufs_opt (is_live strmp st) ib ob ow itok otok;
         tables_rep gsh gv; crc_table_at tsh gv; mem_mgr gv; zfuncs gv).""",
     """          match st with Some L => Zlib.proof.inflate.InvW.swfW (l_s L) | None => True end;
          za_now tr + 2 ^ 23 <= za_cap; is_pointer_or_null za_opaque)
    PARAMS (strmp; Vint (Int.repr flush)) GLOBALS (gv)
    SEP (istream_opt gv shs strmp z st; head_opt (is_live strmp st); bufs_opt (is_live strmp st) ib ob [] itok otok;
         tables_rep gsh gv; crc_table_at tsh gv; za_res gv tr; zfuncs gv)
  POST [ tint ]
    EX r: Z, EX z': zfields, EX st': option live, EX ow: list Z,
    PROP (inflate_rel flush strmp z st ib inp ob r z' st' ow;
          match st' with Some L' => Zlib.proof.inflate.InvW.swfW (l_s L') | None => True end)
    RETURN (Vint (Int.repr r))
    SEP (istream_opt gv shs strmp z' st'; head_opt (is_live strmp st'); bufs_opt (is_live strmp st) ib ob ow itok otok;
         tables_rep gsh gv; crc_table_at tsh gv;
         za_res gv (tr ++ match st, st' with Some L, Some L' => win_ev (l_s L) (l_s L') | _, _ => [] end);
         zfuncs gv)."""),
    # inflateInit2_ on a stream with the caller's allocator (strm->zalloc, zfree non-NULL: kept), the state's
    # allocation (and its release when inflateReset2 rejects windowBits) as the events init_ev
    ('Zlib.proof.inflate_api.Spec5',
     "  if ret =? Z_VERSION_ERROR then raw_strm gv shs strmp r msgv stv nullval nullval opq",
     "  if ret =? Z_VERSION_ERROR then raw_strm gv shs strmp r msgv stv za_alloc za_free za_opaque"),
    ('Zlib.proof.inflate_api.Spec5',
     """  WITH gv: globals, shs: share, strmp: val, r: rawf, msgv: val, stv: val, opq: val, w: Z,
       ver: val, vsh: share, vc: list val, c: Z, ssize: Z
  PRE [ tptr t_strm, tint, tptr tschar, tint ]
    PROP (readable_share vsh; isptr ver; 1 <= Zlength vc <= Ptrofs.max_unsigned; Znth 0 vc = Vint (Int.repr c);
          -128 <= c <= 127;
          Int.min_signed <= w <= Int.max_signed; Int.min_signed <= ssize <= Int.max_signed;
          strmp <> nullval -> writable_share shs)
    PARAMS (strmp; Vint (Int.repr w); ver; Vint (Int.repr ssize)) GLOBALS (gv)
    SEP (if eq_dec strmp nullval then emp else raw_strm gv shs strmp r msgv stv nullval nullval opq;
         data_at vsh (tarray tschar (Zlength vc)) vc ver; version_lit gv; mem_mgr gv; zfuncs gv)
  POST [ tint ]
    EX alloc_ok: bool, EX sp: val,
    PROP (alloc_ok = true -> isptr sp)
    RETURN (Vint (Int.repr (init_ret strmp c ssize w alloc_ok)))
    SEP (init_mem gv shs strmp r msgv stv opq (init_ret strmp c ssize w alloc_ok) sp w;
         data_at vsh (tarray tschar (Zlength vc)) vc ver; version_lit gv; mem_mgr gv; zfuncs gv).""",
     """  WITH gv: globals, shs: share, strmp: val, r: rawf, msgv: val, stv: val, w: Z,
       ver: val, vsh: share, vc: list val, c: Z, ssize: Z, tr: list zev
  PRE [ tptr t_strm, tint, tptr tschar, tint ]
    PROP (readable_share vsh; isptr ver; 1 <= Zlength vc <= Ptrofs.max_unsigned; Znth 0 vc = Vint (Int.repr c);
          -128 <= c <= 127;
          Int.min_signed <= w <= Int.max_signed; Int.min_signed <= ssize <= Int.max_signed;
          strmp <> nullval -> writable_share shs; za_now tr + state_size <= za_cap;
          is_pointer_or_null za_opaque)
    PARAMS (strmp; Vint (Int.repr w); ver; Vint (Int.repr ssize)) GLOBALS (gv)
    SEP (if eq_dec strmp nullval then emp else raw_strm gv shs strmp r msgv stv za_alloc za_free za_opaque;
         data_at vsh (tarray tschar (Zlength vc)) vc ver; version_lit gv; za_res gv tr; zfuncs gv)
  POST [ tint ]
    EX alloc_ok: bool, EX sp: val,
    PROP (alloc_ok = true -> isptr sp)
    RETURN (Vint (Int.repr (init_ret strmp c ssize w alloc_ok)))
    SEP (init_mem gv shs strmp r msgv stv za_opaque (init_ret strmp c ssize w alloc_ok) sp w;
         data_at vsh (tarray tschar (Zlength vc)) vc ver; version_lit gv;
         za_res gv (tr ++ init_ev (if eq_dec strmp nullval then true else false) c ssize w alloc_ok); zfuncs gv)."""),
    # inflateEnd: the window (when allocated) and the state given back, events end_ev
    ('Zlib.proof.inflate_api.Spec5',
     """  WITH gv: globals, shs: share, strmp: val, z: zfields, st: option live
  PRE [ tptr t_strm ]
    PROP () PARAMS (strmp) GLOBALS (gv)
    SEP (istream_opt gv shs strmp z st; mem_mgr gv; zfuncs gv)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (match is_live strmp st with Some _ => Z_OK | None => Z_STREAM_ERROR end)))
    SEP (istream_opt gv shs strmp z None; mem_mgr gv; zfuncs gv).""",
     """  WITH gv: globals, shs: share, strmp: val, z: zfields, st: option live, tr: list zev
  PRE [ tptr t_strm ]
    PROP (is_pointer_or_null za_opaque) PARAMS (strmp) GLOBALS (gv)
    SEP (istream_opt gv shs strmp z st; za_res gv tr; zfuncs gv)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (match is_live strmp st with Some _ => Z_OK | None => Z_STREAM_ERROR end)))
    SEP (istream_opt gv shs strmp z None;
         za_res gv (tr ++ match is_live strmp st with Some L => end_ev (l_s L) | None => [] end); zfuncs gv)."""),
    # inflateReset2: the window given back when its size changes, events reset2_ev
    ('Zlib.proof.inflate_api.Spec5',
     """  WITH gv: globals, shs: share, strmp: val, z: zfields, r: rst, w: Z
  PRE [ tptr t_strm, tint ]
    PROP (Int.min_signed <= w <= Int.max_signed; reset_pre strmp r (reset2_f w) z)
    PARAMS (strmp; Vint (Int.repr w)) GLOBALS (gv)
    SEP (rstream_opt gv shs strmp z r; mem_mgr gv; zfuncs gv)
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (reset_ret strmp r (reset2_f w) z)))
    SEP (reset_post gv shs strmp z r (reset2_f w); mem_mgr gv; zfuncs gv).""",
     """  WITH gv: globals, shs: share, strmp: val, z: zfields, r: rst, w: Z, tr: list zev
  PRE [ tptr t_strm, tint ]
    PROP (Int.min_signed <= w <= Int.max_signed; reset_pre strmp r (reset2_f w) z;
          is_pointer_or_null za_opaque)
    PARAMS (strmp; Vint (Int.repr w)) GLOBALS (gv)
    SEP (rstream_opt gv shs strmp z r; za_res gv tr; zfuncs gv)
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (reset_ret strmp r (reset2_f w) z)))
    SEP (reset_post gv shs strmp z r (reset2_f w);
         za_res gv (tr ++ match rs_live strmp r with Some L => reset2_ev (l_s L) w | None => [] end);
         zfuncs gv)."""),
    # inflateReset: the window given back when bit 3 of wrap is set (patch F8), events reset_ev
    ('Zlib.proof.inflate_api.Spec5',
     """  WITH gv: globals, shs: share, strmp: val, z: zfields, r: rst
  PRE [ tptr t_strm ]
    PROP (reset_pre strmp r reset_f z) PARAMS (strmp) GLOBALS (gv)
    SEP (rstream_opt gv shs strmp z r; mem_mgr gv; zfuncs gv)
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (reset_ret strmp r reset_f z)))
    SEP (reset_post gv shs strmp z r reset_f; mem_mgr gv; zfuncs gv).""",
     """  WITH gv: globals, shs: share, strmp: val, z: zfields, r: rst, tr: list zev
  PRE [ tptr t_strm ]
    PROP (reset_pre strmp r reset_f z; is_pointer_or_null za_opaque) PARAMS (strmp) GLOBALS (gv)
    SEP (rstream_opt gv shs strmp z r; za_res gv tr; zfuncs gv)
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (reset_ret strmp r reset_f z)))
    SEP (reset_post gv shs strmp z r reset_f;
         za_res gv (tr ++ match rs_live strmp r with Some L => reset_ev (l_s L) | None => [] end);
         zfuncs gv)."""),
    # inflateSync: its inflateReset call has bit 3 hidden, nothing is given back (no event)
    ('Zlib.proof.inflate_api.Spec5',
     """  WITH gv: globals, shs: share, strmp: val, z: zfields, st: option live, ib: inbuf, inp: list Z
  PRE [ tptr t_strm ]
    PROP (ib <> InNull; in_ok ib inp; zf_ni z = in_ptr ib 0; zf_ai z = Zlength inp)
    PARAMS (strmp) GLOBALS (gv)
    SEP (istream_opt gv shs strmp z st; in_rep ib; mem_mgr gv; zfuncs gv)""",
     """  WITH gv: globals, shs: share, strmp: val, z: zfields, st: option live, ib: inbuf, inp: list Z, tr: list zev
  PRE [ tptr t_strm ]
    PROP (ib <> InNull; in_ok ib inp; zf_ni z = in_ptr ib 0; zf_ai z = Zlength inp; is_pointer_or_null za_opaque)
    PARAMS (strmp) GLOBALS (gv)
    SEP (istream_opt gv shs strmp z st; in_rep ib; za_res gv tr; zfuncs gv)"""),
    ('Zlib.proof.inflate_api.Spec5',
     """         in_rep ib; mem_mgr gv; zfuncs gv).""",
     """         in_rep ib; za_res gv tr; zfuncs gv)."""),
    # inflateSetDictionary: the window allocated when there is none, or its failed allocation (events dict_ev)
    ('Zlib.proof.inflate_api.Spec5',
     """       dsh: share, p: val, lo: Z, n: Z, c: list val, dict: list Z, tok: bool
  PRE [ tptr t_strm, tptr tuchar, tuint ]""",
     """       dsh: share, p: val, lo: Z, n: Z, c: list val, dict: list Z, tok: bool, tr: list zev
  PRE [ tptr t_strm, tptr tuchar, tuint ]"""),
    ('Zlib.proof.inflate_api.Spec5',
     """          n <= Ptrofs.max_unsigned; sublist lo (lo + Zlength dict) c = byte_vals dict; bytes_ok dict)
    PARAMS (strmp; offset_val lo p; Vint (Int.repr (Zlength dict))) GLOBALS (gv)
    SEP (istream_opt gv shs strmp z st; data_at dsh (tarray tuchar n) c p;
         if tok then malloc_token Ews (tarray tuchar n) p else emp; mem_mgr gv; zfuncs gv)""",
     """          n <= Ptrofs.max_unsigned; sublist lo (lo + Zlength dict) c = byte_vals dict; bytes_ok dict;
          za_now tr + 2 ^ 23 <= za_cap; is_pointer_or_null za_opaque)
    PARAMS (strmp; offset_val lo p; Vint (Int.repr (Zlength dict))) GLOBALS (gv)
    SEP (istream_opt gv shs strmp z st; data_at dsh (tarray tuchar n) c p;
         if tok then malloc_token Ews (tarray tuchar n) p else emp; za_res gv tr; zfuncs gv)"""),
    ('Zlib.proof.inflate_api.Spec5',
     """         data_at dsh (tarray tuchar n) c p; if tok then malloc_token Ews (tarray tuchar n) p else emp;
         mem_mgr gv; zfuncs gv).""",
     """         data_at dsh (tarray tuchar n) c p; if tok then malloc_token Ews (tarray tuchar n) p else emp;
         za_res gv (tr ++ match is_live strmp st with Some L => dict_ev (l_s L) dict alloc_ok | None => [] end);
         zfuncs gv)."""),
    # (proof patches of the shared base: the modules every part needs)
    # a rewrite with a lemma of another module: its allocator / adler-cell arguments explicit (as implicit
    # arguments they are evars and the rewrite's matching takes minutes)
    ('Zlib.proof.inflate.CaseKit5',
     "  rewrite (case_post2_eq F m m' E).",
     "  rewrite (@case_post2_eq ZA ZAV F m m' E)."),
    # (the original proof takes minutes: intuition on every side goal; the same argument, directly)
    ('Zlib.proof.inflate.MwfLemmas',
     "  apply mwf_set_mode; auto; try (intros; subst; congruence); try (intros D; apply ND; unfold decode_mode; intuition).",
     "  apply mwf_set_mode; auto; intros E; try (exfalso; subst md; congruence);\n"
     "    apply ND; unfold decode_mode in *; tauto."),
    # the contexts: ZALLOC / ZFREE call through the function pointers (za_funcs), not zcalloc / zcfree
    ('Zlib.proof.inflate_api.Bodies5',
     "Definition Gp_init2 : funspecs := [inflateReset2_spec; zcalloc_i; zcfree_i; memset_i].",
     "Definition Gp_init2 : funspecs := [inflateReset2_spec; memset_i]."),
    ('Zlib.proof.inflate_api.Bodies5',
     "Definition Gp_reset : funspecs := [inflateStateCheck_spec; inflateResetKeep_spec; zcfree_i].",
     "Definition Gp_reset : funspecs := [inflateStateCheck_spec; inflateResetKeep_spec]."),
    ('Zlib.proof.inflate_api.Bodies5',
     "Definition Gp_reset2 : funspecs := [inflateStateCheck_spec; inflateReset_spec; zcfree_i].",
     "Definition Gp_reset2 : funspecs := [inflateStateCheck_spec; inflateReset_spec]."),
    ('Zlib.proof.inflate_api.Bodies5',
     "Definition Gp_end : funspecs := [inflateStateCheck_spec; zcfree_i].",
     "Definition Gp_end : funspecs := [inflateStateCheck_spec]."),
]

for _a in ['kit', 'fast', 'cases', 'body', 'api']:
    PATCHES += _area(_a)
