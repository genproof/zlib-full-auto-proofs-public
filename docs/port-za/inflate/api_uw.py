"""Patches of the inflate port, part api (updatewindow, BodyUw5): see docs/port-za/inflate/api.py."""

PATCHES = [
    # updatewindow's callees: ZALLOC calls through strm->zalloc (zfuncs), not zcalloc
    ('Zlib.proof.inflate.BodyUpdatewindow',
     "  [Zlib.proof.zutil.Spec.zcalloc_spec; (_memcpy, snd (@Zlib.proof.zutil.Libc.memcpy_spec Zlib.units.Inflate.CS))].",
     "  [(_memcpy, snd (@Zlib.proof.zutil.Libc.memcpy_spec Zlib.units.Inflate.CS))]."),
]

# the stream (strm->opaque is the allocator's), the state's predicates after the window allocation carry the
# allocator's trace: tr ++ uw_ev s 0 (the window allocated when there was none)
_SV = "(ni, (ai, (ti, (no, (ao, (tout, (msg, (sp, (za_alloc, (zfp, (nullval, (dt, (adl, res)))))))))))))"
_SVZ = "(ni, (ai, (ti, (no, (ao, (tout, (msg, (sp, (za_alloc, (zfp, (za_opaque, (dt, (adl, res)))))))))))))"
_M = 'Zlib.proof.inflate.BodyUw5'
PATCHES += [
    (_M, "(data: list Z) (zfp: val) : environ -> mpred :=",
     "(data: list Z) (zfp: val) (tr: list zev) : environ -> mpred :="),
    (_M, """         data_at ssh (tarray tuchar n) c p; mem_mgr gv;
         func_ptr' (snd (@Zlib.proof.zutil.Spec.zcalloc_spec Zlib.units.Inflate.CS)) za_alloc;
         func_ptr' (snd (@Zlib.proof.zutil.Spec.zcfree_spec Zlib.units.Inflate.CS)) zfp))%assert.""",
     """         data_at ssh (tarray tuchar n) c p; za_res gv (tr ++ uw_ev s 0);
         func_ptr' (@zalloc_spec Zlib.units.Inflate.CS ZA) za_alloc;
         func_ptr' (@zfree_spec Zlib.units.Inflate.CS ZA) zfp))%assert."""),
    (_M, "(c: list val) (data: list Z) : ret_assert :=",
     "(c: list val) (data: list Z) (tr: list zev) : ret_assert :="),
    (_M, "data_at ssh (tarray tuchar n) c p; mem_mgr gv; zfuncs gv))%assert)",
     "data_at ssh (tarray tuchar n) c p; za_res gv (tr ++ uw_ev s r); zfuncs gv))%assert)"),
    # the copy (section Copy): the trace as a section variable
    (_M, "(e: Z) (data: list Z) (zfp: val).\nHypotheses",
     "(e: Z) (data: list Z) (zfp: val) (tr: list zev).\nHypotheses"),
]
for _a, _b in [('A', 'A'), ('B', 'B')]:
    PATCHES.append((_M,
     "    (PC gv shs strmp %s sp headp winp' s ssh p n c e data zfp)\n    (Ssequence uw_D%s uw_ret)\n"
     "    (uw_post gv shs strmp %s sp headp winp s ssh p n c data)." % (_SV, _a, _SV),
     "    (PC gv shs strmp %s sp headp winp' s ssh p n c e data zfp tr)\n    (Ssequence uw_D%s uw_ret)\n"
     "    (uw_post gv shs strmp %s sp headp winp s ssh p n c data tr)." % (_SVZ, _a, _SVZ)))
    PATCHES.append((_M,
     "      (PC gv shs strmp %s sp headp winp' s ssh p n c e data zfp)\n      (Ssequence uw_D%s uw_ret)\n"
     "      (uw_post gv shs strmp %s sp headp winp s ssh p n c data))." % (_SV, _a, _SV),
     "      (PC gv shs strmp %s sp headp winp' s ssh p n c e data zfp tr)\n      (Ssequence uw_D%s uw_ret)\n"
     "      (uw_post gv shs strmp %s sp headp winp s ssh p n c data tr))." % (_SVZ, _a, _SVZ)))
_END = "Exists 0 winp'. change (0 =? 0) with true. cbv iota. unfold zfuncs. rewrite <- Hzfp. entailer!."
_ENDZ = "Exists 0 winp'. change (0 =? 0) with true. cbv iota. unfold zfuncs, za_funcs. rewrite <- Hzfp. entailer!."
for _ctx in ["               ltac:(rewrite <- C4; list_solve)).\n  return_noent.\n  ",
             "L1) C1 C2 C3 C4).\n    return_noent.\n    ",
             "_ C1 C3 C2 C4).\n    return_noent.\n    "]:
    PATCHES.append((_M, _ctx + _END, _ctx + _ENDZ))
# the body
PATCHES += [
    (_M, "assert (Hsv: st = sp /\\ za = za_alloc /\\ zf = za_free /\\ op = nullval) by exact H; clear H end.",
     "assert (Hsv: st = sp /\\ za = za_alloc /\\ zf = za_free /\\ op = za_opaque) by exact H; clear H end."),
    (_M, "  match goal with H: bytes_ok data |- _ => rename H into Hbok end.\n",
     "  match goal with H: bytes_ok data |- _ => rename H into Hbok end.\n"
     "  match goal with H: i_win s = false -> za_now tr + _ <= za_cap |- _ => rename H into Hcap end.\n"),
    (_M, "  rewrite state_rep_split. unfold zfuncs. Intros.",
     "  rewrite state_rep_split. unfold zfuncs, za_funcs. Intros."),
    (_M, "(Q := P1 gv shs strmp sv sp headp winp s ssh p n c e data zfp) end.",
     "(Q := P1 gv shs strmp sv sp headp winp s ssh p n c e data zfp tr) end."),
    (_M, "      + forward. Exists winp. entailer!.",
     "      + forward. Exists winp. unfold uw_ev. rewrite Hw, app_nil_r. entailer!."),
    (_M, """        forward_call (tarray tuchar (2 ^ i_wbits s), gv, nullval, 2 ^ i_wbits s, 1).
        { change (Int.unsigned Int.iwordsize) with 32. lia. }
        { entailer!. simpl. rewrite shl_one by lia. reflexivity. }
        { simpl. lia. }""",
     """        forward_call (tarray tuchar (2 ^ i_wbits s), 2 ^ i_wbits s, 1, gv, tr).
        { change (Int.unsigned Int.iwordsize) with 32. lia. }
        { entailer!. simpl. rewrite shl_one by lia. reflexivity. }
        { pose proof (Hcap eq_refl). simpl. rep_lia. }"""),
    (_M, "             rewrite Hw. unfold zfuncs. rewrite <- Hzfp. entailer!.",
     "             rewrite Hw. unfold zfuncs, za_funcs, uw_ev. rewrite Hw. simpl (1 =? 0). cbv iota.\n"
     "             rewrite <- Hzfp. entailer!."),
    (_M, "(P2 gv shs strmp sv sp headp winp' s ssh p n c e data zfp) in",
     "(P2 gv shs strmp sv sp headp winp' s ssh p n c e data zfp tr) in"),
    # the window allocated: the event ZAlloc (2^wbits) of uw_ev (above: its failure, the event ZFail)
    (_M, "             replace (2 ^ i_wbits s - Zlength (@nil Z)) with (2 ^ i_wbits s) by (rewrite Zlength_nil; lia).\n"
         "             entailer!.",
     "             replace (2 ^ i_wbits s - Zlength (@nil Z)) with (2 ^ i_wbits s) by (rewrite Zlength_nil; lia).\n"
     "             entailer!. unfold uw_ev. rewrite Hw. change (0 =? 0) with true. cancel."),
]
