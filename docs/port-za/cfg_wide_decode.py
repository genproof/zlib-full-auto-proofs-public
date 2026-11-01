"""Configuration of docs/port-za/port.py for the decode theory (src/proof/rfc1951/) WIDE: calls of up to
2^32 - 1 bytes of input and of output space (Inv.mwf's two bounds raised from Int.max_signed to
Int.max_unsigned) on inputs of any length (DecodeDefs.dctx_ok's bound 2^31 - 1 on the input raised to
2^64 - 1), with inflateInit2's windowBits of a zlib stream anywhere from the header's window to 15
(DecodeDefs.accepts; inflate's HEAD rejects a zlib header only when its window is larger than state->wbits,
and keeps state->wbits).  Output: src/proof/wide/ (modules Zlib.proof.wide.*), suffix _wide."""

SUFFIX = '_wide'
OUT = 'wide'
SECTION = None
REQUIRES = ''
WHAT = ('the\n   bounds of the machine invariant Inv.mwf and of DecodeDefs.dctx_ok, here raised to calls of up to '
        '2^32 - 1 bytes\n   on inputs of any length, and on the windowBits accepted for a zlib stream (DecodeDefs.accepts),')

PREFIXES = ['Zlib.proof.rfc1951.', 'Zlib.proof.inflate.Inv', 'Zlib.proof.inflate.MwfLemmas']

TARGETS = [
    'Zlib.proof.rfc1951.DecKit',
    'Zlib.proof.rfc1951.DecHdr',
    'Zlib.proof.rfc1951.DecType',
    'Zlib.proof.rfc1951.DecTab',
    'Zlib.proof.rfc1951.DecDec',
    'Zlib.proof.rfc1951.DecFast',
    'Zlib.proof.rfc1951.DecTrl',
    'Zlib.proof.rfc1951.DecCall',
    'Zlib.proof.rfc1951.Decode',
]

# One pass of the switch keeps the wide invariant only outside EXLEN / EXTRA (the gzip extra field, where a
# length near 2^32 would let `len + copy` wrap: InvW.hdrW); the decode theory's machines never are in these
# modes (at_mode), so the passes use [stepf2_kd_stmt] (DecodeDefs) instead of Inv3's stepf2_mwf3_stmt.
SUBST = [
    (r'\bstepf2_mwf3_stmt\b', 'stepf2_kd_stmt'),
    # DecCall.dc_loop
    (r'\(SM flush m W L0\)', '(SM flush m W (kd_not_ext _ _ _ _ _ K) L0)'),
    # DecTab.dt_final and its three uses
    (r'\(SM Z_TREES m W L\)', '(SM Z_TREES m W NX L)'),
    (r'(\(dt_final SM DEC G pos inp ob flush m \(ttab_\w+ m\) OK P0 PL0 E) W L\)', r'\1 (kd_not_ext _ _ _ _ _ K) W L)'),
    # DecCall.dec_call_fx / dec_call: the bound on the input of the call
    (r'\bZF AO P0 PL IE RUN\b', 'ZF AO LIN P0 PL IE RUN'),
    # the output space of a call (DecDecDefs.dw, copy_stmt and its proof DecDecCopy.copy_ok_fix)
    (r'm_aout m <= 2 \^ 31 - 1', 'm_aout m <= 2 ^ 32 - 1'),
]


PATCHES = [
    ('Zlib.proof.inflate.Inv',
     "  mw_inp : Zlength (m_inp m) <= Int.max_signed /\\ bytes_ok (m_inp m);\n"
     "  mw_aout : 0 <= m_aout m <= Int.max_signed;",
     "  mw_inp : Zlength (m_inp m) <= Int.max_unsigned /\\ bytes_ok (m_inp m);\n"
     "  mw_aout : 0 <= m_aout m <= Int.max_unsigned;"),
    ('Zlib.proof.rfc1951.DecodeDefs',
     "slen G <= Zlength (dc_src G) /\\ Zlength (dc_src G) <= 2 ^ 31 - 1 /\\",
     "slen G <= Zlength (dc_src G) /\\ Zlength (dc_src G) <= 2 ^ 64 - 1 /\\"),
    ('Zlib.proof.inflate.Inv',
     "Lemma mwf_left: forall m, mwf m -> 0 <= m_left m <= Int.max_signed.",
     "Lemma mwf_left: forall m, mwf m -> 0 <= m_left m <= Int.max_unsigned."),
    ('Zlib.proof.inflate.Inv',
     "Lemma mwf_have: forall m, mwf m -> 0 <= m_have m <= Int.max_signed.",
     "Lemma mwf_have: forall m, mwf m -> 0 <= m_have m <= Int.max_unsigned."),
    ('Zlib.proof.rfc1951.DecodeDefs',
     "    dstep_post G pos inp ob flush m (stepf2 flush lenfix_list distfix_list m).",
     """    dstep_post G pos inp ob flush m (stepf2 flush lenfix_list distfix_list m).

(* the machine at a loop head is never in EXLEN or EXTRA (gzip headers without an extra field) *)
Lemma kd_not_ext G pos inp ob m : Kd G pos inp ob m -> m_mode m <> EXLEN /\\ m_mode m <> EXTRA.
Proof.
  intros K. destruct (kd_at _ _ _ _ _ K) as (_ & A). unfold m_mode.
  unfold HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, Zlib.proof.inflate.Model.TYPE, TYPEDO, STORED, COPY_, COPY, TABLE,
    LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, CHECK, LENGTH, DONE in *.
  repeat match goal with H: _ \\/ _ |- _ => destruct H end;
    repeat match goal with H: _ /\\ _ |- _ => destruct H end; split; lia.
Qed.

(* one pass of the switch keeps the machine invariant, outside the gzip extra field *)
Definition stepf2_kd_stmt : Prop :=
  forall flush m, mwf3 m -> m_mode m <> EXLEN /\\ m_mode m <> EXTRA -> m_leave m = 0 ->
  match stepf2 flush lenfix_list distfix_list m with IBrk m' => mwf3 m' | IRet _ m' => mwf3 m' end."""),
    ('Zlib.proof.rfc1951.DecDec',
     "split; [change Int.max_signed with (2 ^ 31 - 1) in A; lia|].",
     "split; [change Int.max_unsigned with (2 ^ 32 - 1) in A; lia|]."),
    ('Zlib.proof.rfc1951.DecTab',
     """  mwf3 m -> m_leave m = 0 ->
  (forall fl, stepf2 fl lenfix_list distfix_list m = ttab_run fl P) ->""",
     """  m_mode m <> EXLEN /\\ m_mode m <> EXTRA -> mwf3 m -> m_leave m = 0 ->
  (forall fl, stepf2 fl lenfix_list distfix_list m = ttab_run fl P) ->"""),
    ('Zlib.proof.rfc1951.DecTab', "  intros OK P0 PL E W L SE O.", "  intros OK P0 PL E NX W L SE O."),
    ('Zlib.proof.rfc1951.DecCall',
     "zf_ao z <= Int.max_signed ->\n  Zlength inp <= Int.max_signed -> bytes_ok inp ->",
     "zf_ao z <= Int.max_unsigned ->\n  Zlength inp <= Int.max_unsigned -> bytes_ok inp ->"),
    ('Zlib.proof.rfc1951.DecCall',
     "dctx_ok G -> dinv G pos out (l_s L) (zf_tout z) -> live_ok L -> zf_ok z -> zf_ao z <= 2 ^ 31 - 1 ->\n    0 <= pos ->",
     "dctx_ok G -> dinv G pos out (l_s L) (zf_tout z) -> live_ok L -> zf_ok z -> zf_ao z <= 2 ^ 32 - 1 ->\n"
     "    Zlength inp <= 2 ^ 32 - 1 -> 0 <= pos ->"),
    ('Zlib.proof.rfc1951.DecCall',
     "assert (LI: Zlength inp <= Int.max_signed) by dc_rep.",
     "assert (LI: Zlength inp <= Int.max_unsigned) by dc_rep."),
    ('Zlib.proof.rfc1951.Decode',
     "dctx_ok G -> dinv G pos out (l_s L) (zf_tout z) -> live_ok L -> zf_ok z -> zf_ao z <= 2 ^ 31 - 1 ->",
     "dctx_ok G -> dinv G pos out (l_s L) (zf_tout z) -> live_ok L -> zf_ok z ->\n"
     "    zf_ao z <= 2 ^ 32 - 1 -> Zlength inp <= 2 ^ 32 - 1 ->"),
    ('Zlib.proof.rfc1951.DecTrl',
     "change compcert.lib.Integers.Int.max_signed with 2147483647 in Hao. lia.",
     "change compcert.lib.Integers.Int.max_unsigned with 4294967295 in Hao. lia."),
    # (the original proof takes minutes: intuition on every side goal; the same argument, directly)
    ('Zlib.proof.inflate.MwfLemmas',
     "  apply mwf_set_mode; auto; try (intros; subst; congruence); try (intros D; apply ND; unfold decode_mode; intuition).",
     "  apply mwf_set_mode; auto; intros E; try (exfalso; subst md; congruence);\n"
     "    apply ND; unfold decode_mode in *; tauto."),
    # inflateInit2's windowBits for a zlib stream: any window from the header's to 15 (zlib's HEAD rejects a header
    # only when CINFO + 8 > state->wbits, and keeps state->wbits); then wbits is that window or 0 before HEAD
    ('Zlib.proof.rfc1951.DecodeDefs',
     "(* inflateInit2's windowBits accepts the stream *)",
     "(* inflateInit2's windowBits accepts the stream (zlib: any window from the header's to 15, 0 or 32 + the\n"
     "   header's) *)"),
    ('Zlib.proof.rfc1951.DecodeDefs',
     "  | WZlib _ _ _ => dc_iw G = dc_wb G \\/ dc_iw G = 0 \\/ dc_iw G = 32 + dc_wb G",
     "  | WZlib _ _ _ => dc_wb G <= dc_iw G <= 15 \\/ dc_iw G = 0 \\/ dc_iw G = 32 + dc_wb G"),
    ('Zlib.proof.rfc1951.DecHdr',
     "  | WZlib _ _ _ => wrap = 5 /\\ (wb0 = dc_wb G \\/ wb0 = 0) \\/ wrap = 7 /\\ wb0 = dc_wb G",
     "  | WZlib _ _ _ => wrap = 5 /\\ (dc_wb G <= wb0 <= 15 \\/ wb0 = 0) \\/ wrap = 7 /\\ wb0 = dc_wb G"),
    ('Zlib.proof.rfc1951.DecHdr',
     "  - destruct Ha as [A|[A|A]]; rewrite A in E.\n    + rewrite R2 in E. inversion E; auto.\n",
     "  - destruct Ha as [A|[A|A]]; [|rewrite A in E..].\n"
     "    + destruct (dh_reset2_vals (dc_iw G) ltac:(lia)) as (_ & R2' & _). rewrite R2' in E.\n"
     "      inversion E; subst. left. split; [reflexivity|left; lia].\n"),
    ('Zlib.proof.rfc1951.DecHdr',
     "  - destruct Ha as [A|[A|A]]; rewrite A; eauto.",
     "  - destruct Ha as [A|[A|A]];\n"
     "      [destruct (dh_reset2_vals (dc_iw G) ltac:(lia)) as (_ & R2' & _); rewrite R2'; eauto|rewrite A; eauto..]."),
    # HEAD on a zlib header: state->wbits is 0 (then it becomes the header's window) or at least the header's window
    ('Zlib.proof.rfc1951.DecHdr',
     "     (i_wbits (m_s m) = 0 \\/ i_wbits (m_s m) = wb) ->",
     "     (i_wbits (m_s m) = 0 \\/ wb <= i_wbits (m_s m) <= 15) ->"),
    ('Zlib.proof.rfc1951.DecHdr',
     "       i_wbits (m_s m2) = wb /\\ i_flags (m_s m2) = 0 /\\ i_check (m_s m2) = 1) /\\",
     "       i_wbits (m_s m2) = (if i_wbits (m_s m) =? 0 then wb else i_wbits (m_s m)) /\\ i_flags (m_s m2) = 0 /\\\n"
     "       i_check (m_s m2) = 1) /\\"),
    ('Zlib.proof.rfc1951.DecHdr',
     "    assert (Ew : (if i_wbits (m_s m) =? 0 then wb else i_wbits (m_s m)) = wb).\n"
     "    { destruct Hwb0 as [B|B]; rewrite B; [reflexivity|]. replace (wb =? 0) with false by (symmetry; apply Z.eqb_neq; lia).\n"
     "      reflexivity. }\n",
     ""),
    ('Zlib.proof.rfc1951.DecHdr',
     "      destruct Hwb0 as [B|B]; rewrite B; [reflexivity|]. rewrite Z.ltb_irrefl. apply andb_false_r. }",
     "      destruct Hwb0 as [B|B]; [rewrite B; reflexivity|].\n"
     "      replace (i_wbits (m_s m) <? wb) with false by (symmetry; apply Z.ltb_ge; lia). apply andb_false_r. }"),
    ('Zlib.proof.rfc1951.DecHdr',
     "    eexists; split; [reflexivity|]. unfold dh_same, dh_keep. dh_red. rewrite Ew.\n",
     "    eexists; split; [reflexivity|]. unfold dh_same, dh_keep. dh_red.\n"),
    ('Zlib.proof.rfc1951.DecHdr',
     "      assert (Hwb0 : i_wbits (m_s m) = 0 \\/ i_wbits (m_s m) = wb) by (rewrite Ewb; lia).",
     "      assert (Hwb0 : i_wbits (m_s m) = 0 \\/ wb <= i_wbits (m_s m) <= 15) by (rewrite Ewb; lia)."),
    ('Zlib.proof.rfc1951.DecHdr',
     "        -- intros _. rewrite W2. lia.",
     "        -- intros _. rewrite W2. destruct (Z.eqb_spec (i_wbits (m_s m)) 0); lia."),
    ('Zlib.proof.rfc1951.DecHdr',
     "        destruct Hwb0 as [X|X]; [right|left; congruence].",
     "        destruct Hwb0 as [X|X];\n"
     "          [right|left; rewrite W2; replace (i_wbits (m_s m) =? 0) with false by (symmetry; apply Z.eqb_neq; lia);\n"
     "                 reflexivity]."),
    # the trailer: a zlib windowBits from the header's window to 15 gives wrap 5 too
    ('Zlib.proof.rfc1951.DecTrl',
     "    repeat match goal with H: _ \\/ _ |- _ => destruct H as [H|H] end; rewrite Ha in R;",
     "    repeat match goal with H: _ \\/ _ |- _ => destruct H as [H|H] end;\n"
     "    try (match type of Ha with _ <= _ <= _ =>\n"
     "           destruct (trl_wb_cases (dc_iw G) ltac:(lia)) as [Ha'|[Ha'|[Ha'|[Ha'|[Ha'|[Ha'|[Ha'|Ha']]]]]]];\n"
     "           clear Ha; rename Ha' into Ha end);\n"
     "    rewrite Ha in R;"),
]
