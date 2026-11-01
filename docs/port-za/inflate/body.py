"""Patches of the inflate port (docs/port-za/cfg_inflate.py), part body: see docs/port-za/inflate/README.md.

inflate()'s body (src/proof/inflate_api/Body5*.v) with the allocator-generic, wide interface of
Spec5.inflate_spec_za:
- the allocator's state za_res gv tr replaces mem_mgr gv.  Along the loop it is part of the frame X (the loop
  and the switch do not allocate); the exit takes it out of X (exit_part5: lstate F (za_res gv tr * X) m),
  updatewindow appends its event, and the exit's return gets za_res gv (tr ++ win_ev (m_s m) s') with s' the
  saved state (exit_ok5);
- the bounds of the wide calls: fin_ok5 / tail_facts / the exit's lemmas with Int.max_unsigned for the input
  and the output space, no avail_in / avail_out bounds in the prologue;
- InvW.swfW of the saved state: leave_fin5 adds it (from InvW.hdrW of the machine, mwf3); m_init_mwf3 takes
  the precondition's swfW for the hdrW part of the loop head's invariant.
The pure facts these patches use are in src/proof/za/inflate_api/BodyKitZ.v (hand-written)."""

P = 'Zlib.proof.inflate_api.'
KIT = 'Require Import Zlib.proof.za.inflate_api.BodyKitZ.'

PATCHES = [
    # ---------------------------------------------------------------------------------------------------
    # Body5Parts: the statements
    (P + 'Body5Parts',
     "(* loop_state (Loop.v) with the header buffers' tokens (CaseHyps5.v hdr_tok), the allocator and the\n"
     "   stream's zalloc/zfree (updatewindow at the exit) and X: what else the body holds (the state's\n"
     "   malloc token and padding, the buffers' tokens) *)",
     "(* loop_state (Loop.v) with the header buffers' tokens (CaseHyps5.v hdr_tok), the stream's zalloc/zfree\n"
     "   (updatewindow at the exit) and X: what else the body holds (the allocator's state, the state's block\n"
     "   token and padding, the buffers' tokens) *)"),
    (P + 'Body5Parts',
     "hdr_tok F m; mem_mgr (f_gv F); zfuncs (f_gv F); X).",
     "hdr_tok F m; zfuncs (f_gv F); X)."),
    (P + 'Body5Parts',
     "hdr_tok F m'; mem_mgr (f_gv F); zfuncs (f_gv F); X]",
     "hdr_tok F m'; zfuncs (f_gv F); X]"),
    (P + 'Body5Parts',
     "  0 <= m_snx m <= Zlength (m_inp m) /\\ Zlength (m_inp m) <= Int.max_signed /\\\n"
     "  0 <= m_sow m <= m_aout m /\\ m_aout m <= Int.max_signed /\\",
     "  0 <= m_snx m <= Zlength (m_inp m) /\\ Zlength (m_inp m) <= Int.max_unsigned /\\\n"
     "  0 <= m_sow m <= m_aout m /\\ m_aout m <= Int.max_unsigned /\\"),
    (P + 'Body5Parts',
     "(* the machine after inf_leave (Model.v) is a live stream's, with the same header and input;\n"
     "   data_type is an int *)",
     "(* the machine after inf_leave (Model.v) is a live stream's (its saved state satisfies InvW.swfW), with\n"
     "   the same header and input; data_type is an int *)"),
    (P + 'Body5Parts',
     "  fin_ok5 (r_m res) /\\ (forall d, r_dtype res = Some d -> srange d) /\\",
     "  Zlib.proof.inflate.InvW.swfW (m_s (r_m res)) /\\\n"
     "  fin_ok5 (r_m res) /\\ (forall d, r_dtype res = Some d -> srange d) /\\"),
    (P + 'Body5Parts',
     "(* each outcome of inf_leave (Model.v) gives the function's return; winp is the window pointer after\n"
     "   the exit (the old one when the window existed) *)",
     "(* each outcome of inf_leave (Model.v) gives the function's return; winp is the window pointer after\n"
     "   the exit (the old one when the window existed); the allocator's trace tr gets the window the exit\n"
     "   allocated (win_ev) *)"),
    (P + 'Body5Parts',
     "Definition exit_ok5 (F: frame) (X: mpred) (m: mst) (R: ret_assert) : Prop :=",
     "Definition exit_ok5 (F: frame) (X: mpred) (tr: list zev) (m: mst) (R: ret_assert) : Prop :="),
    (P + 'Body5Parts',
     "               mem_mgr (f_gv F); zfuncs (f_gv F); X]))\n"
     "      |-- RA_return R (Some (zv (r_ret res))).",
     "               za_res (f_gv F) (tr ++ win_ev (m_s m) (m_s (r_m res))); zfuncs (f_gv F); X]))\n"
     "      |-- RA_return R (Some (zv (r_ret res)))."),
    (P + 'Body5Parts',
     "  forall {Espec: OracleKind} (F: frame) (X: mpred) (m: mst) (R: ret_assert),\n"
     "  frame_ok5 F -> mwf3 m -> m_leave m = 1 -> out_inv m -> win_inv5 (m_s m) -> exit_ok5 F X m R ->\n"
     "  semax Delta_inflate5 (lstate F X m) inflate_exit R.",
     "  forall {Espec: OracleKind} (F: frame) (X: mpred) (tr: list zev) (m: mst) (R: ret_assert),\n"
     "  frame_ok5 F -> mwf3 m -> m_leave m = 1 -> out_inv m -> win_inv5 (m_s m) -> za_now tr + 2 ^ 23 <= za_cap ->\n"
     "  is_pointer_or_null za_opaque -> exit_ok5 F X tr m R ->\n"
     "  semax Delta_inflate5 (lstate F (za_res (f_gv F) tr * X) m) inflate_exit R."),
    (P + 'Body5Parts',
     "(gsh tsh: share) (itok otok: bool) (vh vl vb: val) : environ -> mpred :=",
     "(gsh tsh: share) (itok otok: bool) (vh vl vb: val) (tr: list zev) : environ -> mpred :="),
    (P + 'Body5Parts',
     "crc_table_at tsh gv; mem_mgr gv; zfuncs gv",
     "crc_table_at tsh gv; za_res gv tr; zfuncs gv"),
    (P + 'Body5Parts',
     "(gsh tsh: share) (itok otok: bool) (vh vl vb: val)\n    : environ -> mpred :=",
     "(gsh tsh: share) (itok otok: bool) (vh vl vb: val)\n    (tr: list zev) : environ -> mpred :="),
    (P + 'Body5Parts',
     "(xfr L itok otok ib o) (m_init z L inp).",
     "(za_res gv tr * xfr L itok otok ib o) (m_init z L inp)."),
    (P + 'Body5Parts',
     "    (vh vl vb: val) (R: ret_assert),",
     "    (vh vl vb: val) (tr: list zev) (R: ret_assert),"),
    (P + 'Body5Parts',
     "  zf_ai z <= Int.max_signed -> zf_ao z <= Int.max_signed ->\n",
     ""),
    (P + 'Body5Parts',
     "(pro_pre gv shs strmp z st ib ob flush gsh tsh itok otok vh vl vb)",
     "(pro_pre gv shs strmp z st ib ob flush gsh tsh itok otok vh vl vb tr)"),
    (P + 'Body5Parts',
     "(pro_post gv shs strmp z st ib inp ob flush gsh tsh itok otok vh vl vb)",
     "(pro_post gv shs strmp z st ib inp ob flush gsh tsh itok otok vh vl vb tr)"),

    # ---------------------------------------------------------------------------------------------------
    # Body5Conv: the loop head's invariant (with InvW.hdrW from the precondition's swfW); fin_ok5 wide
    (P + 'Body5Conv',
     "  live_ok L -> zf_ok z -> zf_ao z <= Int.max_signed ->\n"
     "  Zlength inp <= Int.max_signed -> bytes_ok inp ->\n"
     "  mwf3 (m_init z L inp).",
     "  live_ok L -> zf_ok z -> Zlib.proof.inflate.InvW.swfW (l_s L) ->\n"
     "  Zlength inp <= Int.max_unsigned -> bytes_ok inp ->\n"
     "  mwf3 (m_init z L inp)."),
    (P + 'Body5Conv',
     "  intros z L inp (HP & HS & HM & HH & HS3 & _) HZ HA HI HB.",
     "  intros z L inp (HP & HS & HM & HH & HS3 & _) HZ HW HI HB."),
    (P + 'Body5Conv',
     "  - apply s_typedo_swf3. exact HS3.\nQed.",
     "  - split; [apply s_typedo_swf3; exact HS3 | ].\n"
     "    unfold Zlib.proof.inflate.InvW.hdrW, m_init, m_mode. cbn [m_s m_hold m_bits].\n"
     "    destruct (i_mode (l_s L) =? Zlib.proof.inflate.Model.TYPE); [ | exact HW].\n"
     "    cbn [i_mode set_i_mode i_hold i_bits i_length]. unfold TYPEDO, EXLEN, EXTRA.\n"
     "    split; intro E; discriminate.\nQed."),
    (P + 'Body5Conv',
     "  intros m [W S3] WI.",
     "  intros m [W [S3 _]] WI."),

    # ---------------------------------------------------------------------------------------------------
    # Body5Fin: leave_fin5 with swfW of the saved state
    (P + 'Body5Fin',
     "Require Import Zlib.proof.inflate_api.Body5Parts.",
     "Require Import Zlib.proof.inflate_api.Body5Parts.\n" + KIT),
    (P + 'Body5Fin',
     "  intros flush m m2 [W S3] WI",
     "  intros flush m m2 [W [S3 _]] WI"),
    (P + 'Body5Fin',
     "  intros flush m res MW O WI IL. pose proof MW as [W S3].",
     "  intros flush m res MW O WI IL. pose proof MW as [W [S3 H3]].\n"
     "  split; [exact (inf_leave_swfW flush m res H3 IL) | ]."),
    # ---------------------------------------------------------------------------------------------------
    # Body5Loop: the loop state and the switch's frame without mem_mgr (the allocator's state is in X)
    (P + 'Body5Loop',
     "hdr_tok F m; mem_mgr (f_gv F); zfuncs (f_gv F); X).",
     "hdr_tok F m; zfuncs (f_gv F); X)."),
    (P + 'Body5Loop',
     "(* what the switch does not touch: the allocator, the stream's functions, X, and the stack variables'\n"
     "   and globals' facts (for the returns) *)",
     "(* what the switch does not touch: the stream's functions, X (with the allocator's state), and the stack\n"
     "   variables' and globals' facts (for the returns) *)"),
    (P + 'Body5Loop',
     "(SEPx [mem_mgr (f_gv F); zfuncs (f_gv F); X])",
     "(SEPx [zfuncs (f_gv F); X])"),

    # ---------------------------------------------------------------------------------------------------
    # Body5ExitKit / Body5ExitTail: RESTORE and the tail, for any X; tail_facts wide
    (P + 'Body5ExitKit',
     "hdr_tok F m; mem_mgr (f_gv F); zfuncs (f_gv F); X",
     "hdr_tok F m; zfuncs (f_gv F); X"),
    (P + 'Body5ExitKit',
     "remember (f_gv F _zcalloc) as zca eqn:Hzca. remember (f_gv F _zcfree) as zcf eqn:Hzcf.",
     "remember za_alloc as zca eqn:Hzca. remember za_free as zcf eqn:Hzcf."),
    (P + 'Body5ExitKit',
     "0 <= m_nx m <= Zlength (m_inp m) /\\ Zlength (m_inp m) <= Int.max_signed /\\\n"
     "  m_left m <= m_out m <= m_aout m /\\ Zlength (m_ow m) <= m_aout m <= Int.max_signed /\\",
     "0 <= m_nx m <= Zlength (m_inp m) /\\ Zlength (m_inp m) <= Int.max_unsigned /\\\n"
     "  m_left m <= m_out m <= m_aout m /\\ Zlength (m_ow m) <= m_aout m <= Int.max_unsigned /\\"),
    (P + 'Body5ExitTail',
     "hdr_tok F m0; mem_mgr (f_gv F); zfuncs (f_gv F); X",
     "hdr_tok F m0; zfuncs (f_gv F); X"),
    (P + 'Body5ExitTail',
     "remember (f_gv F _zcalloc) as zca eqn:Hzca. remember (f_gv F _zcfree) as zcf eqn:Hzcf.",
     "remember za_alloc as zca eqn:Hzca. remember za_free as zcf eqn:Hzcf."),
    (P + 'Body5ExitTail',
     "0 <= inn <= Int.max_signed -> 0 <= o <= Int.max_signed ->",
     "0 <= inn <= Int.max_unsigned -> 0 <= o <= Int.max_unsigned ->"),
    # ---------------------------------------------------------------------------------------------------
    # Body5ExitWin: the window update with the allocator's state taken out of X; its event
    (P + 'Body5ExitWin',
     "Require Import Zlib.proof.inflate_api.Body5ExitKit.",
     "Require Import Zlib.proof.inflate_api.Body5ExitKit.\n" + KIT),
    (P + 'Body5ExitWin',
     "hdr_tok F m; mem_mgr (f_gv F); zfuncs (f_gv F); X).",
     "hdr_tok F m; zfuncs (f_gv F); X)."),
    (P + 'Body5ExitWin',
     "m_sow m = Zlength (m_ow m) -> urange (m_out m) -> 0 <= m_left m <= Int.max_signed ->",
     "m_sow m = Zlength (m_ow m) -> urange (m_out m) -> 0 <= m_left m <= Int.max_unsigned ->"),
    (P + 'Body5ExitWin',
     "              mem_mgr (f_gv F); zfuncs (f_gv F); X]))",
     "              za_res (f_gv F) (tr ++ [ZFail]); zfuncs (f_gv F); X]))"),
    (P + 'Body5ExitWin',
     "Lemma semax_ex_call {Espec: OracleKind} (F: frame) (X: mpred) (m: mst) (v: val) (R: ret_assert):",
     "Lemma semax_ex_call {Espec: OracleKind} (F: frame) (X: mpred) (tr: list zev) (m: mst) (v: val)\n"
     "    (R: ret_assert):"),
    (P + 'Body5ExitWin',
     "  Zlength (m_ow m) <= m_aout m <= Int.max_signed -> bytes_ok (m_ow m) ->\n"
     "  (i_win (m_s m) = false ->\n",
     "  Zlength (m_ow m) <= m_aout m <= Int.max_unsigned -> bytes_ok (m_ow m) ->\n"
     "  (i_win (m_s m) = false -> za_now tr + 2 ^ i_wbits (m_s m) <= za_cap) -> is_pointer_or_null za_opaque ->\n"
     "  (i_win (m_s m) = false ->\n"),
    (P + 'Body5ExitWin',
     "  semax Delta_inflate5 (lstate_t F X m v) ex_call\n"
     "    (overridePost (EX winp: val, !! (i_win (m_s m) = true -> winp = f_winp F) &&\n"
     "                     lstate (set_f_winp_dt F winp (f_dt F)) X (mupd m)) R).",
     "  semax Delta_inflate5 (lstate_t F (za_res (f_gv F) tr * X) m v) ex_call\n"
     "    (overridePost (EX winp: val, !! (i_win (m_s m) = true -> winp = f_winp F) &&\n"
     "                     lstate (set_f_winp_dt F winp (f_dt F))\n"
     "                       (za_res (f_gv F) (tr ++ win_ev (m_s m) (m_s (mupd m))) * X) (mupd m)) R)."),
    (P + 'Body5ExitWin',
     "  intros [FOK FL] SW ESOW RO RA BO HMEM.",
     "  intros [FOK FL] SW ESOW RO RA BO HCAP HOP HMEM."),
    (P + 'Body5ExitWin',
     "     olo + Zlength (m_ow m), win_data m).",
     "     olo + Zlength (m_ow m), win_data m, tr)."),
    (P + 'Body5ExitWin',
     "    destruct R as [Rn Rb Rc Rr]; cbn [RA_normal].\n    Exists winp'.",
     "    destruct R as [Rn Rb Rc Rr]; cbn [RA_normal].\n    Exists winp'.\n"
     "    rewrite (uw_ev_win_ev (m_s m) (win_data m))."),
    (P + 'Body5ExitWin',
     "  - subst r winp'. cbn [Z.eqb].",
     "  - subst r winp'. cbn [Z.eqb].\n"
     "    replace (uw_ev (m_s m) 1) with [ZFail] by (unfold uw_ev; rewrite HWF; reflexivity)."),
    (P + 'Body5ExitWin',
     "Lemma semax_ex_win {Espec: OracleKind} (F: frame) (X: mpred) (m: mst) (R: ret_assert):\n"
     "  frame_ok5 F -> mwf3 m -> out_inv m ->",
     "Lemma semax_ex_win {Espec: OracleKind} (F: frame) (X: mpred) (tr: list zev) (m: mst) (R: ret_assert):\n"
     "  frame_ok5 F -> mwf3 m -> out_inv m -> za_now tr + 2 ^ 23 <= za_cap -> is_pointer_or_null za_opaque ->"),
    (P + 'Body5ExitWin',
     "  semax Delta_inflate5 (lstate F X (restore m)) ex_win\n"
     "    (overridePost (EX winp: val, !! (i_win (m_s m) = true -> winp = f_winp F) &&\n"
     "                     lstate (set_f_winp_dt F winp (f_dt F)) X (mwin (f_flush F) m)) R).",
     "  semax Delta_inflate5 (lstate F (za_res (f_gv F) tr * X) (restore m)) ex_win\n"
     "    (overridePost (EX winp: val, !! (i_win (m_s m) = true -> winp = f_winp F) &&\n"
     "                     lstate (set_f_winp_dt F winp (f_dt F))\n"
     "                       (za_res (f_gv F) (tr ++ win_ev (m_s m) (m_s (mwin (f_flush F) m))) * X)\n"
     "                       (mwin (f_flush F) m)) R)."),
    (P + 'Body5ExitWin',
     "  intros FO [W W3] [O1 [O2 _]] HMEM.",
     "  intros FO [W W3] [O1 [O2 _]] HCAP HOP HMEM."),
    (P + 'Body5ExitWin',
     "    change (i_win (m_s m)) with (i_win (m_s (restore m))).\n"
     "    pose proof (mw_ow _ W) as [OW BO]. pose proof (mw_aout _ W) as AO.\n"
     "    change Delta with Delta_inflate5. specialize (HMEM eq_refl).\n"
     "    eapply semax_pre; [ | apply (semax_ex_call F X (restore m) (Vint (Int.repr (b2z true))) R); auto;\n"
     "                          exact (conj OW (proj2 AO))].",
     "    change (i_win (m_s m)) with (i_win (m_s (restore m))).\n"
     "    change (win_ev (m_s m)) with (win_ev (m_s (restore m))).\n"
     "    pose proof (mw_ow _ W) as [OW BO]. pose proof (mw_aout _ W) as AO.\n"
     "    assert (CAPW: i_win (m_s (restore m)) = false -> za_now tr + 2 ^ i_wbits (m_s (restore m)) <= za_cap).\n"
     "    { intros _. pose proof (sw_wbits _ SR).\n"
     "      assert (2 ^ i_wbits (m_s (restore m)) <= 2 ^ 23) by (apply Z.pow_le_mono_r; lia). lia. }\n"
     "    change Delta with Delta_inflate5. specialize (HMEM eq_refl).\n"
     "    eapply semax_pre; [ | apply (semax_ex_call F X tr (restore m) (Vint (Int.repr (b2z true))) R); auto;\n"
     "                          first [exact (conj OW (proj2 AO)) | exact CAPW]]."),
    (P + 'Body5ExitWin',
     "    replace (mwin (f_flush F) m) with (restore m) by (unfold mwin; rewrite HB; reflexivity).\n"
     "    unfold lstate. entailer!.",
     "    replace (mwin (f_flush F) m) with (restore m) by (unfold mwin; rewrite HB; reflexivity).\n"
     "    rewrite (win_ev_same (m_s m) (m_s (restore m)) eq_refl eq_refl), app_nil_r.\n"
     "    unfold lstate. entailer!."),

    # ---------------------------------------------------------------------------------------------------
    # Body5Exit: the exit with the allocator's state and the window's event
    (P + 'Body5Exit',
     "Require Import Zlib.proof.inflate_api.Body5ExitTail.",
     "Require Import Zlib.proof.inflate_api.Body5ExitTail.\n" + KIT),
    (P + 'Body5Exit',
     "  intros Espec F X m R FO W L O WI HEX.",
     "  intros Espec F X tr m R FO W L O WI HCAP HOP HEX."),
    (P + 'Body5Exit',
     "    exact (HEX (Res Z_MEM_ERROR (set_mode (restore m) MEM) None) nullval\n"
     "               (il_mem _ _ HB E) (fun E' => ltac:(congruence))). }",
     "    pose proof (HEX (Res Z_MEM_ERROR (set_mode (restore m) MEM) None) nullval\n"
     "               (il_mem _ _ HB E) (fun E' => ltac:(congruence))) as HM.\n"
     "    pose proof (leave_mem_ev (f_flush F) m (mw_s _ (proj1 W)) HB E) as LM.\n"
     "    change (m_s (set_mode (restore m) MEM))\n"
     "      with (m_s (r_m (Res Z_MEM_ERROR (set_mode (restore m) MEM) None))) in LM.\n"
     "    rewrite LM in HM.\n"
     "    exact HM. }"),
    (P + 'Body5Exit',
     "  apply (ex_tail_ok Espec (set_f_winp_dt F winp (f_dt F)) X (mwin (f_flush F) m) R).",
     "  apply (ex_tail_ok Espec (set_f_winp_dt F winp (f_dt F))\n"
     "           (za_res (f_gv F) (tr ++ win_ev (m_s m) (m_s (mwin (f_flush F) m))) * X) (mwin (f_flush F) m) R)."),
    (P + 'Body5Exit',
     "    rewrite leave_fin_eq in E. exact E.",
     "    rewrite leave_fin_win_ev, leave_fin_eq in E.\n"
     "    apply ENTAIL_sep_perm'. exact E."),
    # ---------------------------------------------------------------------------------------------------
    # Body5Pro: the prologue with the allocator's state, without avail_in / avail_out bounds
    (P + 'Body5Pro',
     "intros Espec gv shs strmp z st ib inp ob flush gsh tsh itok otok vh vl vb R\n"
     "  HF HG HT HIT HOT HNI HIB HOB HAI HAO HBAD.",
     "intros Espec gv shs strmp z st ib inp ob flush gsh tsh itok otok vh vl vb tr R\n"
     "  HF HG HT HIT HOT HNI HIB HOB HBAD."),
    (P + 'Body5Pro',
     "   (nullval, (zv (zf_dt z), (lv (zf_adler z), zf_res z)))",
     "   (za_opaque, (zv (zf_dt z), (adler_val (zf_adler z), zf_res z)))"),
    (P + 'Body5ExitTail',
     "Require Import Zlib.proof.inflate_api.Body5ExitKit.",
     "Require Import Zlib.proof.inflate_api.Body5ExitKit.\n" + KIT),
    (P + 'Body5ExitTail',
     "  subst ct.\n  entailer!.",
     "  subst ct.\n  sep_apply strm_adler_weaken.\n  entailer!."),
    (P + 'Body5Pro',
     "pose proof ZOK as (ZA & _).",
     "pose proof ZOK as (ZAI & _)."),
    # ---------------------------------------------------------------------------------------------------
    # Body5_inflate: the assembly with the allocator's trace, the window's event and swfW
    (P + 'Body5_inflate',
     "Require Import Zlib.proof.inflate_api.Body5Fin.",
     "Require Import Zlib.proof.inflate_api.Body5Fin.\n" + KIT +
     "\nRequire Import Zlib.proof.za.inflate_api.RetModeZ.\nRequire Import Zlib.proof.za.inflate_api.NoMemZ.\n"
     "Require Zlib.proof.inflate.Steps2."),
    (P + 'Body5_inflate',
     "assert (RET: forall (F: frame) (Y T X: mpred) (r: Z),",
     "assert (RET: forall (F: frame) (Y T X: mpred) (r: Z) (ev: list zev),"),
    (P + 'Body5_inflate',
     "          !! (inflate_rel flush strmp z st ib inp ob r z' st' ow) &&\n"
     "          (istream_opt gv shs strmp z' st' * head_opt (is_live strmp st') *\n"
     "           bufs_opt (is_live strmp st) ib ob ow itok otok *\n"
     "           tables_rep gsh gv * crc_table_at tsh gv)) ->\n"
     "  ENTAIL Delta_inflate5, PROPx [] (LOCALx (ret_locals F)\n"
     "     (SEPx [Y; locals_rep F; T; mem_mgr (f_gv F); zfuncs (f_gv F); X])) |-- RA_return RR (Some (zv r))).",
     "          !! (inflate_rel flush strmp z st ib inp ob r z' st' ow /\\\n"
     "              match st' with Some L' => Zlib.proof.inflate.InvW.swfW (l_s L') | None => True end /\\\n"
     "              ev = match st, st' with Some L, Some L' => win_ev (l_s L) (l_s L') | _, _ => [] end) &&\n"
     "          (istream_opt gv shs strmp z' st' * head_opt (is_live strmp st') *\n"
     "           bufs_opt (is_live strmp st) ib ob ow itok otok *\n"
     "           tables_rep gsh gv * crc_table_at tsh gv * za_res gv (tr ++ ev))) ->\n"
     "  ENTAIL Delta_inflate5, PROPx [] (LOCALx (ret_locals F)\n"
     "     (SEPx [Y; locals_rep F; T; zfuncs (f_gv F); X])) |-- RA_return RR (Some (zv r)))."),
    (P + 'Body5_inflate',
     "{ intros F Y T X r E1 E2 E3 E4 HX.",
     "{ intros F Y T X r ev E1 E2 E3 E4 HX."),
    (P + 'Body5_inflate',
     "  Intros z' st' ow. Exists r z' st' ow. entailer!. }",
     "  Intros z' st' ow.\n"
     "  repeat match goal with Hc: _ /\\ _ |- _ => destruct Hc end. subst ev.\n"
     "  Exists r z' st' ow. entailer!. }"),
    (P + 'Body5_inflate',
     "{ apply (pro_part5 _ gv shs strmp z st ib inp ob flush gsh tsh itok otok v_here v_last v_hbuf RR); auto.",
     "{ apply (@pro_part5 ZA ZAV _ gv shs strmp z st ib inp ob flush gsh tsh itok otok v_here v_last v_hbuf tr RR);\n"
     "    auto."),
    (P + 'Body5_inflate',
     "  Exists Z_STREAM_ERROR z st (@nil Z). entailer!.\n  left. auto. }",
     "  Exists Z_STREAM_ERROR z st (@nil Z).\n"
     "  destruct st as [L0|]; cbv beta iota;\n"
     "    [rewrite (win_ev_same (l_s L0) (l_s L0) eq_refl eq_refl) | ]; rewrite app_nil_r; entailer!; left; auto. }"),
    (P + 'Body5_inflate',
     "assert (INP: Zlength inp <= Int.max_signed /\\ bytes_ok inp).\n"
     "{ destruct ib as [ | ish ip ilo ilen ic].\n"
     "  - subst inp. split; [rewrite Zlength_nil; rep_lia | constructor].\n"
     "  - destruct H3 as [(_ & _ & _ & _ & _ & _ & _ & HB) HA]. split; [lia | exact HB]. }",
     "assert (INP: Zlength inp <= Int.max_unsigned /\\ bytes_ok inp).\n"
     "{ destruct ib as [ | ish ip ilo ilen ic].\n"
     "  - subst inp. split; [rewrite Zlength_nil; rep_lia | constructor].\n"
     "  - pose proof ZOK as (ZAI & _).\n"
     "    destruct H3 as [(_ & _ & _ & _ & _ & _ & _ & HB) HA]. split; [lia | exact HB]. }"),
    (P + 'Body5_inflate',
     "{ apply m_init_mwf3; tauto. }",
     "{ apply m_init_mwf3; try tauto.\n"
     "  all: match goal with Hs: context [Zlib.proof.inflate.InvW.swfW] |- _ => exact Hs end. }"),
    (P + 'Body5_inflate',
     "{ apply (loop_part5 _ F X m0\n",
     "{ apply (@loop_part5 ZA ZAV _ F (za_res gv tr * X) m0\n"),
    (P + 'Body5_inflate',
     "           (fun m => i_win (m_s m) = i_win (m_s m0) /\\ win_inv5 (m_s m) /\\ m_inp m = inp)\n",
     "           (fun m => i_win (m_s m) = i_win (m_s m0) /\\ win_inv5 (m_s m) /\\ m_inp m = inp /\\\n"
     "                     Zlib.proof.inflate.InvW.swfW (m_s m) /\\ (i_mode (m_s m) = MEM -> i_mode (m_s m0) = MEM))\n"),
    (P + 'Body5_inflate',
     "    destruct (stepf2 (f_flush F) lenfix_list distfix_list m); intuition congruence.",
     "    pose proof (stepf2_ret_swfW (f_flush F) lenfix_list distfix_list m) as HSR.\n"
     "    pose proof (stepf2_brk_not_mem (f_flush F) lenfix_list distfix_list m) as HNB.\n"
     "    pose proof (stepf2_ret_mem (f_flush F) lenfix_list distfix_list m) as HRM.\n"
     "    (* a pass in mode MEM returns: a call starting in MEM stays at m0; the switch never goes on in MEM *)\n"
     "    assert (MB: i_mode (m_s m0) = MEM -> exists r m', stepf2 (f_flush F) lenfix_list distfix_list m = IRet r m').\n"
     "    { intros M0. rewrite (MM0 M0). exists Z_MEM_ERROR, m0. apply Zlib.proof.inflate.Steps2.stepf2_MEM. exact M0. }\n"
     "    destruct (stepf2 (f_flush F) lenfix_list distfix_list m) eqn:ES.\n"
     "    { first [pose proof (HNB _ eq_refl) as NB' | pose proof (HNB _ ES) as NB'].\n"
     "      split; [ | split; [ | split; [ | split; [ | split]]]];\n"
     "        [intuition congruence .. | intros M0; destruct (MB M0) as (? & ? & EB);\n"
     "          first [discriminate EB | rewrite ES in EB; discriminate EB]\n"
     "        | intros M1; exfalso; exact (NB' M1)]. }\n"
     "    first [pose proof (HSR _ _ eq_refl) as HSW | pose proof (HSR _ _ ES) as HSW].\n"
     "    first [pose proof (HRM _ _ eq_refl) as HRM' | pose proof (HRM _ _ ES) as HRM'].\n"
     "    split; [ | split; [ | split; [ | split; [exact HSW | intros M; exact (MM1 (HRM' M))]]]];\n"
     "      intuition congruence."),
    (P + 'Body5_inflate',
     "  - intros r m' HL HW HDm (HWin & HWV & HIP).\n"
     "    apply RET; [reflexivity | reflexivity | reflexivity | reflexivity | ].",
     "  - intros r m' HL HW HDm (HWin & HWV & HIP & HSW & HMM).\n"
     "    apply (RET _ _ _ _ _ []); [reflexivity | reflexivity | reflexivity | reflexivity | ]."),
    (P + 'Body5_inflate',
     "    + apply prop_right. right. split; [exact NB | ].\n"
     "      exists L, o, (Res r m' None), (l_winp L).",
     "    + apply prop_right.\n"
     "      split; [ | split; [exact HSW | cbv beta iota; symmetry; apply win_ev_nomem;\n"
     "                         [exact (eq_trans HWin WIN0) | intros M; apply M0L, HMM, M]]].\n"
     "      right. split; [exact NB | ].\n"
     "      exists L, o, (Res r m' None), (l_winp L)."),
    (P + 'Body5_inflate',
     "    + rewrite ISL. unfold X, xfr. sep_apply (mem_rep_istream5 F m' HLV HZV WS NN).",
     "    + rewrite ISL, app_nil_r. unfold X, xfr. sep_apply (@mem_rep_istream5 ZA ZAV F m' HLV HZV WS NN)."),
    (P + 'Body5_inflate',
     "apply (exit_part5 _ F X m RR FOK MW' ML OI' WV).",
     "apply (@exit_part5 ZA ZAV _ F X tr m RR FOK MW' ML OI' WV); [assumption | assumption | ]."),
    (P + 'Body5_inflate',
     "as (FO & DTr & EH & EHd & EI).",
     "as (SWr & FO & DTr & EH & EHd & EI)."),
    (P + 'Body5_inflate',
     "rewrite TK.\napply (RET F'); [reflexivity | reflexivity | reflexivity | reflexivity | ].",
     "rewrite TK.\napply ENTAIL_sep_perm.\n"
     "apply (RET F' _ _ _ _ (win_ev (m_s m) (m_s (r_m res))));\n"
     "  [reflexivity | reflexivity | reflexivity | reflexivity | ]."),
    (P + 'Body5_inflate',
     "- apply prop_right. right. split; [exact NB | ].\n  exists L, o, res, winp.",
     "- apply prop_right.\n"
     "  split; [ | split; [exact SWr | cbv beta iota;\n"
     "                     apply win_ev_congr; [rewrite WI; exact WIN0 | reflexivity | reflexivity | exact MEQ | reflexivity]]].\n"
     "  right. split; [exact NB | ].\n  exists L, o, res, winp."),
    (P + 'Body5ExitTail',
     "  apply semax_ret_tmp with (r := lt_r (f_flush F) inn o (m_ret m2)).",
     "  apply (@semax_ret_tmp ZA ZAV) with (r := lt_r (f_flush F) inn o (m_ret m2))."),
    (P + 'Body5ExitWin',
     "m_left m <= m_out m <= m_aout m -> Zlength (m_ow m) <= m_aout m <= Int.max_signed ->",
     "m_left m <= m_out m <= m_aout m -> Zlength (m_ow m) <= m_aout m <= Int.max_unsigned ->"),
    (P + 'Body5ExitWin',
     "(nullval, (Vint (Int.repr dt), (Vlong (Int64.repr (m_adler m)), vres))",
     "(za_opaque, (Vint (Int.repr dt), (adler_val (m_adler m), vres))"),
    (P + 'Body5_inflate',
     "- rewrite ISL. unfold X, xfr. sep_apply (mem_rep_istream5 F' (r_m res) HLV HZV WS NN).",
     "- rewrite ISL. unfold X, xfr. sep_apply (@mem_rep_istream5 ZA ZAV F' (r_m res) HLV HZV WS NN)."),
    (P + 'Body5_inflate',
     "assert (DT: srange (zf_dt z)) by (destruct ZOK as (_&_&_&_&?&_); exact H7).",
     "assert (DT: srange (zf_dt z)) by (destruct ZOK as (_&_&_&_&HDT&_); exact HDT)."),
    # the mode MEM along the loop (the event of a failed window allocation, win_ev): the loop head's machine
    # is in MEM iff the call started in MEM (M0L); a call that starts in MEM never leaves m0 (it returns at
    # once), and a machine of the loop is in MEM only when the call started in MEM
    (P + 'Body5_inflate',
     "assert (WIN0: i_win (m_s m0) = i_win (l_s L)).\n"
     "{ unfold m0. rewrite m_init_s. unfold s_typedo.\n"
     "  destruct (i_mode (l_s L) =? Zlib.proof.inflate.Model.TYPE); reflexivity. }",
     "assert (WIN0: i_win (m_s m0) = i_win (l_s L)).\n"
     "{ unfold m0. rewrite m_init_s. unfold s_typedo.\n"
     "  destruct (i_mode (l_s L) =? Zlib.proof.inflate.Model.TYPE); reflexivity. }\n"
     "assert (M0L: i_mode (m_s m0) = MEM <-> i_mode (l_s L) = MEM).\n"
     "{ unfold m0. rewrite m_init_s. unfold s_typedo.\n"
     "  destruct (Z.eqb_spec (i_mode (l_s L)) Zlib.proof.inflate.Model.TYPE) as [T|T]; [ | tauto].\n"
     "  cbn [i_mode set_i_mode]. rewrite T. unfold TYPEDO, Zlib.proof.inflate.Model.TYPE, MEM.\n"
     "  split; intro Y; discriminate Y. }"),
    (P + 'Body5_inflate',
     "           (fun m => out_inv m /\\ i_win (m_s m) = i_win (m_s m0) /\\ win_inv5 (m_s m) /\\ m_inp m = inp)",
     "           (fun m => out_inv m /\\ i_win (m_s m) = i_win (m_s m0) /\\ win_inv5 (m_s m) /\\ m_inp m = inp /\\\n"
     "                     (i_mode (m_s m0) = MEM -> m = m0) /\\ (i_mode (m_s m) = MEM -> i_mode (m_s m0) = MEM))"),
    (P + 'Body5_inflate',
     "  - split; [exact OI | split; [reflexivity | split; [exact WI0 | reflexivity]]].",
     "  - split; [exact OI | split; [reflexivity | split; [exact WI0 | split; [reflexivity | split; [intros _; reflexivity | intros M; exact M]]]]]."),
    (P + 'Body5_inflate',
     "intros (LP' & MW' & HDm & ML & (OI' & WI & WV & IPm)).",
     "intros (LP' & MW' & HDm & ML & (OI' & WI & WV & IPm & MM0 & MM1)).\n"
     "(* the loop left (leave = 1): the call did not start in MEM, its machine is not in MEM *)\n"
     "assert (MEQ: (i_mode (m_s m) =? MEM) = (i_mode (l_s L) =? MEM)).\n"
     "{ assert (N0: i_mode (m_s m0) <> MEM).\n"
     "  { intros M0. assert (E0: m_leave m0 = 0) by reflexivity. rewrite <- (MM0 M0) in E0. congruence. }\n"
     "  rewrite (proj2 (Z.eqb_neq _ _) (fun M => N0 (MM1 M))).\n"
     "  rewrite (proj2 (Z.eqb_neq _ _) (fun M => N0 (proj2 M0L M))). reflexivity. }"),
    (P + 'Body5_inflate',
     "  - intros m HW HL0 _ (OIm & WIm & WVm & IPm).",
     "  - intros m HW HL0 _ (OIm & WIm & WVm & IPm & MM0 & MM1)."),
]
