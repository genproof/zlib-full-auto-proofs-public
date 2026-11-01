"""Patches of the inflate port, part api (inflateEnd and the resets, Body5_end, Body5_reset): see
docs/port-za/inflate/api.py."""

# the stream value given to inflateStateCheck: strm->opaque is the allocator's, strm->adler the adler cell
_SV_LIVE = "(nullval, (zv (zf_dt z), (lv (zf_adler z), zf_res z))))))))))))), "
_SV_LIVE_ZA = "(za_opaque, (zv (zf_dt z), (adler_val (zf_adler z), zf_res z))))))))))))), "
_SV_RAW = "(nullval, (rf_dt rf, (rf_adler rf, rf_res rf))))))))))))), "
_SV_RAW_ZA = "(za_opaque, (rf_dt rf, (rf_adler rf, rf_res rf))))))))))))), "

PATCHES = []
for _m in ['Zlib.proof.inflate_api.Body5_end', 'Zlib.proof.inflate_api.Body5_reset']:
    PATCHES += [
        (_m, _SV_LIVE + "nullval, 0, false, gv).", _SV_LIVE_ZA + "nullval, 0, false, gv)."),
        (_m, _SV_LIVE + "sp, i_mode s, true, gv).", _SV_LIVE_ZA + "sp, i_mode s, true, gv)."),
    ]
PATCHES += [
    (m, _SV_RAW + "sp, i_mode s, true, gv).", _SV_RAW_ZA + "sp, i_mode s, true, gv).")
    for m in ['Zlib.proof.inflate_api.Body5_reset']
]
PATCHES += [
    # a Z_NULL stream: no event
    ('Zlib.proof.inflate_api.Body5_end',
     "    forward_if; [forward; cancel | discriminate].",
     "    forward_if; [forward; rewrite app_nil_r; cancel | discriminate]."),
    # a stream without state: no event
    ('Zlib.proof.inflate_api.Body5_end',
     """    { forward. unfold is_live, istream_opt, istream, zstrm_at, strm_rep.
      rewrite !if_false by auto. entailer!. }""",
     """    { forward. unfold is_live, istream_opt, istream, zstrm_at, strm_rep.
      rewrite !if_false by auto. rewrite app_nil_r. entailer!. }"""),
]

# inflateEnd on a live stream: the window (when allocated), then the state, given back through strm->zfree
PATCHES += [
    ('Zlib.proof.inflate_api.Body5_end',
     """    assert (HSP: isptr sp) by (destruct H1 as (P & _); exact P).
    forward_call""",
     """    assert (HSP: isptr sp) by (destruct H1 as (P & _); exact P).
    assert (HW: 0 < 2 ^ i_wbits s)
      by (destruct H1 as (_ & SW & _); cbn [l_s] in SW; pose proof (sw_wbits _ SW); apply Z.pow_pos_nonneg; lia).
    forward_call"""),
    ('Zlib.proof.inflate_api.Body5_end',
     """    match goal with |- semax _ (PROPx ?P (LOCALx (_ :: ?Q) (SEPx [?A; ?B; ?C; ?D; ?E2; ?F; ?G; win_rep winp s; ?I; ?J]))) _ _ =>
      forward_if (PROPx P (LOCALx Q (SEPx [A; B; C; D; E2; F; G; I; J]))) end.""",
     """    match goal with |- semax _ (PROPx ?P (LOCALx (_ :: ?Q) (SEPx [?A; ?B; ?C; ?D; ?E2; ?F; ?G; win_rep winp s; ?I; za_res gv tr]))) _ _ =>
      forward_if (PROPx P (LOCALx Q (SEPx [A; B; C; D; E2; F; G; I;
        za_res gv (tr ++ if i_win s then [ZFree (2 ^ i_wbits s)] else [])]))) end."""),
    ('Zlib.proof.inflate_api.Body5_end',
     """      unfold zfuncs. rewrite <- Hzcf, <- Hzca. flatten_sepcon_in_SEP.
      forward_call (tarray tuchar (2 ^ i_wbits s), winp, gv, nullval).
      { rewrite if_false by (destruct winp; try contradiction; discriminate).
        sep_apply (data_at_data_at_ Ews (tarray tuchar (2 ^ i_wbits s))). cancel. }
      unfold zfuncs. rewrite <- Hzcf, <- Hzca. entailer!. }
    { forward. destruct (i_win s) eqn:EW.
      - assert_PROP (isptr winp) by (unfold win_rep; rewrite EW; entailer!). subst; contradiction.
      - unfold win_rep; rewrite EW. entailer!. }""",
     """      unfold zfuncs, za_funcs. rewrite <- Hzcf, <- Hzca. flatten_sepcon_in_SEP.
      forward_call (tarray tuchar (2 ^ i_wbits s), winp, gv, tr).
      replace (sizeof (tarray tuchar (2 ^ i_wbits s))) with (2 ^ i_wbits s)
        by (simpl sizeof; rewrite Z.max_r by lia; lia).
      unfold zfuncs, za_funcs. rewrite <- Hzcf, <- Hzca. entailer!. }
    { forward. destruct (i_win s) eqn:EW.
      - unfold win_rep; rewrite EW. Intros.
        sep_apply (data_at_isptr Ews (tarray tuchar (2 ^ i_wbits s))). Intros. subst; contradiction.
      - unfold win_rep; rewrite EW, app_nil_r. entailer!. }"""),
    ('Zlib.proof.inflate_api.Body5_end',
     """    unfold zfuncs. rewrite <- Hzcf, <- Hzca. flatten_sepcon_in_SEP.
    forward_call (t_state, sp, gv, nullval).
    { rewrite if_false by (destruct sp; try contradiction; discriminate).
      sep_apply (state_free_end gv sp strmp headp winp s). cancel. }
    forward. (* strm->state = Z_NULL *)
    forward. (* return Z_OK *)
    unfold is_live, istream_opt, istream, zstrm_at, strm_rep, zfuncs. rewrite !if_false by auto.
    entailer!.""",
     """    unfold zfuncs, za_funcs. rewrite <- Hzcf, <- Hzca. flatten_sepcon_in_SEP.
    sep_apply (state_free_end gv sp strmp headp winp s).
    forward_call (t_state, sp, gv, tr ++ if i_win s then [ZFree (2 ^ i_wbits s)] else []).
    forward. (* strm->state = Z_NULL *)
    forward. (* return Z_OK *)
    unfold is_live, istream_opt, istream, zstrm_at, strm_rep, zfuncs, za_funcs. rewrite !if_false by auto.
    unfold end_ev. cbn [l_s]. rewrite app_assoc. change (sizeof t_state) with state_size.
    entailer!."""),
]

# the precondition's fact about strm->opaque (what the loads of strm->opaque before ZFREE need) is named Hop,
# so that the names of the other hypotheses are the original ones
PATCHES += [
    ('Zlib.proof.inflate_api.Body5_end',
     "  start_function.\n  unfold istream_opt.",
     "  start_function.\n  rename H into Hop.\n  unfold istream_opt."),
    ('Zlib.proof.inflate_api.Body5_reset',
     "  semax_body Vprog_inflate Gp_reset2 f_inflateReset2 inflateReset2_spec.\nProof.\n  start_function.",
     "  semax_body Vprog_inflate Gp_reset2 f_inflateReset2 inflateReset2_spec.\nProof.\n  start_function.\n"
     "  rename H1 into Hop."),
    ('Zlib.proof.inflate_api.Body5_reset',
     "  semax_body Vprog_inflate Gp_reset f_inflateReset inflateReset_spec.\nProof.\n  start_function.",
     "  semax_body Vprog_inflate Gp_reset f_inflateReset inflateReset_spec.\nProof.\n  start_function.\n"
     "  rename H0 into Hop."),
]

# inflateResetKeep on a live stream: strm->adler is the adler cell (adler_val); it is written only when
# state->wrap <> 0 (with wrap & 1, which the cell's representation admits: AdlerZ.data_at_adler_val)
PATCHES += [
    ('Zlib.proof.inflate_api.Body5_reset',
     "Require Import Zlib.proof.inflate_api.Body5_end.",
     "Require Import Zlib.proof.inflate_api.Body5_end.\nRequire Import Zlib.proof.za.inflate.AdlerZ."),
    ('Zlib.proof.inflate_api.Body5_reset',
     "        (lv (if i_wrap s =? 0 then zf_adler z else Z.land (i_wrap s) 1), a14))))))))))))) p :: R))))",
     "        ((if i_wrap s =? 0 then a13 else lv (Z.land (i_wrap s) 1)), a14))))))))))))) p :: R))))"),
    ('Zlib.proof.inflate_api.Body5_reset',
     """    revert ZOK. unfold reset_keep_z. rk_simpl. cbn [zf_ni zf_ai zf_no zf_ao zf_tin zf_tout zf_msg zf_dt zf_adler zf_res msg_val tref_val]. intro ZOK.
    rewrite codes_at0 by auto.
    entailer!.""",
     """    revert ZOK. unfold reset_keep_z. rk_simpl. cbn [zf_ni zf_ai zf_no zf_ao zf_tin zf_tout zf_msg zf_dt zf_adler zf_res msg_val tref_val]. intro ZOK.
    rewrite codes_at0 by auto.
    destruct (Z.eqb_spec (i_wrap s) 0) as [EW0 | EW0].
    { entailer!. }
    match goal with |- context [data_at ?sh t_strm (?a1, (?a2, (?a3, (?a4, (?a5, (?a6, (?a7, (?a8, (?a9, (?a10,
        (?a11, (?a12, (lv (Z.land (i_wrap s) 1), ?a14))))))))))))) ?p] =>
      sep_apply (data_at_adler_val sh p a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a14
        (lv (Z.land (i_wrap s) 1)) (Z.land (i_wrap s) 1) (fun _ => eq_refl)) end.
    entailer!."""),
]

# inflateReset2: no event on a Z_NULL stream or a stream without state
PATCHES += [
    ('Zlib.proof.inflate_api.Body5_reset',
     "    forward_if; [forward; cancel | discriminate].",
     "    forward_if; [forward; rewrite app_nil_r; cancel | discriminate]."),
    ('Zlib.proof.inflate_api.Body5_reset',
     """    { forward. unfold reset_ret, reset_post, rs_live, rstream_opt, rstream, istream, zstrm_at, strm_rep.
      rewrite !if_false by auto. entailer!. }""",
     """    { forward. unfold reset_ret, reset_post, rs_live, rstream_opt, rstream, istream, zstrm_at, strm_rep.
      rewrite !if_false by auto. entailer!; rewrite ?app_nil_r; cancel. }"""),
]

# inflateReset2 rejecting windowBits (reset2_wb w = None): no event
PATCHES += [
    ('Zlib.proof.inflate_api.Body5_reset',
     "  unfold reset2_f, fst3; rewrite EN; cbn [fst snd];\n",
     "  unfold reset2_f, fst3, reset2_ev; rewrite EN; cbn [fst snd]; rewrite ?app_nil_r;\n"),
]

# inflateReset2 on a live state (both halves of the proof: a raw stream RRaw and a live one RLive): the window is
# given back through strm->zfree when its size changes, the trace carried to the call of inflateReset (whose free,
# reset_ev, completes reset2_ev: reset2_ev_split)
_R2_BLOCK = """    forward. (* t'8 = state->window (@STREAM@) *)
    { unfold win_rep; destruct (i_win s); entailer!. }
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp _t'3 (Vint (Int.repr (if andb (i_win s) (negb (i_wbits s =? wb0 w)) then 1 else 0))) :: Q) (SEPx R))) end.
    { unfold win_rep; destruct (i_win s); entailer!. }
    { destruct (i_win s) eqn:EW; [ | contradiction].
      forward. forward. entailer!.
      simpl andb. destruct (Z.eqb_spec (i_wbits s) (wb0 w)); destruct (zeq (i_wbits s) (wb0 w)); try lia; reflexivity. }
    { destruct (i_win s) eqn:EW.
      - assert_PROP (isptr winp) by (unfold win_rep; rewrite EW; entailer!). subst; contradiction.
      - forward. entailer!. }
    match goal with |- semax _ (PROPx _ (LOCALx (_ :: _ :: ?Q) (SEPx (?A :: ?B :: ?C :: ?D :: ?E2 :: ?F :: ?G :: _ :: ?I :: _ :: ?K :: ?L :: nil)))) _ _ =>
      forward_if (PROPx [] (LOCALx Q (SEPx [A; B; C; D; E2; F; G;
        field_at Ews t_state (DOT _window) (if i_win (wfree (wb0 w) s) then winp else nullval) sp;
        I; win_rep winp (wfree (wb0 w) s); K; L]))) end.
    { (* free the window *)
      destruct (i_win s) eqn:EW;
        [ | match goal with H: (if _ then 1 else 0) <> 0 |- _ => exfalso; apply H; reflexivity end].
      destruct (Z.eqb_spec (i_wbits s) (wb0 w));
        [match goal with H: (if _ then 1 else 0) <> 0 |- _ => exfalso; apply H; reflexivity end | ].
      unfold win_rep at 1. rewrite EW. Intros.
      assert_PROP (isptr zcf).
      { go_lower. rewrite (add_andp (zfuncs gv) _ (zfuncs_isptr gv zcf Hzcf)). normalize; try (apply prop_right; auto). }
      forward. forward. forward.
      assert_PROP (isptr winp) by entailer!.
      unfold zfuncs. rewrite <- Hzcf, <- Hzca. flatten_sepcon_in_SEP.
      forward_call (tarray tuchar (2 ^ i_wbits s), winp, gv, nullval).
      { rewrite if_false by (destruct winp; try contradiction; discriminate).
        sep_apply (data_at_data_at_ Ews (tarray tuchar (2 ^ i_wbits s))). cancel. }
      forward.
      unfold wfree. rewrite EW. destruct (Z.eqb_spec (i_wbits s) (wb0 w)); [lia | ].
      unfold win_rep, zfuncs. cbn [i_win set_i_win andb negb]. rewrite <- Hzcf, <- Hzca. entailer!. }
    { forward. unfold wfree. destruct (i_win s) eqn:EW; cbn [andb].
      - destruct (Z.eqb_spec (i_wbits s) (wb0 w)).
        + cbn [negb]. rewrite EW. entailer!.
        + match goal with H: Int.repr (if _ then 1 else 0) = Int.zero |- _ => simpl in H; discriminate end.
      - rewrite EW. entailer!. }"""
_R2_FREE_OLD = """      - assert_PROP (isptr winp) by (unfold win_rep; rewrite EW; entailer!). subst; contradiction.
      - forward. entailer!. }
    match goal with |- semax _ (PROPx _ (LOCALx (_ :: _ :: ?Q) (SEPx (?A :: ?B :: ?C :: ?D :: ?E2 :: ?F :: ?G :: _ :: ?I :: _ :: ?K :: ?L :: nil)))) _ _ =>
      forward_if (PROPx [] (LOCALx Q (SEPx [A; B; C; D; E2; F; G;
        field_at Ews t_state (DOT _window) (if i_win (wfree (wb0 w) s) then winp else nullval) sp;
        I; win_rep winp (wfree (wb0 w) s); K; L]))) end."""
_R2_FREE_NEW = """      - unfold win_rep; rewrite EW. Intros.
        sep_apply (data_at_isptr Ews (tarray tuchar (2 ^ i_wbits s))). Intros. subst; contradiction.
      - forward. entailer!. }
    match goal with |- semax _ (PROPx _ (LOCALx (_ :: _ :: ?Q) (SEPx (?A :: ?B :: ?C :: ?D :: ?E2 :: ?F :: ?G :: _ :: ?I :: _ :: ?K :: za_res gv tr :: nil)))) _ _ =>
      forward_if (PROPx [] (LOCALx Q (SEPx [A; B; C; D; E2; F; G;
        field_at Ews t_state (DOT _window) (if i_win (wfree (wb0 w) s) then winp else nullval) sp;
        I; win_rep winp (wfree (wb0 w) s); K;
        za_res gv (tr ++ if andb (i_win s) (negb (i_wbits s =? wb0 w)) then [ZFree (2 ^ i_wbits s)] else [])]))) end."""
_R2_CALL_OLD = """      unfold zfuncs. rewrite <- Hzcf, <- Hzca. flatten_sepcon_in_SEP.
      forward_call (tarray tuchar (2 ^ i_wbits s), winp, gv, nullval).
      { rewrite if_false by (destruct winp; try contradiction; discriminate).
        sep_apply (data_at_data_at_ Ews (tarray tuchar (2 ^ i_wbits s))). cancel. }
      forward.
      unfold wfree. rewrite EW. destruct (Z.eqb_spec (i_wbits s) (wb0 w)); [lia | ].
      unfold win_rep, zfuncs. cbn [i_win set_i_win andb negb]. rewrite <- Hzcf, <- Hzca. entailer!. }
    { forward. unfold wfree. destruct (i_win s) eqn:EW; cbn [andb].
      - destruct (Z.eqb_spec (i_wbits s) (wb0 w)).
        + cbn [negb]. rewrite EW. entailer!.
        + match goal with H: Int.repr (if _ then 1 else 0) = Int.zero |- _ => simpl in H; discriminate end.
      - rewrite EW. entailer!. }"""
_R2_CALL_NEW = """      unfold zfuncs, za_funcs. rewrite <- Hzcf, <- Hzca. flatten_sepcon_in_SEP.
      forward_call (tarray tuchar (2 ^ i_wbits s), winp, gv, tr).
      forward.
      unfold wfree. rewrite EW. destruct (Z.eqb_spec (i_wbits s) (wb0 w)); [lia | ].
      replace (sizeof (tarray tuchar (2 ^ i_wbits s))) with (2 ^ i_wbits s)
        by (simpl sizeof; rewrite Z.max_r by lia; lia).
      unfold win_rep, zfuncs, za_funcs. cbn [i_win set_i_win andb negb]. rewrite <- Hzcf, <- Hzca. entailer!. }
    { forward. unfold wfree. destruct (i_win s) eqn:EW; cbn [andb].
      - destruct (Z.eqb_spec (i_wbits s) (wb0 w)).
        + cbn [negb]. rewrite EW, app_nil_r. entailer!.
        + match goal with H: Int.repr (if _ then 1 else 0) = Int.zero |- _ => simpl in H; discriminate end.
      - rewrite EW, app_nil_r. entailer!. }"""
_R2_TAIL = """
    { unfold reset_pre, rs_live in H0 |- *. rewrite if_false in H0 |- * by auto.
      unfold reset2_f in H0. rewrite ES in H0. exact H0. }
    forward.
    unfold reset_ret, reset_post, rs_live. rewrite !if_false by auto. unfold reset2_f. rewrite ES.
    subst L1 s2. unfold reset_f, fst3, snd3, thd3, reset2_s, wfree, set_l_s.
    cbn [fst snd l_s l_sp l_winp l_h l_headp l_hsh l_xb l_nb l_cb]. rewrite Z.eqb_refl. entailer!."""
_R2_OWN = "(if andb (i_win s) (negb (i_wbits s =? wb0 w)) then [ZFree (2 ^ i_wbits s)] else [])"
for _st in ['raw stream', 'live stream']:
    _b = _R2_BLOCK.replace('@STREAM@', _st)
    PATCHES += [('Zlib.proof.inflate_api.Body5_reset', _b,
                 _b.replace(_R2_FREE_OLD, _R2_FREE_NEW).replace(_R2_CALL_OLD, _R2_CALL_NEW))]
for _r in ['RRaw L1 rf vl vd vn vs', 'RLive L1 vl vd vn vs']:
    PATCHES += [
        ('Zlib.proof.inflate_api.Body5_reset',
         "(SEPx [rstream_opt gv shs strmp z (" + _r + "); mem_mgr gv; zfuncs gv]))) end.",
         "(SEPx [rstream_opt gv shs strmp z (" + _r + "); za_res gv (tr ++ " + _R2_OWN + ");\n"
         "        zfuncs gv]))) end."),
        ('Zlib.proof.inflate_api.Body5_reset',
         "    forward_call (gv, shs, strmp, z, " + _r + ")." + _R2_TAIL,
         "    forward_call (gv, shs, strmp, z, " + _r + ", tr ++ " + _R2_OWN + ")." +
         _R2_TAIL.replace("rewrite Z.eqb_refl. entailer!.",
                          "rewrite Z.eqb_refl.\n    rewrite <- app_assoc, (reset2_ev_split s w (wrap0 w) (wb0 w) ES WRP). entailer!.")),
    ]
PATCHES += [
    # the events of inflateReset2: its own free, then that of its inflateReset call
    ('Zlib.proof.inflate_api.Body5_reset',
     "Lemma or8_eq: forall x, 0 <= x <= 7 -> Int.or (Int.repr x) (Int.repr 8) = Int.repr (Z.lor x 8).",
     """Lemma reset2_ev_split: forall s w wrap wb, reset2_wb w = Some (wrap, wb) -> 0 <= wrap <= 7 ->
  (if andb (i_win s) (negb (i_wbits s =? wb)) then [ZFree (2 ^ i_wbits s)] else []) ++
  reset_ev (set_i_wbits (set_i_wrap (if andb (i_win s) (negb (i_wbits s =? wb)) then set_i_win s false else s)
                         (reset2_wrap wrap wb)) wb) = reset2_ev s w.
Proof.
  intros s w wrap wb ES WR. unfold reset2_ev, reset_ev, reset2_wrap. rewrite ES.
  assert (L8: Z.land wrap 8 = 0 /\\ Z.land (Z.lor wrap 8) 8 = 8).
  { assert (C: wrap = 0 \\/ wrap = 1 \\/ wrap = 2 \\/ wrap = 3 \\/ wrap = 4 \\/ wrap = 5 \\/ wrap = 6 \\/ wrap = 7) by lia.
    destruct C as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; split; reflexivity. }
  destruct L8 as [L8a L8b].
  destruct (i_win s) eqn:EW; cbn [andb negb orb].
  - destruct (Z.eqb_spec (i_wbits s) wb) as [E | E]; cbn [negb andb orb i_win i_wbits i_wrap set_i_win set_i_wbits set_i_wrap].
    + rewrite EW. subst wb. destruct (Z.eqb_spec (i_wbits s) 0) as [E0 | E0]; cbn [orb].
      * rewrite L8b, E0. reflexivity.
      * rewrite L8a. reflexivity.
    + rewrite andb_false_r. reflexivity.
  - cbn [i_win i_wbits i_wrap set_i_win set_i_wbits set_i_wrap]. rewrite EW, andb_false_r. reflexivity.
Qed.

Lemma or8_eq: forall x, 0 <= x <= 7 -> Int.or (Int.repr x) (Int.repr 8) = Int.repr (Z.lor x 8)."""),
]

# inflateReset on a live state (both halves): with bit 3 set the window is given back through strm->zfree (the event
# of reset_ev), the trace carried to the call of inflateResetKeep
_R1_BLOCK = """    set (s1 := reset_hdr_s s). (* bit 3 of wrap, @STREAM@ *)
    freeze [1;2;4;5;7;8;9;11;13] FR.
    match goal with |- semax _ (PROPx _ (LOCALx (_ :: ?Q) (SEPx (?F0 :: ?A :: ?D :: _ :: _ :: _ :: ?N :: nil)))) _ _ =>
      forward_if (PROPx [] (LOCALx Q (SEPx [F0; A; D;
        field_at Ews t_state (DOT _wbits) (zv (i_wbits s1)) sp;
        field_at Ews t_state (DOT _window) (if i_win s1 then winp else nullval) sp;
        win_rep winp s1; N]))) end.
    { (* bit 3: the window freed, wbits = 0 *)
      match goal with Hc: Int.and _ _ <> Int.zero |- _ => rewrite EA in Hc; rename Hc into Hc8 end.
      assert (H8: Z.land (i_wrap s) 8 <> 0) by (intro X; rewrite X in Hc8; contradiction).
      assert (Es1: s1 = set_i_wbits (set_i_win s false) 0)
        by (subst s1; unfold reset_hdr_s; rewrite (proj2 (Z.eqb_neq _ _) H8); reflexivity).
      forward. (* t'4 = state->window *)
      { unfold win_rep; destruct (i_win s); entailer!. }
      destruct (i_win s) eqn:EW.
      - unfold win_rep at 1. rewrite EW. Intros.
        assert_PROP (isptr winp) by entailer!.
        match goal with |- semax _ (PROPx _ (LOCALx (_ :: ?Q) (SEPx (?F0 :: ?A :: ?D :: ?G :: _ :: _ :: _ :: ?N :: nil)))) _ _ =>
          forward_if (PROPx [] (LOCALx Q (SEPx [F0; A; D; G;
            field_at Ews t_state (DOT _window) nullval sp; N]))) end.
        2: { exfalso. destruct winp; try contradiction. match goal with Hc: _ = nullval |- _ => inversion Hc end. }
        assert_PROP (isptr zcf).
        { go_lower. rewrite (add_andp (zfuncs gv) _ (zfuncs_isptr gv zcf Hzcf)). normalize; try (apply prop_right; auto). }
        forward. forward. forward.
        unfold zfuncs. rewrite <- Hzcf, <- Hzca. flatten_sepcon_in_SEP.
        forward_call (tarray tuchar (2 ^ i_wbits s), winp, gv, nullval).
        { rewrite if_false by (destruct winp; try contradiction; discriminate).
          sep_apply (data_at_data_at_ Ews (tarray tuchar (2 ^ i_wbits s))). cancel. }
        forward. unfold zfuncs. rewrite <- Hzcf, <- Hzca. entailer!.
        forward.
        rewrite Es1. unfold win_rep. cbn [i_win i_wbits set_i_win set_i_wbits]. entailer!.
      - match goal with |- semax _ (PROPx _ (LOCALx (_ :: ?Q) (SEPx ?R))) _ _ =>
          forward_if (PROPx [] (LOCALx Q (SEPx R))) end.
        { discriminate. }
        { forward. entailer!. }
        forward.
        rewrite Es1. unfold win_rep. rewrite EW. cbn [i_win i_wbits set_i_win set_i_wbits]. entailer!. }
    { (* bit 3 clear: nothing *)
      match goal with Hc: Int.and _ _ = Int.zero |- _ => rewrite EA in Hc; rename Hc into Hc8 end.
      assert (H8: Z.land (i_wrap s) 8 = 0).
      { apply (f_equal Int.unsigned) in Hc8. rewrite Int.unsigned_repr in Hc8 by rep_lia. exact Hc8. }
      assert (Es1: s1 = s) by (subst s1; unfold reset_hdr_s; rewrite (proj2 (Z.eqb_eq _ _) H8); reflexivity).
      forward. rewrite Es1. entailer!. }
    thaw FR."""
_R1_EDITS = [('        win_rep winp s1; N]))) end.', '        win_rep winp s1; za_res gv (tr ++ reset_ev s)]))) end.'), ('            field_at Ews t_state (DOT _window) nullval sp; N]))) end.', '            field_at Ews t_state (DOT _window) nullval sp; za_res gv (tr ++ [ZFree (2 ^ i_wbits s)])]))) end.'), ('        unfold zfuncs. rewrite <- Hzcf, <- Hzca. flatten_sepcon_in_SEP.\n        forward_call (tarray tuchar (2 ^ i_wbits s), winp, gv, nullval).\n        { rewrite if_false by (destruct winp; try contradiction; discriminate).\n          sep_apply (data_at_data_at_ Ews (tarray tuchar (2 ^ i_wbits s))). cancel. }\n        forward. unfold zfuncs. rewrite <- Hzcf, <- Hzca. entailer!.', '        unfold zfuncs, za_funcs. rewrite <- Hzcf, <- Hzca. flatten_sepcon_in_SEP.\n        forward_call (tarray tuchar (2 ^ i_wbits s), winp, gv, tr).\n        assert (HW2: 0 < 2 ^ i_wbits s) by (apply Z.pow_pos_nonneg; lia).\n        replace (sizeof (tarray tuchar (2 ^ i_wbits s))) with (2 ^ i_wbits s)\n          by (simpl sizeof; rewrite Z.max_r by lia; lia).\n        forward. unfold zfuncs, za_funcs. rewrite <- Hzcf, <- Hzca. entailer!.'), ('        rewrite Es1. unfold win_rep. cbn [i_win i_wbits set_i_win set_i_wbits]. entailer!.', '        rewrite Es1. unfold win_rep, reset_ev. rewrite EW, (proj2 (Z.eqb_neq _ _) H8).\n        cbn [i_win i_wbits set_i_win set_i_wbits negb andb]. entailer!.'), ('        rewrite Es1. unfold win_rep. rewrite EW. cbn [i_win i_wbits set_i_win set_i_wbits]. entailer!.', '        rewrite Es1. unfold win_rep, reset_ev. rewrite EW, andb_false_r.\n        cbn [i_win i_wbits set_i_win set_i_wbits]. rewrite app_nil_r. entailer!.'), ('      forward. rewrite Es1. entailer!. }', '      forward. rewrite Es1. unfold reset_ev. rewrite (proj2 (Z.eqb_eq _ _) H8). cbn [negb andb].\n      rewrite app_nil_r. entailer!. }')]
for _st in ['raw stream', 'live stream']:
    _b = _R1_BLOCK.replace('@STREAM@', _st)
    _n = _b
    for _o, _w in _R1_EDITS:
        assert _n.count(_o) == 1, _o
        _n = _n.replace(_o, _w)
    PATCHES += [('Zlib.proof.inflate_api.Body5_reset', _b, _n)]
for _r in ["RRaw L' rf vl vd vn vs", "RLive L' vl vd vn vs"]:
    PATCHES += [
        ('Zlib.proof.inflate_api.Body5_reset',
         "(SEPx [rstream_opt gv shs strmp z (" + _r + "); mem_mgr gv; zfuncs gv]))) end.",
         "(SEPx [rstream_opt gv shs strmp z (" + _r + "); za_res gv (tr ++ reset_ev s); zfuncs gv]))) end."),
    ]
