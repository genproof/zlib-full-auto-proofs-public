"""Patches of the inflate port, part api (inflateSetDictionary, Body5_dict): see docs/port-za/inflate/api.py."""

_M = 'Zlib.proof.inflate_api.Body5_dict'
PATCHES = [
    # the stream given to inflateStateCheck: strm->opaque is the allocator's, strm->adler the adler cell
    (_M, "     (nullval, (Vint (Int.repr (zf_dt z)), (Vlong (Int64.repr (zf_adler z)), zf_res z))))))))))))),\n"
         "     l_sp L, i_mode (l_s L), true, gv).",
     "     (za_opaque, (Vint (Int.repr (zf_dt z)), (adler_val (zf_adler z), zf_res z))))))))))))),\n"
     "     l_sp L, i_mode (l_s L), true, gv)."),
    # the allocator's state in place of malloc's
    (_M, "(state_pad _) (mem_mgr _).", "(state_pad _) (za_res _ _)."),
    # a Z_NULL stream, a stream without state: no event
    (_M, "    Exists false nullval. unfold on_live, is_live; rewrite ?if_true by auto. entailer!. }",
     "    Exists false nullval. unfold on_live, is_live; rewrite ?if_true by auto. entailer!.\n"
     "    rewrite app_nil_r. cancel. }"),
    (_M, "    apply andp_right; [apply prop_right; reflexivity|]. rewrite prop_true_andp by auto. cancel. }",
     "    apply andp_right; [apply prop_right; reflexivity|]. rewrite prop_true_andp by auto.\n"
     "    rewrite ?app_nil_r. cancel. }"),
    # an early return (Z_STREAM_ERROR / Z_DATA_ERROR): the state unchanged, no window allocated (dict_ev)
    (_M, "  rewrite !prop_true_andp by (first [assumption | split; assumption]); cancel.",
     "  rewrite !prop_true_andp by (first [assumption | split; assumption]); cancel;\n"
     "  unfold dict_ev; rewrite HS, app_nil_r; cancel."),
    # updatewindow with the allocator's trace
    (_M, "                  l_s L, dsh, p, n, c, lo + Zlength dict, dict) end.",
     "                  l_s L, dsh, p, n, c, lo + Zlength dict, dict, tr) end."),
    (_M, "    intros W; rewrite W; reflexivity. }",
     "    split; [intros W; rewrite W; reflexivity | ].\n"
     "    intros _. pose proof (sw_wbits _ Hswf).\n"
     "    assert (2 ^ i_wbits (l_s L) <= 2 ^ 23) by (apply Z.pow_le_mono_r; lia). lia. }"),
    # the window was there (no allocation) or updatewindow allocated it: uw_ev of updatewindow is dict_ev
    (_M, '      unfold set_l_s; cbn [l_sp l_winp l_s l_headp l_h l_hsh l_xb l_nb l_cb].\n      apply andp_right; [apply prop_right; reflexivity|].\n      rewrite !prop_true_andp by (first [split; assumption | apply live_setdict; auto]).\n      unfold setdict_s. rewrite state_rep_hd, win_rep_hd. entailer!.',
     "      unfold set_l_s; cbn [l_sp l_winp l_s l_headp l_h l_hsh l_xb l_nb l_cb].\n      apply andp_right; [apply prop_right; reflexivity|].\n      rewrite !prop_true_andp by (first [split; assumption | apply live_setdict; auto]).\n      unfold setdict_s. rewrite state_rep_hd, win_rep_hd. entailer!.\n      apply derives_refl'. f_equal. f_equal. unfold uw_ev, dict_ev. rewrite HU, HW0. reflexivity."),
    (_M, '      unfold set_l_winp, set_l_s; cbn [l_sp l_winp l_s l_headp l_h l_hsh l_xb l_nb l_cb].\n      apply andp_right; [apply prop_right; reflexivity|].\n      rewrite !prop_true_andp by (first [split; assumption | apply live_setdict; auto]).\n      unfold setdict_s. rewrite state_rep_hd, win_rep_hd. entailer!.',
     "      unfold set_l_winp, set_l_s; cbn [l_sp l_winp l_s l_headp l_h l_hsh l_xb l_nb l_cb].\n      apply andp_right; [apply prop_right; reflexivity|].\n      rewrite !prop_true_andp by (first [split; assumption | apply live_setdict; auto]).\n      unfold setdict_s. rewrite state_rep_hd, win_rep_hd. entailer!.\n      apply derives_refl'. f_equal. f_equal. unfold uw_ev, dict_ev. rewrite HU, HW0. reflexivity."),
    # the window allocation failed (Z_MEM_ERROR): the event ZFail
    (_M, "      unfold win_rep in *. rewrite ?HW. entailer!; unfold rest_g; apply derives_refl. }",
     "      replace (uw_ev (l_s L) 1) with [ZFail] by (unfold uw_ev; rewrite HW; reflexivity).\n"
     "      replace (dict_ev (l_s L) dict false) with [ZFail] by (unfold dict_ev; rewrite HU, HW; reflexivity).\n"
     "      unfold win_rep in *. rewrite ?HW. entailer!; unfold rest_g; apply derives_refl. }"),
]
