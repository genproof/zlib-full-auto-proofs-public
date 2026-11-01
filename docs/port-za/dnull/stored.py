"""deflate_stored: the two direct copies from next_in into the window.

deflate_stored copies `next_in - w_size` (or `next_in - used`) into the window only when it consumed input
(used > 0).  At next_in = Z_NULL there is no input (in_objN gives z_in = []), so nothing is consumed: the window
fragment takes the hypothesis `pin = nullval -> used = 0`, which deflate_stored's body proves from the input objects
at entry and after the loop (no input bytes, hence avail_in = 0 twice), and both copies run with pin <> Z_NULL.
The in_obj split lemmas (used only for those copies) assume field_compatible at pin, which excludes Z_NULL."""

PATCHES = []

# in_obj_split: field_compatible excludes pin = Z_NULL; the other case is the old in_obj
for _m in ['Zlib.proof.deflate.StoredWinKit', 'Zlib.proof.deflate.StoredSlideKit']:
    PATCHES.append(
        (_m, "  intros FC H1 H2 H3. unfold in_obj.\n",
         "  intros FC H1 H2 H3. unfold in_obj, in_objN.\n"
         "  destruct (eq_dec pin nullval) as [Pnull | _]; [subst pin; destruct FC as [FC _]; contradiction FC |].\n"))

W = 'Zlib.proof.deflate.StoredWin'
PATCHES += [
    # the window fragment: no input consumed at next_in = Z_NULL
    (W, "  0 <= used <= Int.max_unsigned ->\n  c_ds_window s z used = Some s' ->",
     "  0 <= used <= Int.max_unsigned ->\n  (pin = nullval -> used = 0) ->\n  c_ds_window s z used = Some s' ->"),
    (W, "  intros Hu Hm.\n", "  intros Hu Hnull Hm.\n"),
    (W, "  assert (Hu0 : used <> 0) by (intro; subst; apply H; reflexivity).\n",
     "  assert (Hu0 : used <> 0) by (intro; subst; apply H; reflexivity).\n"
     "  assert (Pnn : pin <> nullval) by (intro; apply Hu0; auto).\n"
     "  assert (Eptr : in_ptrN pin (z_next_in z) = offset_val (z_next_in z) pin)\n"
     "    by (unfold in_ptrN; rewrite if_false by auto; reflexivity).\n"),
]

# the input object and next_in at pin <> Z_NULL are the old ones (once per copy; next_in is folded back after it)
for _r in ['    destruct (mb_vals_write _ _ _ _ (proj1 R2) Hw) as (Ew & Lw1 & Lw2 & W1 & W2).\n    ',
           '      destruct (mb_vals_write _ _ _ _ (proj1 Q2) Hw) as (Ew & Lw1 & Lw2 & W1 & W2).\n      ']:
    PATCHES.append(
        (W, _r + "assert_PROP (field_compatible (tarray tuchar (Zlength (z_in z))) [] pin) as FCi by (unfold in_obj; entailer!).",
         _r + "assert_PROP (field_compatible (tarray tuchar (Zlength (z_in z))) [] pin) as FCi\n"
         + _r[_r.index('\n') + 1:] + "  by (unfold in_obj, in_objN; rewrite if_false by auto; entailer!).\n"
         + _r[_r.index('\n') + 1:] + "rewrite Eptr."))
for _i in ['    ', '      ']:
    _l = "\n" + _i + "sep_apply (in_obj_join_b ish z pin _ bytes FCi Hb).\n"
    PATCHES.append((W, _l, _l + _i + "rewrite <- Eptr.\n"))

# deflate_stored's body: at next_in = Z_NULL both input objects (at entry and after the loop) are empty, so
# avail_in is 0 at both points and used = 0, as the window fragment requires
B = 'Zlib.proof.deflate.Body_stored'
PATCHES += [
    (B, "Theorem deflate_stored_body : ob_deflate_stored.\n",
     "(** At next_in = Z_NULL the input object holds no bytes. *)\n"
     "Lemma in_obj_null_prop ish z pin :\n"
     "  in_obj ish z pin = (!! (pin = nullval -> z_in z = []) && in_obj ish z pin)%logic.\n"
     "Proof.\n"
     "  apply pred_ext; [| apply andp_left2, derives_refl].\n"
     "  apply andp_right; [| apply derives_refl]. unfold in_obj, in_objN.\n"
     "  destruct (eq_dec pin nullval); [Intros; apply prop_right; auto | apply prop_right; intro; contradiction].\n"
     "Qed.\n\n"
     "Theorem deflate_stored_body : ob_deflate_stored.\n"),
    (B, "  unfold dfull. Intros.\n",
     "  unfold dfull. Intros.\n"
     "  rewrite in_obj_null_prop. Intros.\n"
     "  match goal with Hx : pin = nullval -> z_in z = [] |- _ => rename Hx into Hin0 end.\n"),
    (B, "  set (used1 := u32 (used0 - z_avail_in z1)) in *.\n",
     "  set (used1 := u32 (used0 - z_avail_in z1)) in *.\n"
     "  rewrite in_obj_null_prop. Intros.\n"
     "  match goal with Hx : pin = nullval -> z_in z1 = [] |- _ => rename Hx into Hin1 end.\n"
     "  assert (Hnull1 : pin = nullval -> used1 = 0).\n"
     "  { intros Pn. specialize (Hin0 Pn). specialize (Hin1 Pn).\n"
     "    match goal with R0 : strm_ranges z, R1 : strm_ranges z1 |- _ =>\n"
     "      pose proof R0 as Q0; pose proof R1 as Q1 end.\n"
     "    unfold strm_ranges in Q0, Q1. rewrite Hin0, Zlength_nil in Q0. rewrite Hin1, Zlength_nil in Q1.\n"
     "    unfold used1, used0. replace (z_avail_in z - z_avail_in z1) with 0 by lia. reflexivity. }\n"),
    (B, "[apply u32_range | exact Hw]]", "[apply u32_range | exact Hnull1 | exact Hw]]"),
]
