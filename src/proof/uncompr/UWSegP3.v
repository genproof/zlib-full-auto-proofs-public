(* uncompress2_z for any sizes (UWSegs.v), statements 10-13: inflateInit (a failed allocation returns Z_MEM_ERROR
   with nothing changed), next_out = dest, avail_out = 0, and the loop invariant at the loop's entry (the model's
   m_first, nothing consumed or written). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Uncompr Zlib.units.Inflate.
Require Import Zlib.uncompr.code.
Require Import Zlib.proof.uncompr.UWSegs.
Require Import Zlib.proof.inflate_api.Spec5.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Uncompr.CS.
Local Open Scope logic.

Lemma uw_p3 : uw_p3_stmt.
Proof.
  intros Espec A v F Pv K.
  destruct A as [gv dnull dsh dp dn dc cap dlp dtok stok ssh sp sn sc src slp gsh tsh].
  unfold uw_A10, uw_lcl, uw_facts, uw_seg10 in *. unfold POST_uw.
  abbreviate_semax.
  (* both destinations: dc has dn elements, cap >= 0, and the code's dest is a pointer *)
  destruct F as (Hd & Hssh & Hsp & Hstok & Hsrc & Hsc & Hsn & Hsub & Hbytes & Hgsh & Htsh).
  assert (Hdc: Zlength dc = dn /\ 0 <= cap /\ isptr (uw_dq dnull dp v)).
  { destruct dnull; unfold uw_dq; simpl in Hd; [destruct Hd as (-> & -> & -> & -> & ->) | ];
      [split3; [reflexivity | lia | destruct v; try contradiction; exact I] | tauto]. }
  destruct Hdc as (Hdc & Hcap & Hdq).
  (* err = inflateInit(&stream); *)
  unfold uversion_lit, inflate_globals. Intros.
  assert_PROP (isptr (gv ___stringlit_uncompr_1)) as Hlit by entailer!.
  forward_call (gv, Tsh, v, RF sp (Vint (Int.repr 0)) Vundef Vundef Vundef Vundef Vundef Vundef Vundef, Vundef, Vundef, nullval, gv ___stringlit_uncompr_1, Ers, map (fun c => Vint (Int.repr c)) [49; 46; 51; 46; 50; 0], 49, 112).
  { rewrite if_false by (intro Hn; rewrite Hn in Pv; exact Pv). cancel. }
  { repeat split; try exact Hlit; cbn; rep_lia. }
  Intros vret. destruct vret as [aok stp]. simpl fst in *; simpl snd in *.
  unfold init_ret. simpl orb. rewrite if_false by (intro Hn; rewrite Hn in Pv; exact Pv).
  unfold init_mem. rewrite if_false by (intro Hn; rewrite Hn in Pv; exact Pv).
  destruct aok; simpl.
  2: { (* the allocation failed: return Z_MEM_ERROR with nothing changed *)
       forget (gv inflate.code._zcalloc) as zca. forget (gv inflate.code._zcfree) as zcf.
       forward_if (PROP (False) LOCAL () SEP ()); [| discriminate].
       unfold raw_strm. change_compspecs Zlib.units.Uncompr.CS.
       forward.
       Exists Z_MEM_ERROR (Zlength src) cap (@nil Z).
       cbn [rf_ni rf_ai rf_tin rf_no rf_ao rf_tout rf_dt rf_adler rf_res].
       apply andp_right; [apply prop_right; split; [left; auto | reflexivity] |].
       unfold dest_after, uversion_lit, inflate_globals. rewrite Zlength_nil, sublist_same by lia. simpl app.
       change (Zlength [Vint (Int.repr 49); Vint (Int.repr 46); Vint (Int.repr 51); Vint (Int.repr 46);
                        Vint (Int.repr 50); Vint (Int.repr 0)]) with 6.
       simpl map. sep_apply (data_at_data_at_ Tsh t_strm). cancel. }
  (* the allocation succeeded: err = Z_OK, the stream is live in mode HEAD *)
  forward_if (temp _err (Vint (Int.repr Z_OK))); [discriminate | forward; entailer! |].
  change (Zlength [Vint (Int.repr 49); Vint (Int.repr 46); Vint (Int.repr 51); Vint (Int.repr 46);
                   Vint (Int.repr 50); Vint (Int.repr 0)]) with 6.
  simpl map. unfold istream_raw. Intros.
  remember (gv inflate.code._zcalloc) as zca. remember (gv inflate.code._zcfree) as zcf.
  unfold raw_strm. cbn [rf_ni rf_ai rf_tin rf_no rf_ao rf_tout rf_dt rf_adler rf_res raw_after_init].
  change (i_wrap (init_s 5 15)) with 5. simpl (5 =? 0). cbv beta iota. change (Z.land 5 1) with 1.
  change (l_sp (init_live stp 15)) with stp.
  change_compspecs Zlib.units.Uncompr.CS.
  (* stream.next_out = dest; stream.avail_out = 0; *)
  forward. forward.
  (* the loop's entry: the model's first state, nothing consumed or written, both offers 0 *)
  eapply semax_pre; [| apply K].
  unfold uw_inv, uw_lcl, uw_sep, uw_fr, uw_sfacts.
  Exists m_first 0 (@nil Z) (ZF sp 0 0 (uw_dq dnull dp v) 0 0 None 0 1 Vundef) (init_live stp 15) 0 0.
  go_lower.
  apply andp_right.
  { apply prop_right. cbn [zf_ni zf_ai zf_tin zf_no zf_ao zf_tout zf_msg zf_dt zf_adler zf_res].
    rewrite eqb_type_refl, Zlength_nil, !isptr_offset_val_zero by auto.
    pose proof init_s_swfW as Hsw. pose proof (Zlength_nonneg src) as Hsl.
    refine (conj (reach_w_first _ _) (conj init_s_vmode (conj (conj init_s_head _) _))).
    - repeat match goal with |- swfW _ => exact Hsw | |- _ /\ _ => split end; try reflexivity; unfold uw_max; lia.
    - repeat split; f_equal; f_equal; lia. }
  rewrite <- istream_raw_istream by (try reflexivity; unfold zf_ok; simpl; rep_lia).
  unfold istream_raw, raw_strm.
  cbn [zf_ni zf_ai zf_tin zf_no zf_ao zf_tout zf_msg zf_dt zf_adler zf_res rf_ni rf_ai rf_tin rf_no rf_ao rf_tout
       rf_dt rf_adler rf_res].
  subst zca zcf. change (l_sp (init_live stp 15)) with stp.
  unfold dest_after. rewrite Zlength_nil, sublist_same by lia. simpl app.
  rewrite prop_true_andp by auto.
  unfold uw_lit.
  change_compspecs Zlib.units.Uncompr.CS. cancel.
Qed.
