(* uncompress2_z with a Z_NULL source of length 0 (UWNSegs.v), the loop's body, part 3: err = inflate(&stream,
   Z_NO_FLUSH) with next_in = Z_NULL, avail_in = 0 (SpecWSelf.inflate_specW_s's InNull input, no bytes): the call
   is the model's UModelW.uw_call on the empty source; it consumes nothing, so next_in stays Z_NULL and avail_in 0.
   The script is UWSegCall.v's. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Uncompr.
Require Zlib.units.Inflate.
Require Import Zlib.uncompr.code.
Require Import Zlib.proof.uncompr.UWNSegs.
Require Import Zlib.proof.uncompr.UWSegCall.
Require Import Zlib.proof.inflate_api.Spec5.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Uncompr.CS.
Local Open Scope logic.

(* inflate's objects: no input object, and the destination (with ow written after out) as the output; for a
   Z_NULL destination the output object is the empty member `reserved` of the stream *)
Lemma un_bufs: forall dnull dsh dp dn dc cap dtok L v out ow,
  dest_ok_w dnull dsh dp dn dc cap dtok -> isptr v -> Zlength out + Zlength ow <= cap ->
  bufs_opt (Some L) InNull (Some (uw_ob dnull dsh dp v dn dc out)) ow false (uw_otok dnull dtok) =
  dest_rep dnull dsh dp dn (dest_after dc dn (out ++ ow)) dtok.
Proof.
  intros dnull dsh dp dn dc cap dtok L v out ow D Pv Hl.
  destruct dnull.
  - pose proof (Zlength_nonneg ow).
    destruct (uw_null_out _ _ _ _ _ _ out (Zlength ow) D) as [-> Hw]; [lia | lia |].
    apply Zlength_nil_inv in Hw. subst ow.
    destruct D as (-> & -> & -> & -> & ->).
    unfold uw_ob, uw_otok, dest_rep. simpl.
    unfold bufs_opt, in_rep, out_opt, out_rep, in_tok, out_tok. simpl.
    rewrite data_at_zero_array_eq by (auto; apply isptr_offset_val; auto).
    rewrite !emp_sepcon. reflexivity.
  - destruct D as (Hw & Hdp & Hc & Ht & Hdc & Hdn).
    unfold uw_ob, uw_otok, dest_rep, bufs_opt, in_rep, out_opt, out_rep, in_tok, out_tok.
    rewrite dest_after_app by lia.
    destruct dtok; change_compspecs Zlib.units.Uncompr.CS; apply pred_ext; cancel.
Qed.

(* the pure part of inflate()'s precondition for the output object (the destination, or for a Z_NULL
   destination the stream's member `reserved` with nothing offered) *)
Lemma un_call_out: forall dnull dsh dp dn dc cap dtok v z out ao,
  dest_ok_w dnull dsh dp dn dc cap dtok -> isptr v ->
  zf_no z = offset_val (Zlength out) (uw_dq dnull dp v) -> zf_ao z = uw_aout cap out ao ->
  0 <= uw_aout cap out ao -> Zlength out + uw_aout cap out ao <= cap ->
  (out_tok_ok (uw_otok dnull dtok) (Some (uw_ob dnull dsh dp v dn dc out)) \/
   self_out v (uw_otok dnull dtok) (Some (uw_ob dnull dsh dp v dn dc out)) (zf_ao z)) /\
  zf_no z = out_ptr (uw_ob dnull dsh dp v dn dc out) 0 /\
  out_ok (uw_ob dnull dsh dp v dn dc out) (zf_ao z).
Proof.
  intros dnull dsh dp dn dc cap dtok v z out ao D Pv Hno Hao Haout Haoutl.
  pose proof (Zlength_nonneg out) as Hol.
  split; [| split].
  - destruct dnull.
    + right. destruct (uw_null_out _ _ _ _ _ _ out _ D Haout Haoutl) as [-> Ha].
      destruct D as (-> & -> & -> & -> & ->).
      split; [reflexivity | split; [lia | exists Tsh; split; [auto | reflexivity]]].
    + left. destruct D as (Hw & Hdp & Hc & Ht & Hdc & Hdn). simpl. auto.
  - rewrite uw_out_ptr, Z.add_0_r. exact Hno.
  - rewrite Hao. destruct dnull.
    + destruct (uw_null_out _ _ _ _ _ _ out _ D Haout Haoutl) as [-> Ha].
      destruct D as (-> & -> & -> & -> & ->). rewrite Ha.
      simpl. split; [apply writable_share_top |]. split; [destruct v; try contradiction; simpl; auto |].
      repeat split; rep_lia.
    + destruct D as (Hw & Hdp & Hc & Ht & Hdc & Hdn). simpl.
      split; [exact Hw |]. split; [exact Hdp |].
      repeat split; try lia. apply Zlength_dest_after; lia.
Qed.

Lemma un_call_body : un_call_stmt.
Proof.
  intros Espec A v F Pv.
  destruct A as [gv dnull dsh dp dn dc cap dlp dtok slp gsh tsh].
  unfold un_M1, un_LC, un_lcl, un_fr, un_sep, un_facts, uw_call_st in *.
  abbreviate_semax.
  Intros m out z L ao.
  unfold un_sfacts, un_fr in *.
  destruct F as (D & Hgsh & Htsh).
  destruct H1 as (Hhd & Hls & Hlh & Had & Hmsg & Htin & Htout & Hni & Hno & Hao & Hoc & Hraw & Hsw).
  pose proof (uw_aout_bounds cap out ao Hao Hoc) as [Haout Haoutl].
  forward_call (gv, Tsh, v, z, Vundef, Some L, InNull, @nil Z, Some (uw_ob dnull dsh dp v dn dc out), 0,
                gsh, tsh, false, uw_otok dnull dtok).
  { rewrite istreamA_opt_ptr, head_emp, is_live_ptr by (rewrite ?Hls; auto).
    rewrite un_bufs with (cap := cap) by (auto; rewrite ?Zlength_nil; lia). rewrite app_nil_r. cancel. }
  { apply (un_call_out dnull dsh dp dn dc cap dtok v z out ao); auto; lia. }
  Intros vret. destruct vret as [[[r z'] st'] ow]. simpl fst in *; simpl snd in *.
  match goal with Hx: inflate_rel _ _ _ _ _ _ _ _ _ _ _ |- _ => rename Hx into Hrel end.
  match goal with Hx: raw_live _ = raw_live _ |- _ => rename Hx into Hraw' end.
  match goal with Hx: match st' with Some _ => _ | None => _ end |- _ => rename Hx into Hsw' end.
  destruct Hrel as [[Hbad _] | [_ [L0 [o [res [winp [HL [Ho [Hrun [Hsnx [Hr [How [Hz' [Hwin Hst']]]]]]]]]]]]]].
  { exfalso. unfold inflate_bad in Hbad. rewrite is_live_ptr in Hbad by auto.
    destruct Hbad as [Hb | [Hb | [Hb Hb']]]; [discriminate | discriminate | contradiction]. }
  injection HL as <-. injection Ho as <-. subst r ow z' st'.
  rewrite Zlength_nil in Hsnx. assert (Hs0: m_snx (r_m res) = 0) by lia. clear Hsnx.
  assert (Hcall: m_init z L [] = uw_call [] cap m 0 out 0 ao) by exact (m_init_call z L m [] cap 0 out 0 ao
    Hls Hlh H3 Had Hmsg Htin Htout).
  rewrite Hcall in Hrun.
  pose proof (run2_frame _ _ _ _ _ (m_next_vmode m _ _ H0) Hrun) as (Fi & Fa & Fs & Fh & Fv).
  unfold uw_call in Fi, Fa, Fh. rewrite m_next_inp in Fi. rewrite m_next_aout in Fa. rewrite m_next_head, Hhd in Fh.
  change (sublist 0 (0 + uw_ain [] 0 0) []) with (@nil Z) in Fi.
  assert (Hret: -5 <= r_ret res <= 2) by (eapply run2_ret; [| exact Hrun]; simpl; unfold Z_OK; lia).
  rewrite Hraw in Hraw'.
  rewrite istreamA_opt_ptr, head_emp, !is_live_ptr by (simpl; auto).
  match goal with |- context [istream _ _ _ ?zz _] =>
    assert_PROP (zf_ok zz) as Hzok by (unfold istream; entailer!) end.
  unfold z_after, zf_ok in Hzok. simpl in Hzok. rewrite Fa, Fs in Hzok.
  rewrite un_bufs with (cap := cap) by (auto; lia).
  replace (cap - Zlength out - uw_aout cap out ao)
    with (cap - Zlength (out ++ m_ow (r_m res)) - (uw_aout cap out ao - Zlength (m_ow (r_m res))))
    by (rewrite Zlength_app; lia).
  Intros. forward.
  Exists (r_ret res) (r_m res) (out ++ m_ow (r_m res))
    (z_after z InNull (uw_ob dnull dsh dp v dn dc out) res)
    (Live (l_sp L) winp (m_s (r_m res)) (m_h (r_m res)) (l_headp L) (l_hsh L) (l_xb L) (l_nb L) (l_cb L))
    (uw_aout cap out ao - Zlength (m_ow (r_m res))).
  entailer!.
  split.
  { intro E. split; [| auto].
    pose proof (reach_w_next [] cap m 0 out 0 ao res H Hrun E) as X.
    rewrite Hs0 in X. exact X. }
  split.
  { intro E. pose proof (reach_w_stop [] cap m 0 out 0 ao res H Hrun E) as X.
    rewrite Hs0 in X. exact X. }
  unfold z_after; cbn [zf_ni zf_no zf_ai zf_ao in_ptr]. rewrite uw_out_ptr, Fi, Fa, Fs, Hs0, Zlength_app.
  split; [split; [f_equal; lia | lia] | split; [reflexivity | lia]].
Qed.
