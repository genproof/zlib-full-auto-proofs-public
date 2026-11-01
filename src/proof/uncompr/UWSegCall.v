(* uncompress2_z for any sizes (UWSegs.v), the loop's body, part 3: err = inflate(&stream, Z_NO_FLUSH) on the
   offered pieces (SpecWSelf.inflate_specW_s; the output is the destination object or, for a Z_NULL destination,
   the empty object at the stream's member reserved): the call is the model's UModelW.uw_call. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Uncompr Zlib.units.Inflate.
Require Import Zlib.uncompr.code.
Require Import Zlib.proof.uncompr.UWSegs.
Require Import Zlib.proof.inflate_api.Spec5.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Uncompr.CS.
Local Open Scope logic.

(* the input object holds the offered piece src[used .. used + k) of the source *)
Lemma uw_sub_bytes: forall (sc: list val) (src: list Z) used k,
  sublist 0 (Zlength src) sc = byte_vals src -> 0 <= used -> 0 <= k -> used + k <= Zlength src ->
  Zlength src <= Zlength sc ->
  sublist used (used + Zlength (sublist used (used + k) src)) sc = byte_vals (sublist used (used + k) src).
Proof.
  intros sc src used k Hs Hu Hk Hl Hsc.
  rewrite Zlength_sublist by lia. replace (used + (used + k - used)) with (used + k) by lia.
  unfold byte_vals in *. rewrite <- sublist_map, <- Hs. rewrite sublist_sublist by lia. f_equal; lia.
Qed.

(* the output object's pointer at k bytes past out is the code's dest advanced by |out| + k *)
Lemma uw_out_ptr: forall dnull dsh dp v dn dc out k,
  out_ptr (uw_ob dnull dsh dp v dn dc out) k = offset_val (Zlength out + k) (uw_dq dnull dp v).
Proof. intros. destruct dnull; reflexivity. Qed.

(* for a Z_NULL destination nothing has been written *)
Lemma uw_null_out: forall dsh dp dn dc cap dtok (out: list Z) k,
  dest_ok_w true dsh dp dn dc cap dtok -> 0 <= k -> Zlength out + k <= cap -> out = [] /\ k = 0.
Proof.
  intros dsh dp dn dc cap dtok out k (_ & -> & _) Hk Hl.
  pose proof (Zlength_nonneg out). split; [apply Zlength_nil_inv |]; lia.
Qed.

(* inflate's input and output objects are the source and the destination (with ow written after out); for a
   Z_NULL destination the output object is the empty member `reserved` of the stream *)
Lemma uw_bufs: forall dnull dsh dp dn dc cap dtok L ssh sp used sn sc v out ow (stok: bool),
  dest_ok_w dnull dsh dp dn dc cap dtok -> isptr v -> Zlength out + Zlength ow <= cap ->
  bufs_opt (Some L) (InBuf ssh sp used sn sc) (Some (uw_ob dnull dsh dp v dn dc out)) ow stok
    (uw_otok dnull dtok) =
  (data_at ssh (tarray tuchar sn) sc sp * (if stok then malloc_token Ews (tarray tuchar sn) sp else emp) *
   dest_rep dnull dsh dp dn (dest_after dc dn (out ++ ow)) dtok).
Proof.
  intros dnull dsh dp dn dc cap dtok L ssh sp used sn sc v out ow stok D Pv Hl.
  destruct dnull.
  - pose proof (Zlength_nonneg ow).
    destruct (uw_null_out _ _ _ _ _ _ out (Zlength ow) D) as [-> Hw]; [lia | lia |].
    apply Zlength_nil_inv in Hw. subst ow.
    destruct D as (-> & -> & -> & -> & ->).
    unfold uw_ob, uw_otok, dest_rep. simpl.
    unfold bufs_opt, in_rep, out_opt, out_rep, in_tok, out_tok. simpl.
    rewrite data_at_zero_array_eq by (auto; apply isptr_offset_val; auto).
    change_compspecs Zlib.units.Uncompr.CS. destruct stok; apply pred_ext; cancel.
  - destruct D as (Hw & Hdp & Hc & Ht & Hdc & Hdn).
    unfold uw_ob, uw_otok, dest_rep.
    rewrite bufs_eq by lia. apply pred_ext; cancel.
Qed.

(* the pure part of inflate()'s precondition: the input object holds the offered piece of the source, the output
   object (the destination, or for a Z_NULL destination the stream's member `reserved` with nothing offered) has
   room for the offered avail_out *)
Lemma uw_call_pre: forall dnull dsh dp dn dc cap dtok ssh sp sn sc src v z used out ai ao,
  dest_ok_w dnull dsh dp dn dc cap dtok -> readable_share ssh -> isptr sp -> Zlength src <= sn ->
  Zlength sc = sn -> sn <= Ptrofs.max_unsigned -> sublist 0 (Zlength src) sc = byte_vals src -> bytes_ok src ->
  isptr v -> zf_ni z = offset_val used sp -> zf_no z = offset_val (Zlength out) (uw_dq dnull dp v) ->
  0 <= used -> zf_ai z = uw_ain src used ai -> zf_ao z = uw_aout cap out ao ->
  0 <= uw_ain src used ai -> used + uw_ain src used ai <= Zlength src ->
  0 <= uw_aout cap out ao -> Zlength out + uw_aout cap out ao <= cap ->
  (out_tok_ok (uw_otok dnull dtok) (Some (uw_ob dnull dsh dp v dn dc out)) \/
   self_out v (uw_otok dnull dtok) (Some (uw_ob dnull dsh dp v dn dc out)) (zf_ao z)) /\
  zf_ni z = in_ptr (InBuf ssh sp used sn sc) 0 /\
  (in_ok (InBuf ssh sp used sn sc) (sublist used (used + uw_ain src used ai) src) /\
   zf_ai z = Zlength (sublist used (used + uw_ain src used ai) src)) /\
  zf_no z = out_ptr (uw_ob dnull dsh dp v dn dc out) 0 /\
  out_ok (uw_ob dnull dsh dp v dn dc out) (zf_ao z).
Proof.
  intros dnull dsh dp dn dc cap dtok ssh sp sn sc src v z used out ai ao
    D Hssh Psp Hsrc Hsc Hsnm Hbytes Hok Pv Hni Hno Hu Hai Hao Hain Hainl Haout Haoutl.
  pose proof (Zlength_nonneg out) as Hol.
  split; [| split; [| split; [| split]]].
  - destruct dnull.
    + right. destruct (uw_null_out _ _ _ _ _ _ out _ D Haout Haoutl) as [-> Ha].
      destruct D as (-> & -> & -> & -> & ->).
      split; [reflexivity | split; [lia | exists Tsh; split; [auto | reflexivity]]].
    + left. destruct D as (Hw & Hdp & Hc & Ht & Hdc & Hdn). simpl. auto.
  - simpl. rewrite Hni, Z.add_0_r. reflexivity.
  - rewrite Zlength_sublist by lia. split; [| lia].
    simpl. repeat split; auto; try lia.
    + rewrite Zlength_sublist by lia. lia.
    + apply uw_sub_bytes; auto; lia.
    + apply Forall_sublist. auto.
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

Lemma uw_call_body : uw_call_stmt.
Proof.
  intros Espec A v F Pv.
  destruct A as [gv dnull dsh dp dn dc cap dlp dtok stok ssh sp sn sc src slp gsh tsh].
  unfold uw_M2, uw_LC, uw_lcl, uw_fr, uw_sep, uw_facts, uw_call_st in *.
  abbreviate_semax.
  Intros m used out z L ai ao.
  unfold uw_sfacts, uw_fr in *.
  destruct F as (D & Hssh & Psp & Hsn & Hsrc & Hsc & Hsnm & Hbytes & Hok & Hgsh & Htsh).
  destruct H1 as (Hhd & Hls & Hlh & Had & Hmsg & Htin & Htout & Hni & Hno & Hu & Hua & Hai & Hao & Hoc & Hraw & Hsw).
  pose proof (uw_ain_bounds src used ai Hu Hai Hua) as [Hain Hainl].
  pose proof (uw_aout_bounds cap out ao Hao Hoc) as [Haout Haoutl].
  forward_call (gv, Tsh, v, z, Vundef, Some L, InBuf ssh sp used sn sc,
                sublist used (used + uw_ain src used ai) src, Some (uw_ob dnull dsh dp v dn dc out), 0,
                gsh, tsh, stok, uw_otok dnull dtok).
  { rewrite istreamA_opt_ptr, head_emp, is_live_ptr by (rewrite ?Hls; auto).
    rewrite uw_bufs with (cap := cap) by (auto; rewrite ?Zlength_nil; lia). rewrite app_nil_r. cancel. }
  { apply uw_call_pre with (cap := cap) (ao := ao); auto; lia. }
  Intros vret. destruct vret as [[[r z'] st'] ow]. simpl fst in *; simpl snd in *.
  match goal with Hx: inflate_rel _ _ _ _ _ _ _ _ _ _ _ |- _ => rename Hx into Hrel end.
  match goal with Hx: raw_live _ = raw_live _ |- _ => rename Hx into Hraw' end.
  match goal with Hx: match st' with Some _ => _ | None => _ end |- _ => rename Hx into Hsw' end.
  destruct Hrel as [[Hbad _] | [_ [L0 [o [res [winp [HL [Ho [Hrun [Hsnx [Hr [How [Hz' [Hwin Hst']]]]]]]]]]]]]].
  { exfalso. unfold inflate_bad in Hbad. rewrite is_live_ptr in Hbad by auto.
    destruct Hbad as [Hb | [Hb | [Hb _]]]; discriminate. }
  injection HL as <-. injection Ho as <-. subst r ow z' st'.
  rewrite (m_init_call _ L m src cap used out ai ao) in Hrun by auto.
  pose proof (run2_frame _ _ _ _ _ (m_next_vmode m _ _ H0) Hrun) as (Fi & Fa & Fs & Fh & Fv).
  unfold uw_call in Fi, Fa, Fh. rewrite m_next_inp in Fi. rewrite m_next_aout in Fa. rewrite m_next_head, Hhd in Fh.
  assert (Hret: -5 <= r_ret res <= 2) by (eapply run2_ret; [| exact Hrun]; simpl; unfold Z_OK; lia).
  rewrite Hraw in Hraw'.
  rewrite istreamA_opt_ptr, head_emp, !is_live_ptr by (simpl; auto).
  match goal with |- context [istream _ _ _ ?zz _] =>
    assert_PROP (zf_ok zz) as Hzok by (unfold istream; entailer!) end.
  unfold z_after, zf_ok in Hzok. simpl in Hzok. rewrite Fi, Fa, Fs in Hzok.
  rewrite Zlength_sublist in Hzok, Hsnx by lia.
  rewrite uw_bufs with (cap := cap) by (auto; lia).
  replace (Zlength src - used - uw_ain src used ai)
    with (Zlength src - (used + m_snx (r_m res)) - (uw_ain src used ai - m_snx (r_m res))) by lia.
  replace (cap - Zlength out - uw_aout cap out ao)
    with (cap - Zlength (out ++ m_ow (r_m res)) - (uw_aout cap out ao - Zlength (m_ow (r_m res))))
    by (rewrite Zlength_app; lia).
  Intros. forward.
  Exists (r_ret res) (r_m res) (used + m_snx (r_m res)) (out ++ m_ow (r_m res))
    (z_after z (InBuf ssh sp used sn sc) (uw_ob dnull dsh dp v dn dc out) res)
    (Live (l_sp L) winp (m_s (r_m res)) (m_h (r_m res)) (l_headp L) (l_hsh L) (l_xb L) (l_nb L) (l_cb L))
    (uw_ain src used ai - m_snx (r_m res)) (uw_aout cap out ao - Zlength (m_ow (r_m res))).
  entailer!.
  split; [intro E; split; [eapply reach_w_next; eauto | auto] |].
  split; [intro E; eapply reach_w_stop; eauto |].
  unfold z_after; cbn [zf_no zf_ai zf_ao]. rewrite uw_out_ptr, Fi, Fa, Fs, Zlength_app, Zlength_sublist by lia.
  split; [split; [f_equal; lia | lia] | split; lia].
Qed.
