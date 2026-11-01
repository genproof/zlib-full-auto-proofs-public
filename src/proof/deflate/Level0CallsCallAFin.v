(** * Level 0 over several deflate() calls: the first call with Z_FINISH

    The first call of the harnesses' loop given all the data (at most [k] blocks) with Z_FINISH: deflate() writes
    the wrapper header, the stored blocks of the data and the trailer and returns Z_STREAM_END; or, with gzip
    when the whole output is more than the 2^32 - 1 bytes of the call's output space, it writes the trailer's
    first bytes, keeps the others pending and returns Z_OK ([Level0CallsInv.l0_stC]; then the data needed
    [k] >= [l0_blocks n] blocks). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.Level0CallsCallANf.
Require Import Zlib.proof.deflate.Level0.
Require Import Zlib.proof.deflate.LTCSpecs.
Require Import Zlib.proof.deflate.AdlerKeep.
Import ListNotations.
Local Open Scope Z_scope.

(** The trailer stage keeps the gz_header pointer. *)
Lemma l0_trailer_gzhead s z f s' z' c :
  c_deflate_trailer s z f = Some (s', z', c) -> d_gzhead s' = d_gzhead s.
Proof.
  unfold c_deflate_trailer. intros H.
  destruct (negb (f =? Z_FINISH)); [inversion H; reflexivity|].
  destruct (d_wrap s <=? 0); [inversion H; reflexivity|].
  cbv zeta in H.
  destruct (if d_wrap s =? 2 then _ else _) as [s0|] eqn:E0; cbn [bind] in H; [|discriminate].
  assert (G0 : d_gzhead s0 = d_gzhead s).
  { destruct (d_wrap s =? 2).
    - exact (dg_dput_bytes _ _ _ E0).
    - destruct (c_putShortMSB s _) as [s1|] eqn:E1; cbn [bind] in E0; [|discriminate].
      rewrite (dg_putShortMSB _ _ _ E0). exact (dg_putShortMSB _ _ _ E1). }
  destruct (c_flush_pending s0 z) as [[s1 z1]|] eqn:E1; cbn [bind] in H; [|discriminate].
  pose proof (dg_flush_pending _ _ _ _ E1) as G1.
  inversion H; subst. destruct (d_wrap s1 >? 0); cbn; congruence.
Qed.

Theorem l0_callA_fin wbits data room pos O s tin tout adler msg k :
  l0_com wbits data room pos O s tin tout adler -> l0_stA wbits pos O s adler -> 1 <= k <= 65532 ->
  Zlength data <= 65535 * k ->
  l0_call_post wbits data room pos O s tin tout adler msg k (l0_blocks (Zlength data) <= k).
Proof.
  intros Hcom HA Hk Hnk.
  pose proof Hcom as (Hb & Hn & Hr & Hti & Hto & HbO & Hgz & Ha).
  pose proof (l0_stA_bad _ _ _ _ _ HA) as Hbad.
  pose proof HA as (-> & -> & _). subst tin tout.
  unfold l0_call_post. rewrite Zlength_nil, Z.sub_0_r. cbv zeta.
  pose proof (Zlength_nonneg data) as Hn0.
  set (n := Zlength data) in *.
  pose proof (l0_hlen_range wbits) as Hhl. pose proof (l0_tlen_range wbits) as Htl.
  pose proof (l0_blocks_pos n Hn0) as HB.
  assert (Einb : l0_inb data 0 k = data).
  { unfold l0_inb, l0_piece. fold n. replace (n - 0 <=? 65535 * k) with true by (symmetry; apply Z.leb_le; lia).
    rewrite Z.add_0_l, Z.sub_0_r. apply sublist_same; reflexivity. }
  assert (Efl : l0_flush n 0 k = Z_FINISH)
    by (unfold l0_flush; replace (n - 0 <=? 65535 * k) with true by (symmetry; apply Z.leb_le; lia); reflexivity).
  rewrite Einb, Efl. fold n.
  set (aout := l0_clip room).
  assert (Hr' : l0_hlen wbits + 5 * l0_blocks n + n + l0_tlen wbits <= room) by (rewrite <- l0_size_eq; lia).
  assert (Hsp : l0_hlen wbits + 5 * l0_blocks n + n <= aout)
    by (apply l0_space_first_fin with (tl := l0_tlen wbits) (k := k); auto; lia).
  assert (Haout : aout <= 4294967295) by (unfold aout, l0_clip; lia).
  destruct (l0_callA_head wbits 0 [] s adler data aout msg Z_FINISH HA Hgz Hb ltac:(right; reflexivity)
              ltac:(lia))
    as (s2 & z2 & H & Eh & HR2 & Hwr2 & Hgz2 & HH & HbH & Ez2 & Had2 & Har2).
  fold n in Eh, Ez2.
  destruct (l0c_comp_fin s2 z2 HR2)
    as (s5 & z5 & Ec & Hstp & Ho5 & Hp5 & Hpo5 & Hbv5 & Hw5 & H85 & Hs5 & Hg5 & Hpbs5 & Hpb5 & Hla5).
  { rewrite Ez2. unfold zall_w, zin_in_w, zout_ok_w. cbn [z_in z_next_in z_avail_in z_total_in z_out
      z_avail_out z_total_out]. unfold l0_max_size in Hn. repeat split; try lia. exact Hb. }
  { exact Had2. }
  { rewrite Ez2. cbn [z_avail_in z_avail_out]. lia. }
  assert (Erun := l0_deflate_run s _ Z_FINISH _ _ _ Hbad ltac:(cbv; split; discriminate)
                    ltac:(rewrite Eh; cbn [then_stage bind]; exact Ec)).
  cbn iota in Erun.
  assert (Hstp' := Hstp). rewrite Ez2 in Hstp'.
  destruct Hstp' as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11).
  cbn [z_in z_next_in z_avail_in z_total_in z_out z_avail_out z_total_out z_adler z_msg] in *.
  rewrite Z.add_0_l, sublist_same in A6, A7, A8, A9, A10 by (fold n; lia).
  rewrite Zlength_stored_blocks in A8, A9, A10. fold n in A8, A9, A10.
  rewrite u64_id in A5, A10 by (unfold l0_max_size in Hn; lia).
  assert (Har5 : 0 <= z_adler z5 <= l0_max_u64).
  { apply (adler_range_zstep (d_wrap s2) z2 z5 n (stored_blocks data)).
    - rewrite Hwr2. apply wrap_of_range.
    - rewrite Ez2 in Hstp |- *. cbn [z_next_in z_avail_in z_in] in Hstp.
      rewrite Z.add_0_l, sublist_same in Hstp by (fold n; lia). exact Hstp.
    - rewrite A6. apply adler_ok_upd; [exact Hb|exact Had2].
    - exact Har2. }
  assert (Hbs : bytes (H ++ stored_blocks data)) by (apply Forall_app; split; [exact HbH|apply bytes_stored_blocks; exact Hb]).
  destruct (Z_le_gt_dec (tlr_len (wrap_of wbits)) (z_avail_out z5)) as [Hfit|Hcut].
  - (* the trailer fits: Z_STREAM_END *)
    destruct (l0c_trail s5 z5 Ho5 Hp5 Hpo5 Hbv5 H85 ltac:(rewrite Hw5, Hwr2; apply wrap_of_range)
                ltac:(rewrite Hw5, Hwr2; lia) ltac:(rewrite A10; lia)
                ltac:(rewrite A10, A9; unfold l0_max_u64 in Hr; lia))
      as (s6 & z6 & T & Et & Hzo & HT & HbT).
    rewrite Hw5, Hwr2, <- l0_tlen_eq in HT. rewrite <- l0_tlen_eq in Hfit.
    destruct Hzo as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
    exists s6, z6, Z_STREAM_END.
    split; [rewrite Erun; exact Et|].
    rewrite B3, A4, Z.sub_diag, Z.sub_0_r.
    split; [congruence|]. split; [lia|]. split; [rewrite B2, A3; lia|]. split; [rewrite B4, A5; lia|].
    split; [rewrite B8, A9; lia|].
    split; [rewrite B8, B7, A7, A9, !Zlength_app, Zlength_stored_blocks; fold n; lia|].
    split; [rewrite B9, B8, A10, A9; lia|].
    split; [rewrite B7, A7; apply Forall_app; split; [exact Hbs|exact HbT]|].
    split; [rewrite (l0_trailer_gzhead _ _ _ _ _ _ Et), Hg5; exact Hgz2|].
    split; [intros C; discriminate C|].
    intros _. split; [reflexivity|].
    exists H, T. rewrite B7, A7, app_nil_l, <- app_assoc.
    split; [reflexivity|]. split; [exact HH|]. split; [exact HT|].
    rewrite B9, A10, l0_size_eq. fold n. lia.
  - (* gzip, the trailer cut *)
    assert (Hlt : aout < l0_hlen wbits + 5 * l0_blocks n + n + l0_tlen wbits)
      by (rewrite <- l0_tlen_eq in Hcut; rewrite A9 in Hcut; lia).
    destruct (l0_cut_gzip (l0_hlen wbits) (l0_tlen wbits) n room Hn0 Hr' k Hk Hnk Hlt) as (Ea & Hgzip).
    assert (Hw2 : wrap_of wbits = 2).
    { unfold l0_hlen, l0_tlen, wrap_of in *. destruct (wbits <? 0); [lia|]. destruct (wbits >? 15); [reflexivity|lia]. }
    assert (Htl8 : l0_tlen wbits = 8) by (rewrite l0_tlen_eq, Hw2; reflexivity).
    destruct (l0x_trail_cut s5 z5 Ho5 Hp5 Hpo5 Hbv5 ltac:(rewrite Hw5, Hwr2; exact Hw2) H85 Hs5
                ltac:(rewrite Hg5; exact Hgz2) Hpbs5 Hpb5 Hla5
                ltac:(unfold zout_ok_w; rewrite A9, A10; unfold l0_max_u64 in Hr; lia)
                ltac:(rewrite Hw2 in Hcut; cbn in Hcut; lia))
      as (s6 & z6 & x & Et & Hzo & Hbx & Hlx & Hpx & Hpend).
    destruct Hzo as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
    exists s6, z6, Z_OK.
    split; [rewrite Erun; exact Et|].
    rewrite B3, A4, Z.sub_diag, Z.sub_0_r.
    split; [congruence|]. split; [lia|]. split; [rewrite B2, A3; lia|]. split; [rewrite B4, A5; lia|].
    split; [rewrite B8, A9; lia|].
    split; [rewrite B8, B7, A7, A9, !Zlength_app, Zlength_stored_blocks; fold n; lia|].
    split; [rewrite B9, B8, A10, A9; lia|].
    split; [rewrite B7, A7; apply Forall_app; split; [exact Hbs|exact Hbx]|].
    split; [destruct Hpend as (_ & _ & _ & _ & _ & _ & _ & _ & Hg6); exact Hg6|].
    split; [|intros C; exfalso; apply C; reflexivity].
    intros _.
    assert (EO : [] ++ z_out z6 = H ++ stored_blocks data ++ x) by (rewrite B7, A7, <- app_assoc; reflexivity).
    assert (LO : Zlength ([] ++ z_out z6) = 4294967295).
    { rewrite EO, !Zlength_app, Zlength_stored_blocks, Hlx, A9, HH. fold n. lia. }
    split; [split|].
    + unfold l0_com. split; [exact Hb|]. split; [exact Hn|]. split; [exact Hr|].
      split; [rewrite B4, A5; lia|]. split; [rewrite LO, B9, A10, Hlx, A9; lia|].
      split; [rewrite EO; apply Forall_app; split; [exact HbH|apply Forall_app; split;
                [apply bytes_stored_blocks; exact Hb|exact Hbx]]|].
      split; [destruct Hpend as (_ & _ & _ & _ & _ & _ & _ & _ & Hg6); exact Hg6|].
      rewrite B5. exact Har5.
    + right; right. exists H, x.
      split; [exact Hpend|]. split; [lia|]. split; [exact EO|]. split; [exact HH|].
      split; [lia|exact LO].
    + intros _. apply l0_blocks_le; lia.
Qed.
