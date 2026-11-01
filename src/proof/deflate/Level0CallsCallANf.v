(** * Level 0 over several deflate() calls: the first call with Z_NO_FLUSH

    The first call of the harnesses' loop, on the state deflateInit2_ left ([Level0CallsInv.l0_stA]), given [k]
    whole blocks of 65535 bytes with more data after them: deflate() writes the wrapper header and the [k]
    blocks as non-final stored blocks and returns Z_OK; the loop goes on from [l0_stB] with [k] blocks done. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.Level0CallsInv.
Require Import Zlib.proof.deflate.Level0.
Require Import Zlib.proof.deflate.LTCMisc.
Require Import Zlib.proof.deflate.LTApiOut.
Import ListNotations.
Local Open Scope Z_scope.

(** The first two stages of the first call (entry, header), as [Level0CallsHead.l0c_head], from [l0_stA]. *)
Lemma l0_callA_head wbits pos O s adler inb aout msg flush :
  l0_stA wbits pos O s adler -> d_gzhead s = None -> bytes inb ->
  (Zlength inb <> 0 \/ flush = Z_FINISH) ->
  l0_hlen wbits < aout <= 4294967295 ->
  exists s2 z2 H,
    then_stage (c_deflate_entry s (zcall inb 0 (Zlength inb) 0 aout 0 adler msg) flush) hdr_stages =
      Some (s2, z2, None) /\
    l0_ready s2 /\ d_wrap s2 = wrap_of wbits /\ d_gzhead s2 = None /\
    Zlength H = l0_hlen wbits /\ bytes H /\
    z2 = mkST inb 0 (Zlength inb) 0 H (aout - l0_hlen wbits) (l0_hlen wbits) (z_adler z2) msg /\
    adler_ok (d_wrap s2) (z_adler z2) /\ 0 <= z_adler z2 <= l0_max_u64.
Proof.
  intros (_ & _ & HW & Ho & Hst & Hwr & Hlf & Hpo & Hpe & Hbv & Hss & Hbs & Hsn & Hlv & Ha) Hgz Hb Hin Hav.
  rewrite l0_hlen_eq in *.
  pose proof (wrap_of_range wbits) as Hw.
  destruct (l0c_head s (zcall inb 0 (Zlength inb) 0 aout 0 adler msg) flush (W_prm s HW) Ho Hpe Hpo Hbv Hsn
              Hss Hgz Hlf ltac:(rewrite Hwr; exact Hw) ltac:(rewrite Hwr; exact Hst)
              ltac:(cbn [zcall z_avail_in]; destruct Hin; [left|right]; auto)
              ltac:(cbn [zcall z_avail_out]; rewrite Hwr; lia) ltac:(cbn [zcall z_total_out]; lia))
    as (s2 & z2 & H & Eh & Hc2 & Ho2 & Hpe2 & Hpo2 & Hbv2 & Hst2 & Hwr2 & Hgz2 & HH & HbH & Hzo2 & Hzi2 & Hzn2 &
        Hza2 & Hzt2 & Hzm2 & Hzao2 & Hzto2 & Had2).
  rewrite Hwr in HH, Hzao2, Hzto2, Had2, Hwr2.
  cbn [zcall z_in z_next_in z_avail_in z_total_in z_out z_avail_out z_total_out z_adler z_msg] in
    Hzo2, Hzi2, Hzn2, Hza2, Hzt2, Hzm2, Hzao2, Hzto2, Had2.
  destruct (core_eq_fields _ _ Hc2) as (_ & _ & _ & _ & Hbs2 & Hss2 & _ & _ & _ & Hlv2 & _).
  exists s2, z2, H. split; [exact Eh|].
  split.
  { refine (conj (W_frame s s2 HW Hc2) (conj Ho2 (conj Hpe2 (conj Hpo2 (conj Hbv2 (conj _ (conj _ Hst2)))))));
      lia. }
  split; [exact Hwr2|]. split; [exact Hgz2|]. split; [exact HH|]. split; [exact HbH|].
  split; [destruct z2; cbn in *; subst; reflexivity|].
  rewrite Hwr2, Had2. split; [apply adler_ok_hdr|].
  unfold l0_max_u64. pose proof (wrap_of_range wbits).
  destruct (wrap_of wbits =? 1); [lia|]. destruct (wrap_of wbits =? 2); [lia|].
  subst adler. destruct (wrap_of wbits =? 2); lia.
Qed.

(** deflate()'s stages on a state that is not in error, with a valid flush. *)
Lemma l0_deflate_run s z flush s2 z2 r :
  bad_state s = false -> 0 <= flush <= Z_BLOCK ->
  then_stage (then_stage (c_deflate_entry s z flush) hdr_stages)
    (fun s0 z0 => c_deflate_compress s0 z0 flush) = Some (s2, z2, r) ->
  c_deflate s z flush = match r with Some c => Some (s2, z2, c) | None => c_deflate_trailer s2 z2 flush end.
Proof.
  intros Hb Hf E. rewrite c_deflate_stages, Hb. cbn [orb].
  replace ((flush >? Z_BLOCK) || (flush <? 0)) with false
    by (destruct (Z.gtb_spec flush Z_BLOCK); destruct (Z.ltb_spec flush 0); try lia; reflexivity).
  cbn [orb]. rewrite E. cbn [bind]. destruct r; reflexivity.
Qed.

Lemma l0_stA_bad wbits pos O s adler : l0_stA wbits pos O s adler -> bad_state s = false.
Proof.
  intros (_ & _ & _ & _ & Hst & _). unfold bad_state, c_deflateStateCheck. rewrite Hst.
  destruct (wrap_of wbits =? 2); reflexivity.
Qed.

Theorem l0_callA_nf wbits data room pos O s tin tout adler msg k :
  l0_com wbits data room pos O s tin tout adler -> l0_stA wbits pos O s adler -> 1 <= k <= 65532 ->
  65535 * k < Zlength data ->
  l0_call_post wbits data room pos O s tin tout adler msg k False.
Proof.
  intros Hcom HA Hk Hnk.
  pose proof Hcom as (Hb & Hn & Hr & Hti & Hto & HbO & Hgz & Ha).
  pose proof (l0_stA_bad _ _ _ _ _ HA) as Hbad.
  pose proof HA as (-> & -> & _). subst tin tout.
  unfold l0_call_post. rewrite Zlength_nil, Z.sub_0_r. cbv zeta.
  pose proof (Zlength_nonneg data) as Hn0.
  set (n := Zlength data) in *.
  pose proof (l0_hlen_range wbits) as Hhl. pose proof (l0_tlen_range wbits) as Htl.
  assert (Einb : l0_inb data 0 k = sublist 0 (65535 * k) data).
  { unfold l0_inb, l0_piece. fold n. replace (n - 0 <=? 65535 * k) with false by (symmetry; apply Z.leb_gt; lia).
    f_equal. }
  assert (Efl : l0_flush n 0 k = Z_NO_FLUSH)
    by (unfold l0_flush; replace (n - 0 <=? 65535 * k) with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
  rewrite Einb, Efl.
  set (inb := sublist 0 (65535 * k) data).
  assert (Li : Zlength inb = 65535 * k) by (unfold inb; rewrite Zlength_sublist; lia).
  assert (Hbi : bytes inb) by (apply bytes_sublist; exact Hb).
  set (aout := l0_clip room).
  assert (Hr' : l0_hlen wbits + 5 * l0_blocks n + n + l0_tlen wbits <= room) by (rewrite <- l0_size_eq; lia).
  assert (Hsp : l0_hlen wbits + 65540 * k + 5 <= aout)
    by (apply l0_space_first_nf with (tl := l0_tlen wbits) (n := n); auto; lia).
  assert (Haout : aout <= 4294967295) by (unfold aout, l0_clip; lia).
  destruct (l0_callA_head wbits 0 [] s adler inb aout msg Z_NO_FLUSH HA Hgz Hbi ltac:(left; lia) ltac:(lia))
    as (s2 & z2 & H & Eh & HR2 & Hwr2 & Hgz2 & HH & HbH & Ez2 & Had2 & Har2).
  rewrite Li in Eh, Ez2.
  destruct (l0c_comp_nf s2 z2 (Z.to_nat k) HR2) as (s' & z' & Ec & Hstp & HR' & Ecp).
  { rewrite Ez2. unfold zall_w, zin_in_w, zout_ok_w. cbn [z_in z_next_in z_avail_in z_total_in z_out
      z_avail_out z_total_out]. rewrite Li. repeat split; try lia. exact Hbi. }
  { exact Had2. }
  { rewrite Ez2. cbn [z_avail_in]. rewrite Z2Nat.id by lia. reflexivity. }
  { lia. }
  { rewrite Ez2. cbn [z_avail_out]. rewrite Z2Nat.id by lia. lia. }
  rewrite Z2Nat.id in Hstp by lia.
  assert (Erun := l0_deflate_run s _ Z_NO_FLUSH _ _ _ Hbad ltac:(cbv; split; discriminate)
                    ltac:(rewrite Eh; cbn [then_stage bind]; exact Ec)).
  destruct (cp_api _ _ Ecp) as (_ & Ew' & Eg').
  rewrite Ez2 in Hstp.
  destruct Hstp as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11).
  cbn [z_in z_next_in z_avail_in z_total_in z_out z_avail_out z_total_out z_adler z_msg] in *.
  rewrite Zlength_nblocks in A8, A9, A10 by (rewrite ?Li; lia).
  rewrite u64_id in A5, A10 by (unfold l0_max_size in Hn; lia).
  assert (Eblk : nblocks 0 (Z.to_nat k) inb = nblocks 0 (Z.to_nat k) data)
    by (unfold inb; apply nblocks_sublist; rewrite ?Z2Nat.id; lia).
  exists s', z', Z_OK. split; [rewrite Li; exact Erun|].
  split; [exact A1|].
  rewrite A4. replace (Zlength inb - (Zlength inb - 65535 * k)) with (65535 * k) by lia.
  split; [lia|]. split; [rewrite A3; lia|]. split; [rewrite A5; lia|].
  split; [rewrite A9; lia|].
  split; [rewrite A7, Zlength_app, Zlength_nblocks, A9 by (rewrite ?Li, ?Z2Nat.id; lia); lia|].
  split; [rewrite A10, A9; lia|].
  split; [rewrite A7; apply Forall_app; split; [exact HbH|apply bytes_nblocks; rewrite ?Li, ?Z2Nat.id; auto; lia]|].
  split; [rewrite Eg'; exact Hgz2|].
  split; [|intros C; exfalso; apply C; reflexivity].
  intros _.
  assert (Hpos : 0 + 65535 * k < n) by lia.
  assert (EO : [] ++ z_out z' = H ++ nblocks 0 (Z.to_nat k) data) by (rewrite A7, Eblk; reflexivity).
  split.
  - split.
    + unfold l0_com. rewrite EO. rewrite Zlength_app, Zlength_nblocks by (rewrite ?Z2Nat.id; lia).
      split; [exact Hb|]. split; [exact Hn|]. split; [exact Hr|].
      split; [rewrite A5; lia|]. split; [rewrite A10, Z2Nat.id; lia|].
      split; [apply Forall_app; split; [exact HbH|apply bytes_nblocks; rewrite ?Z2Nat.id; auto; lia]|].
      split; [rewrite Eg'; exact Hgz2|].
      apply (adler_range_zstep (d_wrap s2) (mkST inb 0 (65535 * k) 0 H (aout - l0_hlen wbits) (l0_hlen wbits)
               (z_adler z2) msg) z' (65535 * k) (nblocks 0 (Z.to_nat k) inb)).
      * rewrite Hwr2. apply wrap_of_range.
      * unfold zstep. cbn [z_in z_next_in z_avail_in z_total_in z_out z_avail_out z_total_out z_adler z_msg].
        rewrite Zlength_nblocks by (rewrite ?Li, ?Z2Nat.id; lia). rewrite u64_id by lia. rewrite u64_id by lia.
        repeat split; auto; lia.
      * rewrite A6. apply adler_ok_upd; [apply bytes_sublist; exact Hbi|exact Had2].
      * cbn [z_adler]. exact Har2.
    + right; left. exists (Z.to_nat k), H.
      split; [exact HR'|]. split; [rewrite Ew'; exact Hwr2|].
      split; [rewrite Ew', A6; apply adler_ok_upd; [apply bytes_sublist; exact Hbi|exact Had2]|].
      split; [rewrite Z2Nat.id; lia|]. split; [lia|].
      split; [exact EO|]. split; [exact HH|exact HbH].
  - intros (H' & T1 & _ & Hp & _). lia.
Qed.
