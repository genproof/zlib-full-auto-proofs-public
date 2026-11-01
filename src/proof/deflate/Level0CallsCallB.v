(** * Level 0 over several deflate() calls: a call after Z_NO_FLUSH calls ([Level0CallsInv.l0_stB])

    The header and [j] whole blocks are written, the stream is ready ([Level0CallsComp.l0_ready]) and some data is
    left.  With [k] blocks drawn:
    - more than [k] blocks left: Z_NO_FLUSH, the call writes [k] non-final stored blocks and returns Z_OK, the
      invariant holds again with [j + k] blocks;
    - otherwise: Z_FINISH with the rest, the call writes its stored blocks (the last one final) and the trailer,
      which fits (at most 65532 * 65540 + 8 < 2^32 - 1 bytes, and room covers it), and returns Z_STREAM_END. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.Level0CallsInv.
Require Import Zlib.proof.deflate.Level0CallsCallAFin.
Require Import Zlib.proof.deflate.Level0.
Require Import Zlib.proof.deflate.LTCMisc.
Require Import Zlib.proof.deflate.LTApiEntry.
Require Import Zlib.proof.deflate.LTCStored2.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** deflate() records the flush in last_flush: the stream stays ready. *)
Lemma l0_ready_lf s f : l0_ready s -> l0_ready (set_d_last_flush s f).
Proof.
  intros (HW & Ho & Hp & Hpo & Hbv & Hlv & Hss & Hst).
  refine (conj (Zlib.proof.deflate.LTCMisc.W_frame s _ HW (ent_core_eq_lf s f)) _).
  exact (conj Ho (conj Hp (conj Hpo (conj Hbv (conj Hlv (conj Hss Hst)))))).
Qed.

Lemma l0_ready_bad s : l0_ready s -> bad_state s = false.
Proof.
  intros (_ & _ & _ & _ & _ & _ & _ & Hst). unfold bad_state, c_deflateStateCheck. rewrite Hst. reflexivity.
Qed.

Lemma l0_callB wbits data room pos O s tin tout adler msg k :
  l0_com wbits data room pos O s tin tout adler -> l0_stB wbits data pos O s adler -> 1 <= k <= 65532 ->
  l0_call_post wbits data room pos O s tin tout adler msg k False.
Proof.
  intros (Hb & Hn & Hr & Hti & Hto & HbO & Hgz & Ha) (j & H & HR & Hw & Hao & Hpos & Hp & HO & HH & HbH) Hk.
  set (n := Zlength data) in *.
  pose proof (l0_hlen_range wbits) as Lh. pose proof (l0_tlen_range wbits) as Lt.
  pose proof (Zlength_nonneg data) as Ln. fold n in Ln.
  assert (HLO : Zlength O = l0_hlen wbits + 65540 * Z.of_nat j)
    by (rewrite HO, Zlength_app, Zlength_nblocks by lia; lia).
  rewrite l0_size_eq in Hr.
  pose proof HR as (_ & _ & Hpd0 & _ & _ & _ & _ & Hst0).
  pose proof (l0_ready_bad s HR) as Hbad.
  assert (Hw2 : 0 <= d_wrap s <= 2) by (rewrite Hw; apply wrap_of_range).
  unfold l0_call_post, l0_inb, l0_flush, l0_piece. cbv zeta. fold n.
  destruct (Z.leb_spec (n - pos) (65535 * k)) as [Hlast|Hmore].
  - (* the last call: Z_FINISH with the rest *)
    set (rest := n - pos).
    set (inb := sublist pos (pos + rest) data).
    assert (Linb : Zlength inb = rest) by (unfold inb; rewrite Zlength_sublist; lia).
    rewrite Linb.
    set (aout := l0_clip (room - Zlength O)).
    pose proof (l0_space_busy_fin (l0_hlen wbits) (l0_tlen wbits) n room Lt ltac:(lia) (Z.of_nat j) k
                  ltac:(lia) Hk ltac:(lia) ltac:(lia)) as Hsp.
    rewrite <- HLO in Hsp. fold aout in Hsp. replace (n - 65535 * Z.of_nat j) with rest in Hsp by lia.
    assert (Haout : aout <= 4294967295 /\ aout <= room - Zlength O) by (unfold aout, l0_clip; lia).
    pose proof (l0_blocks_pos rest ltac:(lia)) as Hbr.
    set (z := zcall inb 0 rest tin aout tout adler msg).
    assert (Hz : zall_w z).
    { unfold zall_w, zin_in_w, zout_ok_w, z. cbn [zcall z_in z_next_in z_avail_in z_total_in z_avail_out z_total_out].
      rewrite Linb. unfold l0_max_size, l0_max_u64 in *.
      repeat split; try lia. unfold inb. apply bytes_sublist; auto. }
    destruct (l0c_comp_fin (set_d_last_flush s Z_FINISH) z (l0_ready_lf s _ HR) Hz ltac:(exact Hao)
                ltac:(unfold z; cbn [zcall z_avail_in z_avail_out]; lia))
      as (s5 & z5 & Ec & Hstp & Ho5 & Hp5 & Hpo5 & Hbv5 & Hw5 & H85 & Hst5 & Hg5 & Hpbs5 & Hpb5 & Hla5).
    change (d_wrap (set_d_last_flush s Z_FINISH)) with (d_wrap s) in Hstp, Hw5.
    change (d_gzhead (set_d_last_flush s Z_FINISH)) with (d_gzhead s) in Hg5.
    pose proof Hstp as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11).
    unfold z in A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11.
    cbn [zcall z_in z_next_in z_avail_in z_total_in z_out z_avail_out z_total_out z_adler z_msg]
      in A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11.
    rewrite Z.add_0_l, (sublist_same 0 rest inb) in A7, A8, A9, A10 by lia.
    rewrite Zlength_stored_blocks, Linb in A8, A9, A10.
    rewrite u64_id in A10 by (unfold l0_max_u64 in *; lia).
    destruct (l0c_trail s5 z5 Ho5 Hp5 Hpo5 Hbv5 H85 ltac:(rewrite Hw5; exact Hw2)
                ltac:(rewrite Hw5, A9, Hw, <- l0_tlen_eq; lia) ltac:(rewrite A10; lia)
                ltac:(rewrite A10, A9; unfold l0_max_u64 in *; lia))
      as (s6 & z6 & T & Et & Hzo & HT & HbT).
    rewrite Hw5, Hw, <- l0_tlen_eq in HT.
    destruct Hzo as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
    assert (Ecall : c_deflate s z Z_FINISH = Some (s6, z6, Z_STREAM_END)).
    { rewrite c_deflate_stages, Hbad. cbv beta iota.
      change ((Z_FINISH >? Z_BLOCK) || (Z_FINISH <? 0)) with false. cbn [orb].
      rewrite (l0c_busy s z Z_FINISH Hst0 Hpd0 ltac:(unfold z; cbn; lia) ltac:(unfold z; cbn; lia)).
      cbn [then_stage bind]. rewrite Ec. cbn [bind]. exact Et. }
    exists s6, z6, Z_STREAM_END. split; [exact Ecall|].
    split; [congruence|].
    split; [lia|]. split; [lia|]. split; [rewrite B4, A5, u64_id by (unfold l0_max_size, l0_max_u64 in *; lia); lia|].
    split; [lia|]. split; [rewrite B7, A7, app_nil_l, Zlength_app, Zlength_stored_blocks, Linb; lia|].
    split; [rewrite B9, A10; lia|].
    split; [rewrite B7, A7; cbn [app]; apply Forall_app; split; [apply bytes_stored_blocks; unfold inb; apply bytes_sublist; auto|exact HbT]|].
    split; [rewrite (l0_trailer_gzhead _ _ _ _ _ _ Et); congruence|].
    split; [intros C; discriminate|].
    intros _. split; [reflexivity|].
    exists H, T. split.
    + rewrite B7, A7. cbn [app]. rewrite HO, <- !app_assoc.
      rewrite (stored_blocks_split j data) by (right; fold n; lia).
      rewrite <- app_assoc. do 2 f_equal. unfold inb. f_equal. f_equal. f_equal; [exact Hpos|unfold rest; fold n; lia].
    + split; [exact HH|]. split; [exact HT|].
      rewrite B9, A10, Hto, HLO, l0_size_eq. fold n.
      rewrite (l0_blocks_split n (Z.of_nat j)) by lia. replace (n - 65535 * Z.of_nat j) with rest by lia. lia.
  - (* more blocks left: Z_NO_FLUSH with k blocks *)
    set (inb := sublist pos (pos + 65535 * k) data).
    assert (Linb : Zlength inb = 65535 * k) by (unfold inb; rewrite Zlength_sublist; lia).
    rewrite Linb.
    set (aout := l0_clip (room - Zlength O)).
    pose proof (l0_space_busy_nf (l0_hlen wbits) (l0_tlen wbits) n room Lt ltac:(lia) (Z.of_nat j) k
                  ltac:(lia) Hk ltac:(lia)) as Hsp.
    rewrite <- HLO in Hsp. fold aout in Hsp.
    assert (Haout : aout <= 4294967295 /\ aout <= room - Zlength O) by (unfold aout, l0_clip; lia).
    set (z := zcall inb 0 (65535 * k) tin aout tout adler msg).
    assert (Hz : zall_w z).
    { unfold zall_w, zin_in_w, zout_ok_w, z. cbn [zcall z_in z_next_in z_avail_in z_total_in z_avail_out z_total_out].
      rewrite Linb. unfold l0_max_size, l0_max_u64 in *.
      repeat split; try lia. unfold inb. apply bytes_sublist; auto. }
    destruct (l0c_comp_nf (set_d_last_flush s Z_NO_FLUSH) z (Z.to_nat k) (l0_ready_lf s _ HR) Hz ltac:(exact Hao)
                ltac:(unfold z; cbn [zcall z_avail_in]; rewrite Z2Nat.id; lia) ltac:(lia)
                ltac:(rewrite Z2Nat.id by lia; unfold z; cbn [zcall z_avail_out]; lia))
      as (s' & z' & Ec & Hstp & HR' & Ecp).
    rewrite Z2Nat.id in Hstp by lia.
    assert (Hkk : Z.of_nat (Z.to_nat k) = k) by (apply Z2Nat.id; lia).
    change (d_wrap (set_d_last_flush s Z_NO_FLUSH)) with (d_wrap s) in Hstp.
    destruct (cp_api _ _ Ecp) as (_ & Ew' & Eg').
    change (d_wrap (set_d_last_flush s Z_NO_FLUSH)) with (d_wrap s) in Ew'.
    change (d_gzhead (set_d_last_flush s Z_NO_FLUSH)) with (d_gzhead s) in Eg'.
    pose proof Hstp as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11).
    unfold z in A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11.
    cbn [zcall z_in z_next_in z_avail_in z_total_in z_out z_avail_out z_total_out z_adler z_msg]
      in A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11.
    rewrite Zlength_nblocks in A8, A9, A10 by (rewrite ?Linb; lia).
    rewrite u64_id in A10 by (unfold l0_max_u64 in *; lia).
    rewrite u64_id in A5 by (unfold l0_max_size, l0_max_u64 in *; lia).
    assert (Ecall : c_deflate s z Z_NO_FLUSH = Some (s', z', Z_OK)).
    { rewrite c_deflate_stages, Hbad. cbv beta iota.
      change ((Z_NO_FLUSH >? Z_BLOCK) || (Z_NO_FLUSH <? 0)) with false. cbn [orb].
      rewrite (l0c_busy s z Z_NO_FLUSH Hst0 Hpd0 ltac:(unfold z; cbn; lia) ltac:(unfold z; cbn; lia)).
      cbn [then_stage bind]. rewrite Ec. reflexivity. }
    assert (Eblk : nblocks 0 (Z.to_nat k) inb = nblocks pos (Z.to_nat k) data)
      by (unfold inb; apply nblocks_sublist; rewrite ?Z2Nat.id; lia).
    assert (HbX : bytes (nblocks 0 (Z.to_nat k) inb))
      by (apply bytes_nblocks; [lia|rewrite Z2Nat.id, Linb; lia|unfold inb; apply bytes_sublist; auto]).
    exists s', z', Z_OK. split; [exact Ecall|].
    split; [congruence|].
    split; [lia|]. split; [lia|]. split; [lia|].
    split; [lia|]. split; [rewrite A7, Zlength_app, Zlength_nblocks by (rewrite ?Linb; lia); cbn; lia|].
    split; [lia|].
    split; [rewrite A7; exact HbX|].
    split; [congruence|].
    split; [|intros C; exfalso; apply C; reflexivity].
    intros _.
    assert (EO' : O ++ z_out z' = H ++ nblocks 0 (j + Z.to_nat k) data).
    { rewrite A7. cbn [app]. rewrite Eblk, HO, <- app_assoc, nblocks_add. do 2 f_equal. f_equal. lia. }
    split.
    + split.
      * unfold l0_com. rewrite A5, A10, Hti, Hto, A4, A7, app_nil_l, Zlength_app, Zlength_nblocks
          by (rewrite ?Linb; lia).
        split; [exact Hb|]. split; [exact Hn|]. split; [rewrite l0_size_eq; exact Hr|].
        split; [lia|]. split; [lia|]. split; [apply Forall_app; split; [exact HbO|exact HbX]|].
        split; [congruence|].
        apply (adler_range_zstep (d_wrap s) z z' (65535 * k) _ Hw2 Hstp); [|exact Ha].
        exact (adler_ok_zstep_l0 _ _ _ _ _ Hz Hao Hstp).
      * right; left. exists (j + Z.to_nat k)%nat, H.
        split; [exact HR'|]. split; [congruence|].
        split; [rewrite Ew'; exact (adler_ok_zstep_l0 _ _ _ _ _ Hz Hao Hstp)|].
        rewrite A4. split; [rewrite Nat2Z.inj_add, Hkk; lia|].
        split; [lia|]. split; [exact EO'|]. split; [exact HH|exact HbH].
    + intros (H' & T1 & (_ & _ & HstC & _) & _).
      destruct HR' as (_ & _ & _ & _ & _ & _ & _ & HstB). rewrite HstC in HstB. cbv in HstB. discriminate.
Qed.
