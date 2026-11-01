(** * The output of deflate at level 0 (the model theorem of rfc_level0_size and rfc_level0_blocks)

    After deflateInit2_ with level 0 returned Z_OK (any windowBits, memLevel and strategy it accepts), one
    deflate(Z_FINISH) offered a whole input object of at most 2^20 bytes and at least [l0_size] bytes of output
    space (at most 2^32 - 1: avail_out is a uInt) returns Z_STREAM_END having written exactly the wrapper header,
    the stored blocks of the data ([Level0Defs.stored_blocks]) and the trailer.

    The stream of the call is the one the caller has after deflateInit2_ and setting next_in / avail_in /
    next_out / avail_out ([zcall]): the counters, adler and msg as deflateInit2_ left them.  Why every block but
    the last has 65535 bytes: deflate_stored's block is min(65535, left + avail_in, avail_out - header bytes);
    nothing is left in the window ([left = 0]: the stream is fresh, the header has been flushed), and the output
    space covers 5 bytes per remaining block, the remaining data and the trailer. *)
From Coq Require Import ZArith List Lia.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.Level0Defs.
Require Import Zlib.proof.deflate.LTCInit Zlib.proof.deflate.LTCMisc Zlib.proof.deflate.LTApiInit.
Require Import Zlib.proof.deflate.Level0Head Zlib.proof.deflate.Level0Stored Zlib.proof.deflate.Level0Trail.
Import ListNotations.
Local Open Scope Z_scope.

Definition level0_stmt : Prop :=
  forall vok sok snull wbits mem strategy a1 a2 a3 a4 a5 z0 os z1 inb room,
    c_deflateInit2_ vok sok snull 0 Z_DEFLATED wbits mem strategy a1 a2 a3 a4 a5 z0 = Some (os, z1, Z_OK) ->
    bytes inb -> Zlength inb <= 1048576 ->
    l0_size wbits (Zlength inb) <= room <= 4294967295 ->
    exists s0 s' z' H T,
      os = Some s0 /\ d_gzhead s0 = None /\
      c_deflate s0 (zcall inb 0 (Zlength inb) (z_total_in z1) room (z_total_out z1) (z_adler z1) (z_msg z1))
        Z_FINISH = Some (s', z', Z_STREAM_END) /\
      z_out z' = H ++ stored_blocks inb ++ T /\ Zlength H = l0_hlen wbits /\ Zlength T = l0_tlen wbits /\
      z_total_out z' = l0_size wbits (Zlength inb).

(** ** The state after deflateInit2_

    Z_OK means that the version and size checks passed, the stream pointer is not Z_NULL, the parameters are
    accepted and every allocation succeeded; then the state is the one [LTCInit.init_ok] describes. *)
Lemma l0_init : forall vok sok snull wbits mem strategy a1 a2 a3 a4 a5 z0 os z1,
  c_deflateInit2_ vok sok snull 0 Z_DEFLATED wbits mem strategy a1 a2 a3 a4 a5 z0 = Some (os, z1, Z_OK) ->
  exists s0, os = Some s0 /\ W s0 /\ outok s0 /\
    d_status s0 = (if wrap_of wbits =? 2 then GZIP_STATE else INIT_STATE) /\ d_wrap s0 = wrap_of wbits /\
    d_gzhead s0 = None /\ d_last_flush s0 = -2 /\
    d_po s0 = 0 /\ d_pending s0 = 0 /\ d_bi_valid s0 = 0 /\
    d_strstart s0 = 0 /\ d_block_start s0 = 0 /\ d_sym_next s0 = 0 /\ d_level s0 = 0 /\
    z1 = mkST (z_in z0) (z_next_in z0) (z_avail_in z0) 0 (z_out z0) (z_avail_out z0) 0
              (if wrap_of wbits =? 2 then 0 else 1) None.
Proof.
  intros vok sok snull wbits mem strategy a1 a2 a3 a4 a5 z0 os z1 H.
  destruct vok, sok; try (unfold c_deflateInit2_ in H; cbn [negb orb] in H; inversion H; discriminate).
  destruct snull; [unfold c_deflateInit2_ in H; cbn [negb orb] in H; inversion H; discriminate|].
  rewrite init_shape in H.
  destruct (params_ok 0 Z_DEFLATED wbits mem strategy) eqn:P; [|inversion H; discriminate].
  destruct a1; [|inversion H; discriminate].
  destruct (andb (andb (andb a2 a3) a4) a5); [|inversion H; discriminate].
  destruct (init_ok 0 Z_DEFLATED wbits mem strategy z0 P)
    as (s & z' & E & HW & Ho & Hst & Hwr & Hgz & Hgi & Hlf & Hpo & Hpe & Hbv & Hss & Hla & Hbs & Hsn & Hlv &
        _ & _ & _ & Hz).
  rewrite E in H. inversion H; subst os z1; clear H.
  exists s. split; [reflexivity|]. split; [exact HW|]. split; [exact Ho|].
  split; [exact Hst|]. split; [exact Hwr|]. split; [exact Hgz|]. split; [exact Hlf|].
  split; [exact Hpo|]. split; [exact Hpe|]. split; [exact Hbv|]. split; [exact Hss|].
  split; [exact Hbs|]. split; [exact Hsn|]. split; [rewrite Hlv; reflexivity|]. exact Hz.
Qed.

Lemma l0_hlen_eq wbits : l0_hlen wbits = hdr_len (wrap_of wbits).
Proof. unfold l0_hlen, hdr_len, wrap_of. destruct (wbits <? 0); [reflexivity|]. destruct (wbits >? 15); reflexivity. Qed.

Lemma l0_tlen_eq wbits : l0_tlen wbits = tlr_len (wrap_of wbits).
Proof. unfold l0_tlen, tlr_len, wrap_of. destruct (wbits <? 0); [reflexivity|]. destruct (wbits >? 15); reflexivity. Qed.

Lemma wrap_of_range wbits : 0 <= wrap_of wbits <= 2.
Proof. unfold wrap_of. destruct (wbits <? 0); [lia|]. destruct (wbits >? 15); lia. Qed.

Lemma hdr_len_range w : 0 <= hdr_len w <= 10.
Proof. unfold hdr_len. destruct (w =? 0); [lia|]. destruct (w =? 1); lia. Qed.

Lemma tlr_len_range w : 0 <= tlr_len w <= 8.
Proof. unfold tlr_len. destruct (w =? 0); [lia|]. destruct (w =? 1); lia. Qed.

Theorem level0_shape : level0_stmt.
Proof.
  intros vok sok snull wbits mem strategy a1 a2 a3 a4 a5 z0 os z1 inb room Hinit Hb Hn Hroom.
  destruct (l0_init _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hinit)
    as (s0 & -> & HW & Ho & Hst & Hwr & Hgz & Hlf & Hpo & Hpe & Hbv & Hss & Hbs & Hsn & Hlv & Hz1).
  subst z1. cbn [z_total_in z_total_out z_adler z_msg].
  set (n := Zlength inb) in *. set (wrap := wrap_of wbits) in *.
  set (adl := if wrap =? 2 then 0 else 1).
  pose proof (wrap_of_range wbits) as Hw. fold wrap in Hw.
  pose proof (hdr_len_range wrap) as Hh. pose proof (tlr_len_range wrap) as Ht.
  pose proof (Zlength_nonneg inb) as Hn0. fold n in Hn0.
  pose proof (l0_blocks_pos n Hn0) as HB.
  unfold l0_size in Hroom. rewrite l0_hlen_eq, l0_tlen_eq in Hroom. fold wrap in Hroom.
  (* the entry and the header stages *)
  destruct (l0_head s0 (zcall inb 0 n 0 room 0 adl None) (W_prm s0 HW) Ho Hpe Hpo Hbv Hsn Hss Hgz Hlf
              ltac:(rewrite Hwr; exact Hw) ltac:(rewrite Hwr; exact Hst)
              ltac:(cbn [zcall z_avail_out]; rewrite Hwr; lia) ltac:(cbn [zcall z_total_out]; lia))
    as (s2 & z2 & H & Eh & Hc2 & Ho2 & Hpe2 & Hpo2 & Hbv2 & Hst2 & Hwr2 & HH & Hzo2 & Hzi2 & Hzn2 & Hza2 &
        Hzt2 & Hzm2 & Hzao2 & Hzto2).
  rewrite Hwr in HH, Hzao2, Hzto2, Hwr2.
  cbn [zcall z_out z_in z_next_in z_avail_in z_total_in z_msg z_avail_out z_total_out] in *.
  destruct (core_eq_fields _ _ Hc2) as (_ & _ & _ & _ & Hbs2 & Hss2 & _ & _ & _ & Hlv2 & _).
  assert (HW2 : W s2) by exact (W_frame s0 s2 HW Hc2).
  assert (Ez2 : z2 = mkST inb 0 n 0 H (room - hdr_len wrap) (0 + hdr_len wrap) (z_adler z2) None).
  { destruct z2; cbn in *. subst. reflexivity. }
  (* deflate_stored *)
  destruct (l0_stored s2 inb H 0 (room - hdr_len wrap) (0 + hdr_len wrap) (z_adler z2) None HW2 Ho2 Hpe2 Hpo2
              Hbv2 ltac:(rewrite Hlv2; exact Hlv) ltac:(rewrite Hss2; exact Hss) ltac:(rewrite Hbs2; exact Hbs)
              Hb Hn ltac:(fold n; lia) ltac:(lia) ltac:(lia))
    as (s3 & z3 & Es & Hzo3 & Hzao3 & Hzto3 & Hzai3 & Hzm3 & Ho3 & Hpe3 & Hpo3 & Hbv3 & Hwr3 & Hlen3).
  fold n in Hzao3, Hzto3, Hzo3.
  (* the trailer, on the state with status FINISH *)
  assert (Hpb : 8 <= Zlength (o_buf (tr_out (d_tr s3)))).
  { rewrite Hlen3. destruct (W_prm s2 HW2) as (_ & _ & _ & Hhb & _ & _ & _ & HL & _ & Hob & _).
    rewrite Hob, HL. assert (2 ^ 7 <= 2 ^ (d_hash_bits s2 - 1)) by (apply Z.pow_le_mono_r; lia). lia. }
  destruct (l0_trail (set_d_status s3 FINISH_STATE) z3 Ho3 Hpe3 Hpo3 Hbv3 Hpb
              ltac:(cbn [d_wrap set_d_status]; rewrite Hwr3, Hwr2; exact Hw)
              ltac:(cbn [d_wrap set_d_status]; rewrite Hwr3, Hwr2, Hzao3; lia)
              ltac:(rewrite Hzto3; lia) ltac:(rewrite Hzto3, Hzao3; lia))
    as (s4 & z4 & T & Et & Hzo4 & HT & Hzto4).
  cbn [d_wrap set_d_status] in HT, Hzto4. rewrite Hwr3, Hwr2 in HT, Hzto4.
  exists s0, s4, z4, H, T.
  split; [reflexivity|]. split; [exact Hgz|].
  split.
  { rewrite c_deflate_stages.
    assert (Hbad : orb (orb (bad_state s0) (Z_FINISH >? Z_BLOCK)) (Z_FINISH <? 0) = false).
    { unfold bad_state, c_deflateStateCheck. rewrite Hst. destruct (wrap =? 2); reflexivity. }
    rewrite Hbad. cbv beta iota.
    rewrite Eh. cbn [then_stage bind].
    unfold c_deflate_compress at 1. rewrite Hst2.
    replace (andb (negb (Z_FINISH =? Z_NO_FLUSH)) (negb (BUSY_STATE =? FINISH_STATE))) with true
      by reflexivity.
    rewrite Bool.orb_true_r. cbv beta iota.
    unfold c_compress_func at 1. rewrite Hlv2, Hlv. change (0 =? 0) with true. cbv beta iota.
    rewrite Ez2. unfold n. rewrite Es. cbn [bind].
    exact Et. }
  split; [rewrite Hzo4, Hzo3; rewrite app_assoc; reflexivity|].
  split; [rewrite HH, l0_hlen_eq; reflexivity|].
  split; [rewrite HT, l0_tlen_eq; reflexivity|].
  rewrite Hzto4, Hzto3. unfold l0_size. rewrite l0_hlen_eq, l0_tlen_eq. fold wrap n. lia.
Qed.
