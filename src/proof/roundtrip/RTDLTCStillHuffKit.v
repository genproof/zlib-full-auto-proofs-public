(** * Kit for cf_still, part huff: FLUSH_BLOCK and the tail keep strstart; deflate_huff run from a
    loop-invariant state (no [zin_ok] needed: the total_in bound is not kept by a fill). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDLTCStill.
Require Zlib.proof.roundtrip.RTDLTCHuffLoop Zlib.proof.roundtrip.RTDLTCHuffFbw Zlib.proof.roundtrip.RTDLTCHuffLit Zlib.proof.roundtrip.RTDLTCHuffRefill Zlib.proof.roundtrip.RTDLTCHuffBflush Zlib.proof.roundtrip.RTDLTCHuffTail.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Lemma sh_fp_strstart s z s' z' : c_flush_pending s z = Some (s', z') -> d_strstart s' = d_strstart s.
Proof.
  unfold c_flush_pending. intros H.
  destruct (c_tr_flush_bits (d_out s)) as [o|]; [|discriminate]. cbn [bind] in H.
  set (len := if d_pending (set_d_out s o) >? z_avail_out z then z_avail_out z
              else u32 (d_pending (set_d_out s o))) in H.
  destruct (len =? 0); [injection H as <- _; reflexivity|].
  destruct (mb_read _ _ len) as [l|]; [|discriminate]. cbn [bind] in H.
  destruct (out_put z l) as [z1|]; [|discriminate]. cbn [bind] in H.
  destruct (d_pending _ =? 0); injection H as <- _; reflexivity.
Qed.

Lemma sh_fbo_strstart s z last s' z' :
  c_flush_block_only s z last = Some (s', z') -> d_strstart s' = d_strstart s.
Proof.
  unfold c_flush_block_only. intros H.
  destruct (in_long _); [|discriminate]. cbn [guard bind] in H.
  destruct (if d_block_start s >=? 0 then _ else _) as [buf|]; [|discriminate]. cbn [bind] in H.
  destruct (c_tr_flush_block _ _ _ _) as [[t k]|]; [|discriminate]. cbn [bind] in H.
  rewrite (sh_fp_strstart _ _ _ _ H). reflexivity.
Qed.

Lemma sh_fb_strstart s z last s' z' r :
  c_flush_block s z last = Some (s', z', r) -> d_strstart s' = d_strstart s.
Proof.
  unfold c_flush_block. intros H.
  destruct (c_flush_block_only s z last) as [[s1 z1]|] eqn:E; [|discriminate]. cbn [bind] in H.
  rewrite <- (sh_fbo_strstart _ _ _ _ _ E).
  destruct (_ && _); injection H as <- _ _; reflexivity.
Qed.

Lemma sh_tail_strstart s z flush s' z' bs :
  c_deflate_tail s z flush = Some (s', z', bs) -> d_strstart s' = d_strstart s.
Proof.
  unfold c_deflate_tail. intros H.
  destruct (flush =? Z_FINISH).
  - destruct (c_flush_block s z 1) as [[[s1 z1] r]|] eqn:E; [|discriminate]. cbn [bind] in H.
    rewrite <- (sh_fb_strstart _ _ _ _ _ _ E). destruct r; injection H as <- _ _; reflexivity.
  - destruct (negb _); [|injection H as <- _ _; reflexivity].
    destruct (c_flush_block s z 0) as [[[s1 z1] r]|] eqn:E; [|discriminate]. cbn [bind] in H.
    rewrite <- (sh_fb_strstart _ _ _ _ _ _ E). destruct r; injection H as <- _ _; reflexivity.
Qed.

(** A loop whose first iteration exits. *)
Lemma sh_loop2_exit {A B : Type} (body : A -> option (A + B)) d a e :
  body a = Some (inr e) -> loop2 d body a = Some (inr e).
Proof.
  revert a. induction d as [|d IH]; intros a H; cbn [loop2]; [exact H|].
  rewrite (IH a H). reflexivity.
Qed.

Lemma sh_loop_exit {A B : Type} (body : A -> option (A + B)) d a e :
  body a = Some (inr e) -> loop d body a = Some e.
Proof. intros H. unfold loop. rewrite (sh_loop2_exit body d a e H). reflexivity. Qed.

(** The kernel must never compute [loop FUEL] (2^40 iterations): Qed hangs otherwise. *)
Local Strategy opaque [loop loop2].

(** deflate_huff from a state of the loop invariant [HFI s z flush s z []]. *)
Lemma sh_huff_run : fill_spec -> tally_spec2 -> fbo_spec ->
  forall s z flush, HFI s z flush s z [] -> 0 <= flush <= 5 -> fn_of s = 3 ->
    z_avail_in z + d_lookahead s < 2 ^ 40 ->
    exists s' z' bs evs, c_deflate_huff s z flush = Some (s', z', bs) /\ hcrel s z flush s' z' evs.
Proof.
  intros Hfill Htally Hfbo s z flush HI Hfl Hfn Hm.
  assert (Hfbw := RTDLTCHuffFbw.hfbw_ok Hfbo).
  assert (Hlit := RTDLTCHuffLit.hlit_ok Htally). assert (Href := RTDLTCHuffRefill.hrefill_ok Hfill).
  assert (Hbfl := RTDLTCHuffBflush.hbflush_ok Hfbw). assert (Htail := RTDLTCHuffTail.htail_ok Hfbw).
  assert (Hm0 : RTDLTCHuffLoop.hm (s, z) < 2 ^ Z.of_nat FUEL).
  { unfold RTDLTCHuffLoop.hm; cbn [fst snd]. change (2 ^ Z.of_nat FUEL) with (2 ^ 40). lia. }
  destruct (RTDLTCHuffLoop.hloop_measure (huff_body flush) (RTDLTCHuffLoop.HP s z flush) (RTDLTCHuffLoop.HQ s z flush)
              RTDLTCHuffLoop.hm (RTDLTCHuffLoop.huff_step Hlit Href Hbfl s z flush Hfl Hfn) FUEL (s, z)
              (ex_intro _ [] HI) Hm0)
    as (r & Er & Hr).
  unfold c_deflate_huff. rewrite Er. cbn [bind].
  destruct r as [[s' z'] [bs|]].
  - destruct Hr as (evs & Hc & Hb). exists s', z', bs, evs. split; [reflexivity|exact Hc].
  - destruct Hr as (evs & HI' & Hla & Hai & Hnf).
    destruct (Htail s z flush s' z' evs HI' Hfl Hfn Hnf Hla Hai) as (s2 & z2 & bs & evs' & E & Hc & Hb).
    exists s2, z2, bs, evs'. split; [exact E|exact Hc].
Qed.

Lemma sh_body_exit flush s z s1 z1 :
  d_lookahead s = 0 -> c_fill_window s z = Some (s1, z1) -> d_lookahead s1 = 0 ->
  huff_body flush (s, z) = Some (inr (s1, z1, if flush =? Z_NO_FLUSH then Some need_more else None)).
Proof.
  intros Hla Ef L0. rewrite huff_body_eq. unfold hrefill. rewrite Hla, Ef. cbn [Z.eqb bind]. rewrite L0.
  cbn [Z.eqb]. destruct (flush =? Z_NO_FLUSH); reflexivity.
Qed.

Lemma sh_body_same flush s z s1 z1 :
  d_lookahead s = 0 -> c_fill_window s z = Some (s1, z1) -> d_lookahead s1 <> 0 ->
  huff_body flush (s, z) = huff_body flush (s1, z1).
Proof.
  intros Hla Ef L0. rewrite !huff_body_eq. unfold hrefill. rewrite Hla, Ef. cbn [Z.eqb bind].
  destruct (Z.eqb_spec (d_lookahead s1) 0); [contradiction|]. reflexivity.
Qed.

Lemma sh_huff_same flush s z s1 z1 :
  huff_body flush (s, z) = huff_body flush (s1, z1) -> c_deflate_huff s z flush = c_deflate_huff s1 z1 flush.
Proof.
  intros Eb. unfold c_deflate_huff. rewrite (loop_body_eq _ FUEL _ _ Eb). reflexivity.
Qed.

Lemma sh_huff_exit flush s z s1 z1 o s' z' bs :
  huff_body flush (s, z) = Some (inr (s1, z1, o)) -> c_deflate_huff s z flush = Some (s', z', bs) ->
  d_strstart s' = d_strstart s1.
Proof.
  intros Eb E. unfold c_deflate_huff in E. rewrite (sh_loop_exit _ FUEL _ _ Eb) in E. cbn [bind] in E.
  destruct o as [r|].
  - injection E as <- _ _. reflexivity.
  - apply sh_tail_strstart in E. rewrite E. reflexivity.
Qed.
