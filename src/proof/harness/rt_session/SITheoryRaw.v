(* Law rt_session: the inflate side's facts for the sessions with a dictionary and the raw wrapper:
   inflateSetDictionary right after inflateInit2 puts the dictionary in the window; then the decode theory for
   calls of any size (Decode7) on the context whose history is the dictionary. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.harness.rt_session.SIFacts.
Require Import Zlib.proof.roundtrip.RTK7.
Require Import Zlib.proof.rfc1951.Decode7.
Require Zlib.proof.wide.Decode7.
Require Zlib.proof.harness.clip_streams.DFacts.
Require Zlib.proof.harness.clip_streams.DCtx.
Require Zlib.proof.roundtrip.RTIPlain.
Require Zlib.proof.roundtrip.RTIRawDictKit.
Require Zlib.proof.harness.inflate_buffers.IBTheory.
Require Zlib.proof.harness.inflate_pieces.Theory.
Require Import Zlib.proof.harness.rt_stream.UIIdle.
Import ListNotations.
Local Open Scope Z_scope.

Module CF := Zlib.proof.harness.clip_streams.DFacts.
Module RK := Zlib.proof.roundtrip.RTIRawDictKit.
Module PT := Zlib.proof.harness.inflate_pieces.Theory.

(* the windowBits of a raw session: deflateInit2 accepted them, so they are -15 .. -9; deflate's window bits are
   their opposite, and so are inflateInit2's (main changes only 8 to 9) *)
Lemma sraw_wbits c D O : sk_raw c -> sc_ok c D O ->
  CF.wbits_acc (sc_wbits c) = true /\ -15 <= sc_wbits c <= -9 /\ rwbe (sc_wbits c) = - sc_wbits c /\
  rts_iw (sc_wbits c) = sc_wbits c /\ sc_gh c = None.
Proof.
  intros [_ KW] ((level & mem & strategy & RP) & _ & _ & GH & _).
  assert (A: CF.wbits_acc (sc_wbits c) = true).
  { unfold rparams_ok, CF.wbits_acc in *.
    repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H end.
    repeat rewrite andb_true_iff. tauto. }
  split; [exact A|].
  unfold sc_wrap in KW.
  destruct (Zlib.proof.harness.clip_streams.DCtx.dctx_wbits _ A)
    as [(R & _ & E & _) | [(_ & W & _) | (_ & W & _)]]; [|congruence|congruence].
  split; [exact R|]. split; [exact E|].
  split; [unfold rts_iw; destruct (Z.eqb_spec (sc_wbits c) 8); [lia|reflexivity]|].
  destruct (sc_gh c) eqn:G; [|reflexivity].
  exfalso. specialize (GH ltac:(discriminate)). unfold sc_wrap in GH. congruence.
Qed.

(* the decode context of a raw session: the raw wrapper, the dictionary as history, the blocks of the stream,
   inflateInit2's windowBits, the input object src = O followed by anything *)
Lemma sraw_ctx wb dict bs D O src :
  9 <= wb <= 15 -> wf (2 ^ wb) dict bs -> data dict bs = D -> O = deflate_bytes bs -> src_ok O src ->
  let G := DCtx WRaw wb dict bs (- wb) src in
  dctx_ok7 G /\ slen G = Zlength O /\ full G = dict ++ D.
Proof.
  intros Hwb Hwf Hd HO (L1 & L2 & L3) G.
  assert (SL: slen G = Zlength O) by (unfold slen; cbn; rewrite <- HO; reflexivity).
  split; [|split; [exact SL|]].
  - unfold dctx_ok7. rewrite SL. cbn [dc_w dc_wb dc_hist dc_bs dc_src dc_iw G stream_bytes].
    rewrite <- HO.
    split; [unfold stream_ok; cbn; split; [lia|]; split; [exact I|]; split; [exact I|exact Hwf]|].
    split; [reflexivity|].
    split; [intros ? E; discriminate E|].
    split; [intros ? ? ? E; discriminate E|].
    split; [lia|]. split; [unfold Zlib.proof.harness.rt_stream.UDFacts.max_size in *; lia|]. split; [|exact L2].
    unfold bytes_ok. eapply Forall_impl; [|exact L3]. intros b B. cbn in B |- *. lia.
  - unfold full. cbn [dc_hist dc_bs G]. rewrite Zlib.proof.roundtrip.RTIPlain.rtip_expand_data, Hd. reflexivity.
Qed.

(* the invariant between inflate() calls: no Z_NEED_DICT asked, no gzip header, the decode theory's [dinv] on
   the context of the stream (whose output starts with the history, the dictionary), and inflate_pieces' pinv
   (no gz_header, a mode of the decoder proper, swfW), which the zero-length call's lemma
   (UIIdle.ui_idle_call) starts from *)
Definition sraw_P : ses_iinv := fun c D O src pos out asked L tout =>
  asked = false /\ sc_gh c = None /\
  (exists G, dctx_ok7 G /\ dc_src G = src /\ slen G = Zlength O /\ full G = sc_dict c ++ D /\
     dinv G pos (sc_dict c ++ out) (l_s L) tout) /\
  i_head (l_s L) = false /\ HEAD <= i_mode (l_s L) <= BAD /\ swfW (l_s L).

(* a raw stream never asks for a dictionary *)
Definition sraw_PN : ses_ninv := fun _ _ _ _ _ _ _ _ => False.

Lemma sraw_init_swf sp w : swfW (l_s (init_live sp w)).
Proof.
  unfold swfW. destruct (reset2_wb w) as [[wr wb]|] eqn:E;
    unfold init_live; cbn [l_s]; rewrite E; split; intros M; discriminate M.
Qed.

(* inflateInit2 accepts the raw windowBits -15 .. -9 *)
Lemma sraw_wbits_ok w : -15 <= w <= -9 -> wbits_ok w = true.
Proof.
  intros R.
  assert (C: w = -15 \/ w = -14 \/ w = -13 \/ w = -12 \/ w = -11 \/ w = -10 \/ w = -9) by lia.
  destruct C as [->|[->|[->|[->|[->|[->| ->]]]]]]; reflexivity.
Qed.

Theorem ses_itheory_raw : ses_itheory_raw_stmt.
Proof.
  destruct Zlib.proof.wide.Decode7.decode7 as [_ DK].
  exists sraw_P, sraw_PN. constructor.
  - (* inflateInit2 *)
    intros c D O src sp K SC SR.
    destruct (sraw_wbits c D O K SC) as (_ & R & _ & I & _). rewrite I.
    split; [apply sraw_wbits_ok; exact R|].
    split; [apply sraw_init_swf|].
    intros _ NR. contradiction.
  - (* no header in a raw session *)
    intros c D O src sp gh headp hsh xb nb cb K SC SR G.
    destruct (sraw_wbits c D O K SC) as (_ & _ & _ & _ & GN). congruence.
  - (* inflateSetDictionary right after inflateInit2 *)
    intros c D O src sp z alloc_ok winp K SC SR KR Z0 L LV sd.
    destruct (sraw_wbits c D O K SC) as (_ & R & E & I & GN).
    pose proof KR as (DN & KW). unfold sc_wrap in KW.
    destruct SC as (_ & (Hwb & bs & Hwf & Hd & HO) & _). unfold sc_wrap in HO. rewrite KW in HO.
    cbv beta iota in HO. rewrite E in Hwb, Hwf.
    set (wb := - sc_wbits c) in *.
    assert (IW: rts_iw (sc_wbits c) = - wb) by (unfold wb; rewrite I; lia).
    destruct (RK.rrd_setdict_check wb sp (sc_dict c) ltac:(lia)) as (Ls & Ck & Wi).
    unfold sd, L, setdict_f. rewrite IW, Ls, Ck, Wi.
    destruct alloc_ok; [|split; [right; reflexivity | intros X; discriminate X]].
    split; [left; reflexivity|]. intros _. unfold fst3, snd3, thd3; cbn [fst snd].
    split; [reflexivity|].
    destruct (PT.pc_setdict_s (init_s 0 wb) (sc_dict c)) as (S1 & S2 & S3).
    destruct (RK.rrd_init_fields 0 wb ltac:(lia) ltac:(lia)) as (F1 & _ & _ & F4 & _).
    assert (SW0: swfW (init_s 0 wb)) by (rewrite <- Ls; apply sraw_init_swf).
    split; [apply PT.pc_setdict_swf; exact SW0|].
    unfold sraw_P, set_l_winp, set_l_s; cbn [l_s].
    split; [reflexivity|]. split; [exact GN|].
    split.
    + destruct (sraw_ctx wb (sc_dict c) bs D O src ltac:(lia) Hwf Hd HO SR) as (OK & SL & FU).
      exists (DCtx WRaw wb (sc_dict c) bs (- wb) src).
      split; [exact OK|]. split; [reflexivity|]. split; [exact SL|]. split; [exact FU|].
      rewrite app_nil_r. apply RK.rrd_dinv. lia.
    + rewrite S1, S2, F1, F4. split; [reflexivity|].
      split; [split; vm_compute; discriminate | apply PT.pc_setdict_swf; exact SW0].
  - (* the header is never attached *)
    intros c D O src pos out asked L tout K (_ & GN & _ & PH & _). rewrite GN. exact PH.
  - (* one inflate() call: the decode theory's call on the context of the session *)
    intros c D O src pos out asked L z inp flush res winp K SC SR
      (Ha & GN & (G & OK & SRC & SL & FU & DV) & PH & PM & PS) LC LS ZF AO LI P0 PL IE RUN.
    unfold live_c in LC. rewrite GN in LC. cbv zeta. subst src.
    assert (PI: PT.pinv z L) by (split; [exact PH | split; assumption]).
    assert (BY: bytes_ok inp).
    { destruct OK as (_ & _ & _ & _ & _ & _ & BO & _). rewrite IE.
      apply Zlib.proof.harness.inflate_buffers.IBTheory.ib_bytes_sublist; exact BO. }
    pose proof (ui_call_ppost flush z L inp res PI LC ZF ltac:(lia) BY RUN) as (_ & _ & _ & _ & Q5 & _ & Q7).
    destruct (DK G pos (sc_dict c ++ out) L z inp flush res OK DV LC ZF ltac:(lia) ltac:(lia) P0 PL IE RUN)
      as [M | (R & SNX & SOW & AOUT & (rest & EX) & DV' & _ & END & _)]; [left; exact M|].
    assert (NM: r_ret res <> Z_MEM_ERROR) by (destruct R as [R|[R|R]]; rewrite R; discriminate).
    destruct (Q7 NM) as (_ & _ & Q9 & _ & Q11).
    rewrite FU, <- app_assoc in EX. apply app_inv_head in EX.
    right. split; [tauto|].
    split; [exact SNX|]. split; [exact SOW|]. split; [exact AOUT|]. split; [exists rest; exact EX|].
    split.
    + intros _. split; [exact Ha|]. split; [exact GN|]. cbn [l_s]. split.
      * exists G. split; [exact OK|]. split; [reflexivity|]. split; [exact SL|]. split; [exact FU|].
        rewrite app_assoc. exact DV'.
      * rewrite Q5. split; [exact PH | split; [exact Q9 | exact Q11]].
    + split.
      * intros E. rewrite E in R. destruct R as [R|[R|R]]; discriminate R.
      * split.
        -- intros E. destruct (END E) as [E1 E2]. rewrite FU, <- app_assoc in E1. apply app_inv_head in E1.
           split; [exact E1|]. split; [rewrite E2; exact SL|].
           split; [split; intros X; [congruence | destruct X as [_ X]; destruct K as [_ KW]; congruence]|].
           intros gh X. congruence.
        -- intros I0 A0. destruct (ui_idle_call flush z L inp res PI LC ZF I0 A0 RUN) as (I1 & I2 & I3).
           split; [exact I1|]. split; [exact I2|]. exact (I3 NM).
  - intros c D O src pos out L tout K F. destruct F.
  - intros c D O src pos out L tout z alloc_ok winp K SC SR F. destruct F.
Qed.
