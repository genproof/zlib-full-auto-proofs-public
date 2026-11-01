(* Law rt_stream_trailing: the inflate side's facts for main ([TIFacts.trl_itheory_stmt]) from the decode theory
   for calls of any size (Decode7: decode_init7_stmt, decode_call7_stmt) on the decode context of the finished
   deflate stream O followed by any bytes (clip_streams' DCtx.clip_dctx: the context's input is src, its stream
   length |O|).  rt_stream's UITheory.urts_itheory with that input; the zero-length call by UIIdle.ui_idle_call. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.harness.rt_stream_trailing.TIFacts.
Require Import Zlib.proof.roundtrip.RTK7.
Require Import Zlib.proof.rfc1951.Decode7.
Require Zlib.proof.harness.clip_streams.IFacts.
Require Zlib.proof.harness.clip_streams.IDecode.
Require Zlib.proof.harness.clip_streams.DCtx.
Require Zlib.proof.harness.inflate_buffers.IBTheory.
Require Zlib.proof.harness.inflate_pieces.Theory.
Require Zlib.proof.harness.rt_stream.UITheory.
Require Import Zlib.proof.harness.rt_stream.UIIdle.
Import ListNotations.
Local Open Scope Z_scope.

Module UT := Zlib.proof.harness.rt_stream.UITheory.

(* the invariant between inflate() calls: the decode theory's [dinv] on a context of the input src (the stream O
   of D, then any bytes), and inflate_pieces' pinv (no gz_header, a mode of the decoder proper, swfW), which the
   zero-length call's lemma starts from *)
Definition trl_P : trl_iinv := fun D O src pos out s tout =>
  (exists G, dctx_ok7 G /\ dc_src G = src /\ slen G = Zlength O /\ full G = D /\ dinv G pos out s tout) /\
  i_head s = false /\ HEAD <= i_mode s <= BAD /\ swfW s.

Theorem trl_itheory : decode_init7_stmt -> decode_call7_stmt -> trl_itheory_stmt.
Proof.
  intros DI DK. exists trl_P. constructor.
  - intros level mem strategy wbits D O src sp RP0 DF LD LS SB BY.
    pose proof (UT.urts_dfinal_of _ _ _ _ _ _ RP0 DF) as DF'.
    pose proof (UT.urts_wbits wbits (proj1 DF')) as WB.
    assert (SW: swfW (l_s (init_live sp (rts_iw wbits)))).
    { unfold swfW. destruct (reset2_wb (rts_iw wbits)) as [[wr wb]|] eqn:E;
        unfold init_live; cbn [l_s]; rewrite E; split; intros M; discriminate M. }
    split; [exact SW|]. split.
    + assert (LS': Zlength O <= Zlength src <= 2 ^ 64 - 1)
        by (unfold Zlib.proof.harness.rt_stream.UDFacts.max_size in LS; lia).
      destruct (Zlib.proof.harness.clip_streams.DCtx.clip_dctx wbits D O src DF' LS' SB BY)
        as (G & OK & SRC & SL & FU & HI & IW & ND & _).
      exists G. split; [exact OK|]. split; [exact SRC|]. split; [exact SL|]. split; [exact FU|].
      replace (rts_iw wbits) with (dc_iw G) by (rewrite IW; reflexivity).
      exact (DI G sp OK HI ND).
    + split; [unfold init_live; destruct (reset2_wb (rts_iw wbits)) as [[a b]|]; reflexivity|].
      split; [|exact SW].
      rewrite (Zlib.proof.harness.inflate_pieces.Theory.pc_init_mode sp _ WB). split; vm_compute; discriminate.
  - intros level mem strategy wbits RP0. apply UT.urts_wbits.
    unfold rparams_ok, Zlib.proof.harness.clip_streams.DFacts.wbits_acc in *.
    repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H end.
    repeat rewrite andb_true_iff. tauto.
  - intros D O src pos out L z inp flush res ((G & OK & SRC & SL & FU & DV) & PH & PM & PS) LV ZF AO LI P0 PL IE RUN.
    subst src. cbv zeta.
    assert (PI: Zlib.proof.harness.inflate_pieces.Theory.pinv z L) by (split; [exact PH | split; assumption]).
    assert (BY: Zlib.proof.zutil.Libc.bytes_ok inp).
    { destruct OK as (_ & _ & _ & _ & _ & _ & BO & _). rewrite IE.
      apply Zlib.proof.harness.inflate_buffers.IBTheory.ib_bytes_sublist; exact BO. }
    pose proof (ui_call_ppost flush z L inp res PI LV ZF ltac:(lia) BY RUN) as (_ & _ & _ & _ & Q5 & _ & Q7).
    destruct (DK G pos out L z inp flush res OK DV LV ZF ltac:(lia) ltac:(lia) P0 PL IE RUN)
      as [M | (R & SNX & SOW & AOUT & EX & DV' & _ & END & _)]; [left; exact M|].
    assert (NM: r_ret res <> Z_MEM_ERROR) by (destruct R as [R|[R|R]]; rewrite R; discriminate).
    destruct (Q7 NM) as (_ & _ & Q9 & _ & Q11).
    right. rewrite <- FU. split; [exact R|]. split; [exact SNX|]. split; [exact SOW|]. split; [exact AOUT|].
    split; [exact EX|].
    split; [split; [exists G; auto | split; [rewrite Q5; exact PH | split; [exact Q9 | exact Q11]]]|].
    split.
    + intros E. destruct (END E) as [E1 E2]. split; [exact E1|]. rewrite E2; exact SL.
    + intros I0 A0. destruct (ui_idle_call flush z L inp res PI LV ZF I0 A0 RUN) as (I1 & I2 & I3).
      split; [exact I1|]. split; [exact I2|]. exact (I3 NM).
Qed.
