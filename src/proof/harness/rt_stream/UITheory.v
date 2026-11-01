(* Law rt_stream (data of any length): the inflate side's facts for main ([UIFacts.urts_itheory_stmt]) from the
   decode theory for calls of any size (Decode7: decode_init7_stmt, decode_call7_stmt) on the decode context of
   the finished deflate stream. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.harness.rt_stream.UIFacts.
Require Import Zlib.proof.roundtrip.RTK7.
Require Import Zlib.proof.rfc1951.Decode7.
Require Zlib.proof.harness.clip_streams.DFacts.
Require Zlib.proof.harness.clip_streams.IFacts.
Require Zlib.proof.harness.clip_streams.IDecode.
Require Zlib.proof.harness.clip_streams.DCtx.
Require Zlib.proof.harness.clip_streams.PfxTheory.
Require Zlib.proof.harness.inflate_buffers.IBTheory.
Require Import Zlib.proof.harness.rt_stream.UIIdle.
Import ListNotations.
Local Open Scope Z_scope.

Module CF := Zlib.proof.harness.clip_streams.DFacts.
Module CI := Zlib.proof.harness.clip_streams.IFacts.

(* the parameters deflateInit2 accepted: the finished stream is one of clip_streams' [dfinal_of] *)
Lemma urts_dfinal_of level mem strategy wbits D O :
  rparams_ok level 8 wbits mem strategy = true -> dfinal [] (rwrap_of wbits) (rwbe wbits) None D O ->
  CI.dfinal_of wbits D O.
Proof.
  intros H F. split; [|exact F].
  unfold rparams_ok, CF.wbits_acc in *.
  repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H end.
  repeat rewrite andb_true_iff. tauto.
Qed.

(* the windowBits main gives inflateInit2 (deflate's, 8 changed to 9) are accepted: the parameters deflateInit2
   accepted have windowBits in -15 .. 31, and the check runs over that range *)
Lemma urts_wbits_range w : -15 <= w <= 31 -> implb (CF.wbits_acc w) (wbits_ok (rts_iw w)) = true.
Proof.
  intros R.
  assert (T: forallb (fun n => implb (CF.wbits_acc (Z.of_nat n - 15)) (wbits_ok (rts_iw (Z.of_nat n - 15))))
               (seq 0 47) = true) by reflexivity.
  rewrite forallb_forall in T. specialize (T (Z.to_nat (w + 15))).
  rewrite Z2Nat.id in T by lia. replace (w + 15 - 15) with w in T by lia.
  apply T. apply in_seq. lia.
Qed.

Lemma urts_wbits w : CF.wbits_acc w = true -> wbits_ok (rts_iw w) = true.
Proof.
  intros A.
  assert (R: -15 <= w <= 31).
  { unfold CF.wbits_acc, rwb_of in A.
    repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H end.
    apply negb_true_iff, Z.ltb_ge in H.
    destruct (Z.ltb_spec w 0); [lia|]. destruct (Z.gtb_spec w 15); apply Z.leb_le in H1; lia. }
  pose proof (urts_wbits_range w R) as I. rewrite A in I. exact I.
Qed.

(* the invariant between inflate() calls: the decode theory's [dinv] on a context of the stream O of D, and
   inflate_pieces' pinv (no gz_header, a mode of the decoder proper, swfW), which the zero-length call's
   lemma (UIIdle.ui_idle_call) starts from *)
Definition urts_P : rts_iinv := fun D O pos out s tout =>
  (exists G, dctx_ok7 G /\ dc_src G = O /\ slen G = Zlength O /\ full G = D /\ dinv G pos out s tout) /\
  i_head s = false /\ HEAD <= i_mode s <= BAD /\ swfW s.

Theorem urts_itheory : decode_init7_stmt -> decode_call7_stmt -> urts_itheory_stmt.
Proof.
  intros DI DK. exists urts_P. constructor.
  - intros level mem strategy wbits D O sp RP0 DF LD LO.
    pose proof (urts_dfinal_of _ _ _ _ _ _ RP0 DF) as DF'.
    pose proof (urts_wbits wbits (proj1 DF')) as WB.
    assert (SW: swfW (l_s (init_live sp (rts_iw wbits)))).
    { unfold swfW. destruct (reset2_wb (rts_iw wbits)) as [[wr wb]|] eqn:E;
        unfold init_live; cbn [l_s]; rewrite E; split; intros M; discriminate M. }
    split; [exact SW|]. split.
    + destruct (Zlib.proof.harness.clip_streams.PfxTheory.pfx_dfinal _ _ _ DF') as [BY _].
      assert (LS: Zlength O <= Zlength O <= 2 ^ 64 - 1) by (unfold Zlib.proof.harness.rt_stream.UDFacts.max_size in LO; lia).
      destruct (Zlib.proof.harness.clip_streams.DCtx.clip_dctx wbits D O O DF' LS
                  ltac:(apply sublist_same; lia) BY)
        as (G & OK & SRC & SL & FU & HI & IW & ND & _).
      exists G. split; [exact OK|]. split; [exact SRC|]. split; [exact SL|]. split; [exact FU|].
      replace (rts_iw wbits) with (dc_iw G) by (rewrite IW; reflexivity).
      exact (DI G sp OK HI ND).
    + split; [unfold init_live; destruct (reset2_wb (rts_iw wbits)) as [[a b]|]; reflexivity|].
      split; [|exact SW].
      rewrite (Zlib.proof.harness.inflate_pieces.Theory.pc_init_mode sp _ WB). split; vm_compute; discriminate.
  - intros level mem strategy wbits RP0. apply urts_wbits.
    unfold rparams_ok, CF.wbits_acc in *.
    repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H end.
    repeat rewrite andb_true_iff. tauto.
  - intros D O pos out L z inp flush res ((G & OK & SRC & SL & FU & DV) & PH & PM & PS) LV ZF AO LI P0 PL IE RUN.
    subst O. cbv zeta.
    assert (PI: Zlib.proof.harness.inflate_pieces.Theory.pinv z L) by (split; [exact PH | split; assumption]).
    assert (BY: bytes_ok inp).
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
