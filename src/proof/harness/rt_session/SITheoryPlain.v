(* Law rt_session: the inflate side's facts for the sessions without a dictionary and without a header: those of
   rt_stream_trailing (the stream followed by any bytes, in any pieces; rt_stream_trailing/TITheory.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require compcert.lib.Integers.
Require Import Zlib.proof.harness.rt_session.SIFacts.
Require Zlib.proof.harness.rt_stream_trailing.TIFacts.
Require Zlib.proof.harness.rt_stream_trailing.TITheory.
Require Zlib.proof.wide.Decode7.
Require Zlib.proof.harness.inflate_pieces.Theory.
Require Zlib.proof.harness.rt_stream.UIIdle.
Import ListNotations.
Local Open Scope Z_scope.

Module TF := Zlib.proof.harness.rt_stream_trailing.TIFacts.

(* the session's byte lists (rbytes) are byte lists in the sense of the inflate side's facts *)
Lemma ses_plain_bytes l : Zlib.proof.roundtrip.RTDIface.rbytes l -> Zlib.proof.zutil.Libc.bytes_ok l.
Proof.
  intros H. unfold Zlib.proof.zutil.Libc.bytes_ok. eapply Forall_impl; [|exact H].
  intros b Hb. cbv beta in Hb. change compcert.lib.Integers.Byte.max_unsigned with 255. lia.
Qed.

Theorem ses_itheory_plain : ses_itheory_plain_stmt.
Proof.
  destruct Zlib.proof.wide.Decode7.decode7 as [DI DK].
  destruct (Zlib.proof.harness.rt_stream_trailing.TITheory.trl_itheory DI DK) as [Pt FT].
  (* rt_stream_trailing's invariant on the state, with the harness's flag still unset and inflate_pieces' pinv
     (no gz_header, a mode of the decoder proper), which carries the header's absence through the calls *)
  exists (fun c D O src pos out asked L tout =>
    asked = false /\ i_head (l_s L) = false /\ HEAD <= i_mode (l_s L) <= BAD /\ Pt D O src pos out (l_s L) tout).
  exists (fun _ _ _ _ _ _ _ _ => False).
  constructor.
  - intros c D O src sp [KD KG] (RP & DF & _ & _ & _ & LD) (LS & SB & BY).
    destruct RP as (level & mem & strategy & RP).
    rewrite KD, KG in DF. unfold sc_wrap in DF.
    pose proof (TF.ti_wbits _ FT _ _ _ _ RP) as WB.
    destruct (TF.ti_init _ FT level mem strategy (sc_wbits c) D O src sp RP DF LD LS SB (ses_plain_bytes _ BY)) as [SW PI].
    split; [exact WB|]. split; [exact SW|]. intros _ _.
    split; [reflexivity|]. split.
    + unfold init_live; destruct (reset2_wb (rts_iw (sc_wbits c))) as [[a b]|]; reflexivity.
    + split; [|exact PI].
      rewrite (Zlib.proof.harness.inflate_pieces.Theory.pc_init_mode sp _ WB). split; vm_compute; discriminate.
  - intros c D O src sp gh headp hsh xb nb cb [_ KG] _ _ G. rewrite KG in G. discriminate G.
  - intros c D O src sp z alloc_ok winp [KD _] _ _ [RD _]. contradiction.
  - intros c D O src pos out asked L tout [_ KG] (_ & H & _). rewrite KG. exact H.
  - intros c D O src pos out asked L z inp flush res winp [KD KG] SC SO (AF & PH & PM & PT) LV SW ZF AO LI P0 PL IE RUN.
    cbv zeta.
    unfold live_c in LV. rewrite KG in LV.
    assert (PI: Zlib.proof.harness.inflate_pieces.Theory.pinv z L) by (split; [exact PH | split; assumption]).
    destruct SO as (_ & _ & BS).
    assert (BY: Zlib.proof.zutil.Libc.bytes_ok inp).
    { rewrite IE. apply Zlib.proof.harness.inflate_buffers.IBTheory.ib_bytes_sublist; exact (ses_plain_bytes _ BS). }
    pose proof (Zlib.proof.harness.rt_stream.UIIdle.ui_call_ppost flush z L inp res PI LV ZF ltac:(lia) BY RUN)
      as (_ & _ & _ & _ & Q5 & _ & Q7).
    destruct (TF.ti_call _ FT D O src pos out L z inp flush res PT LV ZF AO LI P0 PL IE RUN)
      as [M | (R & SNX & SOW & AOUT & EX & PT' & END & IDLE)]; [left; exact M|].
    assert (NM: r_ret res <> Z_MEM_ERROR) by (destruct R as [R|[R|R]]; rewrite R; discriminate).
    destruct (Q7 NM) as (_ & _ & Q9 & _ & _).
    right. split; [tauto|]. split; [exact SNX|]. split; [exact SOW|]. split; [exact AOUT|].
    split; [exact EX|].
    split; [intros _; cbn [l_s]; split; [exact AF|]; split; [rewrite Q5; exact PH|]; split; [exact Q9|exact PT']|].
    split; [intros E; destruct R as [R|[R|R]]; rewrite R in E; discriminate E|].
    split; [|exact IDLE].
    intros E. destruct (END E) as [E1 E2]. split; [exact E1|]. split; [exact E2|]. split.
    + subst asked. unfold sk_zdict. rewrite KD. split; [discriminate | intros [N _]; contradiction].
    + intros gh G. rewrite KG in G. discriminate G.
  - intros c D O src pos out L tout _ [].
  - intros c D O src pos out L tout z alloc_ok winp _ _ _ [].
Qed.
