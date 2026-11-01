(* Law api_reset, the theory of TABLE / LENLENS / CODELENS (ARSimTab.v): the statements of its parts.
   They are x_inflate_reset's (IRTabKit.v) with the one-stream invariant of the table cases for wide calls,
   StepWTables.v's mwf3xW (InvW.mwfW: inputs and output spaces of up to 2^32-1 bytes), in place of
   Step3Tables.v's mwf3x.  The passes (irt_tab, irt_ll, irt_cl, irt_clpost), their relation irt_rr and the
   ways to build Kr are IRTabKit.v's: they do not mention the invariant. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.harness.inflate_reset.IRDefs.
Require Export Zlib.proof.harness.inflate_reset.IRTabKit.
Require Export Zlib.proof.inflate.StepWKit.
Import ListNotations.
Local Open Scope Z_scope.

(* CODELENS's while loop, in lockstep (ARSimTabCL.v) *)
Definition irt_clloop_stmtW : Prop :=
  forall k W0 wrap src pos inp aout ma mb,
    Kr W0 wrap src pos inp aout ma mb -> mwf3xW ma -> mwf3xW mb -> m_leave mb = 0 -> m_mode mb = CODELENS ->
    match codelens_loop lenfix_list distfix_list k ma, codelens_loop lenfix_list distfix_list k mb with
    | CLnext ma', CLnext mb' => Kr W0 wrap src pos inp aout ma' mb'
    | CLleave ma', CLleave mb' => Kr W0 wrap src pos inp aout ma' mb'
    | CLbad ma', CLbad mb' => Kr W0 wrap src pos inp aout ma' mb'
    | _, _ => False
    end.

(* CODELENS after the loop: the LENS and DISTS tables (ARSimTabCL.v) *)
Definition irt_clpost_stmtW : Prop :=
  forall W0 wrap src pos inp aout ma mb,
    Kr W0 wrap src pos inp aout ma mb -> mwf3xW ma -> mwf3xW mb -> m_leave mb = 0 -> m_mode mb = CODELENS ->
    i_nlen (m_s mb) + i_ndist (m_s mb) <= i_have (m_s mb) ->
    irt_rr W0 wrap src pos inp aout (irt_clpost ma) (irt_clpost mb).

(* CODELENS: loop and tables (ARSimTabCL.v, from the two above) *)
Definition irt_cl_stmtW : Prop :=
  forall W0 wrap src pos inp aout ma mb,
    Kr W0 wrap src pos inp aout ma mb -> mwf3xW ma -> mwf3xW mb -> m_leave mb = 0 -> m_mode mb = CODELENS ->
    irt_rr W0 wrap src pos inp aout (irt_cl ma) (irt_cl mb).

(* LENLENS: loop, zeros, the code length code, then CODELENS (ARSimTabLL.v) *)
Definition irt_ll_stmtW : Prop :=
  forall W0 wrap src pos inp aout ma mb,
    Kr W0 wrap src pos inp aout ma mb -> mwf3xW ma -> mwf3xW mb -> m_leave mb = 0 -> m_mode mb = LENLENS ->
    irt_rr W0 wrap src pos inp aout (irt_ll ma) (irt_ll mb).

(* TABLE, then LENLENS (ARSimTabTab.v) *)
Definition irt_tab_stmtW : Prop :=
  forall W0 wrap src pos inp aout ma mb,
    Kr W0 wrap src pos inp aout ma mb -> mwf3xW ma -> mwf3xW mb -> m_leave mb = 0 -> m_mode mb = TABLE ->
    irt_rr W0 wrap src pos inp aout (irt_tab ma) (irt_tab mb).

