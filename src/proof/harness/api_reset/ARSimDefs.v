(* Law api_reset, the theory: the simulation of x_inflate_reset (src/proof/harness/inflate_reset/IRDefs.v: srel,
   mrel, Kr, sim_post; IRRunCall.v: the boundary invariant IRinv) for calls offered up to 2^32-1 bytes of input
   and of output space.  x_inflate_reset's harness offers at most 2^24 and 2^20 bytes, and its parts are
   proved under Inv3.mwf3 (sizes up to 2^31-1); here every part is stated under the wide machine invariant
   InvW.mwf3W (StepW.stepf2_mwf3W: one pass of the switch keeps it).  The relation itself is x_inflate_reset's:
   srel lets every field that inflate() writes before reading it differ, which is what a stream reset after any
   use and a fresh one differ in (with fix F8 also wbits and the window are those of a fresh stream, the
   window aside: a reset stream may keep its allocation, emptied). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.harness.inflate_reset.IRDefs.
Require Export Zlib.proof.harness.inflate_reset.IRRunCall.
Require Export Zlib.proof.inflate.InvW.
Import ListNotations.
Local Open Scope Z_scope.

(* IRDefs.sgroup_ok under the wide machine invariant *)
Definition sgroup_okW (P: Z -> Prop) : Prop :=
  forall W0 wrap src pos inp aout flush ma mb,
    ir_ctx src pos inp -> Kr W0 wrap src pos inp aout ma mb -> mwf3W ma -> mwf3W mb -> m_leave mb = 0 ->
    P (m_mode mb) ->
    sim_post W0 wrap src pos inp aout (stepf2 flush lenfix_list distfix_list ma)
      (stepf2 flush lenfix_list distfix_list mb).

(* IRDefs.fast_sim_stmt under the wide machine invariant *)
Definition fast_sim_stmtW : Prop :=
  forall W0 wrap src pos inp aout ma mb,
    ir_ctx src pos inp -> Kr W0 wrap src pos inp aout ma mb -> mwf3W ma -> mwf3W mb -> m_leave mb = 0 ->
    m_mode mb = LEN -> m_out mb = m_aout mb -> 6 <= m_have mb -> 258 <= m_left mb -> m_bits mb < 8 ->
    Kr W0 wrap src pos inp aout (fast lenfix_list distfix_list (restore ma))
      (fast lenfix_list distfix_list (restore mb)).

(* the parts, per group of modes (IRDefs.v's groups) *)
Definition head_sim_stmtW : Prop := sgroup_okW md_head.
Definition hdr_sim_stmtW : Prop := sgroup_okW md_hdr.
Definition dict_sim_stmtW : Prop := sgroup_okW md_dict.
Definition block_sim_stmtW : Prop := sgroup_okW md_block.
Definition dec_sim_stmtW : Prop := fast_sim_stmtW -> sgroup_okW decode_mode.
(* TABLE -> LENLENS -> CODELENS fall into LEN_ (dec) *)
Definition tab_sim_stmtW : Prop := sgroup_okW decode_mode -> sgroup_okW md_tab.

(* One inflate() call on each stream from related call boundaries (IRRunCall.irc_call for wide calls): the same
   outcome, and the invariant at the next boundary. *)
Definition ar_call_stmt : Prop :=
  sgroup_okW (fun _ => True) ->
  forall W0 wrap src pos za La zb Lb strma strmb flush iba ibb inp oa ob ain aout
         ra za' sta' owa rb zb' stb' owb,
  IRinv W0 wrap src pos za La zb Lb -> live_ok La -> live_ok Lb -> zf_ok za -> zf_ok zb ->
  swfW (l_s La) -> swfW (l_s Lb) -> strma <> nullval -> strmb <> nullval ->
  0 <= pos -> 0 <= ain <= Int.max_unsigned -> pos + ain <= Zlength src -> bytes_ok src ->
  0 <= aout <= Int.max_unsigned -> iba <> InNull -> ibb <> InNull -> inp = sublist pos (pos + ain) src ->
  inflate_rel flush strma (ir_call za (in_ptr iba 0) ain (out_ptr oa 0) aout) (Some La) iba inp (Some oa)
    ra za' sta' owa ->
  ra <> Z_MEM_ERROR ->
  inflate_rel flush strmb (ir_call zb (in_ptr ibb 0) ain (out_ptr ob 0) aout) (Some Lb) ibb inp (Some ob)
    rb zb' stb' owb ->
  rb <> Z_MEM_ERROR ->
  exists La' Lb', sta' = Some La' /\ stb' = Some Lb' /\
    ra = rb /\ zf_ai za' = zf_ai zb' /\ zf_ao za' = zf_ao zb' /\ owa = owb /\
    Zlength owa = aout - zf_ao za' /\ 0 <= zf_ai za' <= ain /\ 0 <= zf_ao za' <= aout /\
    IRinv W0 wrap src (pos + (ain - zf_ai za')) za' La' zb' Lb'.
