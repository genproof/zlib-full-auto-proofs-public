(* Law rfc_level0_blocks, main: statements 23-27 (l0_LB -> return): `if (code != Z_STREAM_END) return 0` (the
   stream given back as the local's memory), then, with Z_STREAM_END, the check of the stored blocks against the
   copy of the data (L0B2Loop.part_loop) with the rest of the stream and of the objects (the data object among
   them) as its frame, given back as the local's memory at the return. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.Rep Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.LawFacts.
Require Zlib.proof.deflate.Api_toend.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.deflate.Level0Calls Zlib.proof.deflate.DeflateCodes.
Require Import Zlib.proof.harness.rfc_level0_blocks.L0B2MainStmt.
Require Import Zlib.proof.harness.rfc_level0_size.L0Kit2.
Require Import Zlib.proof.harness.rfc_level0_blocks.L0B2Kit.
Require Import Zlib.proof.harness.rfc_level0_blocks.L0B2Blocks.
Require Import Zlib.proof.harness.rfc_level0_blocks.L0B2Loop.
Require Import Zlib.harness.rfc_level0_blocks.code.
Module DC := Zlib.deflate.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

Ltac simplify_remove_localdef_temp ::= l0_rlt.

(* the stream, whatever its state, back to the local's memory *)
Lemma l0_strm_ret os vs ghp gv nin ai tin nout ao tout msgv adler :
  dstream 2 os vs ghp gv * api_fields vs nin ai tin nout ao tout msgv adler * l0_srest vs
  |-- data_at_ Tsh t_zsl vs * TT.
Proof.
  unfold l0_srest.
  sep_apply (BoundKit.dstream_data_at_ os vs ghp gv nin ai tin nout ao tout msgv adler
               Zlib.proof.deflate.Api_toend.dstream_to_end).
  change t_strm with t_zsl.
  rewrite (BoundKit.data_at__Tsh_split t_zsl vs). cancel.
Qed.

Lemma seg_end_ok : seg_end_stmt.
Proof.
  intros Espec gv vs n D dp ep cp wbits room.
  unfold l0_seg23, l0_LB. abbreviate_semax.
  Intros code O os nin ai tin ao tout adler msgv.
  match goal with H : code4 code |- _ => rename H into C4 end.
  match goal with H : code = Z_STREAM_END -> _ |- _ => rename H into HF end.
  forward_if.
  { (* the last call did not return Z_STREAM_END: return 0, the stream back to the local's memory *)
    sep_apply (l0_strm_ret os vs nullval gv nin ai tin (offset_val (Zlength O) cp) ao tout msgv adler).
    forward. Exists (Int.repr 0). entailer!. }
  assert (Ec : code = Z_STREAM_END).
  { destruct C4 as [E | [E | [E | E]]]; subst code; try reflexivity;
      match goal with H : Int.repr _ = Int.repr _ |- _ =>
        apply (f_equal Int.unsigned) in H; vm_compute in H; discriminate H end. }
  destruct (HF Ec) as (Et & (Hh & Tt & EO & Hhl & Htl)).
  subst O tout code.
  unfold api_fields. Intros.
  set (hl := l0_hlen wbits).
  set (junk := Zrepeat Vundef (room - Zlength (Hh ++ stored_blocks D ++ Tt))).
  set (tot := l0_size wbits n).
  pose (Fr := (dstream 2 os vs nullval gv *
              field_at Ews t_strm (DOT DC._next_in) nin vs * field_at Ews t_strm (DOT DC._avail_in) (vi ai) vs *
              field_at Ews t_strm (DOT DC._total_in) (vl tin) vs *
              field_at Ews t_strm (DOT DC._next_out) (offset_val (Zlength (Hh ++ stored_blocks D ++ Tt)) cp) vs *
              field_at Ews t_strm (DOT DC._avail_out) (vi ao) vs * field_at Ews t_strm (DOT DC._msg) msgv vs *
              field_at Ews t_strm (DOT DC._adler) (vl adler) vs * l0_srest vs *
              mem_mgr gv * R gv * l0_data n D dp * malloc_token Ews (tarray tuchar n) ep *
              malloc_token Ews (tarray tuchar room) cp)%logic).
  assert (HCl : (field_at Ews t_strm (DOT DC._total_out) (vl tot) vs * Fr |-- data_at_ Tsh t_strm vs * TT)%logic).
  { subst Fr.
    sep_apply (l0_api_fold vs nin ai tin (offset_val (Zlength (Hh ++ stored_blocks D ++ Tt)) cp) ao tot msgv adler);
      auto.
    sep_apply (l0_strm_ret os vs nullval gv nin ai tin (offset_val (Zlength (Hh ++ stored_blocks D ++ Tt)) cp)
                 ao tot msgv adler).
    change t_zsl with t_strm. cancel. }
  assert (Hhl10 : 0 <= hl <= 10) by (subst hl; unfold l0_hlen; destruct (wbits <? 0), (wbits >? 15); lia).
  assert (Htl0 : 0 <= Zlength Tt) by apply Zlength_nonneg.
  assert (Htot : hl + Zlength (stored_blocks D) <= tot <= Int64.max_unsigned).
  { subst tot hl. rewrite Zlength_stored_blocks. pose proof (l0_size_range wbits n ltac:(unfold l0_max_size in *; lia)).
    unfold l0_size in *. rewrite Htl in Htl0. subst n. rep_lia. }
  assert (Hjunk : Zlength (Hh ++ stored_blocks D ++ Tt) + Zlength junk = room)
    by (subst junk; rewrite Zlength_Zrepeat by lia; lia).
  eapply semax_pre;
    [| apply (part_loop gv vs ep cp n hl room tot D Hh Tt junk Fr HCl)].
  subst Fr. unfold A_loop, l0_comp, l0_data. entailer!.
Qed.
