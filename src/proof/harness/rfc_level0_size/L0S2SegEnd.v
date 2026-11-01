(* Law rfc_level0_size, main: statement 21 (gp_assert(code == Z_STREAM_END && strm.total_out == size);
   return 0), the stream given back as the local's memory (l0_LB -> return). *)
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
Require Import Zlib.proof.deflate.Level0CallsFit.
Require Import Zlib.proof.harness.rfc_level0_size.L0S2MainStmt.
Require Import Zlib.proof.harness.rfc_level0_size.L0Kit2.
Require Import Zlib.proof.harness.rfc_level0_size.L0S2Kit.
Require Import Zlib.harness.rfc_level0_size.code.
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
  intros Espec gv vs n D dp cp wbits room.
  unfold l0_seg21, l0_LB, POST_B, POST_l0. abbreviate_semax.
  Intros O os nin ai tin ao adler msgv.
  unfold api_fields. Intros.
  forward_if (temp _t'14 (Vint (Int.repr 1))).
  { forward. forward. entailer!. unfold Int64.cmpu. rewrite Int64.eq_true. reflexivity. }
  { match goal with H : Int.repr _ <> Int.repr 1 |- _ => elim H; reflexivity end. }
  forward_call (Int.repr 1).
  sep_apply (l0_api_fold vs nin ai tin (offset_val (Zlength O) cp) ao (l0_size wbits n) msgv adler);
    auto.
  sep_apply (l0_strm_ret os vs nullval gv nin ai tin (offset_val (Zlength O) cp) ao (l0_size wbits n) msgv adler).
  forward. Exists (Int.repr 0). entailer!.
Qed.
