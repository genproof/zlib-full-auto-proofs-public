(* Law api_inflate_deterministic, main: the second and fourth asserts of seg_tail (AIDMainTailChkA.chk_part,
   seg_c2 and seg_c4). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.api_inflate_deterministic.AIDMainDefs.
Require Import Zlib.proof.harness.api_inflate_deterministic.AIDMainKit.
Require Import Zlib.proof.harness.api_inflate_deterministic.AIDMainTailChkA.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.harness.api_inflate_deterministic.code.
Local Open Scope logic.

(* gp_assert(first.avail_in == second.avail_in && first.avail_out == second.avail_out) *)
Lemma chk_c2 : chk_part seg_c2.
Proof.
  intros Espec J gv va vb w inp src pos take room ia ib oa ob ra za La zb Lb ow MF.
  unfold seg_c2, chk_pre at 1, chk_tup. Intros. abbreviate_semax.
  forward. forward.
  apply semax_if_seq. forward_if.
  2: { exfalso. auto. }
  forward. forward. forward. forward_call (Int.repr 1).
  { entailer!. rewrite Int.eq_true. reflexivity. }
  unfold chk_pre, chk_tup. entailer!.
Qed.

(* gp_assert(first.total_in == second.total_in && first.total_out == second.total_out) *)
Lemma chk_c4 : chk_part seg_c4.
Proof.
  intros Espec J gv va vb w inp src pos take room ia ib oa ob ra za La zb Lb ow MF.
  unfold seg_c4, chk_pre at 1, chk_tup. Intros. abbreviate_semax.
  forward. forward.
  apply semax_if_seq. forward_if.
  2: { exfalso. auto. }
  forward. forward. forward. forward_call (Int.repr 1).
  { entailer!. rewrite Int64.eq_true. reflexivity. }
  unfold chk_pre, chk_tup. entailer!.
Qed.
