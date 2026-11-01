(* Law api_reset, main: the fourth assert of phase 1 (ARMainChkA.chk_part, seg_c4). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.api_reset.ARMainDefs.
Require Import Zlib.proof.harness.api_reset.ARMainKit.
Require Import Zlib.proof.harness.api_reset.ARMainChkA.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.harness.api_reset.code.
Local Open Scope logic.

(* gp_assert(used.total_in == fresh.total_in && used.total_out == fresh.total_out) *)
Lemma chk_c4 : chk_part seg_c4.
Proof.
  intros Espec J0 J1 gv va vb w inp src pos take room iu ifr ou ofr ra za La zb Lb ow MF.
  unfold seg_c4, chk_pre at 1, chk_tup. Intros. abbreviate_semax.
  forward. forward.
  apply semax_if_seq. forward_if.
  2: { exfalso. auto. }
  forward. forward. forward. forward_call (Int.repr 1).
  { entailer!. rewrite Int64.eq_true. reflexivity. }
  unfold chk_pre, chk_tup. entailer!.
Qed.
