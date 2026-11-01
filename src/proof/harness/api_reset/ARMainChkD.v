(* Law api_reset, main: the fifth assert of phase 1 (ARMainChkA.chk_part, seg_c5). *)
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

(* gp_assert(used.msg == fresh.msg && used.data_type == fresh.data_type): msg is NULL or one of inflate's
   message literals, whose first byte (ir_msg_lits) makes the pointer comparison defined *)
Lemma chk_c5 : chk_part seg_c5.
Proof.
  intros Espec J0 J1 gv va vb w inp src pos take room iu ifr ou ofr ra za La zb Lb ow MF.
  unfold seg_c5, chk_pre at 1, chk_tup. Intros.
  assert_PROP (isptr (msg_val gv (zf_msg za)) \/ msg_val gv (zf_msg za) = nullval) as Pm.
  { destruct (zf_msg za) as [m | ]; [ | entailer!].
    rewrite (add_andp (ir_msg_lits gv) _ (ar_msg_ptr gv m)). Intros. entailer!. }
  abbreviate_semax.
  forward.
  { entailer!. destruct Pm as [Pm | Pm]; [destruct (msg_val gv (zf_msg za)); try contradiction; simpl; auto |
                                         rewrite Pm; simpl; auto]. }
  forward.
  apply semax_if_seq. forward_if.
  { destruct (zf_msg za) as [m | ]; simpl msg_val; [ | entailer!].
    pose proof (ar_msg_valid gv m). apply denote_tc_test_eq_split; auto with valid_pointer. }
  2: { exfalso. auto. }
  forward. forward. forward. forward_call (Int.repr 1).
  { entailer!. rewrite Int.eq_true. reflexivity. }
  unfold chk_pre, chk_tup. entailer!.
Qed.
