(* Law api_inflate_deterministic, main: the fifth and sixth asserts of seg_tail (AIDMainTailChkA.chk_part,
   seg_c5 and seg_c6). *)
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

(* gp_assert(first.msg == second.msg && first.data_type == second.data_type): msg is NULL or one of inflate's
   message literals, whose first byte (ir_msg_lits) makes the pointer comparison defined *)
Lemma chk_c5 : chk_part seg_c5.
Proof.
  intros Espec J gv va vb w inp src pos take room ia ib oa ob ra za La zb Lb ow MF.
  unfold seg_c5, chk_pre at 1, chk_tup. Intros.
  assert_PROP (isptr (msg_val gv (zf_msg za)) \/ msg_val gv (zf_msg za) = nullval) as Pm.
  { destruct (zf_msg za) as [m | ]; [ | entailer!].
    rewrite (add_andp (ir_msg_lits gv) _ (aid_msg_ptr gv m)). Intros. entailer!. }
  abbreviate_semax.
  forward.
  { entailer!. destruct Pm as [Pm | Pm]; [destruct (msg_val gv (zf_msg za)); try contradiction; simpl; auto |
                                         rewrite Pm; simpl; auto]. }
  forward.
  apply semax_if_seq. forward_if.
  { destruct (zf_msg za) as [m | ]; simpl msg_val; [ | entailer!].
    pose proof (aid_msg_valid gv m). apply denote_tc_test_eq_split; auto with valid_pointer. }
  2: { exfalso. auto. }
  forward. forward. forward. forward_call (Int.repr 1).
  { entailer!. rewrite Int.eq_true. reflexivity. }
  unfold chk_pre, chk_tup. entailer!.
Qed.

(* gp_assert(window_bits < 0 || first.adler == second.adler): for windowBits >= 0 neither stream is raw, so
   strm->adler holds the model's adler on both, equal by mid_facts *)
Lemma chk_c6 : chk_part seg_c6.
Proof.
  intros Espec J gv va vb w inp src pos take room ia ib oa ob ra za La zb Lb ow MF.
  pose proof MF as ((_ & _ & Hw & _) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                    Eadl & _).
  unfold seg_c6, chk_pre at 1, chk_tup. Intros. abbreviate_semax.
  destruct (Z.ltb_spec w 0) as [Hn | Hn]; unfold adler_v.
  - apply semax_if_seq. forward_if.
    + forward. forward_call (Int.repr 1).
      unfold chk_pre, chk_tup, adler_v. rewrite (proj2 (Z.ltb_lt w 0) Hn). entailer!.
    + exfalso. lia.
  - apply semax_if_seq. forward_if.
    + exfalso. lia.
    + forward. forward. forward. forward_call (Int.repr 1).
      { entailer!. rewrite (Eadl Hn), Int64.eq_true. reflexivity. }
      unfold chk_pre, chk_tup, adler_v. rewrite (proj2 (Z.ltb_ge w 0) Hn). entailer!.
Qed.
