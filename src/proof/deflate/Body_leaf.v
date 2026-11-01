(** * Body proofs: read_buf, putShortMSB, flush_pending, slide_hash, lm_init, deflateStateCheck.

    The target: every function's body satisfies its shared specification (see Obligations.v: ob_X =
    semax_body Vprog Gprog_X f_X X_spec; specs in src/proof/trees/TSpec.v, src/proof/deflate/DSpec.v,
    src/proof/compress/CSpec.v; checked models in src/proof/trees/CModel.v, src/proof/deflate/DModel*.v).
    Prove each body as its own lemma (in this file or in new files it imports) and conclude. *)
Require Import Zlib.proof.deflate.Obligations.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.deflate.code.
Require Import Zlib.proof.deflate.Body_read_buf Zlib.proof.deflate.Body_flush_pending
  Zlib.proof.deflate.Body_slide_hash Zlib.proof.deflate.Body_lm_init
  Zlib.proof.deflate.Body_deflateStateCheck.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

Lemma shru8_repr (b : Z) : 0 <= b <= Int.max_unsigned ->
  Int.shru (Int.repr b) (Int.repr 8) = Int.repr (Z.shiftr b 8).
Proof.
  intros. rewrite shru_repr by (cbn; rep_lia). rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma body_putShortMSB : ob_putShortMSB.
Proof.
  unfold ob_putShortMSB. start_function.
  destruct o as [buf p bb bv bu]. unfold c_putShortMSB_o in H0.
  inv_bind H0.
  apply c_put_byte_inv in Ha. cbn [o_buf o_pending] in Ha. destruct Ha as [Hi1 ->].
  apply c_put_byte_inv' in H0. cbn [fst snd put_byte_c o_buf o_pending] in H0. destruct H0 as [Hi2 ->].
  open_out_at.
  fwd. fwd. fwd. fwd.
  rewrite shru8_repr by lia.
  fold_put_byte. open_out_at.
  fwd. fwd. fwd. fwd.
  fold_put_byte.
  entailer!. apply derives_refl.
Qed.

Theorem deflate_leaf : ob_read_buf /\ ob_putShortMSB /\ ob_flush_pending /\ ob_slide_hash /\ ob_lm_init /\ ob_deflateStateCheck.
Proof.
  split; [exact body_read_buf|]. split; [exact body_putShortMSB|]. split; [exact body_flush_pending|].
  split; [exact body_slide_hash|]. split; [exact body_lm_init|]. exact body_deflateStateCheck.
Qed.
