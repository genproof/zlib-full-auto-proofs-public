(** * compress_block part [cb_dsend] (see CBKit.v): its macro block against the model. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.trees.TSpec.
Require Import Zlib.proof.trees.SendKit2.
Require Import Zlib.proof.trees.CBKit.
Require Import Zlib.trees.code.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

Lemma cb_dsend_ok : cb_dsend_stmt.
Proof.
  intros Espec sx dist code sp pbp ltp dtp gv ts lsh ln lt dsh dn dt om r (Hl & Hd & Hlt & Hdt) Hc H.
  unfold cb_assert, cb_sep, cb_base, Delta_cb. unfold tree_codes.
  unfold c_send_code in H. inv_bind H. rename Ha into Hlen. inv_bind H. rename Ha into Hcode, H into Hsb.
  apply cb_rd_inv in Hlen. destruct Hlen as [Hi1 ->].
  apply cb_rd_inv in Hcode. destruct Hcode as [Hi2 ->].
  pose proof Hdt as (Hfd & Hdd & _).
  assert (Hidn : code < dn) by lia.
  destruct om as [o m]; destruct o as [buf p bb bv bu]; cbn [fst snd].
  unfold cb_dsend.
  sb_block Hsb ltac:(idtac) ltac:(sb_val_default).
  cbn [fst snd]. unfold vi. entailer!.
Qed.
