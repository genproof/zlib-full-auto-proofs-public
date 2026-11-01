(** * send_tree: the REPZ_3_10 and REPZ_11_138 branches (SendTreeKit.st_z10_stmt, st_z138_stmt) *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.trees.TSpec.
Require Import Zlib.proof.trees.SendKit2.
Require Import Zlib.proof.trees.SendTreeKit.
Require Import Zlib.proof.trees.SendSplit.
Require Import Zlib.trees.code.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

Lemma st_z10_ok : st_z10_stmt.
Proof.
  intros Espec cnt i pl cl nl xc nc sp tp max_code om r pbp tsh n t bl Hsh Hbl Hcnt H.
  unfold st_pre, st_post, st_locals, st_sep, st_z10, Delta_st.
  simplify_func_tycontext. abbreviate_semax.
  destruct om as [o m].
  inv_bind H. rename Ha into Hc, H into Hsb2.
  unfold c_send_code in Hc. inv_bind Hc. inv_bind Hc. rename Ha into Hlen, Ha0 into Hcode, Hc into Hsb.
  apply rd_inv in Hlen. apply rd_inv in Hcode. destruct Hlen as [Hl0 ->]. destruct Hcode as [Hc0 ->].
  cbn [fst snd]. change REPZ_3_10 with 17 in *.
  sb_pre Hsb ltac:(idtac).
  { sb_cond. sbt1 Hsb ltac:(idtac) ltac:(sb_val_default). sbt2 Hsb. sbt3 Hsb. sbt4 Hsb. }
  { sb_cond. sb_else Hsb ltac:(idtac) ltac:(sb_val_default). }
  sb_pre Hsb2 ltac:(idtac).
  { sb_cond. sbt1 Hsb2 ltac:(idtac) ltac:(rewrite ?sub_repr32; apply sb_val_repr). sbt2 Hsb2. sbt3 Hsb2. sbt4 Hsb2. }
  { sb_cond. sb_else Hsb2 ltac:(idtac) ltac:(rewrite ?sub_repr32; apply sb_val_repr). }
  cbn [fst snd]. entailer!.
Qed.

Lemma st_z138_ok : st_z138_stmt.
Proof.
  intros Espec cnt i pl cl nl xc nc sp tp max_code om r pbp tsh n t bl Hsh Hbl Hcnt H.
  unfold st_pre, st_post, st_locals, st_sep, st_z138, Delta_st.
  simplify_func_tycontext. abbreviate_semax.
  destruct om as [o m].
  inv_bind H. rename Ha into Hc, H into Hsb2.
  unfold c_send_code in Hc. inv_bind Hc. inv_bind Hc. rename Ha into Hlen, Ha0 into Hcode, Hc into Hsb.
  apply rd_inv in Hlen. apply rd_inv in Hcode. destruct Hlen as [Hl0 ->]. destruct Hcode as [Hc0 ->].
  cbn [fst snd]. change REPZ_11_138 with 18 in *.
  sb_pre Hsb ltac:(idtac).
  { sb_cond. sbt1 Hsb ltac:(idtac) ltac:(sb_val_default). sbt2 Hsb. sbt3 Hsb. sbt4 Hsb. }
  { sb_cond. sb_else Hsb ltac:(idtac) ltac:(sb_val_default). }
  sb_pre Hsb2 ltac:(idtac).
  { sb_cond. sbt1 Hsb2 ltac:(idtac) ltac:(rewrite ?sub_repr32; apply sb_val_repr). sbt2 Hsb2. sbt3 Hsb2. sbt4 Hsb2. }
  { sb_cond. sb_else Hsb2 ltac:(idtac) ltac:(rewrite ?sub_repr32; apply sb_val_repr). }
  cbn [fst snd]. entailer!.
Qed.
