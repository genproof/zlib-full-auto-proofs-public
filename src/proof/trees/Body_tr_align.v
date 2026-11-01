(** * The body of trees.c's _tr_align against its shared specification (TSpec.tr_align_spec).

    Two inlined macro blocks (send_bits of the block type, send_code of END_BLOCK on the static tree), both by
    [SendKit.sb_block]; then bi_flush by its spec. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.trees.TSpec.
Require Import Zlib.proof.trees.SendKit2.
Require Import Zlib.trees.code.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

Lemma body_tr_align : semax_body Vprog Gprog_tr_align f__tr_align tr_align_spec.
Proof.
  start_function.
  unfold c_tr_align in H. inv_bind H. rename Ha into Hsb.
  change (Z.shiftl STATIC_TREES 1) with 2 in Hsb.
  sb_block Hsb ltac:(idtac) ltac:(sb_val_default).
  unfold c_send_code in H. inv_bind H. rename Ha into Hc. inv_bind Hc. inv_bind Hc.
  rename Ha into Hlen, Ha0 into Hcode, Hc into Hsb2.
  change (rd static_ltree_len END_BLOCK) with (Some 7) in Hlen. injection Hlen as <-.
  change (rd static_ltree_code END_BLOCK) with (Some 0) in Hcode. injection Hcode as <-.
  unfold static_trees. rewrite !sk_tree_arr_codes. Intros.
  assert (Hslt0 : Znth 256 (fc static_ltree_t) = 0) by reflexivity.
  assert (Hslt7 : Znth 256 (dl static_ltree_t) = 7) by reflexivity.
  assert (Hslt0' : Znth 256 static_ltree_code = 0) by reflexivity.
  unfold tree_codes.
  destruct o as [b1 p1 bb1 bv1 bu1]. destruct x as [o2 m2].
  sfwd; rewrite ?Hslt7; try (solve [sb_side]).
  assert (0 <= 7 <= 65535) by rep_lia.
  open_out_at.
  pose proof (out_ok_bv _ _ _ _ _ _ H8). pose proof (out_ok_bb _ _ _ _ _ _ H8).
  sfwd.
  sb_forward_if o2 m2.
  - sb_cond.
    sb_then Hsb2 ltac:(rewrite ?Hslt7, ?Hslt0, ?Hslt0') ltac:(rewrite ?Hslt0, ?Hslt0'; sb_val_default).
  - sb_cond.
    sb_else Hsb2 ltac:(rewrite ?Hslt7, ?Hslt0, ?Hslt0') ltac:(rewrite ?Hslt0, ?Hslt0'; sb_val_default).
  - lazymatch goal with Hf : c_bi_flush (?o, ?m) = Some _ |- _ => forward_call (sp, pbp, o, m, r) end.
    unfold static_trees. rewrite !sk_tree_arr_codes. unfold tree_codes.
    entailer!.
Qed.
