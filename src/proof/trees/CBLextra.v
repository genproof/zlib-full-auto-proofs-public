(** * compress_block part [cb_lextra] (see CBKit.v): its macro block against the model. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.trees.TSpec.
Require Import Zlib.proof.trees.SendKit2.
Require Import Zlib.proof.trees.CBKit.
Require Import Zlib.trees.code.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

Lemma cb_lextra_ok : cb_lextra_stmt.
Proof.
  intros Espec sx lc dist code extra sp pbp ltp dtp gv ts lsh ln lt dsh dn dt om r (Hl & Hd & Hlt & Hdt) Hlc Hcode Hx H.
  pose proof (rd_extra_lbits_range _ _ Hx) as Hxr.
  unfold cb_assert, cb_sep, cb_base, Delta_cb. unfold cb_lextra.
  forward_if (PROP () LOCAL (temp _dist (vi dist); temp _sx (vi sx); temp _s sp; temp _ltree ltp;
      temp _dtree dtp; gvars gv)
    SEP (out_at (fst r) (snd r) sp pbp; sym_at ts sp pbp; tree_codes lsh ln lt ltp; tree_codes dsh dn dt dtp;
      trees_tables gv)).
  - rewrite (proj2 (negb_true_iff _) (proj2 (Z.eqb_neq _ _) H0)) in H.
    inv_bind H. rename Ha into Hbl, H into Hsb.
    pose proof (rd_base_length_range _ _ Hbl) as Hblr.
    apply cb_rd_inv in Hbl. destruct Hbl as [Hbi Hbl].
    destruct om as [o m]; destruct o as [buf p bb bv bu]; cbn [fst snd].
    unfold trees_tables. Intros.
    forward. rewrite <- Hbl. forward. rewrite sub_repr.
    sb_block Hsb ltac:(idtac) ltac:(sb_val_default).
    cbn [fst snd]. unfold trees_tables, vi. entailer!.
  - subst extra. cbn in H. injection H as <-. forward. entailer!.
Qed.
