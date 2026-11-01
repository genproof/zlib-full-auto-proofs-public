(** * send_tree: the curlen != 0 branch (send_code curlen if curlen != prevlen, count--; send_code REP_3_6; send_bits(count - 3, 2)) (SendTreeKit.st_rep_stmt) *)
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

Lemma st_rep_ok : st_rep_stmt.
Proof.
  intros Espec cnt i pl cl nl xc nc sp tp max_code om r pbp tsh n t bl Hsh Hbl Hcnt Hpl Hcl H.
  unfold st_pre, st_post, st_locals, st_sep, st_rep, Delta_st.
  simplify_func_tycontext. abbreviate_semax.
  destruct om as [o m].
  inv_bind H. destruct x as [om1 cnt1].
  forward_if (PROP (cnt - 1 <= cnt1 <= cnt) LOCAL (temp _count (vi cnt1); temp _curlen (vi cl); temp _nextlen (vi nl);
      temp _n (vi i); temp _prevlen (vi pl); temp _max_count (vi xc); temp _min_count (vi nc);
      temp _s sp; temp _tree tp; temp _max_code (vi max_code))
    SEP (out_at (fst om1) (snd om1) sp pbp; @data_at DCS.CS tsh (tarray t_ct n) (ct_arr ffalse ftrue t) tp;
      @field_at DCS.CS Ews t_ds (DOT _bl_tree) (ct_arr ftrue ftrue bl) sp)).
  { apply Z.eqb_neq in H0. rewrite H0 in Ha. cbn [negb] in Ha.
    inv_bind Ha. injection Ha as <- <-. rename Ha0 into Hc.
    unfold c_send_code in Hc. inv_bind Hc. inv_bind Hc. rename Ha into Hlen, Ha0 into Hcode, Hc into Hsb.
    apply rd_inv in Hlen. apply rd_inv in Hcode. destruct Hlen as [Hl0 ->]. destruct Hcode as [Hc0 ->].
    assert (Hcl39 : 0 <= cl < 39)
      by (pose proof Hbl as (_ & Hd & _); change (2 * BL_CODES + 1) with 39 in Hd; lia).
    cbn [fst snd].
    sb_pre Hsb ltac:(idtac).
    { sb_cond. sbt1 Hsb ltac:(idtac) ltac:(sb_val_default). sbt2 Hsb. sbt3 Hsb. sbt4 Hsb. }
    { sb_cond. sb_else Hsb ltac:(idtac) ltac:(sb_val_default). }
    forward. entailer!. apply derives_refl. }
  { subst pl. rewrite Z.eqb_refl in Ha. cbn in Ha. injection Ha as <- <-. forward. entailer!. }
  Intros. clear Ha. destruct om1 as [o1 m1].
  inv_bind H. rename Ha into Hc, H into Hsb2.
  unfold c_send_code in Hc. inv_bind Hc. inv_bind Hc. rename Ha into Hlen, Ha0 into Hcode, Hc into Hsb.
  apply rd_inv in Hlen. apply rd_inv in Hcode. destruct Hlen as [Hl0 ->]. destruct Hcode as [Hc0 ->].
  cbn [fst snd]. change REP_3_6 with 16 in *.
  sb_pre Hsb ltac:(idtac).
  { sb_cond. sbt1 Hsb ltac:(idtac) ltac:(sb_val_default). sbt2 Hsb. sbt3 Hsb. sbt4 Hsb. }
  { sb_cond. sb_else Hsb ltac:(idtac) ltac:(sb_val_default). }
  sb_pre Hsb2 ltac:(idtac).
  { sb_cond. sbt1 Hsb2 ltac:(idtac) ltac:(rewrite ?sub_repr32; apply sb_val_repr). sbt2 Hsb2. sbt3 Hsb2. sbt4 Hsb2. }
  { sb_cond. sb_else Hsb2 ltac:(idtac) ltac:(rewrite ?sub_repr32; apply sb_val_repr). }
  cbn [fst snd]. entailer!.
Qed.
