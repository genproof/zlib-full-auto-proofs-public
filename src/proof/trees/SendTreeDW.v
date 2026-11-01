(** * send_tree: the do-while branch [do { send_code(s, curlen, s->bl_tree); } while (--count != 0);] (SendTreeKit.st_dw_stmt) *)
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

Lemma st_dw_ok : st_dw_stmt.
Proof.
  intros Espec cnt i pl cl nl xc nc sp tp max_code om r pbp tsh n t bl Hsh Hbl Hcnt H.
  unfold st_pre, st_post, st_locals, st_sep, st_dw, Delta_st.
  simplify_func_tycontext. abbreviate_semax.
  forward_loop
    (EX k : Z, EX om' : cout,
     PROP (1 <= k <= cnt; c_send_codes (Z.to_nat k) om' cl (fc bl) (dl bl) k = Some r)
     LOCAL (temp _count (vi k); temp _curlen (vi cl); temp _nextlen (vi nl); temp _n (vi i);
            temp _prevlen (vi pl); temp _max_count (vi xc); temp _min_count (vi nc); temp _s sp;
            temp _tree tp; temp _max_code (vi max_code))
     SEP (out_at (fst om') (snd om') sp pbp; @data_at DCS.CS tsh (tarray t_ct n) (ct_arr ffalse ftrue t) tp;
          @field_at DCS.CS Ews t_ds (DOT _bl_tree) (ct_arr ftrue ftrue bl) sp))
  continue:
    (EX k : Z, EX om' : cout,
     PROP (1 <= k <= cnt;
           if negb (k - 1 =? 0) then c_send_codes (Z.to_nat (k - 1)) om' cl (fc bl) (dl bl) (k - 1) = Some r
           else Some om' = Some r)
     LOCAL (temp _count (vi k); temp _curlen (vi cl); temp _nextlen (vi nl); temp _n (vi i);
            temp _prevlen (vi pl); temp _max_count (vi xc); temp _min_count (vi nc); temp _s sp;
            temp _tree tp; temp _max_code (vi max_code))
     SEP (out_at (fst om') (snd om') sp pbp; @data_at DCS.CS tsh (tarray t_ct n) (ct_arr ffalse ftrue t) tp;
          @field_at DCS.CS Ews t_ds (DOT _bl_tree) (ct_arr ftrue ftrue bl) sp))
  break:
    (PROP ()
     LOCAL (temp _curlen (vi cl); temp _nextlen (vi nl); temp _n (vi i);
            temp _prevlen (vi pl); temp _max_count (vi xc); temp _min_count (vi nc); temp _s sp;
            temp _tree tp; temp _max_code (vi max_code))
     SEP (out_at (fst r) (snd r) sp pbp; @data_at DCS.CS tsh (tarray t_ct n) (ct_arr ffalse ftrue t) tp;
          @field_at DCS.CS Ews t_ds (DOT _bl_tree) (ct_arr ftrue ftrue bl) sp)).
  { Exists cnt om. entailer!. }
  { Intros k om'. rename H0 into Hk, H1 into Hr.
    assert (Hfu : Z.to_nat k = S (Z.to_nat (k - 1))) by lia.
    rewrite Hfu in Hr. cbn [c_send_codes] in Hr.
    inv_bind Hr. rename Ha into Hc.
    unfold c_send_code in Hc. inv_bind Hc. inv_bind Hc. rename Ha into Hlen, Ha0 into Hcode, Hc into Hsb.
    apply rd_inv in Hlen. apply rd_inv in Hcode. destruct Hlen as [Hl0 ->]. destruct Hcode as [Hc0 ->].
    pose proof Hbl as (Hbl1 & Hbl2 & _). change (2 * BL_CODES + 1) with 39 in Hbl1, Hbl2.
    destruct om' as [o m]. cbn [fst snd].
    sb_pre Hsb ltac:(idtac).
    { sb_cond. sbt1 Hsb ltac:(idtac) ltac:(sb_val_default). sbt2 Hsb. sbt3 Hsb. sbt4 Hsb. }
    { sb_cond. sb_else Hsb ltac:(idtac) ltac:(sb_val_default). }
    Exists k (o, m0). cbn [fst snd]. entailer!. destruct (negb (k - 1 =? 0)); exact Hr. }
  { Intros k om'. rename H0 into Hk, H1 into Hr.
    forward. forward.
    rewrite ?sub_repr32. destruct (Z.eq_dec (k - 1) 0) as [E|E].
    - rewrite E in Hr. cbn in Hr. injection Hr as <-. rewrite E. forward_if.
      + discriminate.
      + forward. entailer!.
    - rewrite (proj2 (Z.eqb_neq _ _) E) in Hr. cbn [negb] in Hr. forward_if.
      + forward. Exists (k - 1) om'. entailer!.
      + contradiction. }
  { unfold POSTCONDITION, abbreviate. apply andp_left2. apply derives_refl. }
Qed.
