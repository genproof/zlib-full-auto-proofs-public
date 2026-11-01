(* Law inflate_reset, main, the loop body's tail (IRMainLoopKit.seg_after): `pos += ain - a.avail_in;`, the six
   free()s, `if (stop == 0) { if (phase == 2) break; <reset> }` (the reset: IRMainKit.rst_stmt, a hypothesis). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_reset.IRLawCS Zlib.proof.harness.inflate_reset.IRGlobals
               Zlib.proof.harness.inflate_reset.IRFacts Zlib.proof.harness.inflate_reset.IRMainKit
               Zlib.proof.harness.inflate_reset.IRMainLoopKit.
Require Import Zlib.harness.x_inflate_reset.code.
Require Import Zlib.proof.crc32.Spec.

Ltac infeas := exfalso; first [ match goal with H: ?a <> ?b |- _ => solve [apply H; reflexivity] end
                              | match goal with H: _ |- _ => solve [discriminate H] end
                              | contradiction
                              | lia ].

Lemma tail_of : rst_stmt -> tail_stmt.
Proof.
  intros RST. unfold tail_stmt.
  intros Espec I1 I2 gv va vb vsa vsb w srcp src rb ph pos w2 aout wsel stop how ain iap ibp oap obp qa qb
         cia cib ca cb da db za La zb Lb TF.
  pose proof TF as TF0.
  destruct TF as (GF & HPI & Hai & Hpos & Hain & Hpa & Haout & Hw2 & Hws & Hst & Hhow
                  & Pva & Pvb & Piap & Pibp & Poap & Pobp & Pqa & Pqb).
  unfold tail_pre, seg_after, loop_post, Delta_m, Gmain_k, POST_m. simplify_func_tycontext. abbreviate_semax.
  rewrite ir_istream_unfold. Intros.
  forward. forward.
  sep_apply (ir_istream_fold gv Tsh va za La); auto.
  rewrite sub_repr, add_repr.
  set (pos' := pos + (ain - zf_ai za)) in *.
  assert (Hpos': 0 <= pos' <= Zlength src) by (unfold pos'; lia).
  clearbody pos'.
  forward_call (tarray tuchar ain, iap, gv).
  { rewrite if_false by (destruct iap; try contradiction; discriminate).
    sep_apply (data_at_data_at_ Ews (tarray tuchar ain) cia iap). cancel. }
  forward_call (tarray tuchar ain, ibp, gv).
  { rewrite if_false by (destruct ibp; try contradiction; discriminate).
    sep_apply (data_at_data_at_ Ews (tarray tuchar ain) cib ibp). cancel. }
  forward_call (tarray tuchar aout, oap, gv).
  { rewrite if_false by (destruct oap; try contradiction; discriminate).
    sep_apply (data_at_data_at_ Ews (tarray tuchar aout) ca oap). cancel. }
  forward_call (tarray tuchar aout, obp, gv).
  { rewrite if_false by (destruct obp; try contradiction; discriminate).
    sep_apply (data_at_data_at_ Ews (tarray tuchar aout) cb obp). cancel. }
  forward.
  forward_call (tarray tuchar aout, qa, gv).
  { rewrite if_false by (destruct qa; try contradiction; discriminate).
    sep_apply (data_at_data_at_ Ews (tarray tuchar aout) da qa). cancel. }
  forward.
  forward_call (tarray tuchar aout, qb, gv).
  { rewrite if_false by (destruct qb; try contradiction; discriminate).
    sep_apply (data_at_data_at_ Ews (tarray tuchar aout) db qb). cancel. }
  forward_if.
  2: { forward. unfold loop_inv, inv_at. Exists ph pos' w2 za La zb Lb. entailer!. }
  unfold ph_inv in HPI. destruct (Z.eqb_spec ph 1) as [-> | Hph1].
  - destruct HPI as [-> HI].
    forward_if. { infeas. }
    unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
    eapply semax_pre; [ | eapply semax_post; [ | | | |
      apply (RST _ I1 I2 gv va vb vsa vsb w srcp src rb pos' wsel how za La GF HI Hpos' Hws Hhow Pva Pvb) ] ].
    { unfold rst_pre. replace (bmem gv vb 1 rb zb Lb) with (braw gv vb rb) by reflexivity. entailer!. }
    { apply andp_left2; apply derives_refl. }
    { simpl RA_break. apply andp_left2. unfold POST_m. simpl RA_break. intro rho. normalize. }
    { simpl RA_continue. apply andp_left2. unfold POST_m. simpl RA_continue. intro rho; normalize. }
    { intros; apply andp_left2; apply derives_refl. }
  - destruct HPI as [-> HI].
    forward_if. 
    { forward. unfold brk_inv, inv_at. Exists pos' w2 za La zb Lb. entailer!. unfold ph_inv; simpl; auto. }
    { infeas. }
Qed.
