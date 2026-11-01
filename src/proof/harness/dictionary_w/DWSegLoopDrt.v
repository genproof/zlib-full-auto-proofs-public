(* Law rt_dictionary, main (DWKit.v): statement 21, the do-while of deflate() calls (LI -> LB), in rt_dictionary's
   context.  As clip_streams/RTSegLoop.v's seg_loop_ok, with the end of an iteration from
   DWSegLoopRestDrt.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.clip_streams.CS.
Require Import Zlib.proof.harness.clip_streams.Globals.
Require Import Zlib.proof.harness.clip_streams.RTKit.
Require Import Zlib.proof.harness.clip_streams.RTMem.
Require Import Zlib.proof.harness.clip_streams.RTSegLoop.
Require Import Zlib.proof.harness.dictionary_w.DWCS.
Require Import Zlib.proof.harness.dictionary_w.DWFacts.
Require Import Zlib.proof.harness.dictionary_w.DWKit.
Require Import Zlib.proof.harness.dictionary_w.DWSegLoopCall.
Require Import Zlib.proof.harness.dictionary_w.DWSegLoopRestDrt.
Require Import Zlib.harness.rt_dictionary.code.
#[local] Existing Instance CS.CS.
Local Open Scope logic.

Ltac simplify_remove_localdef_temp ::= rt_rlt.

(* one iteration: from the loop head to the state after deflate() *)
Lemma dw_loop_body_drt {Espec : OracleKind} J0 J1 J gv vc vd n D dp op dict ddp wbits b cp :
  dict_dfacts J0 J1 J ->
  semax Delta_drt (LI lit_drt gv vc vd J n D dp op dict ddp wbits b cp) dw_lbody_drt
    (normal_ret_assert (dw_LC lit_drt gv vc vd J n D dp op dict ddp wbits b cp)).
Proof.
  intros DF.
  unfold dw_lbody_drt. abbreviate_semax.
  unfold LI. Intros pos O s tin tout adler ai ao msg msgv.
  pose proof (dw_range _ _ _ DF _ _ _ _ _ _ _ _ _ _ ltac:(eassumption)) as RG.
  destruct RG as (Hpos & Hn & HO & Hb & RD & RO & Hgz & Htin & Htout & Had).
  match goal with Hc : dw_cf _ _ _ _ _ _ _ |- _ => pose proof Hc as CF; destruct Hc as (Hn0 & HD & BD & Pdp & Pop & _) end.
  rewrite rt_api_fields_L. unfold api_fieldsL. Intros.
  subst n.
  forward.
  forward.
  { entailer!. apply prop_right. apply rt_sameblock; auto. }
  rewrite rt_rest_val by (auto; unfold max_size in *; rep_lia).
  forward.
  forward_if (temp _flush (Vint (Int.repr (dflush (Zlength D - pos))))).
  { forward. entailer!. unfold dflush, umax.
    rewrite !Int64.unsigned_repr in * by (unfold max_size in *; rep_lia).
    match goal with |- context [Z.leb ?x _] => destruct (Z.leb_spec x 4294967295) end; [reflexivity | lia]. }
  { forward. entailer!. unfold dflush, umax.
    rewrite !Int64.unsigned_repr in * by (unfold max_size in *; rep_lia).
    match goal with |- context [Z.leb ?x _] => destruct (Z.leb_spec x 4294967295) end; [lia | reflexivity]. }
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre;
    [ | apply (dw_loop_rest_drt J0 J1 J gv vc vd D dp op dict ddp wbits b cp pos O s tin tout adler ai ao msg msgv DF) ].
  unfold dw_X0.
  sep_apply (rt_api_fields_fold vc (offset_val pos dp) ai tin (offset_val (Zlength O) cp) ao tout msgv adler
               H H2 H3 H4 H5).
  entailer!.
Qed.

Lemma seg_loop_drt_ok : seg_loop_drt_stmt.
Proof.
  intros Espec J0 J1 J gv vc vd n D dp op dict ddp wbits b cp DF.
  unfold seg_loop_drt, POST_drt. abbreviate_semax.
  forward_loop (LI lit_drt gv vc vd J n D dp op dict ddp wbits b cp)
    continue: (dw_LC lit_drt gv vc vd J n D dp op dict ddp wbits b cp)
    break: (LB lit_drt gv vc vd n D dp op dict ddp wbits b cp).
  { apply ENTAIL_refl. }
  { eapply semax_post; [ | | | | apply (dw_loop_body_drt J0 J1 J gv vc vd n D dp op dict ddp wbits b cp DF) ];
      intros; simpl RA_normal; simpl RA_break; simpl RA_continue; simpl RA_return; normalize. }
  { (* while (code == Z_OK) *)
    unfold dw_LC. Intros code pos O s tin tout adler ai ao msg msgv.
    forward_if.
    { forward. unfold LI. Exists pos O s tin tout adler ai ao msg msgv.
      assert (code = 0) by (apply repr_inj_signed; auto; unfold rs32 in *; rep_lia).
      entailer!. }
    { forward. unfold LB. Exists code O (Some s) (offset_val pos dp) ai tin ao tout adler msgv.
      entailer!. } }
  unfold POSTCONDITION, abbreviate. simpl RA_normal. apply ENTAIL_refl.
Qed.
