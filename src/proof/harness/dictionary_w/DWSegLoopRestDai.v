(* Law api_dict_id, main (DWKit.v): the end of an iteration of statement 20, the do-while of deflate() calls, from
   the state after its first three statements (DWSegLoopCall.dw_X0) to the state after the call (dw_LC), in
   api_dict_id's context (its load of next_out uses the temporary _t'29).
   The proof of DWSegLoopRestDrt.v in the other program. *)
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
Require Import Zlib.harness.api_dict_id.code.
#[local] Existing Instance CS.CS.
Local Open Scope logic.

Ltac simplify_remove_localdef_temp ::= rt_rlt.

(* the clip() calls and the deflate() call of an iteration *)
Lemma dw_loop_rest_dai {Espec : OracleKind} J0 J1 J gv vc vd D dp op dict ddp wbits b cp pos O s tin tout adler
    ai ao msg msgv :
  dict_dfacts J0 J1 J ->
  semax Delta_dai (dw_X0 lit_dai gv vc vd J D dp op dict ddp wbits b cp pos O s tin tout adler ai ao msg msgv)
    dw_lrest_dai (normal_ret_assert (dw_LC lit_dai gv vc vd J (Zlength D) D dp op dict ddp wbits b cp)).
Proof.
  intros DF.
  unfold dw_lrest_dai, dw_X0. abbreviate_semax.
  Intros.
  pose proof (dw_range _ _ _ DF _ _ _ _ _ _ _ _ _ _ ltac:(eassumption)) as RG.
  destruct RG as (Hpos & Hn & HO & Hb & RD & RO & Hgz & Htin & Htout & Had).
  match goal with Hc : dw_cf _ _ _ _ _ _ _ |- _ => pose proof Hc as CF; destruct Hc as (Hn0 & HD & BD & Pdp & Pop & _) end.
  rewrite rt_api_fields_L. unfold api_fieldsL. Intros.
  forward_call (Zlength D - pos).
  { unfold max_size in *; rep_lia. }
  forward.
  forward.
  forward_call (b - Zlength O).
  { apply prop_right. apply rt_sameblock; auto. }
  { entailer!. simpl. rewrite rt_sub_arg by (auto; unfold max_u64 in *; rep_lia). reflexivity. }
  { unfold max_u64 in *; rep_lia. }
  forward.
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre;
    [ | apply (dw_loop_call_dai J0 J1 J lit_dai gv vc vd D dp op dict ddp wbits b cp pos O s tin tout adler msg msgv DF) ].
  unfold dw_X1.
  assert (Hinb : Zlength (dpiece D pos) = Z.min (Zlength D - pos) Int.max_unsigned)
    by (unfold dpiece, clipz, umax; rewrite Zlength_sublist; rep_lia).
  assert (Hcl : clipz (b - Zlength O) = Z.min (b - Zlength O) Int.max_unsigned) by reflexivity.
  rewrite <- Hinb, <- Hcl.
  assert (U1 : u32_ok (Zlength (dpiece D pos))) by (rewrite Hinb; unfold u32_ok; rep_lia).
  assert (U2 : u32_ok (clipz (b - Zlength O))) by (rewrite Hcl; unfold u32_ok, max_u64 in *; rep_lia).
  sep_apply (rt_api_fields_fold vc (offset_val pos dp) (Zlength (dpiece D pos)) tin (offset_val (Zlength O) cp)
               (clipz (b - Zlength O)) tout msgv adler U1 ltac:(assumption) U2 ltac:(assumption) ltac:(assumption)).
  entailer!.
Qed.
