(* Laws rt_dictionary and api_dict_id, main (DWKit.v): statement 15 (rt_dictionary's numbers; 14 in api_dict_id), deflateSetDictionary(&compressor, dict, (uInt) dict_len) and its test (A12 -> A13, DWFacts.dw_dict), in each program's context (the same proof). *)
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
Require Import Zlib.proof.harness.dictionary_w.DWCS.
Require Import Zlib.proof.harness.dictionary_w.DWFacts.
Require Import Zlib.proof.harness.dictionary_w.DWKit.
#[local] Existing Instance CS.CS.
Local Open Scope logic.

Ltac simplify_remove_localdef_temp ::= rt_rlt.

(* the dictionary object of the harness (at the law's compspecs) is the object deflateSetDictionary reads (at the
   deflate API's) *)
Lemma dw_dict_obj (dict : list Z) (ddp : val) :
  1 <= Zlength dict -> is_bytes dict ->
  data_at Ews (tarray tuchar (Zlength dict)) (bytes_rep dict) ddp = opt_obj Ews (Some dict) ddp.
Proof.
  intros L B. unfold opt_obj.
  replace (Zlength dict =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite <- rt_bytes_dcs. unfold bytes_rep.
  apply pred_ext; entailer!.
  eapply Forall_impl; [ | exact B]. simpl. intros; rep_lia.
Qed.

(* the normal exit of a segment whose postcondition overrides the normal one of main's *)
Lemma dw_override_normal Delta (P Q : environ -> mpred) (R : ret_assert) :
  ENTAIL Delta, P |-- Q -> ENTAIL Delta, P |-- RA_normal (overridePost Q R).
Proof. intros H. destruct R. exact H. Qed.

(* rt_dictionary *)
Lemma seg_dict_drt_ok : seg_dict_drt_stmt.
Proof.
  intros Espec J0 J1 J gv vc vd n D dp op dict ddp wbits s tin tout adler msg msgv DF.
  unfold seg_dict_drt, A12, A13, POST_drt. abbreviate_semax.
  Intros.
  pose proof H as Hcf. destruct Hcf as (Hn & HD & HbD & Pdp & Pop & Hdl & Hbd & Pddp & Hw).
  assert (Hrd : rbytes dict) by (eapply Forall_impl; [ | exact Hbd]; simpl; intros; rep_lia).
  destruct (dw_dict _ _ _ DF wbits s tin tout adler dict 0 0 msg H0 Hrd ltac:(unfold dict_max in *; lia)
              ltac:(unfold umax; lia) ltac:(unfold umax; lia)) as (s' & z' & Hc & HJ1).
  rewrite (dw_dict_obj dict ddp) by (auto; lia).
  unfold R_of. Intros.
  forward_call (Some s, vc, nullval, nullval, 0, tin, nullval, 0, tout, msgv, msg, adler,
                ddp, Ews, dict, (Some s', z', Z_OK), gv).
  { entailer!. cbv [firstn Datatypes.length typeof eval_cast]. simpl.
    destruct vc; try contradiction; destruct ddp; try contradiction; simpl;
    rewrite Int64.Z_mod_modulus_eq, Z.mod_small by (unfold dict_max in *; rep_lia); reflexivity. }
  { split; [unfold dict_max in *; rep_lia | ].
    unfold on_state, c_on_state.
    change (zmk [] 0 0 tin 0 tout adler msg) with (rzcall [] 0 0 tin 0 tout adler msg).
    rewrite Hc. reflexivity. }
  cbn [fst snd]. Intros msgv'.
  forward_if.
  { discriminate. }
  forward. apply dw_override_normal.
  Exists s' (z_total_in z') (z_total_out z') (z_adler z') (z_avail_in z') (z_avail_out z') (z_msg z') msgv'.
  rewrite <- (dw_dict_obj dict ddp) by (auto; lia). unfold R_of.
  entailer!.
Qed.

(* api_dict_id: the same proof with its own statement, context and literal *)
Lemma seg_dict_dai_ok : seg_dict_dai_stmt.
Proof.
  intros Espec J0 J1 J gv vc vd n D dp op dict ddp wbits s tin tout adler msg msgv DF.
  unfold seg_dict_dai, A12, A13, POST_dai. abbreviate_semax.
  Intros.
  pose proof H as Hcf. destruct Hcf as (Hn & HD & HbD & Pdp & Pop & Hdl & Hbd & Pddp & Hw).
  assert (Hrd : rbytes dict) by (eapply Forall_impl; [ | exact Hbd]; simpl; intros; rep_lia).
  destruct (dw_dict _ _ _ DF wbits s tin tout adler dict 0 0 msg H0 Hrd ltac:(unfold dict_max in *; lia)
              ltac:(unfold umax; lia) ltac:(unfold umax; lia)) as (s' & z' & Hc & HJ1).
  rewrite (dw_dict_obj dict ddp) by (auto; lia).
  unfold R_of. Intros.
  forward_call (Some s, vc, nullval, nullval, 0, tin, nullval, 0, tout, msgv, msg, adler,
                ddp, Ews, dict, (Some s', z', Z_OK), gv).
  { entailer!. cbv [firstn Datatypes.length typeof eval_cast]. simpl.
    destruct vc; try contradiction; destruct ddp; try contradiction; simpl;
    rewrite Int64.Z_mod_modulus_eq, Z.mod_small by (unfold dict_max in *; rep_lia); reflexivity. }
  { split; [unfold dict_max in *; rep_lia | ].
    unfold on_state, c_on_state.
    change (zmk [] 0 0 tin 0 tout adler msg) with (rzcall [] 0 0 tin 0 tout adler msg).
    rewrite Hc. reflexivity. }
  cbn [fst snd]. Intros msgv'.
  forward_if.
  { discriminate. }
  forward. apply dw_override_normal.
  Exists s' (z_total_in z') (z_total_out z') (z_adler z') (z_avail_in z') (z_avail_out z') (z_msg z') msgv'.
  rewrite <- (dw_dict_obj dict ddp) by (auto; lia). unfold R_of.
  entailer!.
Qed.

Lemma seg_dict_ok : seg_dict_drt_stmt /\ seg_dict_dai_stmt.
Proof. exact (conj seg_dict_drt_ok seg_dict_dai_ok). Qed.
