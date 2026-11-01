(* Laws rt_dictionary and api_dict_id, main (DWKit.v): statements 22-23 (rt_dictionary's numbers; 21-22 in api_dict_id), `if (code != Z_STREAM_END) return 0` and compressed_len = next_out - compressed, the compressor given back as the local's memory (LB -> DH), in each program's context. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.clip_streams.CS.
Require Import Zlib.proof.harness.clip_streams.RTKit.
Require Import Zlib.proof.harness.clip_streams.RTMem.
Require Import Zlib.proof.harness.clip_streams.RTSegEnd.
Require Import Zlib.proof.harness.dictionary_w.DWFacts.
Require Import Zlib.proof.harness.dictionary_w.DWKit.
#[local] Existing Instance CS.CS.
Local Open Scope logic.

Ltac simplify_remove_localdef_temp ::= rt_rlt.

(* rt_dictionary: compressed_len's load of next_out in _t'39 *)
Lemma seg_end_drt_ok : seg_end_drt_stmt.
Proof.
  intros Espec gv vc vd n D dp op dict ddp wbits b cp.
  unfold seg_end_drt, LB. abbreviate_semax.
  Intros code O os nin ai tin ao tout adler msgv.
  forward_if.
  { sep_apply (rt_strm_ret os vc nullval gv nin ai tin (offset_val (Zlength O) cp) ao tout msgv adler).
    unfold POST_drt, POST_of. forward. Exists (Int.repr 0). entailer!. }
  rewrite rt_api_fields_L. unfold api_fieldsL. Intros.
  forward.
  forward.
  { unfold rt_comp. entailer!. apply prop_right. destruct cp; try contradiction. unfold sameblock; simpl.
    destruct (peq b0 b0); [reflexivity | congruence]. }
  assert (code = 1) by (apply repr_inj_signed; auto; unfold rs32 in *; rep_lia).
  subst code. specialize (H4 eq_refl).
  rewrite rt_sub_ptr by (auto; unfold max_u64 in *; rep_lia).
  sep_apply (rt_api_fields_fold vc nin ai tin (offset_val (Zlength O) cp) ao tout msgv adler); auto.
  sep_apply (rt_strm_ret os vc nullval gv nin ai tin (offset_val (Zlength O) cp) ao tout msgv adler).
  destruct POST_drt as [? ? ? ?] eqn:EP. cbv beta iota. clear EP.
  Exists O. unfold DH, dw_hf, rt_comp.
  assert (HrD : rbytes D)
    by (destruct H as (_ & _ & HbD & _); eapply Forall_impl; [ | exact HbD]; simpl; intros; rep_lia).
  entailer!.
Qed.

(* api_dict_id: the same statements, the load in _t'28 *)
Lemma seg_end_dai_ok : seg_end_dai_stmt.
Proof.
  intros Espec gv vc vd n D dp op dict ddp wbits b cp.
  unfold seg_end_dai, LB. abbreviate_semax.
  Intros code O os nin ai tin ao tout adler msgv.
  forward_if.
  { sep_apply (rt_strm_ret os vc nullval gv nin ai tin (offset_val (Zlength O) cp) ao tout msgv adler).
    unfold POST_dai, POST_of. forward. Exists (Int.repr 0). entailer!. }
  rewrite rt_api_fields_L. unfold api_fieldsL. Intros.
  forward.
  forward.
  { unfold rt_comp. entailer!. apply prop_right. destruct cp; try contradiction. unfold sameblock; simpl.
    destruct (peq b0 b0); [reflexivity | congruence]. }
  assert (code = 1) by (apply repr_inj_signed; auto; unfold rs32 in *; rep_lia).
  subst code. specialize (H4 eq_refl).
  rewrite rt_sub_ptr by (auto; unfold max_u64 in *; rep_lia).
  sep_apply (rt_api_fields_fold vc nin ai tin (offset_val (Zlength O) cp) ao tout msgv adler); auto.
  sep_apply (rt_strm_ret os vc nullval gv nin ai tin (offset_val (Zlength O) cp) ao tout msgv adler).
  destruct POST_dai as [? ? ? ?] eqn:EP. cbv beta iota. clear EP.
  Exists O. unfold DH, dw_hf, rt_comp.
  assert (HrD : rbytes D)
    by (destruct H as (_ & _ & HbD & _); eapply Forall_impl; [ | exact HbD]; simpl; intros; rep_lia).
  entailer!.
Qed.

Lemma seg_end_ok : seg_end_drt_stmt /\ seg_end_dai_stmt.
Proof. exact (conj seg_end_drt_ok seg_end_dai_ok). Qed.
