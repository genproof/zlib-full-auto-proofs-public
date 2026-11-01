(* Law rj_truncated, main: statements 17-18 (`if (code != Z_STREAM_END) return 0`, compressed_len =
   next_out - compressed), the compressor given back as the local's memory (rt_LB -> rt_DH). *)
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
Require Zlib.proof.deflate.DSpec9.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.clip_streams.CS.
Require Import Zlib.proof.harness.clip_streams.Globals.
Require Import Zlib.proof.harness.clip_streams.DFacts.
Require Import Zlib.proof.harness.clip_streams.MainDefs.
Require Import Zlib.proof.harness.clip_streams.RTKit.
Require Import Zlib.proof.harness.clip_streams.RTMem.
Require Import Zlib.harness.rj_truncated.code.
#[local] Existing Instance CS.CS.
Local Open Scope logic.

Ltac simplify_remove_localdef_temp ::= rt_rlt.


(* compressed_len = next_out - compressed, next_out = compressed + k inside the object *)
Lemma rt_sub_ptr (p : val) k : isptr p -> 0 <= k <= Ptrofs.max_unsigned ->
  force_val (sem_binary_operation' Osub (tptr tuchar) (tptr tuchar) (offset_val k p) p) = Vlong (Int64.repr k).
Proof.
  intros Pp Hk. destruct p; try contradiction. simpl.
  unfold sem_sub_pp. simpl. rewrite if_true by auto. simpl.
  f_equal. rewrite Ptrofs.sub_add_l, Ptrofs.sub_idem, Ptrofs.add_zero_l.
  unfold Ptrofs.divs. rewrite (Ptrofs.signed_repr 1) by rep_lia. rewrite Z.quot_1_r, Ptrofs.repr_signed.
  rewrite Vptrofs_unfold_true by reflexivity. unfold Ptrofs.to_int64.
  rewrite Ptrofs.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma seg_end_ok : seg_end_stmt.
Proof.
  intros Espec gv vc vd n D dp op wbits b cp K.
  unfold rt_seg17, rt_LB, POST_B, POST_rt. abbreviate_semax.
  Intros code O os nin ai tin ao tout adler msgv.
  forward_if.
  { sep_apply (rt_strm_ret os vc nullval gv nin ai tin (offset_val (Zlength O) cp) ao tout msgv adler).
    ret0. }
  rewrite rt_api_fields_L. unfold api_fieldsL. Intros.
  forward.
  forward.
  { unfold rt_comp. entailer!. apply prop_right. destruct cp; try contradiction. unfold sameblock; simpl.
    destruct (peq b0 b0); [reflexivity | congruence]. }
  assert (code = 1) by (apply repr_inj_signed; auto; unfold rs32 in *; rep_lia).
  subst code.
  rewrite rt_sub_ptr by (auto; unfold max_u64 in *; rep_lia).
  sep_apply (rt_api_fields_fold vc nin ai tin (offset_val (Zlength O) cp) ao tout msgv adler); auto.
  sep_apply (rt_strm_ret os vc nullval gv nin ai tin (offset_val (Zlength O) cp) ao tout msgv adler).
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre; [ | apply (K O)].
  unfold rt_DH, rt_comp.
  match goal with Hf : 1 = Z_STREAM_END -> _ |- _ => specialize (Hf eq_refl) end.
  entailer!.
  match goal with Hb : is_bytes D |- _ => eapply Forall_impl; [ | exact Hb] end. simpl. intros; rep_lia.
Qed.
