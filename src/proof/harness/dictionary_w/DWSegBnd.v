(* Laws rt_dictionary and api_dict_id, main (DWKit.v): statements 16-20 (rt_dictionary's numbers; 15-19 in api_dict_id), out_size = deflateBound_z(&compressor, data_len), compressed = malloc(out_size) and its NULL test, next_in = data, next_out = compressed (A13 -> LI at pos 0, DWFacts.dw_bound), in each program's context (the same proof). *)
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
Require Import Zlib.proof.harness.clip_streams.RTKit.
Require Import Zlib.proof.harness.clip_streams.RTMem.
Require Import Zlib.proof.harness.clip_streams.RTSegBnd.
Require Import Zlib.proof.harness.dictionary_w.DWFacts.
Require Import Zlib.proof.harness.dictionary_w.DWKit.
#[local] Existing Instance CS.CS.
Local Open Scope logic.

Ltac simplify_remove_localdef_temp ::= rt_rlt.

(* rt_dictionary *)
Lemma seg_bnd_drt_ok : seg_bnd_drt_stmt.
Proof.
  intros Espec J0 J1 J gv vc vd n D dp op dict ddp wbits s tin tout adler ai ao msg msgv DF.
  unfold seg_bnd_drt, A13, POST_drt, POST_of. abbreviate_semax.
  Intros.
  destruct H as (Hn & HD & HbD & Hdp & Hop & Hdl & Hbd & Hddp & Hw).
  assert (Hrb : rbytes D) by (eapply Forall_impl; [ | eassumption]; simpl; intros; rep_lia).
  destruct (dw_range1 _ _ _ DF _ _ _ _ _ _ H0) as (Hgz & Htin & Htout & Had).
  destruct (dw_bound _ _ _ DF wbits dict s tin tout adler n H0 Hn) as (b & Hb & Hbr & HJ).
  rewrite rt_af_split. Intros.
  sep_apply (rt_hdr_add (mem_mgr gv) s (Ews, nullval, nullval, nullval) Hgz).
  forward_call (Some s, vc, nullval, nullval, (Ews, nullval, nullval, nullval), n, b, gv).
  { cancel. }
  { unfold u64_ok, max_size in *. repeat split; first [exact Hb | rep_lia]. }
  sep_apply (rt_hdr_drop s (Ews, nullval, nullval, nullval) Hgz).
  sep_apply (rt_af_fold vc nullval ai tin nullval ao tout msgv adler); auto.
  forward_call (tarray tuchar b, gv).
  { simpl. rewrite Z.max_r by lia. unfold max_u64 in *; rep_lia. }
  Intros cp.
  destruct (eq_dec cp nullval) as [PC|PC].
  { subst cp. forward_if.
    { sep_apply (rt_strm_ret (Some s) vc nullval gv nullval ai tin nullval ao tout msgv adler). ret0. }
    { rt_bad. } }
  Intros.
  forward_if.
  { rt_bad. }
  rewrite rt_api_fields_L. unfold api_fieldsL. Intros.
  forward. forward.
  assert_PROP (isptr cp) as Pcp by entailer!.
  sep_apply (rt_api_fields_fold vc dp ai tin cp ao tout msgv adler); auto.
  Exists b cp. unfold LI. Exists 0 (@nil Z) s tin tout adler ai ao msg msgv.
  unfold rt_comp. rewrite !isptr_offset_val_zero by auto.
  change (Zlength (@nil Z)) with 0. rewrite Z.sub_0_r.
  assert (Hcf : dw_cf n D dp op dict ddp wbits) by (unfold dw_cf; tauto).
  entailer!.
Qed.

(* api_dict_id: the same proof with its own statement, context and literal *)
Lemma seg_bnd_dai_ok : seg_bnd_dai_stmt.
Proof.
  intros Espec J0 J1 J gv vc vd n D dp op dict ddp wbits s tin tout adler ai ao msg msgv DF.
  unfold seg_bnd_dai, A13, POST_dai, POST_of. abbreviate_semax.
  Intros.
  destruct H as (Hn & HD & HbD & Hdp & Hop & Hdl & Hbd & Hddp & Hw).
  assert (Hrb : rbytes D) by (eapply Forall_impl; [ | eassumption]; simpl; intros; rep_lia).
  destruct (dw_range1 _ _ _ DF _ _ _ _ _ _ H0) as (Hgz & Htin & Htout & Had).
  destruct (dw_bound _ _ _ DF wbits dict s tin tout adler n H0 Hn) as (b & Hb & Hbr & HJ).
  rewrite rt_af_split. Intros.
  sep_apply (rt_hdr_add (mem_mgr gv) s (Ews, nullval, nullval, nullval) Hgz).
  forward_call (Some s, vc, nullval, nullval, (Ews, nullval, nullval, nullval), n, b, gv).
  { cancel. }
  { unfold u64_ok, max_size in *. repeat split; first [exact Hb | rep_lia]. }
  sep_apply (rt_hdr_drop s (Ews, nullval, nullval, nullval) Hgz).
  sep_apply (rt_af_fold vc nullval ai tin nullval ao tout msgv adler); auto.
  forward_call (tarray tuchar b, gv).
  { simpl. rewrite Z.max_r by lia. unfold max_u64 in *; rep_lia. }
  Intros cp.
  destruct (eq_dec cp nullval) as [PC|PC].
  { subst cp. forward_if.
    { sep_apply (rt_strm_ret (Some s) vc nullval gv nullval ai tin nullval ao tout msgv adler). ret0. }
    { rt_bad. } }
  Intros.
  forward_if.
  { rt_bad. }
  rewrite rt_api_fields_L. unfold api_fieldsL. Intros.
  forward. forward.
  assert_PROP (isptr cp) as Pcp by entailer!.
  sep_apply (rt_api_fields_fold vc dp ai tin cp ao tout msgv adler); auto.
  Exists b cp. unfold LI. Exists 0 (@nil Z) s tin tout adler ai ao msg msgv.
  unfold rt_comp. rewrite !isptr_offset_val_zero by auto.
  change (Zlength (@nil Z)) with 0. rewrite Z.sub_0_r.
  assert (Hcf : dw_cf n D dp op dict ddp wbits) by (unfold dw_cf; tauto).
  entailer!.
Qed.

Lemma seg_bnd_ok : seg_bnd_drt_stmt /\ seg_bnd_dai_stmt.
Proof. exact (conj seg_bnd_drt_ok seg_bnd_dai_ok). Qed.
