(* Law rt_partial, main: statements 13-17 (out_size = deflateBound_z(&compressor, data_len), compressed =
   malloc(out_size) and `return 0` if NULL, next_in = data, next_out = compressed) (rpd_A13 -> rpd_LI at pos 0,
   DFacts.cd_bound). *)
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
Require Import Zlib.proof.harness.clip_streams.RPKit.
Require Import Zlib.proof.harness.clip_streams.RPDKit.
Require Import Zlib.proof.harness.clip_streams.RPDMem.
Require Import Zlib.harness.rt_partial.code.
#[local] Existing Instance CS.CS.
Local Open Scope logic.

Ltac simplify_remove_localdef_temp ::= rpd_rlt.

(* the gzip header of a state without one: nothing *)
Lemma rpd_hdr_add (P : mpred) s hx : d_gzhead s = None -> P |-- P * hdr_at (Some s) nullval hx.
Proof. intros H. unfold hdr_at. rewrite H. entailer!. Qed.
Lemma rpd_hdr_drop s hx : d_gzhead s = None -> hdr_at (Some s) nullval hx |-- emp.
Proof. intros H. unfold hdr_at. rewrite H. entailer!. Qed.

(* api_fields: next_in and the rest *)
Lemma rpd_af_split vc ni ai tin no ao tout msgv adler :
  api_fields vc ni ai tin no ao tout msgv adler =
  !! (u32_ok ai /\ u64_ok tin /\ u32_ok ao /\ u64_ok tout /\ u64_ok adler) &&
  (@field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT Zlib.deflate.code._next_in) ni vc *
   (@field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT Zlib.deflate.code._avail_in) (vi ai) vc *
    @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT Zlib.deflate.code._total_in) (vl tin) vc *
    @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT Zlib.deflate.code._next_out) no vc *
    @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT Zlib.deflate.code._avail_out) (vi ao) vc *
    @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT Zlib.deflate.code._total_out) (vl tout) vc *
    @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT Zlib.deflate.code._msg) msgv vc *
    @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT Zlib.deflate.code._adler) (vl adler) vc)).
Proof. unfold api_fields. apply pred_ext; entailer!. Qed.

Lemma rpd_af_fold vc ni ai tin no ao tout msgv adler :
  u32_ok ai -> u64_ok tin -> u32_ok ao -> u64_ok tout -> u64_ok adler ->
  @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT Zlib.deflate.code._next_in) ni vc *
  @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT Zlib.deflate.code._avail_in) (vi ai) vc *
  @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT Zlib.deflate.code._total_in) (vl tin) vc *
  @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT Zlib.deflate.code._next_out) no vc *
  @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT Zlib.deflate.code._avail_out) (vi ao) vc *
  @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT Zlib.deflate.code._total_out) (vl tout) vc *
  @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT Zlib.deflate.code._msg) msgv vc *
  @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT Zlib.deflate.code._adler) (vl adler) vc
  |-- api_fields vc ni ai tin no ao tout msgv adler.
Proof. intros. unfold api_fields. entailer!. Qed.


Lemma rpd_seg_bound : rpd_bound_stmt.
Proof.
  intros Espec J0 J gv vc vd n D dp ep op wbits s tin tout adler msg msgv DF K.
  unfold rpd_seg13, rpd_A13, POST_B, POST_rp. abbreviate_semax.
  Intros.
  assert (Hrb : rbytes D) by (eapply Forall_impl; [ | eassumption]; simpl; intros; rep_lia).
  destruct (cd_bound _ _ DF wbits s tin tout adler n ltac:(assumption) ltac:(assumption)) as (b & Hb & Hbr & HJ).
  rewrite rpd_af_split. Intros.
  sep_apply (rpd_hdr_add (mem_mgr gv) s (Ews, nullval, nullval, nullval) ltac:(assumption)).
  forward_call (Some s, vc, nullval, nullval, (Ews, nullval, nullval, nullval), n, b, gv).
  { cancel. }
  { unfold u64_ok, max_size in *. repeat split; first [exact Hb | rep_lia]. }
  sep_apply (rpd_hdr_drop s (Ews, nullval, nullval, nullval) ltac:(assumption)).
  sep_apply (rpd_af_fold vc nullval 0 tin nullval 0 tout msgv adler); auto.
  forward_call (tarray tuchar b, gv).
  { simpl. rewrite Z.max_r by lia. unfold max_u64 in *; rep_lia. }
  Intros cp.
  destruct (eq_dec cp nullval) as [PC|PC].
  { subst cp. forward_if.
    { sep_apply (rpd_strm_ret (Some s) vc nullval gv nullval 0 tin nullval 0 tout msgv adler). ret0. }
    { rpd_bad. } }
  Intros.
  forward_if.
  { rpd_bad. }
  rewrite rpd_api_fields_L. unfold api_fieldsL. Intros.
  forward. forward.
  assert_PROP (isptr cp) as Pcp by entailer!.
  sep_apply (rpd_api_fields_fold vc dp 0 tin cp 0 tout msgv adler); auto.
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre; [ | apply (K b cp)].
  unfold rpd_LI. Exists 0 (@nil Z) s tin tout adler 0 0 msg msgv.
  unfold rpd_comp. rewrite !isptr_offset_val_zero by auto.
  change (Zlength (@nil Z)) with 0. rewrite Z.sub_0_r.
  entailer!.
Qed.
