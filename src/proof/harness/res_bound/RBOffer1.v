(* Law res_bound, main: the local z_stream around laws_common.h's offer (used by RBRun.part_run): the six
   fields a live stream's dstream_sp holds, and offer's precondition from the stream's fields. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.Rep Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.LawFactsW Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.deflate.Obligations.
Require Zlib.proof.harness.bound_common.BoundKit Zlib.proof.harness.deflate_bound.MainKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.res_bound.RBCS Zlib.proof.harness.res_bound.RBString Zlib.proof.harness.res_bound.RBKit.
Require Import Zlib.harness.res_bound.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

(* laws_common.h's offer is specified at the compress unit's compspecs; main's body is at DCS.CS *)
Lemma rr_strm_cs sh (v : @reptype Zlib.units.Compress.CS t_zs) (p : val) :
  @data_at Zlib.units.Compress.CS sh t_zs v p = @data_at DCS.CS sh t_strm v p.
Proof.
  apply equal_f. apply (@data_at_change_composite _ _ CC_compress_dcs); [apply JMeq_refl | reflexivity].
Qed.

(* The six fields of the z_stream that a live stream's dstream_sp holds: state, zalloc, zfree, opaque,
   data_type (inside the deflate_state's representation) and reserved. *)
Definition rr_own (p sp : val) (gv : globals) (s : dstate) : mpred :=
  field_at Ews t_strm (DOT deflate.code._state) sp p *
  field_at Ews t_strm (DOT deflate.code._zalloc) (gv deflate.code._zcalloc) p *
  field_at Ews t_strm (DOT deflate.code._zfree) (gv deflate.code._zcfree) p *
  field_at Ews t_strm (DOT deflate.code._opaque) nullval p *
  field_at Ews t_strm (DOT deflate.code._data_type) (vi (tr_data_type (fst (d_trm s)))) p *
  field_at_ Ews t_strm (DOT deflate.code._reserved) p.

(* those six fields out of dstream_sp, the rest kept as a wand (offer writes the whole struct and gives the six
   fields back unchanged) *)
Lemma rr_dstream_open (s : dstate) (p ghp sp : val) (gv : globals) :
  dstream_sp 2 (Some s) p ghp sp gv |-- rr_own p sp gv s * (rr_own p sp gv s -* dstream_sp 2 (Some s) p ghp sp gv).
Proof.
  unfold dstream_sp at 1. Intros pp. change (dstate_at' 2 s pp gv) with (dstate_at s pp gv).
  unfold dstate_at, trees_at, dtype_at. Intros.
  unfold rr_own. subst.
  cancel.
  rewrite <- wand_sepcon_adjoint.
  unfold dstream_sp. Exists pp. change (dstate_at' 2 s pp gv) with (dstate_at s pp gv).
  unfold dstate_at, trees_at, dtype_at. entailer!.
Qed.

(* offer's precondition from the stream's fields, the six fields and the padding *)
Lemma rr_offer_pre (p : val) (ai tin ao tout : Z) (msgv : val) (adler : Z) (sp : val) (gv : globals) (s : dstate) :
  api_fields p nullval ai tin nullval ao tout msgv adler * rr_own p sp gv s * BoundKit.strm_pad p
  |-- @data_at Zlib.units.Compress.CS Ews t_zs
        (zs_val nullval (vi ai) (vl tin) nullval (vi ao) (vl tout) msgv sp (gv deflate.code._zcalloc)
           (gv deflate.code._zcfree) nullval (vi (tr_data_type (fst (d_trm s)))) (vl adler) Vundef) p.
Proof.
  rewrite rr_strm_cs. unfold api_fields, rr_own, BoundKit.strm_pad. Intros. unfold_data_at (data_at _ _ _ p).
  unfold field_at_; simpl. cancel.
Qed.

