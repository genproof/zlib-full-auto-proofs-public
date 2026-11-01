(* Law api_deterministic (data of any length): memory lemmas of main's proof (DetKit2.v) about main's
   z_stream locals: the moves between the compspecs of laws_common.h's specifications and DCS.CS, and offer's
   precondition from the pieces of a stream.  (In a file of their own: unfolding the z_stream at DCS.CS is slow.) *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Rep.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.GlobalsInit.
Require Zlib.proof.deflate.ApiKit.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.api_deterministic.DetCS2.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.
Module DC := Zlib.deflate.code.

(** ** Memory lemmas *)

(* laws_common.h's specifications are at the compress unit's compspecs (z_stream) and the adler32 unit's (byte
   objects); main's body is at DCS.CS *)
Lemma det_strm_cs sh (v : @reptype Zlib.units.Compress.CS t_zs) (p : val) :
  @data_at Zlib.units.Compress.CS sh t_zs v p = @data_at DCS.CS sh t_strm v p.
Proof.
  apply equal_f. apply (@data_at_change_composite _ _ CC_compress_dcs); [apply JMeq_refl | reflexivity].
Qed.

Lemma det_bytes_cs sh k (l : list val) (p : val) :
  @data_at Zlib.units.Adler32.CS sh (tarray tuchar k) l p = @data_at DCS.CS sh (tarray tuchar k) l p.
Proof.
  apply equal_f. apply (@data_at_change_composite _ _ CC_adler32_dcs); [apply JMeq_refl | reflexivity].
Qed.

Lemma det_token_cs sh k (p : val) :
  @malloc_token Zlib.units.Adler32.CS sh (tarray tuchar k) p = @malloc_token DCS.CS sh (tarray tuchar k) p.
Proof. apply equal_f. apply (@malloc_token_change_composite _ _ CC_adler32_dcs). reflexivity. Qed.

(* the uninitialized local (its Ews half) as new_stream's precondition *)
Lemma det_strm_undef (p : val) :
  data_at_ Ews t_strm p |--
  @data_at Zlib.units.Compress.CS Ews t_zs
    (zs_val Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef) p.
Proof. rewrite det_strm_cs. apply derives_refl. Qed.

(* The six fields of the z_stream that a live stream's dstream_sp holds: state, zalloc, zfree, opaque,
   data_type (inside the deflate_state's representation) and reserved. *)
Definition strm_own (p sp za zf op dt : val) : mpred :=
  field_at Ews t_strm (DOT DC._state) sp p * field_at Ews t_strm (DOT DC._zalloc) za p *
  field_at Ews t_strm (DOT DC._zfree) zf p * field_at Ews t_strm (DOT DC._opaque) op p *
  field_at Ews t_strm (DOT DC._data_type) dt p * field_at_ Ews t_strm (DOT DC._reserved) p.

(* offer's precondition from the pieces *)
Lemma det_offer_pre (p ni ai tin no ao tout msgv adler sp za zf op dt : val) :
  field_at Ews t_strm (DOT DC._next_in) ni p * reset_fields p tin tout msgv adler *
  (field_at Ews t_strm (DOT DC._avail_in) ai p * field_at Ews t_strm (DOT DC._next_out) no p *
   field_at Ews t_strm (DOT DC._avail_out) ao p) *
  strm_own p sp za zf op dt * BoundKit.strm_pad p
  |-- @data_at Zlib.units.Compress.CS Ews t_zs (zs_val ni ai tin no ao tout msgv sp za zf op dt adler Vundef) p.
Proof.
  rewrite det_strm_cs. unfold reset_fields, strm_own, BoundKit.strm_pad. unfold_data_at (data_at _ _ _ p).
  unfold field_at_; simpl. cancel.
Qed.
