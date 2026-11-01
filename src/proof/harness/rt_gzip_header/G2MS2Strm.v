(* Law rt_gzip_header on the round-2 harness, main's body, segment 2 (G2MainSeg2.v): the local compressor's memory
   around new_stream and deflateInit2_ (round 1's MainSeg3Strm.v on G2MainKit: the same C statements).

   new_stream (laws_common.h) sees the compressor at the compress unit's compspecs, deflate.c at DCS.CS, main at
   its own.  deflateInit2__spec_v9 takes the z_stream field by field; [g2ms2_strm_eq] is the one unfolding of the
   struct into its 14 fields and padding (unfolding the struct is slow, about 25 s: it is done once, for any
   values), from which the split after new_stream and the way back to the uninitialized struct follow. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.Rep.
Require Import Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_gzip_header.CS.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainKit.
Require Zlib.deflate.code.
Require Zlib.units.Compress.
Require Import Zlib.harness.rt_gzip_header.code.
#[local] Existing Instance Zlib.proof.harness.rt_gzip_header.CS.CS.
Local Open Scope logic.

Module DC := Zlib.deflate.code.

(* laws_common's new_stream sees the compressor at the compress unit's compspecs *)
#[export] Instance G2MS2_CC_compress : change_composite_env Zlib.units.Compress.CS CS.
  make_cs_preserve Zlib.units.Compress.CS CS. Defined.

(** ** The local compressor at the compspecs of its users *)

Lemma g2ms2_cs_compress sh (v : @reptype Zlib.units.Compress.CS t_zs) (p : val) :
  @data_at Zlib.units.Compress.CS sh t_zs v p = @data_at CS sh t_z v p.
Proof.
  apply equal_f. apply (@data_at_change_composite _ _ G2MS2_CC_compress); [apply JMeq_refl | reflexivity].
Qed.

Lemma g2ms2_cs_dcs sh (v : @reptype DCS.CS t_strm) (p : val) :
  @data_at DCS.CS sh t_strm v p = @data_at CS sh t_z v p.
Proof.
  apply equal_f. apply (@data_at_change_composite _ _ CC_dcs); [apply JMeq_refl | reflexivity].
Qed.

(* the uninitialized Ews half of the local as new_stream's precondition *)
Lemma g2ms2_strm_undef (p : val) :
  data_at_ Ews t_z p |--
  @data_at Zlib.units.Compress.CS Ews t_zs
    (zs_val Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef) p.
Proof. rewrite g2ms2_cs_compress. apply derives_refl. Qed.

Section DCSView.
#[local] Existing Instance DCS.CS.

(* the Ews z_stream is its 14 fields and its padding *)
Lemma g2ms2_strm_eq (p nin ain tin no ao tout msgv st za zf op dt ad rs : val) :
  data_at Ews t_strm (nin, (ain, (tin, (no, (ao, (tout, (msgv, (st, (za, (zf, (op, (dt, (ad, rs))))))))))))) p =
  field_at Ews t_strm (DOT DC._next_in) nin p * field_at Ews t_strm (DOT DC._avail_in) ain p *
  field_at Ews t_strm (DOT DC._total_in) tin p * field_at Ews t_strm (DOT DC._next_out) no p *
  field_at Ews t_strm (DOT DC._avail_out) ao p * field_at Ews t_strm (DOT DC._total_out) tout p *
  field_at Ews t_strm (DOT DC._msg) msgv p * field_at Ews t_strm (DOT DC._state) st p *
  field_at Ews t_strm (DOT DC._zalloc) za p * field_at Ews t_strm (DOT DC._zfree) zf p *
  field_at Ews t_strm (DOT DC._opaque) op p * field_at Ews t_strm (DOT DC._data_type) dt p *
  field_at Ews t_strm (DOT DC._adler) ad p * field_at Ews t_strm (DOT DC._reserved) rs p *
  BoundKit.strm_pad p.
Proof.
  unfold BoundKit.strm_pad. unfold_data_at (data_at _ _ _ p).
  apply pred_ext; cancel.
Qed.

(* new_stream's postcondition as deflateInit2__spec_v9's precondition pieces, the three fields the spec does not
   mention (avail_in, next_out, avail_out) and the padding *)
Lemma g2ms2_new_stream_split (p : val) :
  @data_at Zlib.units.Compress.CS Ews t_zs
    (zs_val nullval (vi 0) Vundef nullval (vi 0) Vundef Vundef Vundef nullval nullval nullval Vundef Vundef Vundef) p
  |-- field_at Ews t_strm (DOT DC._next_in) nullval p * reset_fields p Vundef Vundef Vundef Vundef *
      (field_at Ews t_strm (DOT DC._avail_in) (vi 0) p * field_at Ews t_strm (DOT DC._next_out) nullval p *
       field_at Ews t_strm (DOT DC._avail_out) (vi 0) p) *
      field_at Ews t_strm (DOT DC._zalloc) nullval p * field_at Ews t_strm (DOT DC._zfree) nullval p *
      field_at Ews t_strm (DOT DC._opaque) nullval p * field_at Ews t_strm (DOT DC._data_type) Vundef p *
      field_at Ews t_strm (DOT DC._state) Vundef p * field_at_ Ews t_strm (DOT DC._reserved) p *
      BoundKit.strm_pad p.
Proof.
  rewrite g2ms2_cs_compress, <- g2ms2_cs_dcs. unfold zs_val. rewrite g2ms2_strm_eq.
  unfold reset_fields, field_at_. cancel.
Qed.

(* the stream's fields, whatever their values, back to the whole uninitialized struct *)
Lemma g2ms2_fields_back (p nin tin tout msgv adler ai no ao st za zf op dt : val) :
  field_at Ews t_strm (DOT DC._next_in) nin p * reset_fields p tin tout msgv adler *
  (field_at Ews t_strm (DOT DC._avail_in) ai p * field_at Ews t_strm (DOT DC._next_out) no p *
   field_at Ews t_strm (DOT DC._avail_out) ao p) *
  field_at Ews t_strm (DOT DC._state) st p * field_at Ews t_strm (DOT DC._zalloc) za p *
  field_at Ews t_strm (DOT DC._zfree) zf p * field_at Ews t_strm (DOT DC._opaque) op p *
  field_at Ews t_strm (DOT DC._data_type) dt p * field_at_ Ews t_strm (DOT DC._reserved) p *
  BoundKit.strm_pad p
  |-- data_at_ Ews t_strm p.
Proof.
  eapply derives_trans; [ | apply (@data_at_data_at_ DCS.CS Ews t_strm
    (nin, (ai, (tin, (no, (ao, (tout, (msgv, (st, (za, (zf, (op, (dt, (adler, Vundef)))))))))))))) ].
  rewrite g2ms2_strm_eq. unfold reset_fields, field_at_. cancel.
Qed.

End DCSView.

(* the Ews half, back at main's compspecs, and the complement: the local *)
Lemma g2ms2_rejoin (p : val) :
  @data_at_ DCS.CS Ews t_strm p * data_at_ BoundKit.Ecomp t_z p |-- data_at_ Tsh t_z p.
Proof.
  rewrite (@data_at__change_composite DCS.CS CS CC_dcs Ews t_strm) by reflexivity.
  rewrite (BoundKit.data_at__Tsh_split t_z p). cancel.
Qed.
