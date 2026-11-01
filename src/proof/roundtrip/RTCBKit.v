(* Round-trip laws, part RT-CB: the kit of compress2_z's body: compspecs moves between compress.c's
   (Compress.CS) and deflate's (DCS.CS), the local z_stream's memory, and the model of compress2_z's loop. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Zlib.proof.compress.CSpec.
Require Zlib.units.Compress.
Require Zlib.deflate.code Zlib.compress.code.
Require Import Zlib.proof.roundtrip.RTDIface.
Require Import Zlib.proof.roundtrip.RTCSpec.
Local Open Scope logic.

#[export] Instance CC_cd : change_composite_env Zlib.units.Compress.CS DCS.CS.
Proof. make_cs_preserve Zlib.units.Compress.CS DCS.CS. Defined.

Notation CCS := Zlib.units.Compress.CS.

(* one field of the z_stream at either compspecs: rewrite every field_at at DCS.CS of the goal into CCS *)
Ltac fa_to_ccs := repeat match goal with |- context [@field_at DCS.CS ?sh ?t ?g ?v ?q] =>
  rewrite <- (@field_at_change_composite CCS DCS.CS CC_cd sh t g v v (JMeq_refl _) eq_refl) end.
Ltac fa_to_dcs := repeat match goal with |- context [@field_at CCS ?sh ?t ?g ?v ?q] =>
  rewrite (@field_at_change_composite CCS DCS.CS CC_cd sh t g v v (JMeq_refl _) eq_refl) end.

Lemma strm_cd sh p :
  @data_at_ CCS sh t_strm p = @data_at_ DCS.CS sh t_strm p.
Proof.
  unfold data_at_.
  apply equal_f. apply (@data_at_change_composite _ _ CC_cd); [apply JMeq_refl | reflexivity].
Qed.

Lemma bytes_cd sh n (v : list val) q :
  @data_at CCS sh (tarray tuchar n) v q = @data_at DCS.CS sh (tarray tuchar n) v q.
Proof. apply data_at_tuchar_cs. Qed.

Lemma tschar_cd sh n (v : list val) q :
  @data_at CCS sh (tarray tschar n) v q = @data_at DCS.CS sh (tarray tschar n) v q.
Proof.
  apply equal_f. apply (@data_at_change_composite _ _ CC_cd); [apply JMeq_refl | reflexivity].
Qed.

Definition strm_pad (sp : val) : mpred := spacer Ews 12 16 sp * spacer Ews 36 40 sp * spacer Ews 92 96 sp.

(* the local z_stream (Tsh at CCS): deflate's half (Ews, field by field at DCS.CS, with the padding) and the
   rest (comp Ews) *)
Lemma strm_open p :
  @data_at_ CCS Tsh t_strm p |--
  @data_at_ CCS (Share.comp Ews) t_strm p *
  @field_at_ DCS.CS Ews t_strm (DOT deflate.code._next_in) p *
  @field_at_ DCS.CS Ews t_strm (DOT deflate.code._avail_in) p *
  @field_at_ DCS.CS Ews t_strm (DOT deflate.code._total_in) p *
  @field_at_ DCS.CS Ews t_strm (DOT deflate.code._next_out) p *
  @field_at_ DCS.CS Ews t_strm (DOT deflate.code._avail_out) p *
  @field_at_ DCS.CS Ews t_strm (DOT deflate.code._total_out) p *
  @field_at_ DCS.CS Ews t_strm (DOT deflate.code._msg) p *
  @field_at_ DCS.CS Ews t_strm (DOT deflate.code._adler) p *
  @field_at_ DCS.CS Ews t_strm (DOT deflate.code._state) p *
  @field_at_ DCS.CS Ews t_strm (DOT deflate.code._zalloc) p *
  @field_at_ DCS.CS Ews t_strm (DOT deflate.code._zfree) p *
  @field_at_ DCS.CS Ews t_strm (DOT deflate.code._opaque) p *
  @field_at_ DCS.CS Ews t_strm (DOT deflate.code._data_type) p *
  @field_at_ DCS.CS Ews t_strm (DOT deflate.code._reserved) p * strm_pad p.
Proof.
  rewrite <- (data_at__share_join Ews (Share.comp Ews) Tsh) by apply comp_join_top.
  rewrite strm_cd with (sh := Ews).
  unfold_data_at (@data_at_ DCS.CS Ews t_strm p).
  unfold strm_pad. cancel.
Qed.

Lemma strm_close p (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 : val) :
  @data_at_ CCS (Share.comp Ews) t_strm p *
  @field_at DCS.CS Ews t_strm (DOT deflate.code._next_in) a1 p *
  @field_at DCS.CS Ews t_strm (DOT deflate.code._avail_in) a2 p *
  @field_at DCS.CS Ews t_strm (DOT deflate.code._total_in) a3 p *
  @field_at DCS.CS Ews t_strm (DOT deflate.code._next_out) a4 p *
  @field_at DCS.CS Ews t_strm (DOT deflate.code._avail_out) a5 p *
  @field_at DCS.CS Ews t_strm (DOT deflate.code._total_out) a6 p *
  @field_at DCS.CS Ews t_strm (DOT deflate.code._msg) a7 p *
  @field_at DCS.CS Ews t_strm (DOT deflate.code._adler) a8 p *
  @field_at DCS.CS Ews t_strm (DOT deflate.code._state) a9 p *
  @field_at DCS.CS Ews t_strm (DOT deflate.code._zalloc) a10 p *
  @field_at DCS.CS Ews t_strm (DOT deflate.code._zfree) a11 p *
  @field_at DCS.CS Ews t_strm (DOT deflate.code._opaque) a12 p *
  @field_at DCS.CS Ews t_strm (DOT deflate.code._data_type) a13 p *
  @field_at_ DCS.CS Ews t_strm (DOT deflate.code._reserved) p * strm_pad p
  |-- @data_at_ CCS Tsh t_strm p.
Proof.
  rewrite <- (data_at__share_join Ews (Share.comp Ews) Tsh) by apply comp_join_top.
  rewrite strm_cd with (sh := Ews).
  unfold_data_at (@data_at_ DCS.CS Ews t_strm p).
  unfold strm_pad.
  sep_apply (@field_at_field_at_ DCS.CS Ews t_strm (DOT deflate.code._next_in) a1 p).
  sep_apply (@field_at_field_at_ DCS.CS Ews t_strm (DOT deflate.code._avail_in) a2 p).
  sep_apply (@field_at_field_at_ DCS.CS Ews t_strm (DOT deflate.code._total_in) a3 p).
  sep_apply (@field_at_field_at_ DCS.CS Ews t_strm (DOT deflate.code._next_out) a4 p).
  sep_apply (@field_at_field_at_ DCS.CS Ews t_strm (DOT deflate.code._avail_out) a5 p).
  sep_apply (@field_at_field_at_ DCS.CS Ews t_strm (DOT deflate.code._total_out) a6 p).
  sep_apply (@field_at_field_at_ DCS.CS Ews t_strm (DOT deflate.code._msg) a7 p).
  sep_apply (@field_at_field_at_ DCS.CS Ews t_strm (DOT deflate.code._adler) a8 p).
  sep_apply (@field_at_field_at_ DCS.CS Ews t_strm (DOT deflate.code._state) a9 p).
  sep_apply (@field_at_field_at_ DCS.CS Ews t_strm (DOT deflate.code._zalloc) a10 p).
  sep_apply (@field_at_field_at_ DCS.CS Ews t_strm (DOT deflate.code._zfree) a11 p).
  sep_apply (@field_at_field_at_ DCS.CS Ews t_strm (DOT deflate.code._opaque) a12 p).
  sep_apply (@field_at_field_at_ DCS.CS Ews t_strm (DOT deflate.code._data_type) a13 p).
  cancel.
  unfold field_at_. simpl. cancel.
Qed.

Lemma fa__cd sh f p :
  @field_at_ CCS sh t_strm (DOT f) p = @field_at_ DCS.CS sh t_strm (DOT f) p.
Proof.
  apply equal_f. apply (@field_at__change_composite CCS DCS.CS CC_cd sh t_strm (DOT f)). reflexivity.
Qed.
