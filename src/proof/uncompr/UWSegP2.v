(* uncompress2_z for any sizes (UWSegs.v), statements 5-9: the stores into the local stream (next_in = source,
   avail_in = 0, zalloc = zfree = opaque = 0). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Uncompr Zlib.units.Inflate.
Require Import Zlib.uncompr.code.
Require Import Zlib.proof.uncompr.UWSegs.
Require Import Zlib.proof.inflate_api.Spec5.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Uncompr.CS.
Local Open Scope logic.

(* statements 5-9 followed by the rest of the body from statement 10 *)
Lemma uw_seg5_eq : uw_seg5 = ltac:(let x := eval cbv beta iota zeta delta [uw_seg5] in uw_seg5 in
  match x with Ssequence ?a (Ssequence ?b (Ssequence ?c (Ssequence ?d (Ssequence ?e _)))) =>
    exact (Ssequence a (Ssequence b (Ssequence c (Ssequence d (Ssequence e uw_seg10))))) end).
Proof. reflexivity. Qed.

(* The stores into a z_stream are much cheaper on its fields than on the whole struct: the stream is split
   into the five fields that statements 5-9 write and the rest (the other fields and the padding), and folded
   back into raw_strm after the stores. *)
Definition uw_strm_rest (v: val) : mpred :=
  spacer Tsh 12 16 v * field_at_ Tsh (Tstruct _z_stream_s noattr) (DOT _total_in) v *
  field_at_ Tsh (Tstruct _z_stream_s noattr) (DOT _next_out) v *
  field_at_ Tsh (Tstruct _z_stream_s noattr) (DOT _avail_out) v * spacer Tsh 36 40 v *
  field_at_ Tsh (Tstruct _z_stream_s noattr) (DOT _total_out) v *
  field_at_ Tsh (Tstruct _z_stream_s noattr) (DOT _msg) v *
  field_at_ Tsh (Tstruct _z_stream_s noattr) (DOT _state) v *
  field_at_ Tsh (Tstruct _z_stream_s noattr) (DOT _data_type) v * spacer Tsh 92 96 v *
  field_at_ Tsh (Tstruct _z_stream_s noattr) (DOT _adler) v *
  field_at_ Tsh (Tstruct _z_stream_s noattr) (DOT _reserved) v.

(* a z_stream as its fields and padding *)
Lemma uw_strm_eq (v a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14: val) :
  data_at Tsh (Tstruct _z_stream_s noattr)
    (a1, (a2, (a3, (a4, (a5, (a6, (a7, (a8, (a9, (a10, (a11, (a12, (a13, a14))))))))))))) v =
  field_at Tsh (Tstruct _z_stream_s noattr) (DOT _next_in) a1 v *
  field_at Tsh (Tstruct _z_stream_s noattr) (DOT _avail_in) a2 v * spacer Tsh 12 16 v *
  field_at Tsh (Tstruct _z_stream_s noattr) (DOT _total_in) a3 v *
  field_at Tsh (Tstruct _z_stream_s noattr) (DOT _next_out) a4 v *
  field_at Tsh (Tstruct _z_stream_s noattr) (DOT _avail_out) a5 v * spacer Tsh 36 40 v *
  field_at Tsh (Tstruct _z_stream_s noattr) (DOT _total_out) a6 v *
  field_at Tsh (Tstruct _z_stream_s noattr) (DOT _msg) a7 v *
  field_at Tsh (Tstruct _z_stream_s noattr) (DOT _state) a8 v *
  field_at Tsh (Tstruct _z_stream_s noattr) (DOT _zalloc) a9 v *
  field_at Tsh (Tstruct _z_stream_s noattr) (DOT _zfree) a10 v *
  field_at Tsh (Tstruct _z_stream_s noattr) (DOT _opaque) a11 v *
  field_at Tsh (Tstruct _z_stream_s noattr) (DOT _data_type) a12 v * spacer Tsh 92 96 v *
  field_at Tsh (Tstruct _z_stream_s noattr) (DOT _adler) a13 v *
  field_at Tsh (Tstruct _z_stream_s noattr) (DOT _reserved) a14 v.
Proof.
  unfold_data_at (data_at Tsh (Tstruct _z_stream_s noattr) _ v). apply pred_ext; cancel.
Qed.

(* the local stream before statement 5, split for the stores *)
Lemma uw_strm_split (v: val) :
  data_at_ Tsh (Tstruct _z_stream_s noattr) v |--
  field_at_ Tsh (Tstruct _z_stream_s noattr) (DOT _next_in) v *
  field_at_ Tsh (Tstruct _z_stream_s noattr) (DOT _avail_in) v *
  field_at_ Tsh (Tstruct _z_stream_s noattr) (DOT _zalloc) v *
  field_at_ Tsh (Tstruct _z_stream_s noattr) (DOT _zfree) v *
  field_at_ Tsh (Tstruct _z_stream_s noattr) (DOT _opaque) v * uw_strm_rest v.
Proof.
  rewrite data_at__eq. eapply derives_trans; [apply derives_refl'; apply (uw_strm_eq v) |].
  unfold uw_strm_rest. cancel.
Qed.

(* the stream after the stores, as one struct *)
Lemma uw_strm_join (v sp: val) :
  field_at Tsh (Tstruct _z_stream_s noattr) (DOT _next_in) sp v *
  field_at Tsh (Tstruct _z_stream_s noattr) (DOT _avail_in) (Vint (Int.repr 0)) v *
  field_at Tsh (Tstruct _z_stream_s noattr) (DOT _zalloc) nullval v *
  field_at Tsh (Tstruct _z_stream_s noattr) (DOT _zfree) nullval v *
  field_at Tsh (Tstruct _z_stream_s noattr) (DOT _opaque) nullval v * uw_strm_rest v |--
  data_at Tsh (Tstruct _z_stream_s noattr)
    (sp, (Vint (Int.repr 0), (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef,
     (nullval, (nullval, (nullval, (Vundef, (Vundef, Vundef))))))))))))) v.
Proof.
  rewrite uw_strm_eq. unfold uw_strm_rest. cancel.
Qed.

(* the stream after statement 9, as uw_A10 states it *)
Lemma uw_strm_fold (gv: globals) (v sp: val) :
  field_at Tsh (Tstruct _z_stream_s noattr) (DOT _next_in) sp v *
  field_at Tsh (Tstruct _z_stream_s noattr) (DOT _avail_in) (Vint (Int.repr 0)) v *
  field_at Tsh (Tstruct _z_stream_s noattr) (DOT _zalloc) nullval v *
  field_at Tsh (Tstruct _z_stream_s noattr) (DOT _zfree) nullval v *
  field_at Tsh (Tstruct _z_stream_s noattr) (DOT _opaque) nullval v * uw_strm_rest v |--
  raw_strm gv Tsh v (RF sp (Vint (Int.repr 0)) Vundef Vundef Vundef Vundef Vundef Vundef Vundef)
    Vundef Vundef nullval nullval nullval.
Proof.
  sep_apply (uw_strm_join v sp).
  unfold raw_strm. change_compspecs Zlib.units.Uncompr.CS. simpl. cancel.
Qed.

Lemma uw_p2 : uw_p2_stmt.
Proof.
  intros Espec A v F K.
  rewrite uw_seg5_eq.
  destruct A as [gv dnull dsh dp dn dc cap dlp dtok stok ssh sp sn sc src slp gsh tsh].
  unfold uw_A5, uw_A10, uw_lcl in *. abbreviate_semax.
  sep_apply (uw_strm_split v). Intros.
  forward.
  forward.
  forward.
  forward.
  forward.
  change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with nullval.
  sep_apply (uw_strm_fold gv v sp).
  eapply semax_pre; [| apply K].
  apply ENTAIL_refl.
Qed.
