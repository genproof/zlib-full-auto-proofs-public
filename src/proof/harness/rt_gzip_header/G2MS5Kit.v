(* Law rt_gzip_header on the round-2 harness, main's body, segment 5: the lemmas of G2MainSeg5.v (the
   decompressor and got at the compspecs of new_stream, inflateInit2_ and inflateGetHeader, the stream after
   inflateInit2_, the header given to inflateGetHeader). Round 1's MainSeg6Kit.v on the round-2 kit: got's
   buffers may now hold up to 2^32 - 1 bytes (RTH8Spec.hwf8 allows any uInt size). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.GlobalsInit.
Require Zlib.proof.deflate.DCS Zlib.proof.deflate.Rep.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_gzip_header.CS.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainDefs.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainKit.
Require Zlib.units.Compress Zlib.units.Inflate.
Require Zlib.proof.inflate_api.Spec5.
Require Zlib.proof.roundtrip.RTH8Spec.
Require Import Zlib.harness.rt_gzip_header.code.
#[local] Existing Instance Zlib.proof.harness.rt_gzip_header.CS.CS.
Local Open Scope logic.

#[export] Instance G2MS5_CC_compress : change_composite_env Zlib.units.Compress.CS CS.
  make_cs_preserve Zlib.units.Compress.CS CS. Defined.

(** ** The local decompressor at the compspecs of its users *)

(* new_stream sees it at the compress unit's compspecs, inflate.c at Inflate.CS, main at CS *)
Lemma ms5_cs_compress sh (v : @reptype Zlib.units.Compress.CS t_zs) (p : val) :
  @data_at Zlib.units.Compress.CS sh t_zs v p = @data_at CS sh t_z v p.
Proof.
  apply equal_f. apply (@data_at_change_composite _ _ G2MS5_CC_compress); [apply JMeq_refl | reflexivity].
Qed.

Lemma ms5_cs_inflate sh (v : @reptype Zlib.units.Inflate.CS Zlib.proof.inflate.Rep.t_strm) (p : val) :
  @data_at Zlib.units.Inflate.CS sh Zlib.proof.inflate.Rep.t_strm v p = @data_at CS sh t_z v p.
Proof.
  apply equal_f. apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity].
Qed.

(* the uninitialized local as new_stream's precondition *)
Lemma ms5_strm_undef (p : val) :
  data_at_ Tsh t_z p =
  @data_at Zlib.units.Compress.CS Tsh t_zs
    (zs_val Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef) p.
Proof. unfold data_at_. rewrite ms5_cs_compress. reflexivity. Qed.

(* the harness's ZLIB_VERSION literal: deflate's view (DCS.CS) and inflate's (Inflate.CS) *)
Lemma ms5_ver_cs sh n (v : list val) q :
  @data_at Zlib.proof.deflate.DCS.CS sh (tarray tschar n) v q = @data_at Zlib.units.Inflate.CS sh (tarray tschar n) v q.
Proof.
  transitivity (@data_at CS sh (tarray tschar n) v q).
  - apply equal_f. apply (@data_at_change_composite _ _ CC_dcs); [apply JMeq_refl | reflexivity].
  - symmetry. apply equal_f. apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity].
Qed.

(* inflateInit2_ with window_bits 25..31: accepted, a gzip-only stream (wrap 6: gzip bit set, zlib bit clear)
   in mode HEAD *)
Lemma ms5_init_facts sp w : 25 <= w <= 31 ->
  AM.wbits_ok w = true /\
  IR.i_wrap (S5.l_s (S5.init_live sp w)) = 6 /\
  IR.i_mode (S5.l_s (S5.init_live sp w)) = Zlib.proof.inflate.Model.HEAD.
Proof.
  intros Hw. assert (w = 25 \/ w = 26 \/ w = 27 \/ w = 28 \/ w = 29 \/ w = 30 \/ w = 31) as T by lia.
  repeat destruct T as [-> | T]; [repeat split; reflexivity .. | subst; repeat split; reflexivity].
Qed.

(** ** got as inflateGetHeader takes it *)

Lemma ms5_head_cs sh (v : @reptype Zlib.units.Inflate.CS Zlib.proof.inflate.Rep.t_head) (p : val) :
  @data_at Zlib.units.Inflate.CS sh Zlib.proof.inflate.Rep.t_head v p = @data_at CS sh t_g v p.
Proof.
  apply equal_f. apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity].
Qed.

Lemma ms5_tok_cs sh n q :
  @malloc_token Zlib.units.Inflate.CS sh (tarray tuchar n) q = @malloc_token CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_inflate). reflexivity. Qed.

(* got with its three fresh buffers: the header of h0 g with every other field and every byte undefined *)
Lemma ms5_raw g vg :
  gs_ok g ->
  data_at Tsh t_g (gval g) vg * data_at_ Ews (tarray tuchar (g_xl g)) (g_gxp g) *
  data_at_ Ews (tarray tuchar (g_nl g + 1)) (g_gnp g) * data_at_ Ews (tarray tuchar (g_cl g + 1)) (g_gcp g)
  |-- RTHSpec.hraw6 Tsh vg (g_gxp g) (g_gnp g) (g_gcp g) (h0 g).
Proof.
  intros (Hx & Hn & Hc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Px & Pn & Pc & _).
  unfold RTHSpec.hraw6, RTHSpec.hbuf6, h0. cbn [IR.h_xp IR.h_np IR.h_cp IR.h_extra_max IR.h_name_max IR.h_comm_max].
  Exists Vundef Vundef Vundef Vundef Vundef Vundef Vundef.
  Exists (Zrepeat Vundef (g_xl g)) (Zrepeat Vundef (g_nl g + 1)) (Zrepeat Vundef (g_cl g + 1)).
  rewrite !if_false by (intros E; rewrite E in *; contradiction).
  rewrite ms5_head_cs, !(data_at_tuchar_cs Zlib.units.Inflate.CS CS).
  unfold data_at_. simpl default_val. unfold Zrepeat.
  rewrite !Zlength_repeat' by lia.
  unfold gval. entailer!.
Qed.

(* the malloc token of a buffer: inflate's token of a zero-size one (btok), main's of the others (nbtok) *)
Lemma ms5_tok q n : q <> nullval ->
  malloc_token Ews (tarray tuchar n) q |-- Zlib.proof.inflate.CaseHyps5.btok q n * nbtok q n.
Proof.
  intros Nq. unfold Zlib.proof.inflate.CaseHyps5.btok, nbtok. rewrite if_false by auto.
  destruct (zeq n 0).
  - subst. rewrite ms5_tok_cs. cancel.
  - cancel.
Qed.

Lemma ms5_toks g :
  gs_ok g ->
  malloc_token Ews (tarray tuchar (g_xl g)) (g_gxp g) * malloc_token Ews (tarray tuchar (g_nl g + 1)) (g_gnp g) *
  malloc_token Ews (tarray tuchar (g_cl g + 1)) (g_gcp g)
  |-- S5.hdr_btoks (g_gxp g) (g_gnp g) (g_gcp g) (h0 g) * gtoks g.
Proof.
  intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Px & Pn & Pc & _).
  unfold S5.hdr_btoks, gtoks, h0. cbn [IR.h_extra_max IR.h_name_max IR.h_comm_max].
  sep_apply (ms5_tok (g_gxp g) (g_xl g) ltac:(intros E; rewrite E in Px; exact Px)).
  sep_apply (ms5_tok (g_gnp g) (g_nl g + 1) ltac:(intros E; rewrite E in Pn; exact Pn)).
  sep_apply (ms5_tok (g_gcp g) (g_cl g + 1) ltac:(intros E; rewrite E in Pc; exact Pc)).
  cancel.
Qed.

(* h0 g is a header of buffers of any uInt size *)
Lemma ms5_hwf g : gs_ok g -> RTH8Spec.hwf8 (h0 g).
Proof.
  intros (Hx & Hn & Hc & _).
  unfold RTH8Spec.hwf8, h0, Zlib.proof.inflate.Inv.srange, Zlib.proof.inflate.Inv.lrange,
    Zlib.proof.inflate.Inv.urange.
  cbn [IR.h_text IR.h_time IR.h_xflags IR.h_os IR.h_extra_len IR.h_extra_max IR.h_name_max IR.h_comm_max
       IR.h_xbuf IR.h_nbuf IR.h_cbuf IR.h_hcrc IR.h_done].
  rewrite !Zlength_Zrepeat by lia.
  repeat split; try rep_lia; unfold Zrepeat; apply Forall_repeat; rep_lia.
Qed.

(** ** The stream after inflateInit2_ *)

(* the decompressor's fields as new_stream left them *)
Definition ms5_r0 : S5.rawf :=
  S5.RF nullval (Vint (Int.repr 0)) Vundef nullval (Vint (Int.repr 0)) Vundef Vundef Vundef Vundef.

(* and after a successful inflateInit2_ of a gzip-only stream (adler = wrap & 1 = 0) *)
Definition ms5_z0 : AM.zfields := AM.ZF nullval 0 0 nullval 0 0 None 0 0 Vundef.

Lemma ms5_izinit : izinit ms5_z0.
Proof. unfold izinit, S5.zf_ok, ms5_z0; cbn; repeat split; first [rep_lia | reflexivity]. Qed.

Lemma ms5_istream gv vd sp w :
  vd <> nullval -> IR.i_wrap (S5.l_s (S5.init_live sp w)) = 6 ->
  S5.istream_raw gv Tsh vd (S5.raw_after_init ms5_r0 (S5.l_s (S5.init_live sp w))) (S5.init_live sp w)
  |-- RTH8Spec.istream8_opt gv Tsh vd ms5_z0 (Some (S5.init_live sp w)).
Proof.
  intros Nd W. unfold RTH8Spec.istream8_opt. rewrite if_false by auto.
  eapply derives_trans; [ | apply RTH8Spec.istream_8].
  rewrite <- S5.istream_raw_istream by (unfold S5.zf_ok, ms5_z0; cbn; rep_lia || reflexivity).
  unfold S5.raw_after_init. rewrite W. apply derives_refl.
Qed.
