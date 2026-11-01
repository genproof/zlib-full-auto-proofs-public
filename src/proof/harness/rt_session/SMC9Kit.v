(* Law rt_session (harness/rt_session.c): the lemmas of main's statements 63-72 with a gzip header (SMSegC9.v):
   the compressor and the gz_headers given back at the Z_MEM_ERROR return, the local decompressor at the
   compspecs of new_stream, inflateInit2_ and inflateGetHeader, inflateInit2_'s gzip-only stream (window_bits
   25..31), got as inflateGetHeader takes it (G2MainKit.h0's buffers: hraw6 and the malloc tokens), and the
   decompressor after main's stores next_in = input, next_out = out as RTH8Spec's istream8.
   As rt_gzip_header's G2MS5Kit.v and rt_stream's USegC.v, at this law's compspecs and on SMKit's setup. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.deflate.GlobalsInit Zlib.proof.deflate.Api_toend.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Zlib.proof.inflate.CaseHyps5.
Require Zlib.proof.roundtrip.RTHSpec Zlib.proof.roundtrip.RTH8Spec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SDFacts.
Require Import Zlib.proof.harness.rt_session.SIFacts.
Require Import Zlib.proof.harness.rt_session.SMainStmt.
Require Import Zlib.proof.harness.rt_session.SMKit.
Require Import Zlib.harness.rt_session.code.
#[local] Existing Instance SCS.CS.
Local Open Scope logic.

(** ** Main's locals given back at a return *)

(* the compressor, whatever its state and gzhead, gives back the local's memory *)
Lemma c9_comp_back (gv : globals) (vc ghp : val) (c : cst) : cstream gv vc ghp c |-- data_at_ Tsh t_z vc * TT.
Proof.
  unfold cstream, srest.
  sep_apply (BoundKit.dstream_data_at_ (Some (cs_s c)) vc ghp gv (cs_ni c) (cs_ain c) (cs_tin c) (cs_no c)
               (cs_aout c) (cs_tout c) (cs_msgv c) (cs_adler c) Api_toend.dstream_to_end).
  rewrite (@data_at__change_composite Zlib.proof.deflate.DCS.CS CS CC_dcs Ews Zlib.proof.deflate.Rep.t_strm)
    by reflexivity.
  rewrite (BoundKit.data_at__Tsh_split t_z vc). cancel.
Qed.

(* head and got, whatever they hold *)
Lemma c9_hobj_back vh u : hobj vh u |-- data_at_ Tsh t_g vh * TT.
Proof. unfold hobj. sep_apply (data_at_data_at_ Tsh t_g (hvals u) vh). cancel. Qed.

Lemma c9_graw_back vg u : graw vg u |-- data_at_ Tsh t_g vg * TT.
Proof. unfold graw. sep_apply (data_at_data_at_ Tsh t_g (gval u) vg). cancel. Qed.

(** ** The local decompressor at the compspecs of its users *)

Lemma c9_cs_compress sh (v : @reptype Zlib.units.Compress.CS t_zs) (p : val) :
  @data_at Zlib.units.Compress.CS sh t_zs v p = @data_at CS sh t_z v p.
Proof. apply equal_f. apply (@data_at_change_composite _ _ CC_compress); [apply JMeq_refl | reflexivity]. Qed.

Lemma c9_cs_inflate sh (v : @reptype Zlib.units.Inflate.CS Zlib.proof.inflate.Rep.t_strm) (p : val) :
  @data_at Zlib.units.Inflate.CS sh Zlib.proof.inflate.Rep.t_strm v p = @data_at CS sh t_z v p.
Proof. apply equal_f. apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity]. Qed.

(* the uninitialized local as new_stream's precondition *)
Lemma c9_undef (p : val) :
  data_at_ Tsh t_z p =
  @data_at Zlib.units.Compress.CS Tsh t_zs
    (zs_val Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef) p.
Proof. unfold data_at_. rewrite c9_cs_compress. reflexivity. Qed.

(* the struct after new_stream(): inflateInit2_'s raw stream *)
Definition c9_r0 : rawf :=
  RF nullval (Vint (Int.repr 0)) Vundef nullval (Vint (Int.repr 0)) Vundef Vundef Vundef Vundef.

Lemma c9_ns_raw gv p :
  @data_at Zlib.units.Compress.CS Tsh t_zs
    (zs_val nullval (Vint (Int.repr 0)) Vundef nullval (Vint (Int.repr 0)) Vundef Vundef Vundef nullval nullval
       nullval Vundef Vundef Vundef) p =
  raw_strm gv Tsh p c9_r0 Vundef Vundef nullval nullval nullval.
Proof. unfold raw_strm, c9_r0, zs_val; simpl. rewrite c9_cs_compress, c9_cs_inflate. reflexivity. Qed.

(* the harness's "1.3.2" (Rm's version_at, at deflate's compspecs) as inflateInit2_ takes it *)
Definition c9_hv : list val := map (fun c => Vint (Int.repr c)) [49; 46; 51; 46; 50; 0].

Lemma c9_version gv :
  Zlib.proof.deflate.GlobalsInit.version_at gv ___stringlit_rt_session_1 =
  @data_at Zlib.units.Inflate.CS Ers (tarray tschar (Zlength c9_hv)) c9_hv (gv ___stringlit_rt_session_1).
Proof.
  unfold Zlib.proof.deflate.GlobalsInit.version_at, c9_hv. change (Zlength _) with 6.
  transitivity (@data_at CS Ers (tarray tschar 6) (map (fun c => Vint (Int.repr c)) [49; 46; 51; 46; 50; 0])
                  (gv ___stringlit_rt_session_1)).
  - apply equal_f. apply (@data_at_change_composite _ _ CC_dcs); [apply JMeq_refl | reflexivity].
  - symmetry. apply equal_f. apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity].
Qed.

(* inflateInit2_ failed: the struct goes back to the stack frame *)
Lemma c9_init_fail gv p r ret sp w :
  isptr p -> ret <> Z_OK ->
  init_mem gv Tsh p r Vundef Vundef nullval ret sp w |-- data_at_ Tsh t_z p.
Proof.
  intros Pp Nok. unfold init_mem. rewrite if_false by (intro; subst; contradiction).
  apply Z.eqb_neq in Nok. rewrite Nok.
  destruct (ret =? Z_VERSION_ERROR); [ | destruct (ret =? Z_MEM_ERROR)];
  unfold raw_strm; rewrite c9_cs_inflate; apply data_at_data_at_.
Qed.

(** ** inflateInit2_ with a gzip header's windowBits *)

(* deflateInit2_ accepted window_bits > 15: 25..31 (24 is refused: 8 only with the zlib wrapper), unchanged by
   main's 8 -> 9 *)
Lemma c9_wb u : su_dok u -> with_head u = true -> 25 <= su_wbits u <= 31 /\ rts_iw (su_wbits u) = su_wbits u.
Proof.
  intros (_ & _ & _ & _ & Hrp & _) WH. unfold with_head in WH. apply andb_prop in WH as [W _].
  apply Z.ltb_lt in W.
  unfold rparams_ok, rwb_of, rwrap_of in Hrp.
  rewrite (proj2 (Z.ltb_ge _ 0)) in Hrp by lia. rewrite (proj2 (Z.gtb_lt _ 15)) in Hrp by lia.
  repeat rewrite andb_true_iff in Hrp.
  assert (8 <= su_wbits u - 16 /\ su_wbits u - 16 <= 15 /\ (negb (su_wbits u - 16 =? 8) || (2 =? 1))%bool = true)
    as (H8 & H15 & H24) by (rewrite <- !Z.leb_le; tauto).
  assert (su_wbits u <> 24).
  { intros E. rewrite E in H24. discriminate. }
  unfold rts_iw. rewrite (proj2 (Z.eqb_neq _ 8)) by lia. lia.
Qed.

(* the stream inflateInit2_ makes of window_bits 25..31: accepted, gzip only (wrap 6), mode HEAD *)
Lemma c9_init_facts sp w : 25 <= w <= 31 ->
  wbits_ok w = true /\ Zlib.proof.inflate.Records.i_wrap (l_s (init_live sp w)) = 6 /\
  Zlib.proof.inflate.Records.i_mode (l_s (init_live sp w)) = Zlib.proof.inflate.Model.HEAD.
Proof.
  intros Hw. assert (w = 25 \/ w = 26 \/ w = 27 \/ w = 28 \/ w = 29 \/ w = 30 \/ w = 31) as T by lia.
  repeat destruct T as [-> | T]; [repeat split; reflexivity .. | subst; repeat split; reflexivity].
Qed.

(* the stream's fields after new_stream and a successful inflateInit2_ of a gzip-only stream *)
Definition c9_z0 : zfields := ZF nullval 0 0 nullval 0 0 None 0 0 Vundef.

Lemma c9_istream gv vd sp w :
  vd <> nullval -> Zlib.proof.inflate.Records.i_wrap (l_s (init_live sp w)) = 6 ->
  istream_raw gv Tsh vd (raw_after_init c9_r0 (l_s (init_live sp w))) (init_live sp w)
  |-- Zlib.proof.roundtrip.RTH8Spec.istream8_opt gv Tsh vd c9_z0 (Some (init_live sp w)).
Proof.
  intros Nd W. unfold Zlib.proof.roundtrip.RTH8Spec.istream8_opt. rewrite if_false by auto.
  eapply derives_trans; [ | apply Zlib.proof.roundtrip.RTH8Spec.istream_8].
  rewrite <- istream_raw_istream by (unfold zf_ok, c9_z0; cbn; rep_lia || reflexivity).
  unfold raw_after_init. rewrite W. apply derives_refl.
Qed.

(** ** got as inflateGetHeader takes it *)

Lemma c9_head_cs sh (v : @reptype Zlib.units.Inflate.CS Zlib.proof.inflate.Rep.t_head) (p : val) :
  @data_at Zlib.units.Inflate.CS sh Zlib.proof.inflate.Rep.t_head v p = @data_at CS sh t_g v p.
Proof. apply equal_f. apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity]. Qed.

Lemma c9_tok_cs sh n q :
  @malloc_token Zlib.units.Inflate.CS sh (tarray tuchar n) q = @malloc_token CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_inflate). reflexivity. Qed.

(* the sizes of got's buffers *)
Lemma c9_sizes u : su_dok u ->
  0 <= Zlength (su_xf u) <= 65535 /\ 0 <= Zlength (su_nm u) <= 4294967294 /\
  0 <= Zlength (su_cm u) <= 4294967294.
Proof.
  intros (_ & _ & _ & _ & _ & _ & _ & _ & Hx & _ & Hn & _ & Hc & _).
  pose proof (Zlength_nonneg (su_xf u)). pose proof (Zlength_nonneg (su_nm u)).
  pose proof (Zlength_nonneg (su_cm u)). lia.
Qed.

(* got with its three fresh buffers: the header h0 u with every other field and every byte undefined *)
Lemma c9_raw u vg :
  su_ok u ->
  data_at Tsh t_g (gval u) vg * data_at_ Ews (tarray tuchar (Zlength (su_xf u))) (su_gxp u) *
  data_at_ Ews (tarray tuchar (Zlength (su_nm u) + 1)) (su_gnp u) *
  data_at_ Ews (tarray tuchar (Zlength (su_cm u) + 1)) (su_gcp u)
  |-- Zlib.proof.roundtrip.RTHSpec.hraw6 Tsh vg (su_gxp u) (su_gnp u) (su_gcp u) (h0 u).
Proof.
  intros (Hd & _ & _ & _ & _ & _ & _ & _ & Px & Pn & Pc).
  destruct (c9_sizes u Hd) as (Hx & Hn & Hc).
  unfold Zlib.proof.roundtrip.RTHSpec.hraw6, Zlib.proof.roundtrip.RTHSpec.hbuf6, h0.
  cbn [IR.h_xp IR.h_np IR.h_cp IR.h_extra_max IR.h_name_max IR.h_comm_max].
  Exists Vundef Vundef Vundef Vundef Vundef Vundef Vundef.
  Exists (Zrepeat Vundef (Zlength (su_xf u))) (Zrepeat Vundef (Zlength (su_nm u) + 1))
         (Zrepeat Vundef (Zlength (su_cm u) + 1)).
  rewrite !if_false by (intros E; rewrite E in *; contradiction).
  rewrite c9_head_cs, !(data_at_tuchar_cs Zlib.units.Inflate.CS CS).
  unfold data_at_. simpl default_val. unfold Zrepeat.
  rewrite !Zlength_repeat' by lia.
  unfold gval. entailer!.
Qed.

(* the malloc token of a buffer: inflate's token of a zero-size one (btok), main's of the others (nbtok) *)
Lemma c9_tok q n : q <> nullval ->
  malloc_token Ews (tarray tuchar n) q |-- Zlib.proof.inflate.CaseHyps5.btok q n * nbtok q n.
Proof.
  intros Nq. unfold Zlib.proof.inflate.CaseHyps5.btok, nbtok. rewrite if_false by auto.
  destruct (zeq n 0).
  - subst. rewrite c9_tok_cs. cancel.
  - cancel.
Qed.

(* got before inflateGetHeader as its precondition takes it, and the tokens main keeps *)
Lemma c9_graw u vg :
  su_ok u ->
  graw vg u
  |-- Zlib.proof.roundtrip.RTHSpec.hraw6 Tsh vg (su_gxp u) (su_gnp u) (su_gcp u) (h0 u) *
      hdr_btoks (su_gxp u) (su_gnp u) (su_gcp u) (h0 u) * gtoks u.
Proof.
  intros Hu. pose proof Hu as (_ & _ & _ & _ & _ & _ & _ & _ & Px & Pn & Pc).
  unfold graw, gbufs, cnew.
  sep_apply (c9_raw u vg Hu).
  unfold hdr_btoks, gtoks, h0. cbn [IR.h_extra_max IR.h_name_max IR.h_comm_max].
  sep_apply (c9_tok (su_gxp u) (Zlength (su_xf u)) ltac:(intros E; rewrite E in Px; exact Px)).
  sep_apply (c9_tok (su_gnp u) (Zlength (su_nm u) + 1) ltac:(intros E; rewrite E in Pn; exact Pn)).
  sep_apply (c9_tok (su_gcp u) (Zlength (su_cm u) + 1) ltac:(intros E; rewrite E in Pc; exact Pc)).
  cancel.
Qed.

(* h0 u is a header of buffers of uInt sizes *)
Lemma c9_hwf u : su_dok u -> Zlib.proof.roundtrip.RTH8Spec.hwf8 (h0 u).
Proof.
  intros Hd. destruct (c9_sizes u Hd) as (Hx & Hn & Hc).
  unfold Zlib.proof.roundtrip.RTH8Spec.hwf8, h0, Zlib.proof.inflate.Inv.srange, Zlib.proof.inflate.Inv.lrange,
    Zlib.proof.inflate.Inv.urange.
  cbn [IR.h_text IR.h_time IR.h_xflags IR.h_os IR.h_extra_len IR.h_extra_max IR.h_name_max IR.h_comm_max
       IR.h_xbuf IR.h_nbuf IR.h_cbuf IR.h_hcrc IR.h_done].
  rewrite !Zlength_Zrepeat by lia.
  repeat split; try rep_lia; unfold Zrepeat; apply Forall_repeat; rep_lia.
Qed.

(** ** The decompressor around main's stores next_in = input, next_out = out *)

(* the stream after inflateGetHeader: its struct at main's compspecs and the state *)
Lemma c9_open gv vd L :
  vd <> nullval ->
  Zlib.proof.roundtrip.RTH8Spec.istream8_opt gv Tsh vd c9_z0 (Some L)
  |-- !! Zlib.proof.roundtrip.RTH8Spec.live_ok8 L &&
      (data_at Tsh t_z
         (nullval, (Vint (Int.repr 0), (Vlong (Int64.repr 0), (nullval, (Vint (Int.repr 0), (Vlong (Int64.repr 0),
          (nullval, (l_sp L, (gv Zlib.inflate.code._zcalloc, (gv Zlib.inflate.code._zcfree, (nullval,
          (Vint (Int.repr 0), (Vlong (Int64.repr 0), Vundef))))))))))))) vd *
       state_mem gv vd L).
Proof.
  intros Nd. unfold Zlib.proof.roundtrip.RTH8Spec.istream8_opt, Zlib.proof.roundtrip.RTH8Spec.istream8.
  rewrite if_false by auto.
  unfold zstrm_at, Zlib.proof.inflate.Rep.strm_rep, c9_z0. cbn.
  rewrite c9_cs_inflate. Intros. entailer!.
Qed.

(* the decompressor's fields once main stored next_in = input and next_out = out *)
Definition c9_z (ip op : val) : zfields := ZF ip 0 0 op 0 0 None 0 0 Vundef.

Lemma c9_close gv vd ip op L :
  Zlib.proof.roundtrip.RTH8Spec.live_ok8 L ->
  data_at Tsh t_z
    (ip, (Vint (Int.repr 0), (Vlong (Int64.repr 0), (op, (Vint (Int.repr 0), (Vlong (Int64.repr 0),
     (nullval, (l_sp L, (gv Zlib.inflate.code._zcalloc, (gv Zlib.inflate.code._zcfree, (nullval,
     (Vint (Int.repr 0), (Vlong (Int64.repr 0), Vundef))))))))))))) vd *
  state_mem gv vd L
  |-- Zlib.proof.roundtrip.RTH8Spec.istream8 gv Tsh vd (c9_z ip op) (Some L).
Proof.
  intros LV. unfold Zlib.proof.roundtrip.RTH8Spec.istream8, zstrm_at, Zlib.proof.inflate.Rep.strm_rep, c9_z.
  cbn [zf_ni zf_ai zf_tin zf_no zf_ao zf_tout zf_msg zf_dt zf_adler zf_res Zlib.proof.inflate.Rep.msg_val].
  rewrite c9_cs_inflate.
  apply andp_right; [apply prop_right; split; [unfold zf_ok; cbn; rep_lia | auto] |].
  apply andp_right; [apply prop_right; exact LV |]. apply derives_refl.
Qed.

(** ** The session *)

(* a header and a dictionary exclude each other (window_bits > 15 against <= 15) *)
Lemma c9_nodict u : with_head u = true -> with_dict u = false.
Proof.
  unfold with_head, with_dict. intros WH. apply andb_prop in WH as [W _]. apply Z.ltb_lt in W.
  rewrite (proj2 (Z.leb_gt _ 15)) by lia. reflexivity.
Qed.

(* inflateGetHeader's result on a stream in mode HEAD, in the form RTH9Spec's inflate() takes; stated on any
   live part so that the record updates are never computed on inflateInit2_'s concrete state *)
Lemma c9_head9 L0 h hp hsh xb nb cb :
  Zlib.proof.inflate.Records.i_mode (l_s L0) = Zlib.proof.inflate.Model.HEAD ->
  Zlib.proof.roundtrip.RTH8Spec.head_mem8
    (Zlib.proof.roundtrip.RTIIface.head_live L0 h hp hsh xb nb cb)
  |-- Zlib.proof.roundtrip.RTH9Spec.head_mem9 (Zlib.proof.roundtrip.RTIIface.head_live L0 h hp hsh xb nb cb).
Proof.
  intros M. apply Zlib.proof.roundtrip.RTH9Spec.head_mem8_9; [reflexivity | left; exact M | reflexivity].
Qed.
