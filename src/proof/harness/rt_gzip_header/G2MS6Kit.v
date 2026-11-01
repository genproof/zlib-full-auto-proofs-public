(* Law rt_gzip_header on the round-2 harness, main's body, segment 6 (statements 46-47: offer(&decompressor,
   compressed, 0, room, 1) and the do-while of inflate(Z_FINISH) calls): the lemmas of G2MainSeg6.v and the
   assertions of the loop.

   - the decompressor's struct at main's compspecs (as a 14-tuple, for the loads and the store of avail_in), at
     the compress unit's (offer's argument), and back as the inflate spec's istream8 after the store;
   - the compressed object and room as the buffers of each inflate() call, and back after it;
   - the pointer arithmetic of the loop (the bytes left, the comparison next_in != compressed + compressed_len);
   - what Spec5.inflate_rel says of a call on the live stream: the stream stays live with the same gz_header
     pointers (the Z_MEM_ERROR return gives got back to the stack frame with them), and the code is in -5 .. 2;
   - the gz_header at the loop's entry and exit (RTH9Spec.head_mem9 from and to RTH8Spec.head_mem8);
   - the loop invariant [g6_inv] (at the head of the body), the state after a call [g6_cont] (at the loop test). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.harness.rt_gzip_header.CS.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainDefs.
Require Import Zlib.proof.deflate.Rep.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_gzip_header.G2DFacts.
Require Import Zlib.proof.roundtrip.RTH9Spec.
Require Zlib.proof.uncompr.URunRet.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainKit.
Require Import Zlib.harness.rt_gzip_header.code.
#[local] Existing Instance Zlib.proof.harness.rt_gzip_header.CS.CS.
#[local] Instance CC_compress : change_composite_env Zlib.units.Compress.CS CS.
  make_cs_preserve Zlib.units.Compress.CS CS. Defined.
Local Open Scope logic.

(** ** The decompressor's struct *)

(* the 14 members of struct z_stream *)
Definition g6_tuple : Type :=
  (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * val)))))))))))))%type.

(* the struct of a live stream with the fields z and the state sp, at main's compspecs *)
Definition g6_tup (gv : globals) (z : AM.zfields) (sp : val) : g6_tuple :=
  (AM.zf_ni z, (vi (AM.zf_ai z), (vl (AM.zf_tin z), (AM.zf_no z, (vi (AM.zf_ao z), (vl (AM.zf_tout z),
   (Zlib.proof.inflate.Rep.msg_val gv (AM.zf_msg z), (sp, (gv Zlib.inflate.code._zcalloc,
   (gv Zlib.inflate.code._zcfree, (nullval, (vi (AM.zf_dt z), (vl (AM.zf_adler z), AM.zf_res z))))))))))))).

Lemma g6_strm_cs sh (v : g6_tuple) q :
  @data_at Zlib.units.Inflate.CS sh Zlib.proof.inflate.Rep.t_strm v q = @data_at CS sh t_z v q.
Proof.
  apply equal_f. apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity].
Qed.

(* offer's view of the struct (laws_common's compspecs) *)
Lemma g6_cs_compress sh a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 q :
  @data_at Zlib.units.Compress.CS sh t_zs (zs_val a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14) q =
  @data_at CS sh t_z ((a1, (a2, (a3, (a4, (a5, (a6, (a7, (a8, (a9, (a10, (a11, (a12, (a13, a14)))))))))))))
    : g6_tuple) q.
Proof.
  apply equal_f. apply (@data_at_change_composite _ _ CC_compress); [apply JMeq_refl | reflexivity].
Qed.

Lemma g6_open gv vd z L :
  istream8 gv Tsh vd z (Some L) =
  !! (S5.zf_ok z /\ live_ok8 L) && (data_at Tsh t_z (g6_tup gv z (S5.l_sp L)) vd * S5.state_mem gv vd L).
Proof.
  unfold istream8, S5.zstrm_at, Zlib.proof.inflate.Rep.strm_rep.
  rewrite g6_strm_cs.
  apply pred_ext; entailer!; apply derives_refl.
Qed.

(* after the store of avail_in = ai: the stream inflate() is given *)
Lemma g6_fold gv vd z L ai :
  isptr vd -> S5.zf_ok z -> live_ok8 L -> 0 <= ai <= Int.max_unsigned ->
  data_at Tsh t_z ((AM.zf_ni z, (vi ai, (vl (AM.zf_tin z), (AM.zf_no z, (vi (AM.zf_ao z), (vl (AM.zf_tout z),
   (Zlib.proof.inflate.Rep.msg_val gv (AM.zf_msg z), (S5.l_sp L, (gv Zlib.inflate.code._zcalloc,
   (gv Zlib.inflate.code._zcfree, (nullval, (vi (AM.zf_dt z), (vl (AM.zf_adler z), AM.zf_res z)))))))))))))
   : g6_tuple) vd * S5.state_mem gv vd L
  |-- istream8_opt gv Tsh vd (GI.offer_z z (AM.zf_ni z) ai (AM.zf_no z) (AM.zf_ao z)) (Some L).
Proof.
  intros Pv Zo Lo Hai. unfold istream8_opt. rewrite if_false by (destruct vd; try contradiction; discriminate).
  rewrite g6_open. apply andp_right; [ | apply derives_refl].
  apply prop_right. split; [ | exact Lo]. unfold S5.zf_ok, GI.offer_z in *; cbn. rep_lia.
Qed.

Lemma g6_opt_ptr gv (vd : val) z st : isptr vd -> istream8_opt gv Tsh vd z st = istream8 gv Tsh vd z st.
Proof. intros Pv. unfold istream8_opt. rewrite if_false by (destruct vd; try contradiction; discriminate). auto. Qed.

Lemma g6_live_ptr (vd : val) st : isptr vd -> S5.is_live vd st = st.
Proof. intros Pv. unfold S5.is_live. rewrite if_false by (destruct vd; try contradiction; discriminate). auto. Qed.

(* the stream at a return: the local's memory *)
Lemma g6_strm_ret gv vd z sp L :
  data_at Tsh t_z (g6_tup gv z sp) vd * S5.state_mem gv vd L |-- data_at_ Tsh t_z vd * TT.
Proof. sep_apply (data_at_data_at_ Tsh t_z). cancel. Qed.

Lemma g6_istream_ret gv vd z st : istream8 gv Tsh vd z st |-- data_at_ Tsh t_z vd * TT.
Proof.
  unfold istream8, S5.zstrm_at, Zlib.proof.inflate.Rep.strm_rep. destruct st as [L | ]; Intros;
  erewrite (@data_at_change_composite _ _ CC_inflate); try (apply JMeq_refl || reflexivity);
  sep_apply (data_at_data_at_ Tsh t_z); cancel.
Qed.

(** ** main's resources: the tables lent to inflate() *)

Definition g6_rest (gv : globals) : mpred :=
  trees_globals gv * errmsg_at gv *
  @data_at Zlib.proof.deflate.DCS.CS Ers (tarray t_config 10) (config_vals gv)
    (gv Zlib.deflate.code._configuration_table) *
  @data_at Zlib.proof.deflate.DCS.CS Ers (tarray tschar 6) (map vi [49; 46; 51; 46; 50; 0])
    (gv Zlib.deflate.code._my_version) *
  Zlib.proof.deflate.GlobalsInit.version_at gv ___stringlit_rt_gzip_header_1 *
  Zlib.proof.inflate_api.Spec5.version_lit gv.

Lemma g6_r_split (gv : globals) :
  R gv = Zlib.proof.crc32.Spec.crc_table_at Ers gv * Zlib.proof.inflate.Rep.tables_rep Ers gv * g6_rest gv.
Proof. unfold R, deflate_globals, g6_rest. apply pred_ext; cancel. Qed.

(** ** The buffers of a call *)

Lemma g6_bytes_cs sh n (v : list val) q :
  @data_at Zlib.units.Inflate.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity]. Qed.
Lemma g6_tok_cs sh n q :
  @malloc_token Zlib.units.Inflate.CS sh (tarray tuchar n) q = @malloc_token CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_inflate). reflexivity. Qed.

(* the compressed object of b bytes (offered from pos on) and room (one byte, no malloc token) *)
Definition g6_ib (cbp : val) (b pos : Z) (O : list Z) : inbuf := InBuf Ews cbp pos b (cbytes b O).
Definition g6_ob (vr : val) : outbuf := OutBuf Tsh vr 0 1 [Vundef].

Lemma g6_bufs_pre L cbp b pos O vr :
  data_at Ews (tarray tuchar b) (cbytes b O) cbp * malloc_token Ews (tarray tuchar b) cbp *
  data_at_ Tsh (tarray tuchar 1) vr
  |-- bufs_opt (Some L) (g6_ib cbp b pos O) (Some (g6_ob vr)) [] true false.
Proof.
  unfold bufs_opt, in_rep, out_opt, out_rep, in_tok, out_tok, g6_ib, g6_ob.
  change (sublist 0 0 [Vundef] ++ byte_vals [] ++ sublist (0 + Zlength (@nil Z)) 1 [Vundef]) with [Vundef].
  rewrite !g6_bytes_cs, !g6_tok_cs. unfold data_at_. simpl default_val. cancel.
Qed.

Lemma g6_bufs_post L cbp b pos O vr ow :
  bufs_opt (Some L) (g6_ib cbp b pos O) (Some (g6_ob vr)) ow true false
  |-- data_at Ews (tarray tuchar b) (cbytes b O) cbp * malloc_token Ews (tarray tuchar b) cbp *
      data_at_ Tsh (tarray tuchar 1) vr.
Proof.
  unfold bufs_opt, in_rep, out_opt, out_rep, in_tok, out_tok, g6_ib, g6_ob.
  rewrite !g6_bytes_cs, !g6_tok_cs.
  sep_apply (data_at_data_at_ Tsh (tarray tuchar 1)). cancel.
Qed.

Lemma g6_in_ok cbp b pos O :
  isptr cbp -> rbytes O -> Zlength O <= b <= max_u64 -> 0 <= pos <= Zlength O ->
  in_ok (g6_ib cbp b pos O) (sublist pos (pos + clipz (Zlength O - pos)) O).
Proof.
  intros Pc BO Hb Hp. unfold in_ok, g6_ib, clipz, umax, max_u64 in *.
  assert (Hs : Zlength (sublist pos (pos + Z.min (Zlength O - pos) 4294967295) O) =
               Z.min (Zlength O - pos) 4294967295) by (rewrite Zlength_sublist; lia).
  rewrite Hs. pose proof (Zlength_nonneg O).
  split; [auto | ]. split; [auto | ]. split; [lia | ]. split; [lia | ].
  split; [unfold cbytes; rewrite Zlength_app, Zlength_map, Zlength_Zrepeat; lia | ]. split; [rep_lia | ]. split.
  - unfold cbytes. rewrite sublist_app1 by (rewrite ?Zlength_map; lia).
    unfold byte_vals. rewrite sublist_map. reflexivity.
  - apply Forall_sublist. eapply Forall_impl; [ | exact BO]. simpl. intros; rep_lia.
Qed.

Lemma g6_out_ok vr : isptr vr -> out_ok (g6_ob vr) 1.
Proof. intros Pv. unfold out_ok, g6_ob. split; [apply writable_share_top | ]. split; [exact Pv | ]. repeat split; try reflexivity; rep_lia. Qed.

(** ** The pointer arithmetic of the loop *)

(* m - (size_t) (p + k - p), the bytes left *)
Lemma g6_ptr_sub (p : val) k m : isptr p -> 0 <= k <= m -> m <= Ptrofs.max_unsigned ->
  force_val (sem_sub_default tulong tulong (Vlong (Int64.repr m)) (force_val (sem_sub_pp tuchar (offset_val k p) p)))
  = Vlong (Int64.repr (m - k)).
Proof.
  intros Pp Hk Hm. destruct p; try contradiction. simpl.
  unfold sem_sub_pp, sem_sub_default. simpl. destruct (eq_block b b); [ | congruence]. simpl.
  rewrite Ptrofs.sub_add_l, Ptrofs.sub_idem, Ptrofs.add_zero_l.
  change (Ptrofs.repr 1) with Ptrofs.one. rewrite Ptrofs.divs_one by (cbv; congruence).
  unfold Vptrofs. simpl. f_equal. unfold Ptrofs.to_int64. rewrite Ptrofs.unsigned_repr by rep_lia.
  unfold Int64.sub. rewrite !Int64.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma g6_sameblock (p : val) k : isptr p -> is_true (sameblock (offset_val k p) p).
Proof. intros Pp. destruct p; try contradiction. simpl. destruct (peq b b); [reflexivity | congruence]. Qed.

(* two pointers into (or just past) an object of b > 0 bytes may be compared (VST makes denote_tc_test_eq
   opaque; it is opened for this lemma only) *)
Local Transparent denote_tc_test_eq.
Lemma g6_test_eq sh b (c : list val) p i j F : sepalg.nonidentity sh -> isptr p -> 0 < b ->
  0 <= i <= b -> 0 <= j <= b ->
  data_at sh (tarray tuchar b) c p * F |-- denote_tc_test_eq (offset_val i p) (offset_val j p).
Proof.
  intros N Pp Hb Hi Hj. destruct p; try contradiction. unfold denote_tc_test_eq, test_eq_ptrs. simpl.
  destruct (peq b0 b0); [ | congruence]. simpl.
  sep_apply (data_at_data_at_ sh (tarray tuchar b) c (Vptr b0 i0)). rewrite data_at__memory_block. Intros.
  simpl sizeof. rewrite Z.max_r by lia. rewrite Z.mul_1_l.
  apply andp_right; apply sepcon_weak_valid_pointer1.
  - change (Vptr b0 (Ptrofs.add i0 (Ptrofs.repr i))) with (offset_val i (Vptr b0 i0)).
    apply memory_block_weak_valid_pointer; auto.
  - change (Vptr b0 (Ptrofs.add i0 (Ptrofs.repr j))) with (offset_val j (Vptr b0 i0)).
    apply memory_block_weak_valid_pointer; auto.
Qed.
Local Opaque denote_tc_test_eq.

(* the comparison's result: two offsets of one pointer are equal exactly when the offsets are *)
Lemma g6_ptr_eq (p : val) i j : isptr p -> 0 <= i <= Ptrofs.max_unsigned -> 0 <= j <= Ptrofs.max_unsigned ->
  offset_val i p = offset_val j p -> i = j.
Proof.
  intros Pp Hi Hj E. destruct p; try contradiction. unfold offset_val in E.
  assert (E2 : Ptrofs.add i0 (Ptrofs.repr i) = Ptrofs.add i0 (Ptrofs.repr j)) by congruence. clear E.
  apply (f_equal (fun x => Ptrofs.unsigned (Ptrofs.sub x i0))) in E2.
  rewrite !Ptrofs.sub_add_l, !Ptrofs.sub_idem, !Ptrofs.add_zero_l, !Ptrofs.unsigned_repr in E2 by lia. exact E2.
Qed.

(* compressed + compressed_len *)
Lemma g6_add_ptr (p : val) n : isptr p -> 0 <= n <= Int64.max_unsigned ->
  force_val (sem_add_ptr_long tuchar p (vl n)) = offset_val n p.
Proof.
  intros Pp Hn. destruct p; try contradiction. unfold vl, sem_add_ptr_long. simpl. f_equal. f_equal.
  unfold Ptrofs.of_int64. rewrite Int64.unsigned_repr by rep_lia.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one. reflexivity.
Qed.

(* the value of (_Bool) (p + i != p + j) *)
Lemma g6_cmp (p : val) i j : isptr p -> 0 <= i <= Ptrofs.max_unsigned -> 0 <= j <= Ptrofs.max_unsigned ->
  force_val (sem_cast_i2bool (force_val (sem_cmp_pp Cne (offset_val i p) (offset_val j p)))) =
  Vint (Int.repr (if zeq i j then 0 else 1)).
Proof.
  intros Pp Hi Hj. destruct p; try contradiction.
  assert (C : Ptrofs.eq (Ptrofs.add i0 (Ptrofs.repr i)) (Ptrofs.add i0 (Ptrofs.repr j)) =
              (if zeq i j then true else false)).
  { destruct (zeq i j) as [E | E]; [subst; apply Ptrofs.eq_true | apply Ptrofs.eq_false].
    intro F. apply E. apply (g6_ptr_eq (Vptr b i0) i j); auto. simpl. rewrite F. reflexivity. }
  unfold sem_cmp_pp, Val.cmplu_bool, offset_val. change Archi.ptr64 with true. simpl.
  first [destruct (eq_block b b) as [_ | N] | destruct (peq b b) as [_ | N]]; [ | congruence]. simpl.
  unfold Ptrofs.cmpu. rewrite C. destruct (zeq i j); reflexivity.
Qed.

(** ** Facts of the model *)

Lemma g6_init_mode sp w : IR.i_mode (S5.l_s (S5.init_live sp w)) = Zlib.proof.inflate.Model.HEAD.
Proof. unfold S5.init_live. destruct (AM.reset2_wb w) as [[a c] | ]; reflexivity. Qed.

(* the stream after inflateInit2_ and inflateGetHeader: header attached, mode HEAD, so InvW.swfW *)
Lemma g6_gL_head g sp vg : IR.i_head (S5.l_s (gL g sp vg)) = true.
Proof. reflexivity. Qed.

Lemma g6_gL_swfW g sp vg : swfW (S5.l_s (gL g sp vg)).
Proof.
  unfold swfW. unfold gL, Zlib.proof.roundtrip.RTIIface.head_live. cbn [S5.l_s S5.set_l_head S5.set_l_s].
  assert (E : IR.i_mode (IR.set_i_head (S5.l_s (S5.init_live sp (g_wb g))) true) =
              IR.i_mode (S5.l_s (S5.init_live sp (g_wb g)))) by reflexivity.
  rewrite E, g6_init_mode. split; intros F; vm_compute in F; discriminate F.
Qed.

(* got's buffers have the sizes of the header's fields *)
Lemma g6_bufs (g : gsetup) : gs_ok g -> GI.g2_bufs (gh_of g) (h0 g).
Proof.
  intros (Hxl & Hnl & Hcl & _ & _ & _ & _ & _ & _ & _ & _ & _ & Lx & _ & Ln & _ & Lc & _).
  unfold GI.g2_bufs, h0, gh_of; cbn.
  rewrite !Zlength_Zrepeat by lia.
  repeat split; try reflexivity; try lia;
    intros l E; unfold selo in E; destruct (has g _); inversion E; subst;
    rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
Qed.

(* a gzip stream is not empty (its trailer alone has 8 bytes) *)
Lemma g6_O_pos wbd gh O : dfinal [] 2 wbd (Some gh) [] O -> 0 < Zlength O.
Proof.
  intros (_ & bs & _ & _ & H). destruct H as (_ & xfl & _ & E). subst O.
  unfold Zlib.proof.rfc1951.Format.stream_bytes.
  rewrite !Zlength_app. unfold Zlib.proof.rfc1951.Format.le_bytes. rewrite !Zlength_map.
  change (Zlength (seq 0 (Z.to_nat 4))) with 4.
  repeat match goal with |- context [Zlength ?a] =>
    lazymatch goal with _ : 0 <= Zlength a |- _ => fail | _ => pose proof (Zlength_nonneg a) end end.
  lia.
Qed.

(* the loop invariant of the theory at the start: position 0 of O, after inflateInit2_ and inflateGetHeader *)
Lemma g6_P0 P g O z sp vg : GI.g2_ifacts P -> gs_ok g -> dfinal [] 2 (rwbe (g_wb g)) (Some (gh_of g)) [] O ->
  Zlength O <= max_u64 -> live_ok8 (gL g sp vg) -> S5.zf_ok z -> AM.zf_tout z = 0 ->
  P (g_wb g - 16) (gh_of g) O (h0 g) 0 z (gL g sp vg).
Proof.
  intros PF OK DF HO LV Zo Zt.
  assert (Hw : 25 <= g_wb g <= 31) by (destruct OK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hw & _); exact Hw).
  assert (E : gL g sp vg = Zlib.proof.roundtrip.RTIIface.head_live (S5.init_live sp (16 + (g_wb g - 16))) (h0 g) vg
                Tsh (g_gxp g) (g_gnp g) (g_gcp g)) by (unfold gL; do 2 f_equal; lia).
  rewrite E in *.
  eapply (GI.gi_init P PF); try eassumption.
  - apply gh_of_ok2; exact OK.
  - lia.
  - apply g6_bufs; exact OK.
Qed.

Lemma g6_head_cs sh (v : @reptype Zlib.units.Inflate.CS Zlib.proof.inflate.Rep.t_head) q :
  @data_at Zlib.units.Inflate.CS sh Zlib.proof.inflate.Rep.t_head v q |-- @data_at_ CS sh t_g q.
Proof.
  erewrite (@data_at_change_composite _ _ CC_inflate sh Zlib.proof.inflate.Rep.t_head v);
    [ apply data_at_data_at_ | apply JMeq_refl | reflexivity ].
Qed.

(* got while the stream holds it (RTH9Spec.head_mem9): whatever disjunct, the local's memory at a return *)
Lemma g6_head_ret L vg :
  S5.l_headp L = vg -> S5.l_hsh L = Tsh -> head_mem9 L |-- data_at_ Tsh t_g vg * TT.
Proof.
  intros Hp Hs. unfold head_mem9. rewrite Hp, Hs.
  rewrite !sepcon_assoc. rewrite !distrib_orp_sepcon. repeat apply orp_left.
  - unfold head_rep6, head_rep6p. Intros. Intros vt vtm vxf vos vxl vhc lx ln lc.
    sep_apply g6_head_cs. cancel.
  - unfold head_rep8a, head_rep6p. Intros. Intros vt vtm vxf vos vxl vhc lx ln lc.
    sep_apply g6_head_cs. cancel.
  - unfold hraw6. Intros. Intros vt vtm vxf vos vxl vhc vdn lx ln lc.
    sep_apply g6_head_cs. cancel.
Qed.

(* the loop's entry: inflateGetHeader's result (mode HEAD, done 0) as inflate_spec9's head_mem9 *)
Lemma g6_head_entry g sp vg : head_mem8 (gL g sp vg) |-- head_mem9 (gL g sp vg).
Proof.
  apply head_mem8_9; [reflexivity | left; apply g6_init_mode | reflexivity].
Qed.

(* the loop's exit: a header passed (out of the header modes, done 1) is A40's head_mem8 *)
Lemma g6_head_exit L :
  IR.i_head (S5.l_s L) = true -> hdr_mode (IR.i_mode (S5.l_s L)) = false -> IR.h_done (S5.l_h L) = 1 ->
  head_mem9 L |-- head_mem8 L.
Proof.
  intros Hh Hm Hd. sep_apply (head_mem9_passed L Hm Hd). unfold head_mem8. rewrite Hh.
  apply sepcon_derives; [apply sepcon_derives; [apply sepcon_derives |] |]; try apply derives_refl.
  apply orp_right2. apply andp_right; [apply prop_right; exact Hm | apply derives_refl].
Qed.

(* a call on the live stream with an input object and an output space leaves it live, with the same
   application header (Spec5.inflate_rel keeps the header's pointers and share); its code is one of zlib's
   return codes (URunRet.run2_ret) *)
Lemma g6_rel_keep flush (vd : val) z L ib inp o r z' st' ow : isptr vd -> ib <> InNull ->
  S5.inflate_rel flush vd z (Some L) ib inp (Some o) r z' st' ow ->
  exists L', st' = Some L' /\ S5.l_headp L' = S5.l_headp L /\ S5.l_hsh L' = S5.l_hsh L /\
    S5.l_xb L' = S5.l_xb L /\ S5.l_nb L' = S5.l_nb L /\ S5.l_cb L' = S5.l_cb L /\ -5 <= r <= 2.
Proof.
  intros Pv Hib REL.
  destruct REL as [[Hbad _] | [_ (L0 & o0 & res & winp & EL & Eo & Hrun & _ & Er & _ & _ & _ & Est)]].
  - exfalso. unfold S5.inflate_bad in Hbad. rewrite g6_live_ptr in Hbad by auto.
    destruct Hbad as [Hb | [Hb | [Hb _]]]; [discriminate | discriminate | contradiction].
  - injection EL as <-. subst st' r.
    assert (R0 : -5 <= IR.m_ret (S5.m_init z L inp) <= 2)
      by (change (IR.m_ret (S5.m_init z L inp)) with 0; lia).
    pose proof (Zlib.proof.uncompr.URunRet.run2_ret _ _ _ _ _ R0 Hrun) as Hr.
    eexists; repeat split; lia.
Qed.

(** ** The assertions of the loop *)
Section Inv.
Context (gv : globals) (vh vg vc vd vr : val) (P : GI.g2_inv) (g : gsetup) (b : Z) (cbp : val) (O : list Z).

Definition g6_locals : list localdef :=
  temp _compressed_len (vl (Zlength O)) :: temp _compressed cbp :: gp_locals g ++ gs_locals g ++
  lv_locals gv vh vg vc vd vr.

(* what holds of the segment's data throughout *)
Definition g6_glob : Prop :=
  gs_ok g /\ dfinal [] 2 (rwbe (g_wb g)) (Some (gh_of g)) [] O /\ rbytes O /\ Zlength O <= b <= max_u64 /\
  isptr cbp /\ 0 < Zlength O.

(* the live stream between the calls: InvW.swfW (P does not carry it), the header attached and given back as got,
   the input from position pos of the compressed object, the output space room (1 byte) *)
Definition g6_live (pos : Z) (z : AM.zfields) (L : S5.live) : Prop :=
  S5.zf_ok z /\ live_ok8 L /\ swfW (S5.l_s L) /\ IR.i_head (S5.l_s L) = true /\
  AM.zf_ni z = offset_val pos cbp /\ AM.zf_no z = vr /\ AM.zf_ao z = 1 /\
  S5.l_headp L = vg /\ S5.l_hsh L = Tsh /\ S5.l_xb L = g_gxp g /\ S5.l_nb L = g_gnp g /\ S5.l_cb L = g_gcp g /\
  0 <= pos <= Zlength O.

Definition g6_sep (z : AM.zfields) (L : S5.live) : list mpred :=
  [data_at Tsh t_z (g6_tup gv z (S5.l_sp L)) vd; S5.state_mem gv vd L; head_mem9 L; gtoks g;
   data_at_ Tsh (tarray tuchar 1) vr; data_at_ Tsh t_z vc; data_at Tsh t_g (hvals g) vh; hobjs g;
   mem_mgr gv; R gv; ifz gv;
   malloc_token Ews (tarray tuchar b) cbp; data_at Ews (tarray tuchar b) (cbytes b O) cbp; TT].

(* the head of the loop's body *)
Definition g6_inv : environ -> mpred :=
  EX pos : Z, EX z : AM.zfields, EX L : S5.live,
  PROPx [g6_glob; P (g_wb g - 16) (gh_of g) O (h0 g) pos z L; g6_live pos z L]
  (LOCALx g6_locals (SEPx (g6_sep z L))).

(* the loop's test, after a call that returned r <> Z_MEM_ERROR (G2IFacts.gi_call) *)
Definition g6_cont_at (r pos : Z) (z : AM.zfields) (L : S5.live) : environ -> mpred :=
  PROPx [g6_glob; -5 <= r <= 2; r = Z_BUF_ERROR -> pos < Zlength O -> P (g_wb g - 16) (gh_of g) O (h0 g) pos z L;
         r <> Z_BUF_ERROR \/ pos = Zlength O -> GI.g2_hdr_out (gh_of g) (h0 g) (S5.l_s L) (S5.l_h L);
         g6_live pos z L]
  (LOCALx (temp _code (vi r) :: g6_locals) (SEPx (g6_sep z L))).

Definition g6_cont : environ -> mpred := EX r : Z, EX pos : Z, EX z : AM.zfields, EX L : S5.live, g6_cont_at r pos z L.

(* the rest of main's memory after the loop *)
Definition g6_fr (z : AM.zfields) (L : S5.live) : mpred :=
  data_at Tsh t_z (g6_tup gv z (S5.l_sp L)) vd * S5.state_mem gv vd L * data_at_ Tsh (tarray tuchar 1) vr *
  data_at_ Tsh t_z vc * ifz gv * malloc_token Ews (tarray tuchar b) cbp *
  data_at Ews (tarray tuchar b) (cbytes b O) cbp * TT.

Lemma g6_fr_back z L : dback vc vd vr (g6_fr z L).
Proof. unfold dback, g6_fr. sep_apply (g6_strm_ret gv vd z (S5.l_sp L) L). cancel. Qed.

End Inv.

(** ** The parts of the segment's proof (G2MS6Body.v, G2MS6TestA.v, G2MS6TestB.v; G2MainSeg6.v assembles them) *)

(* seg6 is `offer(..); do g6_body while (g6_incr)` *)
Definition g6_body : statement :=
  ltac:(let x := eval cbv delta [seg6] in seg6 in lazymatch x with Ssequence _ (Sloop ?c _) => exact c end).
Definition g6_incr : statement :=
  ltac:(let x := eval cbv delta [seg6] in seg6 in lazymatch x with Ssequence _ (Sloop _ ?c) => exact c end).

(* the body: avail_in = clip(..), code = inflate(&decompressor, Z_FINISH), the Z_MEM_ERROR return; X and Y stand
   for the loop's break assertion and the segment's postcondition, which the body does not reach *)
Definition g6_body_stmt : Prop :=
  forall {Espec : OracleKind} P gv vh vg vc vd vr g b cbp O (X Y : environ -> mpred),
  GI.g2_ifacts P -> isptr vd -> isptr vr ->
  semax Delta_m (g6_inv gv vh vg vc vd vr P g b cbp O) g6_body
    (loop1_ret_assert (g6_cont gv vh vg vc vd vr P g b cbp O) (overridePost X (overridePost Y POST_m))).

(* the loop's test from the state after a call with the code r at position pos (the case of r and pos is
   cs O r pos): back to the invariant, or out of the loop with A40 *)
Definition g6_test_stmt (cs : list Z -> Z -> Z -> Prop) : Prop :=
  forall {Espec : OracleKind} P gv vh vg vc vd vr g b cbp O r pos z L Rc Rr,
  cs O r pos ->
  semax Delta_m (g6_cont_at gv vh vg vc vd vr P g b cbp O r pos z L) g6_incr
    {| RA_normal := g6_inv gv vh vg vc vd vr P g b cbp O;
       RA_break := EX L1 : S5.live, EX Fr : mpred, A40 gv vh vg vc vd vr g L1 Fr;
       RA_continue := Rc; RA_return := Rr |}.

(** ** Tactics of the parts *)

(* `if (c) { .. t = (..); } else t = 0;` with the value v of t known *)
Ltac g6_ifk t v := match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_if (PROPx [] (LOCALx (temp t (Vint (Int.repr v)) :: Q) (SEPx R))) end.

(* a branch that cannot be taken *)
Ltac g6_infeas := exfalso; first [ match goal with H : ?a <> ?b |- _ => solve [apply H; reflexivity] end
                                 | match goal with H : _ |- _ => solve [discriminate H] end
                                 | contradiction
                                 | match goal with H : Int.repr _ = Int.repr _ |- _ =>
                                     apply repr_inj_signed in H; [lia | rep_lia | rep_lia] end
                                 | lia ].

(* the comparison next_in != compressed + compressed_len: both pointers into the compressed object *)
Ltac g6_cmp_tc :=
  rewrite g6_add_ptr by (auto; unfold max_u64 in *; rep_lia);
  eapply derives_trans with (data_at Ews (tarray tuchar _) (cbytes _ _) _ * TT); [cancel | ];
  apply g6_test_eq; [apply readable_nonidentity, writable_readable, writable_Ews | auto | lia | lia | lia].
Ltac g6_cmp_val :=
  rewrite g6_add_ptr by (auto; unfold max_u64 in *; rep_lia);
  rewrite g6_cmp by (auto; unfold max_u64 in *; rep_lia);
  destruct (zeq _ _); first [reflexivity | lia].

(* the loop's exit: got holds the header (g2_hdr_out from the theory's last call), A40 with the rest of the
   memory as the frame g6_fr *)
Ltac g6_exit Hend HE L0 Hh gv vc vd vr b cbp O z0 Eni0 :=
  let HO := fresh "HO" in let HM := fresh "HM" in let HD := fresh "HD" in
  pose proof (Hend HE) as HO; destruct HO as (? & HM & HD & ?);
  pose proof (Hend HE) as HO;
  sep_apply (g6_head_exit L0 Hh HM HD);
  Exists L0 (g6_fr gv vc vd vr b cbp O z0 L0);
  pose proof (g6_fr_back gv vc vd vr b cbp O z0 L0) as FB;
  unfold A40, gp_locals, gs_locals, lv_locals; cbn [app];
  entailer!; unfold g6_fr, g6_tup; rewrite ?Eni0; cancel.
