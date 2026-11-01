(* Law rt_stream (harness/rt_stream.c, data of any length), main's body: statements 22-29 (compressed_len,
   new_stream, windowBits 8 -> 9, code = inflateInit2_, Z_MEM_ERROR: return, gp_assert(code == Z_OK), next_in,
   next_out), from DE to the inflate loop's invariant II
   (UMainKit.segC_stmt).  Round 1's proof of the same statements, with the sizes of round 2 (data and the
   compressed stream up to PTRDIFF_MAX bytes) and the model facts of UIFacts.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.DSpec9.
Require Zlib.proof.deflate.Obligations.
Require Zlib.proof.deflate.Api_toend.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.rt_stream.UDFacts.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.rt_stream.UIFacts.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_stream.LawCS.
Require Import Zlib.proof.harness.rt_stream.UMainStmt.
Require Import Zlib.proof.harness.rt_stream.UMainKit.
Require Import Zlib.proof.harness.rt_stream.USegCStores.
Require Import Zlib.harness.rt_stream.code.
#[local] Existing Instance LawCS.CS.
Local Open Scope logic.

(** ** The compressor *)

(* main reads compressor.next_out (at the law's compspecs) out of the deflate specifications' fields *)
Definition cs_rest (gv : globals) (vc : val) (c : cst) : mpred :=
  dstream 2 (Some (cs_s c)) vc nullval gv *
  (!! (u32_ok (cs_ain c) /\ u64_ok (cs_tin c) /\ u32_ok (cs_aout c) /\ u64_ok (cs_tout c) /\ u64_ok (cs_adler c)) &&
   (@field_at DCS.CS Ews Zlib.proof.deflate.Rep.t_strm (DOT deflate.code._next_in) (cs_ni c) vc *
    @field_at DCS.CS Ews Zlib.proof.deflate.Rep.t_strm (DOT deflate.code._avail_in) (vi (cs_ain c)) vc *
    @field_at DCS.CS Ews Zlib.proof.deflate.Rep.t_strm (DOT deflate.code._total_in) (vl (cs_tin c)) vc *
    @field_at DCS.CS Ews Zlib.proof.deflate.Rep.t_strm (DOT deflate.code._avail_out) (vi (cs_aout c)) vc *
    @field_at DCS.CS Ews Zlib.proof.deflate.Rep.t_strm (DOT deflate.code._total_out) (vl (cs_tout c)) vc *
    @field_at DCS.CS Ews Zlib.proof.deflate.Rep.t_strm (DOT deflate.code._msg) (cs_msgv c) vc *
    @field_at DCS.CS Ews Zlib.proof.deflate.Rep.t_strm (DOT deflate.code._adler) (vl (cs_adler c)) vc)) *
  srest vc.

Lemma sc_next_out_cs (v q : val) :
  @field_at DCS.CS Ews Zlib.proof.deflate.Rep.t_strm (DOT deflate.code._next_out) v q = field_at Ews t_z (DOT _next_out) v q.
Proof. apply equal_f; apply (@field_at_change_composite _ _ CC_dcs); [apply JMeq_refl | reflexivity]. Qed.

Lemma cstream_split gv vc c :
  cstream gv vc c = field_at Ews t_z (DOT _next_out) (cs_no c) vc * cs_rest gv vc c.
Proof.
  unfold cstream, cs_rest, api_fields. rewrite sc_next_out_cs.
  apply pred_ext; Intros; entailer!.
Qed.

(* the compressor, whatever its state, gives back the local's memory (at a return) *)
Lemma sc_comp_back (gv : globals) (vc : val) (c : cst) : cstream gv vc c |-- data_at_ Tsh t_z vc * TT.
Proof.
  unfold cstream, srest.
  sep_apply (BoundKit.dstream_data_at_ (Some (cs_s c)) vc nullval gv (cs_ni c) (cs_ain c) (cs_tin c) (cs_no c)
               (cs_aout c) (cs_tout c) (cs_msgv c) (cs_adler c) Api_toend.dstream_to_end).
  rewrite (@data_at__change_composite DCS.CS CS CC_dcs Ews Zlib.proof.deflate.Rep.t_strm) by reflexivity.
  rewrite (BoundKit.data_at__Tsh_split t_z vc). cancel.
Qed.

(** ** The decompressor at the compspecs of its users *)

(* laws_common's new_stream sees it at the compress unit's compspecs, inflate.c at Inflate.CS, main at the
   law's *)
Lemma sc_cs_compress sh (v : @reptype Zlib.units.Compress.CS t_zs) (p : val) :
  @data_at Zlib.units.Compress.CS sh t_zs v p = @data_at CS sh t_z v p.
Proof. apply equal_f. apply (@data_at_change_composite _ _ CC_compress); [apply JMeq_refl | reflexivity]. Qed.

Lemma sc_cs_inflate sh (v : @reptype Zlib.units.Inflate.CS Zlib.proof.inflate.Rep.t_strm) (p : val) :
  @data_at Zlib.units.Inflate.CS sh Zlib.proof.inflate.Rep.t_strm v p = @data_at CS sh t_z v p.
Proof. apply equal_f. apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity]. Qed.

(* the uninitialized local as new_stream's precondition *)
Lemma sc_undef (p : val) :
  data_at_ Tsh t_z p =
  @data_at Zlib.units.Compress.CS Tsh t_zs
    (zs_val Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef) p.
Proof. unfold data_at_. rewrite sc_cs_compress. reflexivity. Qed.

(* the struct after new_stream(): inflateInit2_'s raw stream *)
Definition ns_raw : rawf :=
  RF nullval (Vint (Int.repr 0)) Vundef nullval (Vint (Int.repr 0)) Vundef Vundef Vundef Vundef.

Lemma sc_ns_raw gv p :
  @data_at Zlib.units.Compress.CS Tsh t_zs
    (zs_val nullval (Vint (Int.repr 0)) Vundef nullval (Vint (Int.repr 0)) Vundef Vundef Vundef nullval nullval
       nullval Vundef Vundef Vundef) p =
  raw_strm gv Tsh p ns_raw Vundef Vundef nullval nullval nullval.
Proof. unfold raw_strm, ns_raw, zs_val; simpl. rewrite sc_cs_compress, sc_cs_inflate. reflexivity. Qed.

(* the harness's "1.3.2" as inflateInit2_ takes it *)
Definition hv_list : list val := map (fun c => Vint (Int.repr c)) [49; 46; 51; 46; 50; 0].

Lemma sc_hversion gv :
  hversion_at gv = @data_at Zlib.units.Inflate.CS Ers (tarray tschar (Zlength hv_list)) hv_list
                     (gv ___stringlit_rt_stream_1).
Proof.
  unfold hversion_at, hv_list. change (Zlength _) with 6. symmetry.
  apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity].
Qed.

(* inflateInit2_ failed: the struct goes back to the stack frame *)
Lemma sc_init_fail gv p r ret sp w :
  isptr p -> ret <> Z_OK ->
  init_mem gv Tsh p r Vundef Vundef nullval ret sp w |-- data_at_ Tsh t_z p.
Proof.
  intros Pp Nok. unfold init_mem. rewrite if_false by (intro; subst; contradiction).
  apply Z.eqb_neq in Nok. rewrite Nok.
  destruct (ret =? Z_VERSION_ERROR); [ | destruct (ret =? Z_MEM_ERROR)];
  unfold raw_strm; rewrite sc_cs_inflate; apply data_at_data_at_.
Qed.

(** ** The decompressor after inflateInit2_ returned Z_OK and main's two stores *)

(* its fields: next_in = compressed, next_out = out, avail_in/avail_out 0 (new_stream), totals 0, msg NULL,
   data_type 0, adler = wrap & 1 for a wrapped stream (a raw stream keeps its undefined member) *)
Definition z_init (cp op : val) (L : live) : zfields :=
  ZF cp 0 0 op 0 0 None 0 (if i_wrap (l_s L) =? 0 then 0 else Z.land (i_wrap (l_s L)) 1) Vundef.

Lemma sc_land1_range x : 0 <= Z.land x 1 <= 1.
Proof.
  change (Z.land x 1) with (Z.land x (Z.ones 1)). rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound x (2 ^ 1) ltac:(reflexivity)). simpl in *. lia.
Qed.

Lemma sc_istreamA gv vd cp op L :
  live_ok L ->
  @data_at CS Tsh t_z
    (cp, (Vint (Int.repr 0), (Vlong (Int64.repr 0), (op, (Vint (Int.repr 0), (Vlong (Int64.repr 0),
     (nullval, (l_sp L, (gv Zlib.inflate.code._zcalloc, (gv Zlib.inflate.code._zcfree, (nullval,
     (Vint (Int.repr 0), (if i_wrap (l_s L) =? 0 then Vundef else Vlong (Int64.repr (Z.land (i_wrap (l_s L)) 1)),
      Vundef))))))))))))) vd * state_mem gv vd L
  |-- istreamA gv Tsh vd (z_init cp op L) Vundef (Some L).
Proof.
  intros LV. unfold istreamA, zstrm_atA, z_init, adler_v, raw_live.
  rewrite <- sc_cs_inflate. pose proof (sc_land1_range (i_wrap (l_s L))).
  destruct (i_wrap (l_s L) =? 0); simpl; entailer!; unfold zf_ok; simpl; rep_lia.
Qed.

Lemma sc_head_init sp w : head_opt (Some (init_live sp w)) = emp.
Proof.
  unfold head_opt, head_mem, init_live, init_s. destruct (reset2_wb w) as [[wr wb] | ]; reflexivity.
Qed.

(* compressed_len = (size_t) (compressor.next_out - compressed) *)
Lemma sc_ptr_sub (p : val) (n : Z) :
  isptr p -> 0 <= n <= max_size ->
  force_val (sem_binary_operation' Osub (tptr tuchar) (tptr tuchar) (offset_val n p) p) = vl n.
Proof.
  intros Pp Hn. destruct p; try contradiction.
  unfold sem_binary_operation', sem_sub; simpl. unfold sem_sub_pp. simpl.
  destruct (eq_block b b); [ | congruence]. simpl. unfold vl.
  rewrite Ptrofs.sub_add_l, Ptrofs.sub_idem, Ptrofs.add_zero_l. change (Ptrofs.repr 1) with Ptrofs.one.
  rewrite Ptrofs.divs_one by reflexivity.
  unfold Vptrofs; simpl. unfold Ptrofs.to_int64.
  rewrite Ptrofs.unsigned_repr by (unfold max_size in *; rep_lia). reflexivity.
Qed.

(* window_bits after `if (window_bits == 8) window_bits = 9;` *)
Lemma sc_iw_8 w : rs32 w -> Int.repr w = Int.repr 8 -> vi 9 = vi (rts_iw w).
Proof.
  intros Hw E. apply repr_inj_signed in E; [ | unfold rs32 in Hw; rep_lia | rep_lia]. subst. reflexivity.
Qed.

Lemma sc_iw_n8 w : Int.repr w <> Int.repr 8 -> vi w = vi (rts_iw w).
Proof.
  intros N. unfold rts_iw. destruct (w =? 8) eqn:E; [apply Z.eqb_eq in E; subst; contradiction | reflexivity].
Qed.

Lemma useg_c : segC_stmt.
Proof.
  intros Espec P gv vc vd va u O c PF.
  unfold DE, II, segC, POST_m, su_locals, lv_locals.
  Intros.
  match goal with H : su_ok u |- _ => pose proof H as (Hlv & Hwb & Hmem & Hstr & Hn & Hdb & Hcap & Pd & Pc & Po) end.
  rewrite (cstream_split gv vc c) at 1. Intros. cbn [app].
  match goal with H : cs_no c = _ |- _ => rewrite H end.
  forward.
  forward.
  { entailer!. destruct (su_cp u); try contradiction. apply prop_right; unfold sameblock; cbn; destruct (peq b b); [reflexivity | congruence]. }
  rewrite sc_ptr_sub by (auto; unfold max_size in *; rep_lia).
  match goal with H : cs_no c = _ |- _ => rewrite <- H end.
  gather_SEP (field_at Ews t_z (DOT _next_out) _ vc) (cs_rest gv vc c). rewrite <- cstream_split.
  rewrite (sc_undef vd).
  forward_call (vd, Tsh, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef,
                Vundef, Vundef, Vundef).
  rewrite (sc_ns_raw gv vd).
  match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
    forward_if (PROPx [] (LOCALx
      [temp _compressed_len (vl (Zlength O)); temp _level (vi (su_level u));
       temp _window_bits (vi (rts_iw (su_wbits u))); temp _mem_level (vi (su_mem u));
       temp _strategy (vi (su_strategy u)); temp _data_len (vl (Zlength (su_data u)));
       temp _out_size (vl (su_cap u)); temp _data (su_dp u); temp _expected (su_ep u); temp _compressed (su_cp u); temp _out (su_op u);
       lvar _decompressor t_z vd; lvar _at t_p va; lvar _compressor t_z vc; gvars gv] (SEPx R))) end.
  { forward. entailer!. symmetry; apply sc_iw_8; auto. }
  { forward. entailer!. first [apply sc_iw_n8; auto | symmetry; apply sc_iw_n8; auto]. }
  make_func_ptr Zlib.inflate.code._zcalloc. make_func_ptr Zlib.inflate.code._zcfree.
  gather_SEP (func_ptr' _ (gv Zlib.inflate.code._zcalloc)) (func_ptr' _ (gv Zlib.inflate.code._zcfree)).
  fold (zfuncs gv).
  unfold Rm at 1. Intros. rewrite sc_hversion.
  assert_PROP (isptr (gv ___stringlit_rt_stream_1)) as Pv by entailer!.
  assert_PROP (isptr vd) as Pvd by entailer!.
  assert (Nd : vd <> nullval) by (intro; subst; contradiction).
  assert (Hw : Int.min_signed <= rts_iw (su_wbits u) <= Int.max_signed)
    by (unfold rts_iw, rs32 in *; destruct (su_wbits u =? 8); rep_lia).
  forward_call (gv, Tsh, vd, ns_raw, Vundef, Vundef, nullval, rts_iw (su_wbits u), gv ___stringlit_rt_stream_1,
                Ers, hv_list, 49, 112).
  { rewrite if_false by auto. cancel. }
  { change (Zlength hv_list) with 6. repeat split; auto; rep_lia. }
  Intros vret. destruct vret as [aok sp]. cbn [fst snd] in *.
  (* the window bits deflateInit2_ accepted are valid for inflateInit2_: Z_OK unless Z_MEM_ERROR *)
  assert (WB : wbits_ok (rts_iw (su_wbits u)) = true) by (eapply (ui_wbits P PF); eassumption).
  replace (init_ret vd 49 112 (rts_iw (su_wbits u)) aok)
    with (if aok then Z_OK else Z_MEM_ERROR)
    by (unfold init_ret; simpl; rewrite if_false by auto; rewrite WB; destruct aok; reflexivity).
  destruct aok; cbv iota.
  2: (* Z_MEM_ERROR: return 0, both locals given back *)
    forward_if; [ | exfalso; match goal with H : Int.repr _ <> _ |- _ => apply H; reflexivity end];
    sep_apply (sc_init_fail gv vd ns_raw Z_MEM_ERROR sp (rts_iw (su_wbits u)) Pvd ltac:(cbv; congruence));
    sep_apply (sc_comp_back gv vc c);
    forward; Exists (Int.repr 0); entailer!.
  (* Z_OK: a live stream *)
  set (L := init_live sp (rts_iw (su_wbits u))).
  replace (init_mem gv Tsh vd ns_raw Vundef Vundef nullval Z_OK sp (rts_iw (su_wbits u)))
    with (istream_raw gv Tsh vd (raw_after_init ns_raw (l_s L)) L)
    by (unfold init_mem; rewrite if_false by auto; reflexivity).
  forward_if; [exfalso; match goal with H : Int.repr _ = _ |- _ =>
                  apply (f_equal Int.unsigned) in H; vm_compute in H; discriminate end | ].
  forward_call (Int.repr 1).
  unfold istream_raw, raw_strm. Intros.
  match goal with H : live_ok L |- _ => rename H into LV end.
  rewrite sc_cs_inflate. unfold raw_after_init, ns_raw.
  cbn [rf_ni rf_ai rf_no rf_ao rf_res rf_tin rf_tout rf_dt rf_adler].
  (* the stores next_in = compressed, next_out = out (USegCStores) *)
  assert (HT : tycontext_sub Delta_m Delta) by (unfold Delta, abbreviate; apply tycontext_sub_refl).
  eapply semax_post_flipped'.
  { eapply (semax_Delta_subsumption Delta_m _ _ _ _ HT).
    unfold abbreviate in MORE_COMMANDS; subst MORE_COMMANDS. change (Ssequence _ _) with segC_stores.
    apply useg_c_stores. }
  unfold scs_locals.
  sep_apply (sc_istreamA gv vd (su_cp u) (su_op u) L LV).
  rewrite <- sc_hversion.
  destruct (ui_init P PF (su_level u) (su_mem u) (su_strategy u) (su_wbits u) (su_data u) O sp H0 H1 Hn
              ltac:(lia)) as [SW P0].
  assert (IL : il_ok P u O (mkIL 0 [] L (z_init (su_cp u) (su_op u) L))).
  { unfold il_ok, z_init; cbn [il_pos il_out il_L il_z zf_tout zf_ni zf_no].
    rewrite Zlength_nil, !isptr_offset_val_zero by auto.
    pose proof (Zlength_nonneg O).
    split; [exact P0 | split; [exact SW | split; [lia | split; [exists (su_data u); reflexivity | auto]]]]. }
  Exists (mkIL 0 [] L (z_init (su_cp u) (su_op u) L)).
  cbn [il_pos il_out il_L il_z]. rewrite (sc_head_init sp (rts_iw (su_wbits u)) : head_opt (Some L) = emp).
  unfold Rm. entailer!.
Qed.
