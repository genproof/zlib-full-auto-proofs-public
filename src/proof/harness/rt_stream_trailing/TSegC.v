(* Law rt_stream_trailing (harness/rt_stream_trailing.c): main's statements 27-33 (new_stream(&decompressor), window_bits 8 -> 9, inflateInit2_ with its Z_MEM_ERROR return and Z_OK assert, next_in = input, next_out = out), from DB_t to the inflate loop's invariant II_t.

   rt_stream's proof of the same statements (USegC.useg_c, whose lemmas on the decompressor and the compressor are
   reused here) without its first statement (compressed_len is computed earlier, in segB_t), with this harness's
   ZLIB_VERSION literal and next_in = input: the initial invariant is TIFacts.ti_init on the input object src
   (O, then any bytes). *)
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
Require Import Zlib.proof.harness.rt_stream.UDFacts.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.rt_stream.UIFacts.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_stream.LawCS.
Require Import Zlib.proof.harness.rt_stream.UMainKit.
Require Import Zlib.proof.harness.rt_stream.USegC.
Require Import Zlib.proof.harness.rt_stream_trailing.TIFacts.
Require Import Zlib.proof.harness.rt_stream_trailing.TMainStmt.
Require Import Zlib.proof.harness.rt_stream_trailing.TMainKit.
Require Import Zlib.proof.harness.rt_stream_trailing.TSegCStores.
Require Import Zlib.harness.rt_stream_trailing.code.
#[local] Existing Instance LawCS.CS.
Local Open Scope logic.

(* VST's after_forward_call simplifies remove_localdef_temp with `simpl rlt_ident_eq`, which runs away on main's
   identifiers (_i against _input); each identifier comparison is decided by vm_compute instead. *)
Ltac tc_rlt_fix u :=
  lazymatch u with
  | context C [rlt_ident_eq ?a ?b] =>
      let v := eval vm_compute in (rlt_ident_eq a b) in
      let u2 := context C [v] in tc_rlt_fix u2
  | _ => u
  end.

Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u := constr:(remove_localdef_temp i L) in
    let u' := eval lazy delta [remove_localdef_temp] beta iota in u in
    let u' := tc_rlt_fix u' in
    let u' := eval lazy beta iota in u' in
    let u' := eval lazy zeta in u' in
    change u with u'
  end.

(* this harness's "1.3.2" as inflateInit2_ takes it *)
Lemma tc_hversion gv :
  hversion_at_t gv = @data_at Zlib.units.Inflate.CS Ers (tarray tschar (Zlength hv_list)) hv_list
                       (gv ___stringlit_rt_stream_trailing_1).
Proof.
  unfold hversion_at_t, hv_list. change (Zlength _) with 6. symmetry.
  apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity].
Qed.

Lemma tseg_c : segC_t_stmt.
Proof.
  intros Espec P gv vc vd va u O c src ip PF.
  unfold DB_t, II_t, segC_t, POST_t, su_locals, lv_locals.
  Intros.
  match goal with H : su_ok u |- _ => pose proof H as (Hlv & Hwb & Hmem & Hstr & Hn & Hdb & Hcap & Pd & Pc & Po) end.
  match goal with H : src_ok O src |- _ => pose proof H as (Hsrc & Hsub & Hbytes) end.
  match goal with H : rparams_ok _ _ _ _ _ = true |- _ => rename H into Hrp end.
  match goal with H : dfinal _ _ _ _ _ _ |- _ => rename H into Hdf end.
  cbn [app].
  rewrite (sc_undef vd).
  forward_call (vd, Tsh, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef,
                Vundef, Vundef, Vundef).
  rewrite (sc_ns_raw gv vd).
  match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
    forward_if (PROPx [] (LOCALx
      [temp _compressed_len (vl (Zlength O)); temp _after (vl (Zlength src - Zlength O)); temp _input ip;
       temp _level (vi (su_level u));
       temp _window_bits (vi (rts_iw (su_wbits u))); temp _mem_level (vi (su_mem u));
       temp _strategy (vi (su_strategy u)); temp _data_len (vl (Zlength (su_data u)));
       temp _out_size (vl (su_cap u)); temp _data (su_dp u); temp _expected (su_ep u); temp _compressed (su_cp u); temp _out (su_op u);
       lvar _decompressor t_z vd; lvar _at t_p va; lvar _compressor t_z vc; gvars gv] (SEPx R))) end.
  { forward. entailer!. symmetry; apply sc_iw_8; auto. }
  { forward. entailer!. first [apply sc_iw_n8; auto | symmetry; apply sc_iw_n8; auto]. }
  make_func_ptr Zlib.inflate.code._zcalloc. make_func_ptr Zlib.inflate.code._zcfree.
  gather_SEP (func_ptr' _ (gv Zlib.inflate.code._zcalloc)) (func_ptr' _ (gv Zlib.inflate.code._zcfree)).
  fold (zfuncs gv).
  unfold Rm_t at 1. Intros. rewrite tc_hversion.
  assert_PROP (isptr (gv ___stringlit_rt_stream_trailing_1)) as Pv by entailer!.
  assert_PROP (isptr vd) as Pvd by entailer!.
  assert (Nd : vd <> nullval) by (intro; subst; contradiction).
  assert (Hw : Int.min_signed <= rts_iw (su_wbits u) <= Int.max_signed)
    by (unfold rts_iw, rs32 in *; destruct (su_wbits u =? 8); rep_lia).
  forward_call (gv, Tsh, vd, ns_raw, Vundef, Vundef, nullval, rts_iw (su_wbits u), gv ___stringlit_rt_stream_trailing_1,
                Ers, hv_list, 49, 112).
  { rewrite if_false by auto. cancel. }
  { change (Zlength hv_list) with 6. repeat split; auto; rep_lia. }
  Intros vret. destruct vret as [aok sp]. cbn [fst snd] in *.
  (* the window bits deflateInit2_ accepted are valid for inflateInit2_: Z_OK unless Z_MEM_ERROR *)
  assert (WB : wbits_ok (rts_iw (su_wbits u)) = true) by (eapply (ti_wbits P PF); eassumption).
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
  (* the stores next_in = input, next_out = out (TSegCStores) *)
  assert (HT : tycontext_sub Delta_t Delta) by (unfold Delta, abbreviate; apply tycontext_sub_refl).
  eapply semax_post_flipped'.
  { eapply (semax_Delta_subsumption Delta_t _ _ _ _ HT).
    unfold abbreviate in MORE_COMMANDS; subst MORE_COMMANDS. change (Ssequence _ _) with segC_t_stores.
    apply tseg_c_stores. }
  unfold tcs_locals.
  sep_apply (sc_istreamA gv vd ip (su_op u) L LV).
  rewrite <- tc_hversion.
  destruct (ti_init P PF (su_level u) (su_mem u) (su_strategy u) (su_wbits u) (su_data u) O src sp Hrp Hdf Hn
              Hsrc Hsub Hbytes) as [SW P0].
  assert (IL : il_ok_t P u O src ip (mkIL 0 [] L (z_init ip (su_op u) L))).
  { unfold il_ok_t, z_init; cbn [il_pos il_out il_L il_z zf_tout zf_ni zf_no].
    rewrite Zlength_nil, !isptr_offset_val_zero by auto.
    pose proof (Zlength_nonneg O).
    split; [exact P0 | split; [exact SW | split; [lia | split; [exists (su_data u); reflexivity | auto]]]]. }
  Exists (mkIL 0 [] L (z_init ip (su_op u) L)).
  cbn [il_pos il_out il_L il_z]. rewrite (sc_head_init sp (rts_iw (su_wbits u)) : head_opt (Some L) = emp).
  unfold Rm_t. entailer!.
Qed.
