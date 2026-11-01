(* Law deflate_roundtrip, gzip header: RTRMSeg1.v in main's context of the law, RTRSKit.Delta_mI
   (the intersections of Spec5's and the v6 specifications of inflate and inflateGetHeader); the proof unchanged.
   RTRMSeg1.v's comment: positions 1-5 of b0: gp_assert(deflateEnd(&s) == Z_OK)
   (ob_dstream_to_end and LawFacts.af_end_end with Iend (rf_s rf), as deflate_api9/MainTailMsg.v mt_end1_ok; then
   s is main's memory again: RTRRunMem.run_mem), stream_defaults(&t) (deflate HarnessLib's spec at DCS.CS; t to
   Spec5.raw_strm at Inflate.CS), iw (= rm_iw rf), inflateInit2_(&t, iw, ZLIB_VERSION, sizeof(z_stream))
   (Spec5.inflateInit2__spec; the version literal is RTRMainSpec.Rm's version_at gv vlit), and
   `if (r != Z_OK) return 0;` (t to data_at_ Tsh: init_mem). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.HarnessRef.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.roundtrip.RTXFacts.
Require Import Zlib.proof.roundtrip.RTRCS Zlib.proof.roundtrip.RTRRunSpec Zlib.proof.roundtrip.RTRRunKit Zlib.proof.roundtrip.RTRApiConv Zlib.proof.roundtrip.RTRMainSpec.
Require Import Zlib.proof.roundtrip.RTIIface.
Require Import Zlib.harness.x_deflate_roundtrip.code.
Require Import Zlib.proof.roundtrip.RTRMKit Zlib.proof.roundtrip.RTRSKit.
#[local] Existing Instance RTRCS.CS.
Local Open Scope logic.

(* api_fields without the next_in field (deflateEnd's spec takes next_in apart; deflate_api9/MainTailMsg.v af_split) *)
Definition rms1_af_rest (sp : val) (ain tin : Z) (nout : val) (aout tout : Z) (msgv : val) (adler : Z) : mpred :=
  !! (u32_ok ain /\ u64_ok tin /\ u32_ok aout /\ u64_ok tout /\ u64_ok adler) &&
  (@field_at DCS.CS Ews Zlib.proof.deflate.Rep.t_strm (DOT Zlib.deflate.code._avail_in) (vi ain) sp *
   @field_at DCS.CS Ews Zlib.proof.deflate.Rep.t_strm (DOT Zlib.deflate.code._total_in) (vl tin) sp *
   @field_at DCS.CS Ews Zlib.proof.deflate.Rep.t_strm (DOT Zlib.deflate.code._next_out) nout sp *
   @field_at DCS.CS Ews Zlib.proof.deflate.Rep.t_strm (DOT Zlib.deflate.code._avail_out) (vi aout) sp *
   @field_at DCS.CS Ews Zlib.proof.deflate.Rep.t_strm (DOT Zlib.deflate.code._total_out) (vl tout) sp *
   @field_at DCS.CS Ews Zlib.proof.deflate.Rep.t_strm (DOT Zlib.deflate.code._msg) msgv sp *
   @field_at DCS.CS Ews Zlib.proof.deflate.Rep.t_strm (DOT Zlib.deflate.code._adler) (vl adler) sp).

Lemma rms1_af_split (sp nin : val) (ain tin : Z) (nout : val) (aout tout : Z) (msgv : val) (adler : Z) :
  api_fields sp nin ain tin nout aout tout msgv adler =
  @field_at DCS.CS Ews Zlib.proof.deflate.Rep.t_strm (DOT Zlib.deflate.code._next_in) nin sp *
  rms1_af_rest sp ain tin nout aout tout msgv adler.
Proof. unfold api_fields, rms1_af_rest. apply pred_ext; entailer!. Qed.

Lemma rms1_af_join (sp nin : val) (ain tin : Z) (nout : val) (aout tout : Z) (msgv : val) (adler : Z) :
  @field_at DCS.CS Ews Zlib.proof.deflate.Rep.t_strm (DOT Zlib.deflate.code._next_in) nin sp *
  rms1_af_rest sp ain tin nout aout tout msgv adler |-- api_fields sp nin ain tin nout aout tout msgv adler.
Proof. rewrite rms1_af_split. apply derives_refl. Qed.

(* s after deflateEnd: main's memory again *)
Lemma rms1_s_mem vs gv nin ain tin nout aout tout msgv adler :
  dstream 2 None vs nullval gv * api_fields vs nin ain tin nout aout tout msgv adler * strm_pad vs *
  data_at_ (Share.comp Ews) t_strmL vs |-- data_at_ Tsh t_strmL vs * TT.
Proof.
  pose proof RTRRunMem.run_mem as (M1 & _ & _).
  sep_apply (M1 None vs nullval gv nin ain tin nout aout tout msgv adler).
  rewrite <- (data_at__share_join Ews (Share.comp Ews) Tsh) by apply join_comp_Tsh.
  cancel.
Qed.

Lemma rms1_dside_fold2 rf vR :
  field_at Ews t_drun (DOT _level) (vi (rs_level (rf_rs rf))) vR *
  field_at Ews t_drun (DOT _method) (vi (rs_method (rf_rs rf))) vR *
  field_at Ews t_drun (DOT _wbits) (vi (rs_wbits (rf_rs rf))) vR *
  field_at Ews t_drun (DOT _mem) (vi (rs_mem (rf_rs rf))) vR *
  field_at Ews t_drun (DOT _strategy) (vi (rs_strategy (rf_rs rf))) vR *
  field_at Ews t_drun (DOT _init) (vi 0) vR *
  field_at Ews t_drun (DOT _wrap) (vi (rf_wrap rf)) vR *
  field_at Ews t_drun (DOT _wb) (vi (wb_of (rs_wbits (rf_rs rf)))) vR *
  field_at Ews t_drun (DOT _data) (rs_datap (rf_rs rf)) vR *
  field_at Ews t_drun (DOT _n) (vi (Zlength (rs_data (rf_rs rf)))) vR *
  field_at Ews t_drun (DOT _nf) (vi (rf_nf rf)) vR *
  field_at Ews t_drun (DOT _dict) (rs_dictp (rf_rs rf)) vR *
  field_at Ews t_drun (DOT _dlen) (vi (Zlength (rs_dict (rf_rs rf)))) vR *
  field_at Ews t_drun (DOT _dict_set) (vi (rf_dset rf)) vR *
  field_at Ews t_drun (DOT _head_set) (vi (rf_hset rf)) vR *
  field_at Ews t_drun (DOT _xf) (rs_xfp (rf_rs rf)) vR *
  field_at Ews t_drun (DOT _nf_) (rs_nfp (rf_rs rf)) vR *
  field_at Ews t_drun (DOT _cf) (rs_cfp (rf_rs rf)) vR *
  field_at Ews t_drun (DOT _xlen) (vi (Zlength (rs_xf (rf_rs rf)))) vR *
  field_at Ews t_drun (DOT _nl) (vi (Zlength (rs_nm (rf_rs rf)))) vR *
  field_at Ews t_drun (DOT _cl) (vi (Zlength (rs_cm (rf_rs rf)))) vR *
  field_at Ews t_drun (DOT _comp) (rs_compp (rf_rs rf)) vR *
  field_at Ews t_drun (DOT _clen) (vl (Zlength (rf_O rf))) vR *
  field_at Ews t_drun (DOT _ended) (vi 1) vR *
  field_at Ews t_drun (DOT _api_ok) (vi 1) vR *
  drun_pad vR * hpart (rf_hset rf) vR * hdr_at (Some (rf_s rf)) (rf_ghp rf) (hx_of (rf_rs rf)) *
  obj (rs_datap (rf_rs rf)) (rs_data (rf_rs rf)) * obj (rs_dictp (rf_rs rf)) (rs_dict (rf_rs rf)) *
  comp_at (rf_O rf) (rs_compp (rf_rs rf)) * data_at_ (Share.comp Ews) t_drun vR |-- rm_dside rf vR.
Proof. unfold rm_dside, drun_rest. cancel. Qed.

Definition rms1_undef : rm_strm_tuple := rm_strm_undef.

Lemma rms1_t_dcs vt :
  @data_at_ CS Tsh t_strmL vt =
  @data_at DCS.CS Tsh Zlib.proof.deflate.Rep.t_strm rms1_undef vt.
Proof. rewrite <- strm_data_at__cs. unfold data_at_. reflexivity. Qed.

Lemma rms1_t_inf sh (v : rm_strm_tuple) q :
  @data_at DCS.CS sh Zlib.proof.deflate.Rep.t_strm v q =
  @data_at Zlib.units.Inflate.CS sh Zlib.proof.inflate.Rep.t_strm v q.
Proof. rewrite rm_strm_cs. apply strm_data_at_cs. Qed.

Lemma rms1_wb_raw Iend vR rf :
  rf_ok Iend vR rf -> rf_wrap rf = 0 -> 9 <= wb_of (rs_wbits (rf_rs rf)) <= 15.
Proof.
  intros OK W. destruct OK as (_ & _ & _ & _ & _ & _ & _ & _ & DF & HW & _).
  destruct DF as [DB _]. rewrite <- HW by exact W. exact DB.
Qed.

(** ** inflateInit2_ *)
Definition rms1_vc : list val := map (fun c => Vint (Int.repr c)) [49; 46; 51; 46; 50; 0].

Lemma rms1_tschar_inf sh n (v : list val) q :
  @data_at Zlib.units.Inflate.CS sh (tarray tschar n) v q = @data_at CS sh (tarray tschar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity]. Qed.

Lemma rms1_tschar_dcs sh n (v : list val) q :
  @data_at DCS.CS sh (tarray tschar n) v q = @data_at CS sh (tarray tschar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_dcs); [apply JMeq_refl | reflexivity]. Qed.

Definition rms1_Rrest (gv : globals) : mpred :=
  deflate_globals gv * Zlib.proof.inflate.Rep.tables_rep Ers gv.

Lemma rms1_ver gv :
  version_at gv vlit = @data_at Zlib.units.Inflate.CS Ers (tarray tschar (Zlength rms1_vc)) rms1_vc (gv vlit).
Proof. unfold version_at. rewrite rms1_tschar_inf, rms1_tschar_dcs. reflexivity. Qed.

Lemma rms1_Rm_open gv :
  Rm gv |-- @data_at Zlib.units.Inflate.CS Ers (tarray tschar (Zlength rms1_vc)) rms1_vc (gv vlit) *
            Zlib.proof.inflate_api.Spec5.version_lit gv * rms1_Rrest gv.
Proof. unfold Rm, rms1_Rrest. rewrite rms1_ver. cancel. Qed.

Lemma rms1_Rm_close gv :
  @data_at Zlib.units.Inflate.CS Ers (tarray tschar (Zlength rms1_vc)) rms1_vc (gv vlit) *
  Zlib.proof.inflate_api.Spec5.version_lit gv * rms1_Rrest gv |-- Rm gv.
Proof. unfold Rm, rms1_Rrest. rewrite rms1_ver. cancel. Qed.

Definition rms1_rr (tin tout dt adl rs0 : Z) : rawf :=
  RF nullval (vi 0) (vl tin) nullval (vi 0) (vl tout) (vi dt) (vl adl) (vl rs0).

Lemma rms1_raw gv vt tin tout dt adl rs0 :
  isptr vt ->
  @data_at DCS.CS Tsh Zlib.proof.deflate.Rep.t_strm
    (nullval, (vi 0, (vl tin, (nullval, (vi 0, (vl tout, (Vundef, (Vundef,
     (nullval, (nullval, (nullval, (vi dt, (vl adl, vl rs0))))))))))))) vt
  |-- if eq_dec vt nullval then emp else raw_strm gv Tsh vt (rms1_rr tin tout dt adl rs0) Vundef Vundef nullval nullval nullval.
Proof.
  intros P. rewrite if_false by (destruct vt; try contradiction; discriminate).
  rewrite rms1_t_inf. unfold raw_strm, rms1_rr. simpl. apply derives_refl.
Qed.

Lemma rms1_init_ret (vt : val) w a : isptr vt ->
  init_ret vt 49 112 w a = if a then (if wbits_ok w then Z_OK else Z_STREAM_ERROR) else Z_MEM_ERROR.
Proof.
  intros P. unfold init_ret, sizeof_z_stream. simpl.
  rewrite if_false by (destruct vt; try contradiction; discriminate). destruct a; reflexivity.
Qed.

(* t after a failed inflateInit2_: main's memory *)
Lemma rms1_init_fail gv vt r msgv stv opq ret sp w :
  isptr vt -> ret <> Z_OK ->
  init_mem gv Tsh vt r msgv stv opq ret sp w |-- data_at_ Tsh t_strmL vt.
Proof.
  intros P Hr. unfold init_mem.
  destruct (eq_dec vt nullval); [subst; contradiction | ].
  destruct (ret =? Z_VERSION_ERROR); [unfold raw_strm; apply rm_strm_to_undef | ].
  destruct (ret =? Z_MEM_ERROR); [unfold raw_strm; apply rm_strm_to_undef | ].
  destruct (Z.eqb_spec ret Z_OK); [contradiction | ].
  unfold raw_strm; apply rm_strm_to_undef.
Qed.

(* the stream fields after stream_defaults and a successful inflateInit2_ *)
Definition rms1_z (adl rs0 : Z) (L : live) : zfields :=
  ZF nullval 0 0 nullval 0 0 None 0 (if i_wrap (l_s L) =? 0 then adl else Z.land (i_wrap (l_s L)) 1) (vl rs0).

Lemma rms1_z_ok adl rs0 L :
  0 <= adl <= Int64.max_unsigned -> 0 <= i_wrap (l_s L) -> rm_zinit (rms1_z adl rs0 L).
Proof.
  intros A W. unfold rm_zinit, zf_ok, rms1_z; cbn [zf_ok zf_ni zf_ai zf_no zf_ao zf_tout zf_msg zf_tin zf_dt zf_adler].
  repeat split; try rep_lia; auto.
  - destruct (i_wrap (l_s L) =? 0); [lia | ].
    assert (M: Z.land (i_wrap (l_s L)) 1 = i_wrap (l_s L) mod 2) by (apply (Z.land_ones _ 1); lia).
    rewrite M. pose proof (Z.mod_pos_bound (i_wrap (l_s L)) 2 ltac:(lia)). rep_lia.
  - destruct (i_wrap (l_s L) =? 0); [lia | ].
    assert (M: Z.land (i_wrap (l_s L)) 1 = i_wrap (l_s L) mod 2) by (apply (Z.land_ones _ 1); lia).
    rewrite M. pose proof (Z.mod_pos_bound (i_wrap (l_s L)) 2 ltac:(lia)). rep_lia.
Qed.

Lemma rms1_istream gv vt tin tout dt adl rs0 L :
  0 <= adl <= Int64.max_unsigned -> 0 <= i_wrap (l_s L) ->
  istream_raw gv Tsh vt (raw_after_init (rms1_rr tin tout dt adl rs0) (l_s L)) L
  = istream gv Tsh vt (rms1_z adl rs0 L) (Some L).
Proof.
  intros A W. rewrite <- istream_raw_istream.
  - unfold raw_after_init, rms1_z, rms1_rr; simpl. f_equal. f_equal. destruct (i_wrap (l_s L) =? 0); reflexivity.
  - apply rms1_z_ok; auto.
  - reflexivity.
Qed.

Lemma rms1_iw_range Iend vR rf : rf_ok Iend vR rf -> -15 <= rm_iw rf <= 32.
Proof.
  intros OK. unfold rm_iw, iw_of.
  destruct (Z.eqb_spec (rf_wrap rf) 0) as [W | W].
  - pose proof (rms1_wb_raw _ _ _ OK W). lia.
  - destruct (rf_wrap rf =? 1); lia.
Qed.

Lemma rms1_wrap_nn sp w : wbits_ok w = true -> 0 <= i_wrap (l_s (init_live sp w)).
Proof.
  (* fix F8: inflateInit2_ stores reset2_wrap wrap wb (bit 3 set when wb = 0), nonnegative in every case *)
  unfold wbits_ok, init_live. destruct (reset2_wb w) as [[wr wb]|] eqn:E; [|discriminate]. intros _.
  cbn [l_s]. destruct (reset2_wrap_ok w wr wb E) as (R & _).
  unfold init_s, reset2_s, reset_full_s, reset_hdr_s. simpl.
  assert (0 <= reset2_wrap wr wb) by lia. destruct (_ =? 0); exact H.
Qed.

Ltac rms1_infeas := exfalso; first [ match goal with H: ?a <> ?b |- _ => solve [apply H; reflexivity] end
                              | match goal with H: _ |- _ => solve [discriminate H] end
                              | contradiction
                              | match goal with H: Int.repr _ = Int.repr _ |- _ =>
                                  apply repr_inj_signed in H; [lia | rep_lia | rep_lia] end
                              | lia ].

Lemma rms_seg1 {Espec : OracleKind} I Iend rf vR vs vt vih gv :
  api_facts I Iend -> Zlib.proof.deflate.Obligations.ob_dstream_to_end ->
  (forall z sp, semax (Delta_mI I Iend) (A6 Iend rf vR vs vt vih gv z sp) seg6 POST_b) ->
  semax (Delta_mI I Iend) (A1 Iend rf vR vs vt vih gv) seg1 POST_b.
Proof.
  intros AF HE K.
  unfold A1, run_ok_at, seg1, Delta_mI, GmI, POST_b, POST_m. Intros.
  simplify_func_tycontext. abbreviate_semax.
  sep_apply (HE (Some (rf_s rf)) vs (rf_ghp rf) gv).
  rewrite rms1_af_split.
  forward_call (Some (rf_s rf), vs, rf_nin rf, zmk [] 0 0 0 0 0 0 None,
                (@None dstate, zmk [] 0 0 0 0 0 0 None, Z_OK), gv).
  all: try (cancel; fail).
  { destruct H as (_ & HI & _). apply (af_end_end _ _ AF); auto. }
  cbn [fst snd].
  forward_call (Int.one).
  sep_apply (rms1_af_join vs (rf_nin rf) (rf_ain rf) (RTRRunSpec.rf_tin rf) (rf_nout rf) (rf_aout rf)
               (RTRRunSpec.rf_tout rf) (rf_msgv rf) (RTRRunSpec.rf_adler rf)).
  sep_apply rms1_s_mem.
  rewrite (rms1_t_dcs vt). unfold rms1_undef, rm_strm_undef.
  forward_call (vt, Tsh, Vundef, Vundef).
  Intros vret. destruct vret as [[[[tin tout] adl] dt] rs0]. cbn [fst snd] in *.
  unfold drun_rest. Intros.
  forward.
  assert (Hwr : 0 <= rf_wrap rf <= 2)
    by (unfold rf_wrap, wrap_of; destruct (_ <? 0); [lia | destruct (_ >? 15); lia]).
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'4 (vi (rm_iw rf)) :: Q) (SEPx R))) end.
  { pose proof (rms1_wb_raw _ _ _ H H5) as WB.
    forward. forward.
    { entailer!. rewrite Int.signed_zero. rep_lia. }
    entailer!. unfold rm_iw, iw_of. rewrite H5. reflexivity. }
  { forward. forward_if.
    - forward. forward. entailer!. unfold rm_iw, iw_of.
      destruct (Z.eqb_spec (rf_wrap rf) 0); [lia | ]. destruct (Z.eqb_spec (rf_wrap rf) 1); [reflexivity | ].
      lia.
    - forward. forward. entailer!. unfold rm_iw, iw_of.
      destruct (Z.eqb_spec (rf_wrap rf) 0); [lia | ]. destruct (Z.eqb_spec (rf_wrap rf) 1); [ | reflexivity].
      exfalso. apply H6. f_equal. assumption. }
  forward.
  sep_apply rms1_dside_fold2.
  assert_PROP (isptr vt) as Pvt by entailer!.
  sep_apply (rms1_raw gv vt tin tout dt adl rs0 Pvt).
  replace_SEP 7 (@data_at Zlib.units.Inflate.CS Ers (tarray tschar (Zlength rms1_vc)) rms1_vc (gv vlit) *
                 Zlib.proof.inflate_api.Spec5.version_lit gv * rms1_Rrest gv).
  { entailer!. apply rms1_Rm_open. }
  flatten_sepcon_in_SEP.
  assert_PROP (isptr (gv vlit)) as Pver by entailer!.
  pose proof (rms1_iw_range _ _ _ H) as IWR.
  forward_call (gv, Tsh, vt, rms1_rr tin tout dt adl rs0, Vundef, Vundef, nullval, rm_iw rf,
                gv vlit, Ers, rms1_vc, 49, 112).
  all: try (cancel; fail).
  { repeat match goal with |- _ /\ _ => split end; try exact Pver; auto; change (Zlength rms1_vc) with 6; rep_lia. }
  Intros vret. destruct vret as [alloc_ok sp]. cbn [fst snd] in *.
  rewrite (rms1_init_ret vt (rm_iw rf) alloc_ok Pvt).
  destruct alloc_ok; [destruct (wbits_ok (rm_iw rf)) eqn:WOK | ].
  2: { forward_if; [ | rms1_infeas ].
       sep_apply (rms1_init_fail gv vt (rms1_rr tin tout dt adl rs0) Vundef Vundef nullval Z_STREAM_ERROR sp
                    (rm_iw rf) Pvt ltac:(discriminate)).
       sep_apply (rm_dside_ret Iend vR rf H).
       forward. Exists (Int.repr 0). entailer!. }
  2: { forward_if; [ | rms1_infeas ].
       sep_apply (rms1_init_fail gv vt (rms1_rr tin tout dt adl rs0) Vundef Vundef nullval Z_MEM_ERROR sp
                    (rm_iw rf) Pvt ltac:(discriminate)).
       sep_apply (rm_dside_ret Iend vR rf H).
       forward. Exists (Int.repr 0). entailer!. }
  forward_if.
  { rms1_infeas. }
  unfold init_mem.
  rewrite if_false by (destruct vt; try contradiction; discriminate).
  change (Z_OK =? Z_VERSION_ERROR) with false; change (Z_OK =? Z_MEM_ERROR) with false;
    change (Z_OK =? Z_OK) with true.
  cbv beta iota zeta.
  pose proof (rms1_wrap_nn sp (rm_iw rf) WOK) as WN.
  rewrite (rms1_istream gv vt tin tout dt adl rs0 (init_live sp (rm_iw rf))) by (auto; unfold u64r in H2; rep_lia).
  pose proof (rms1_z_ok adl rs0 (init_live sp (rm_iw rf)) ltac:(unfold u64r in H2; rep_lia) WN) as ZI.
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre; [ | apply (K (rms1_z adl rs0 (init_live sp (rm_iw rf))) sp) ].
  unfold A6. entailer!.
  sep_apply rms1_Rm_close. cancel.
Qed.
