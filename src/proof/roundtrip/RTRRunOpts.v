(* Law deflate_api, deflate_run: deflateTune, deflateSetDictionary, deflateSetHeader, up to the loop (RunKit.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.roundtrip.RTXFacts.
Require Import Zlib.proof.roundtrip.RTRCS Zlib.proof.roundtrip.RTRRunSpec
               Zlib.proof.roundtrip.RTRApiConv Zlib.proof.roundtrip.RTRRunKit.
Require Import Zlib.harness.x_deflate_roundtrip.code.
#[local] Existing Instance RTRCS.CS.
Local Open Scope logic.

Definition rsuf53 : statement := ltac:(get_rsuf 53%nat).

(* A3 (before if (hsel == 0)): deflateTune / deflateSetDictionary done *)
Definition A3 I Iend Rp sp api vosn gv (rs : rsetup) (s : dstate) (dict : list Z) (dset : Z) (tin tout adler : Z)
    (nin : val) (ain : Z) (nout : val) (aout : Z) (msg : option Z) (msgv : val) : environ -> mpred :=
  PROP (rs_ok rs; api_facts I Iend; s32 api;
        I dict (wrap_of (rs_wbits rs)) [] [] None s tin tout adler; d_gzhead s = None; msg_ok msg msgv;
        (dset = 1 /\ dict = rs_dict rs /\ rs_dict rs <> []) \/ (dset = 0 /\ dict = []);
        rt_extra I; wbx rs s)
  LOCAL (temp _mtime (vl (rs_mtime rs)); temp _hsel (vi (rs_hsel rs)); temp _text (vi (rs_text rs));
         temp _os (vi (rs_os rs)); temp _hcrc (vi (rs_hcrc rs));
         temp _R Rp; temp _s sp; temp _api (vi api); lvar _osnap (tptr tuchar) vosn; gvars gv)
  SEP (drun_rest rs (vi 0) (vi (wrap_of (rs_wbits rs))) (vi (wb_of (rs_wbits rs))) (Zlength (rs_data rs)) dset 0 0 0 Rp;
       field_at_ Ews t_drun (DOT _h) Rp;
       dstream 2 (Some s) sp nullval gv; api_fields sp nin ain tin nout aout tout msgv adler; strm_pad sp;
       allobjs rs; mem_mgr gv; deflate_globals gv; data_at_ Tsh (tptr tuchar) vosn; TT; version_at gv vlit).

(** ** Helpers of run_head_ok: R->h as the gz_header of deflateSetHeader *)

(* the three spacers of struct gz_header (field_at does not hold them): one SEP item *)
Definition h_pad (hp : val) : mpred := spacer Ews 4 8 hp * spacer Ews 52 56 hp * spacer Ews 76 80 hp.

Lemma h_field_dcs (Rp : val) (v : reptype t_gzh) :
  field_at Ews t_drun (DOT _h) v Rp = @data_at DCS.CS Ews t_gzh v (hp_of Rp).
Proof.
  rewrite field_at_data_at. unfold hp_of. change (nested_field_type t_drun (DOT _h)) with t_gzh.
  symmetry. apply equal_f. apply (@data_at_change_composite _ _ CC_dcs); [apply JMeq_refl | reflexivity].
Qed.

Lemma h_field__dcs (Rp : val) :
  field_at_ Ews t_drun (DOT _h) Rp = @data_at_ DCS.CS Ews t_gzh (hp_of Rp).
Proof.
  unfold field_at_, data_at_. apply h_field_dcs.
Qed.

Lemma gzh_split (hp a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 : val) :
  @data_at DCS.CS Ews t_gzh (a1, (a2, (a3, (a4, (a5, (a6, (a7, (a8, (a9, (a10, (a11, (a12, a13)))))))))))) hp =
  @field_at DCS.CS Ews t_gzh (DOT _text) a1 hp * @field_at DCS.CS Ews t_gzh (DOT _time) a2 hp *
  @field_at DCS.CS Ews t_gzh (DOT _xflags) a3 hp * @field_at DCS.CS Ews t_gzh (DOT _os) a4 hp *
  @field_at DCS.CS Ews t_gzh (DOT _extra) a5 hp * @field_at DCS.CS Ews t_gzh (DOT _extra_len) a6 hp *
  @field_at DCS.CS Ews t_gzh (DOT _extra_max) a7 hp * @field_at DCS.CS Ews t_gzh (DOT _name) a8 hp *
  @field_at DCS.CS Ews t_gzh (DOT _name_max) a9 hp * @field_at DCS.CS Ews t_gzh (DOT _comment) a10 hp *
  @field_at DCS.CS Ews t_gzh (DOT _comm_max) a11 hp * @field_at DCS.CS Ews t_gzh (DOT _hcrc) a12 hp *
  @field_at DCS.CS Ews t_gzh (DOT _done) a13 hp * h_pad hp.
Proof.
  unfold h_pad. unfold_data_at (@data_at DCS.CS _ _ _ hp). apply pred_ext; cancel.
Qed.

Lemma gzh_of_stores_h (h : gzh) (hp xp np cp xv xm nm cm dn : val) :
  gzh_ok h ->
  @data_at DCS.CS Ews t_gzh (vi (gz_text h), (vl (gz_time h), (xv, (vi (gz_os h), (xp, (vi (gz_extra_len h),
    (xm, (np, (nm, (cp, (cm, (vi (gz_hcrc h), dn)))))))))))) hp *
  opt_obj Ews (gz_extra h) xp * opt_obj Ews (gz_name h) np * opt_obj Ews (gz_comment h) cp
  |-- gzh_at Ews h hp xp np cp * h_pad hp.
Proof.
  intros. rewrite gzh_split. unfold gzh_at. Exists dn cm nm xm xv.
  entailer!.
Qed.

Lemma gzh_at_back_h (h : gzh) (hp xp np cp : val) :
  gzh_at Ews h hp xp np cp * h_pad hp
  |-- @data_at_ DCS.CS Ews t_gzh hp *
      opt_obj Ews (gz_extra h) xp * opt_obj Ews (gz_name h) np * opt_obj Ews (gz_comment h) cp.
Proof.
  unfold gzh_at. Intros v1 v2 v3 v4 v5.
  change (@data_at_ DCS.CS Ews t_gzh hp) with (@data_at DCS.CS Ews t_gzh
    (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef,
    (Vundef, Vundef)))))))))))) hp).
  rewrite gzh_split. cancel.
Qed.

(* text & 1, hcrc & 1 *)
Lemma and1_repr (x : Z) : 0 <= x < 256 -> Int.and (Int.repr x) (Int.repr 1) = Int.repr (Z.land x 1).
Proof.
  intros Hx. unfold Int.and. rewrite !Int.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma land1_01 (x : Z) : Z.land x 1 = 0 \/ Z.land x 1 = 1.
Proof.
  assert (E : Z.land x 1 = x mod 2) by (apply (Z.land_ones x 1); lia).
  rewrite E. pose proof (Z.mod_pos_bound x 2 ltac:(lia)). lia.
Qed.

Lemma hdr_of_ok (rs : rsetup) : rs_ok rs -> hdr_ok (hdr_of rs) /\ gzh_ok (hdr_of rs).
Proof.
  intros OK. unfold rs_ok in OK.
  destruct OK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hmt & _ & _ & _ & Htx & Hos & Hhc & _ & _ & Hxl & Hnl & Hcl &
    _ & _ & Hxb & Hnb & Hcb & _).
  unfold u32r in *.
  pose proof (land1_01 (rs_text rs)) as Et. pose proof (land1_01 (rs_hcrc rs)) as Ec.
  pose proof (Zlength_nonneg (rs_xf rs)).
  split.
  - unfold hdr_ok, hdr_of; cbn [gz_text gz_time gz_os gz_extra gz_extra_len gz_name gz_comment gz_hcrc].
    split; [ exact Et | ]. split; [ exact Ec | ]. split; [ lia | ]. split; [ unfold u32r; lia | ].
    split; [ lia | ]. split; [ | split ].
    + intros x Ex. inversion Ex; subst; auto.
    + unfold cstr_ok. intros l El. inversion El; subst.
      exists (rs_nm rs). split; [ reflexivity | ]. split; [ lia | exact Hnb ].
    + unfold cstr_ok. intros l El. inversion El; subst.
      exists (rs_cm rs). split; [ reflexivity | ]. split; [ lia | exact Hcb ].
  - unfold gzh_ok, hdr_of; cbn [gz_text gz_time gz_os gz_extra_len gz_hcrc]. rep_lia.
Qed.

(* an object as the header's optional object (the token of a non-empty one is left over); v6: of bytes *)
Lemma obj_opt (q : val) (l : list Z) : Forall (fun x => 0 <= x < 256) l -> obj q l |-- opt_obj Ews (Some l) q * TT.
Proof.
  intros HB. unfold obj, opt_obj. rewrite prop_true_andp by exact HB. rewrite (bytes_cs CS DCS.CS).
  destruct (Zlength l =? 0) eqn:E.
  - apply Z.eqb_eq in E. rewrite E. rewrite tok_tuchar_cs. cancel.
  - cancel.
Qed.

Lemma nz_bytes0 (l : list Z) : Forall (fun b => 0 < b < 256) l -> Forall (fun x => 0 <= x < 256) (l ++ [0]).
Proof.
  intros H. apply Forall_app; split.
  - eapply Forall_impl; [| exact H]. simpl; intros; lia.
  - repeat constructor; lia.
Qed.

(* the dictionary object as deflateSetDictionary's opt_obj (v7) and the rest of it *)
Definition obj_rest (q : val) (l : list Z) : mpred :=
  if Zlength l =? 0 then emp else malloc_token Ews (tarray tuchar (Zlength l)) q.

Lemma obj_opt_obj (q : val) (l : list Z) :
  Forall (fun x => 0 <= x < 256) l -> obj q l = opt_obj Ews (Some l) q * obj_rest q l.
Proof.
  intros HB. unfold obj, opt_obj, obj_rest. rewrite prop_true_andp by exact HB. rewrite (bytes_cs CS DCS.CS).
  destruct (Zlength l =? 0) eqn:E; [apply Z.eqb_eq in E; rewrite E; rewrite tok_tuchar_cs |];
    apply pred_ext; cancel.
Qed.

(* the 13 stores of R->h and the objects xf, nf_, cf: the header of [hdr_of rs] *)
Lemma h_stores (rs : rsetup) (Rp : val) :
  rs_ok rs ->
  field_at Ews t_drun (DOT _h)
     (Vint (Int.and (Int.repr (rs_text rs)) (Int.repr 1)),
      (vl (rs_mtime rs),
       (Vint (Int.repr 0),
        (Vint (Int.repr (rs_os rs)),
         (rs_xfp rs,
          (Vint (Int.repr (Zlength (rs_xf rs))),
           (Vint (Int.repr 0),
            (rs_nfp rs,
             (Vint (Int.repr 0),
              (rs_cfp rs,
               (Vint (Int.repr 0),
                (Vint (Int.and (Int.repr (rs_hcrc rs)) (Int.repr 1)),
                 Vint (Int.repr 0))))))))))))) Rp *
  allobjs rs
  |-- gzh_at Ews (hdr_of rs) (hp_of Rp) (rs_xfp rs) (rs_nfp rs) (rs_cfp rs) * h_pad (hp_of Rp) *
      obj (rs_datap rs) (rs_data rs) * obj (rs_dictp rs) (rs_dict rs) * comp_at [] (rs_compp rs) * TT.
Proof.
  intros OK. pose proof (hdr_of_ok rs OK) as [_ Gok].
  destruct OK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Htx & _ & Hhc & _ & _ & _ & _ & _ &
    _ & _ & Hxb & Hnb & Hcb & _).
  rewrite !and1_repr by assumption.
  rewrite h_field_dcs. unfold allobjs.
  sep_apply (obj_opt (rs_xfp rs) (rs_xf rs) Hxb).
  sep_apply (obj_opt (rs_nfp rs) (rs_nm rs ++ [0]) (nz_bytes0 _ Hnb)).
  sep_apply (obj_opt (rs_cfp rs) (rs_cm rs ++ [0]) (nz_bytes0 _ Hcb)).
  sep_apply (gzh_of_stores_h (hdr_of rs) (hp_of Rp) (rs_xfp rs) (rs_nfp rs) (rs_cfp rs) (Vint (Int.repr 0))
    (Vint (Int.repr 0)) (Vint (Int.repr 0)) (Vint (Int.repr 0)) (Vint (Int.repr 0)) Gok).
  cancel.
Qed.

(* the header part: statements 53..56 *)
Lemma run_head_ok {Espec : OracleKind} I Iend Rp sp api vosn gv rs s dict dset tin tout adler nin ain nout aout
    msg msgv :
  (forall ls, semax Delta_r (J_at I Iend Rp sp api vosn gv rs ls) rsuf57 (POST_r Iend Rp sp gv)) ->
  semax Delta_r (A3 I Iend Rp sp api vosn gv rs s dict dset tin tout adler nin ain nout aout msg msgv) rsuf53
    (POST_r Iend Rp sp gv).
Proof.
  intros HJ. unfold A3, rsuf53. Intros.
  pose proof H as OK. unfold rs_ok in OK.
  destruct OK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hmt & _ & _ & Hhs & Htx & Hos & Hhc & _ & _ & Hxl & Hnl & Hcl &
    _ & _ & Hxb & Hnb & Hcb & _ & _ & Pxf & Pnf & Pcf & _).
  forward_if (EX hset : Z, EX ghp : val, EX s' : dstate,
    PROP (I dict (wrap_of (rs_wbits rs)) [] [] None s' tin tout adler; wbx rs s';
          hset = 1 -> wrap_of (rs_wbits rs) = 2;
          (hset = 1 /\ ghp = hp_of Rp /\ d_gzhead s' = Some (hdr_of rs)) \/ (hset = 0 /\ d_gzhead s' = None))
    LOCAL (temp _R Rp; temp _s sp; temp _api (vi api); lvar _osnap (tptr tuchar) vosn; gvars gv)
    SEP (drun_rest rs (vi 0) (vi (wrap_of (rs_wbits rs))) (vi (wb_of (rs_wbits rs))) (Zlength (rs_data rs))
           dset hset 0 0 Rp;
         hpart hset Rp; dstream 2 (Some s') sp ghp gv; hdr_at (Some s') ghp (hx_of rs);
         api_fields sp nin ain tin nout aout tout msgv adler; strm_pad sp;
         obj (rs_datap rs) (rs_data rs); obj (rs_dictp rs) (rs_dict rs); comp_at [] (rs_compp rs);
         mem_mgr gv; deflate_globals gv; data_at_ Tsh (tptr tuchar) vosn; TT; version_at gv vlit)).
  { unfold drun_rest. Intros.
    freeze [0;1;2;3;4;5;7;8;9;10;11;12;13;19;20;21;22;23;24;25;29;31;32;33] FR.
    forward. forward. forward. forward. forward. forward. forward. forward. forward. forward. forward.
    forward. forward. forward. forward. forward. forward.
    destruct (hdr_of_ok rs H) as [Hok Gok].
    pose proof H0 as [_ _ _ Fhead _ _ _ _ _ _].
    set (zz := zcall [] 0 0 0 0 0 0 None).
    destruct (Fhead dict (wrap_of (rs_wbits rs)) s tin tout adler (hdr_of rs) zz H2 Hok) as [Hw2 Hwn].
    assert_PROP (field_compatible t_drun (DOT _h) Rp) as FCh by entailer!.
    sep_apply (h_stores rs Rp H). Intros.
    unfold api_fields. Intros.
    destruct (Z.eq_dec (wrap_of (rs_wbits rs)) 2) as [Ew|Ew].
    - (* gzip: Z_OK *)
      destruct (Hw2 Ew) as [Hc HI'].
      forward_call (Some s, sp, nin, nullval, hp_of Rp, hdr_of rs, rs_xfp rs, rs_nfp rs, rs_cfp rs,
        (Some (set_d_gzhead s (Some (hdr_of rs))), zz, Z_OK), zz, gv).
      { entailer!. simpl. unfold hp_of. rewrite field_address_offset by auto. reflexivity. }
      { unfold on_state, c_on_state. rewrite Hc. reflexivity. }
      cbn [fst snd]. simpl (Z_OK =? Z_OK). cbv iota.
      clear Hw2 Hwn Fhead.
      forward_if True.
      { forward. forward_if (temp _t'49 (vi 1)).
        { forward_if. { forward. entailer!. } { exfalso. auto. } }
        { exfalso. match goal with Hx : Int.repr 1 <> _ |- _ => apply Hx end. rewrite Ew. reflexivity. }
        forward_call Int.one. entailer!. }
      { forward. entailer!. }
      forward.
      Exists 1 (hp_of Rp) (set_d_gzhead s (Some (hdr_of rs))).
      thaw FR. unfold drun_rest, hpart, hdr_at, hx_of, gzh_pad, h_pad, api_fields. simpl (1 =? 1). cbv iota.
      change (d_gzhead (set_d_gzhead s (Some (hdr_of rs)))) with (Some (hdr_of rs)).
      assert (Hwbs : wbx rs (set_d_gzhead s (Some (hdr_of rs))))
        by (match goal with Hx : wbx rs s |- _ => exact Hx end).
      assert (Hhw : 1 = 1 -> wrap_of (rs_wbits rs) = 2) by (intros; exact Ew).
      entailer!.
    - (* not gzip: Z_STREAM_ERROR *)
      specialize (Hwn Ew) as Hc.
      forward_call (Some s, sp, nin, nullval, hp_of Rp, hdr_of rs, rs_xfp rs, rs_nfp rs, rs_cfp rs,
        (Some s, zz, Z_STREAM_ERROR), zz, gv).
      { entailer!. simpl. unfold hp_of. rewrite field_address_offset by auto. reflexivity. }
      { unfold on_state, c_on_state. rewrite Hc. reflexivity. }
      cbn [fst snd]. simpl (Z_STREAM_ERROR =? Z_OK). cbv iota.
      clear Hw2 Hwn Fhead.
      forward_if True.
      { forward. forward_if (temp _t'49 (vi 1)).
        { forward_if. { exfalso. discriminate. } { forward. forward. entailer!. } }
        { exfalso. match goal with Hx : Int.repr 0 <> _ |- _ => apply Hx end. unfold wrap_of in *.
          repeat destruct (_ <? _); repeat destruct (_ >? _); try reflexivity; congruence. }
        forward_call Int.one. entailer!. }
      { forward. entailer!. }
      forward.
      Exists 0 nullval s.
      thaw FR. unfold drun_rest, hpart, hdr_at, hx_of, api_fields. simpl (0 =? 1). cbv iota. rewrite H3.
      sep_apply (gzh_at_back_h (hdr_of rs) (hp_of Rp) (rs_xfp rs) (rs_nfp rs) (rs_cfp rs)).
      rewrite <- h_field__dcs.
      assert (Hhw : 0 = 1 -> wrap_of (rs_wbits rs) = 2) by (intros; discriminate).
      entailer!. }
  { forward. Exists 0 nullval s. unfold hdr_at, hpart. rewrite H3. simpl (0 =? 1). unfold allobjs.
    assert (Hhw : 0 = 1 -> wrap_of (rs_wbits rs) = 2) by (intros; discriminate).
    entailer!. }
  Intros hset ghp s'.
  forward. forward. forward.
  eapply semax_pre; [ | apply (HJ (mkLS dict 0 [] None s' tin tout adler nin ain nout aout msg msgv
    (Zlength (rs_data rs)) dset hset ghp)) ].
  unfold J_at, lsep, J_ok. cbn [ls_dict ls_pos ls_O ls_fin ls_s ls_tin ls_tout ls_adler ls_nin ls_ain ls_nout
    ls_aout ls_msg ls_msgv ls_nf ls_dset ls_hset ls_ghp fin_flag].
  rewrite sublist_nil, Zlength_nil.
  entailer!. unfold bytes. constructor.
Qed.

Lemma run_opts_ok {Espec : OracleKind} I Iend Rp sp api vosn gv rs s tin tout adler nin ain nout aout msg msgv :
  is_pointer_or_null nin ->
  (forall ls, semax Delta_r (J_at I Iend Rp sp api vosn gv rs ls) rsuf57 (POST_r Iend Rp sp gv)) ->
  semax Delta_r (A2 I Iend Rp sp api vosn gv rs s tin tout adler nin ain nout aout msg msgv) rsuf51
    (POST_r Iend Rp sp gv).
Proof.
  intros Hnin HJ. unfold rsuf51, A2. abbreviate_semax. Intros.
  rename H into RSOK, H0 into AF, H1 into Sapi, H2 into HI, H3 into Hgz, H4 into Hmsg, H5 into RX, H6 into Hwb0.
  pose proof AF as [_ Ftune Fdict _ _ _ _ _ _ _].
  forward_if (EX s1 : dstate, A2 I Iend Rp sp api vosn gv rs s1 tin tout adler nin ain nout aout msg msgv).
  - set (zz := zcall [] 0 0 0 0 0 0 None).
    assert (RS := RSOK). destruct RS as (?&?&?&?&?&T1&T2&T3&T4&_).
    destruct (Ftune _ s tin tout adler (rs_t1 rs) (rs_t2 rs) (rs_t3 rs) (rs_t4 rs) zz HI T1 T2 T3 T4)
      as [s1 [Ht [Hg1 HI1]]].
    assert (Hwb1 : wbx rs s1).
    { pose proof (rx_tune _ RX _ s tin tout adler (rs_t1 rs) (rs_t2 rs) (rs_t3 rs) (rs_t4 rs) zz s1 zz Z_OK
                    HI T1 T2 T3 T4 Ht) as Hw.
      unfold wbx in *. rewrite Hw. exact Hwb0. }
    unfold api_fields. Intros.
    forward_call (Some s, sp, nin, nullval, rs_t1 rs, rs_t2 rs, rs_t3 rs, rs_t4 rs, (Some s1, zz, Z_OK), zz, gv).
    { unfold on_state, c_on_state. rewrite Ht. reflexivity. }
    forward_if.
    + forward_call Int.one. Exists s1. unfold A2, api_fields. entailer!; cancel.
    + forward. Exists s1. unfold A2, api_fields. entailer!; cancel.
  - forward. Exists s. unfold A2. entailer!.
  - Intros s1. unfold A2. Intros. clear HI Hgz. rename H into HI1, H0 into Hgz1.
    match goal with Hx : wbx rs s1 |- _ => rename Hx into Hwb1 end.
    forward_if (EX s2 : dstate, EX dict : list Z, EX dset : Z, EX tin2 : Z, EX tout2 : Z, EX adler2 : Z,
                EX ain2 : Z, EX aout2 : Z, EX msg2 : option Z, EX msgv2 : val,
                A3 I Iend Rp sp api vosn gv rs s2 dict dset tin2 tout2 adler2 nin ain2 nout aout2 msg2 msgv2).
    + assert_PROP (u32_ok ain /\ u32_ok aout) as Hr. { unfold api_fields. entailer!. }
      assert (RS := RSOK).
      destruct RS as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&Hld&_&_&_&_&Hbd&_).
      destruct (Fdict _ s1 tin tout adler (rs_dict rs) ain aout msg HI1 Hbd Hld) as
        (s2 & z' & code & Hc & Hg2 & Hcode & Hcw & HI2); [unfold u32_ok, u32r in *; rep_lia .. |].
      assert (Hwb2 : wbx rs s2).
      { assert (Hw : d_w_bits s2 = d_w_bits s1).
        { eapply (rx_dict _ RX _ s1 tin tout adler (rs_dict rs) ain aout msg s2 z' code HI1 Hbd Hld);
            [unfold u32_ok, u32r in *; rep_lia .. | exact Hc]. }
        unfold wbx in *. rewrite Hw. exact Hwb1. }
      unfold drun_rest, allobjs. rewrite (obj_opt_obj (rs_dictp rs) (rs_dict rs) Hbd). Intros.
      assert (Pdp : isptr (rs_dictp rs))
        by (destruct RSOK as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&Pdp&_); exact Pdp).
      forward. forward.
      forward_call (Some s1, sp, nullval, nin, ain, tin, nout, aout, tout, msgv, msg, adler, rs_dictp rs, Ews,
                    rs_dict rs, (Some s2, z', code), gv).
      { unfold on_state, c_on_state. change zmk with zcall. rewrite Hc. reflexivity. }
      cbn [fst snd]. Intros msgv2.
      assert (Hwr : wrap_of (rs_wbits rs) = 0 \/ wrap_of (rs_wbits rs) = 1 \/ wrap_of (rs_wbits rs) = 2)
        by (unfold wrap_of; repeat destruct (_ <? _); repeat destruct (_ >? _); auto).
      clear Ftune Fdict.
      destruct Hcode as [-> | ->].
      * (* Z_OK: not gzip *)
        assert (Hw : wrap_of (rs_wbits rs) <> 2) by (intro X; apply Hcw in X; discriminate).
        forward. forward_if True.
        { forward. forward_if (temp _t'46 (vi 1)).
          { forward_if. { forward. entailer!. } { exfalso. auto. } }
          { exfalso. apply H2. destruct Hwr as [E|[E|E]]; [rewrite E; reflexivity .. | contradiction]. }
          forward_call Int.one. entailer!. }
        { forward. entailer!. }
        forward_if (temp _t'47 (bool2val (zlt 0 (Zlength (rs_dict rs))))).
        { forward. forward. entailer!. }
        { exfalso. auto. }
        forward.
        assert (HI2' := HI2). rewrite (proj2 (Z.eqb_neq _ _) Hw) in HI2'.
        destruct (zlt 0 (Zlength (rs_dict rs))) as [Hp|Hp].
        -- Exists s2 (rs_dict rs) 1 (z_total_in z') (z_total_out z') (z_adler z') (z_avail_in z') (z_avail_out z')
             (z_msg z') msgv2.
           unfold A3, drun_rest, allobjs. rewrite (obj_opt_obj (rs_dictp rs) (rs_dict rs) Hbd). entailer!.
           left; split3; auto. intro X; pose proof Hp as Hp0; rewrite X, Zlength_nil in Hp0; lia.
        -- assert (Hnil : rs_dict rs = []) by (apply Zlength_nil_inv; pose proof (Zlength_nonneg (rs_dict rs)); lia).
           Exists s2 (@nil Z) 0 (z_total_in z') (z_total_out z') (z_adler z') (z_avail_in z') (z_avail_out z')
             (z_msg z') msgv2.
           unfold A3, drun_rest, allobjs. rewrite (obj_opt_obj (rs_dictp rs) (rs_dict rs) Hbd). rewrite Hnil in HI2'. entailer!.
      * (* Z_STREAM_ERROR: gzip *)
        assert (Hw : wrap_of (rs_wbits rs) = 2) by (apply Hcw; reflexivity).
        assert (HI2' := HI2). rewrite Hw in HI2'. cbn in HI2'.
        forward. forward_if True.
        { forward. forward_if (temp _t'46 (vi 1)).
          { forward_if. { exfalso. discriminate. } { forward. forward. entailer!. } }
          { exfalso. apply H2. rewrite Hw. reflexivity. }
          forward_call Int.one. entailer!. }
        { forward. entailer!. }
        forward_if (temp _t'47 (vi 0)).
        { exfalso. discriminate. }
        { forward. entailer!. }
        forward.
        Exists s2 (@nil Z) 0 (z_total_in z') (z_total_out z') (z_adler z') (z_avail_in z') (z_avail_out z')
          (z_msg z') msgv2.
        unfold A3, drun_rest, allobjs. rewrite (obj_opt_obj (rs_dictp rs) (rs_dict rs) Hbd). rewrite <- Hw in HI2'. entailer!.
    + forward. Exists s1 (@nil Z) 0 tin tout adler ain aout msg msgv. unfold A3. entailer!; cancel.
    + Intros s2 dict dset tin2 tout2 adler2 ain2 aout2 msg2 msgv2.
      apply run_head_ok; auto.
Qed.
