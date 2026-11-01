(* Round-trip laws, part RT-CB: the body of compress.c's compress2_z (RTCSpec.compress2_z_spec). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Zlib.proof.deflate.Obligations.
Require Zlib.proof.compress.CSpec.
Require Zlib.units.Compress.
Require Zlib.deflate.code.
Require Import Zlib.compress.code.
Require Import Zlib.proof.roundtrip.RTDIface Zlib.proof.roundtrip.RTC2.
Require Import Zlib.proof.roundtrip.RTCSpec.
Require Import Zlib.proof.roundtrip.RTCBKit Zlib.proof.roundtrip.RTCBModel Zlib.proof.roundtrip.RTCBDest.
Require Import Zlib.proof.deflate.InitStrm Zlib.proof.roundtrip.RTCBPure.
Require Zlib.proof.deflate.DeflateParams8.
Local Open Scope logic.

#[local] Existing Instance Zlib.units.Compress.CS.

#[local] Instance CC_dc : change_composite_env DCS.CS Zlib.units.Compress.CS.
Proof. make_cs_preserve DCS.CS Zlib.units.Compress.CS. Defined.

Lemma buf_valid sh n c p :
  readable_share sh -> 0 < n -> data_at sh (tarray tuchar n) c p |-- valid_pointer p.
Proof. intros. apply data_at_valid_ptr; [auto | simpl; rep_lia]. Qed.

Lemma dstream_sp_fold' lvl os strmp ghp sp gv :
  dstream_sp lvl os strmp ghp sp gv |-- dstream lvl os strmp ghp gv.
Proof. rewrite dstream_sp_eq. Exists sp. cancel. Qed.

Lemma sub_pp_val: forall n p a b,
  field_compatible (tarray tuchar n) [] p -> 0 <= a <= n -> 0 <= b <= n ->
  force_val (sem_sub_pp tuchar (offset_val a p) (offset_val b p)) = Vlong (Int64.repr (a - b)).
Proof.
  intros n p a b FC Ha Hb.
  destruct p; try (destruct FC; contradiction).
  destruct FC as (_ & _ & SZ & _). simpl in SZ. rewrite Z.max_r in SZ by lia.
  pose proof (Ptrofs.unsigned_range i) as R0.
  unfold sem_sub_pp, offset_val. simpl. destruct (eq_block b0 b0) as [_|NE]; [|congruence]. simpl.
  rewrite (Ptrofs.add_commut i (Ptrofs.repr a)), (Ptrofs.add_commut i (Ptrofs.repr b)), Ptrofs.sub_shifted.
  unfold Vptrofs. destruct Archi.ptr64 eqn:A; [|discriminate]. f_equal.
  assert (D: Ptrofs.divs (Ptrofs.sub (Ptrofs.repr a) (Ptrofs.repr b)) (Ptrofs.repr 1) =
             Ptrofs.sub (Ptrofs.repr a) (Ptrofs.repr b)).
  { unfold Ptrofs.divs. change (Ptrofs.signed (Ptrofs.repr 1)) with 1. rewrite Z.quot_1_r. apply Ptrofs.repr_signed. }
  rewrite D. unfold Ptrofs.to_int64. unfold Ptrofs.sub.
  rewrite (Ptrofs.unsigned_repr a), (Ptrofs.unsigned_repr b) by (unfold Ptrofs.max_unsigned; lia).
  apply Int64.eqm_samerepr. unfold Int64.eqm. apply Zbits.eqmod_sym.
  change Int64.modulus with Ptrofs.modulus. apply Ptrofs.eqm_unsigned_repr.
Qed.

Lemma sub_pp_val0 n p a :
  field_compatible (tarray tuchar n) [] p -> 0 <= a <= n ->
  force_val (sem_sub_pp tuchar (offset_val a p) p) = vl a.
Proof.
  intros FC Ha. pose proof (sub_pp_val n p a 0 FC Ha ltac:(lia)) as E.
  assert (isptr p) by (destruct p; try (destruct FC; contradiction); exact I).
  rewrite isptr_offset_val_zero in E by auto. rewrite E, Z.sub_0_r. reflexivity.
Qed.

(* the z_stream fields deflateEnd leaves, whatever its outcome *)
Lemma end_fields (os' : option dstate) (SF : dstate) strmp gv :
  match os' with None => dstream 2 None strmp nullval gv | Some _ => dstream_end (Some SF) strmp gv end
  |-- EX st : val, EX za : val, EX zf : val, EX op : val, EX dt : val,
      @field_at_ DCS.CS Ews t_strm (DOT deflate.code._reserved) strmp *
      @field_at DCS.CS Ews t_strm (DOT deflate.code._state) st strmp *
      @field_at DCS.CS Ews t_strm (DOT deflate.code._zalloc) za strmp *
      @field_at DCS.CS Ews t_strm (DOT deflate.code._zfree) zf strmp *
      @field_at DCS.CS Ews t_strm (DOT deflate.code._opaque) op strmp *
      @field_at DCS.CS Ews t_strm (DOT deflate.code._data_type) dt strmp * TT.
Proof.
  destruct os'.
  - unfold dstream_end. Intros p dt. Exists (p_s p) (gv deflate.code._zcalloc) (gv deflate.code._zcfree) nullval dt.
    cancel.
  - unfold dstream. Intros za zf op dt. Exists nullval za zf op dt. cancel.
Qed.

Lemma rtcb_compress2_z : Obligations.ob_dstream_to_end -> ob_compress2_z.
Proof.
  intros HDE.
  unfold ob_compress2_z, Gprog_compress2_z, compress2_z_spec, c2_pre, c2_sep_pre, c2_sep_post.
  start_function.
  forward.
  assert_PROP (isptr dlp) as Hdlp by entailer!.
  assert (Hsl : 0 <= Zlength src) by apply Zlength_nonneg.
  unfold umax in H1, H3.
  forward_if (temp _t'1 (Val.of_bool false)).
  { forward.
    - entailer!.
      match goal with Hx : Int64.unsigned _ < Int64.unsigned _ |- _ => rewrite !Int64.unsigned_repr in Hx by rep_lia end.
      apply denote_tc_test_eq_split; [| auto with valid_pointer].
      apply derives_trans with (data_at ssh (tarray tuchar (Zlength src)) (map vi src) sp * TT); [cancel|].
      apply sepcon_valid_pointer1, buf_valid; auto; lia.
    - entailer!. destruct sp; try contradiction; reflexivity. }
  { forward. entailer!. }
  forward_if (temp _t'2 (Val.of_bool false)).
  { contradiction. }
  { forward. entailer!. destruct dlp; try contradiction; reflexivity. }
  forward_if (temp _t'3 (Val.of_bool false)).
  { contradiction. }
  { forward. forward_if (temp _t'3 (Val.of_bool false)).
    - forward.
      forward. entailer!. destruct dp; try contradiction; reflexivity.
    - forward. entailer!.
    - entailer!. }
  forward_if.
  { contradiction. }
  forward. forward.
  sep_apply (strm_open v_stream).
  Intros.
  freeze FCOMP := (@data_at_ CCS (Share.comp Ews) t_strm v_stream).
  rewrite <- (fa__cd Ews deflate.code._zalloc v_stream), <- (fa__cd Ews deflate.code._zfree v_stream),
    <- (fa__cd Ews deflate.code._opaque v_stream).
  forward. forward. forward.
  fa_to_dcs. unfold cversion_lit. rewrite tschar_cd.
  forward_call (v_stream, level, gv ___stringlit_compress_1, Ers, [49;46;51;46;50;0], 112, Vundef, Vundef,
                Vundef, Vundef, Vundef, nullval, Vundef, Vundef, gv).
  { unfold reset_fields. cancel. }
  { split; [unfold s32_ok; rep_lia|]. split; [list_solve|]. split; [cbn; rep_lia|].
    intros a1 a2 a3 a4 a5. destruct (H6 a1 a2 a3 a4 a5) as (r & out & os & z1 & code & HI & _).
    exists (os, z1, code). exact HI. }
  Intros vret. destruct vret as [[[[[a1 a2] a3] a4] a5] [[os z1] code]]. cbn [fst snd] in *.
  match goal with H : c_deflateInit2_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ |- _ => rename H into HI end.
  change (Znth 0 [49; 46; 51; 46; 50; 0] =? 49) with true in HI. change (112 =? 112) with true in HI.
  pose proof (c2_init_code _ _ _ _ _ _ _ _ _ _ HI) as Hcode.
  forward_if.
  { (* deflateInit failed *)
    assert (Hc : code <> Z_OK) by (intros ->; contradiction).
    pose proof (c2_init_none _ _ _ _ _ _ _ _ _ _ HI Hc) as ->.
    Intros st za zf op' dt' msgv'.
    thaw FCOMP. unfold reset_fields.
    change (@field_at_ DCS.CS Ews t_strm (DOT deflate.code._avail_in) v_stream)
      with (@field_at DCS.CS Ews t_strm (DOT deflate.code._avail_in) Vundef v_stream).
    change (@field_at_ DCS.CS Ews t_strm (DOT deflate.code._next_out) v_stream)
      with (@field_at DCS.CS Ews t_strm (DOT deflate.code._next_out) Vundef v_stream).
    change (@field_at_ DCS.CS Ews t_strm (DOT deflate.code._avail_out) v_stream)
      with (@field_at DCS.CS Ews t_strm (DOT deflate.code._avail_out) Vundef v_stream).
    sep_apply (strm_close v_stream).
    forward.
    Exists a1 a2 a3 a4 a5 code (@nil Z).
    unfold cversion_lit. rewrite tschar_cd.
    entailer!.
    - split; [exists None, z1, code; split; [exact HI | left; auto] | rewrite Zlength_nil; lia].
    - rewrite Zlength_nil, app_nil_l, sublist_same by lia. cancel. }
  (* deflateInit succeeded *)
  assert (Hok : code = Z_OK) by (destruct Hcode as [E|[E|E]]; auto; rewrite E in H8; unfold Z_STREAM_ERROR, Z_MEM_ERROR in H8;
    apply repr_inj_signed in H8; try discriminate; rep_lia).
  subst code. clear Hcode.
  destruct (H6 a1 a2 a3 a4 a5) as (R & OUT & os' & z1' & code' & HI' & Hcases).
  rewrite HI in HI'. injection HI' as <- <- <-.
  destruct Hcases as [[Hc _] | [_ (s & E & SF & ZF & -> & Hgz & Hrun & HR)]]; [contradiction|].
  destruct (init_ok_strm _ _ _ _ _ _ _ _ _ _ _ _ _ HI) as (Hti & Hto & Had & _ & _ & Hmsg).
  Intros msgv'. change (Z_OK =? Z_OK) with true in *. unfold rfv.
  match goal with Hx : (if Z_OK =? Z_VERSION_ERROR then _ else _) |- _ => cbn in Hx; rewrite Hmsg in Hx; cbn in Hx; subst msgv' end.
  fa_to_ccs.
  rewrite <- (fa__cd Ews deflate.code._avail_in v_stream), <- (fa__cd Ews deflate.code._next_out v_stream),
    <- (fa__cd Ews deflate.code._avail_out v_stream).
  forward. forward. forward. forward.
  fa_to_dcs.
  forward_loop (EX s0 : dstate, EX z : strm, EX left : Z, EX srcleft : Z, EX out : list Z, EX msgv : val,
    PROP (c2_run src s0 z left srcleft out E OUT SF ZF; d_gzhead s0 = None;
          (z_next_in z + z_avail_in z + srcleft = Zlength src)%Z; (0 <= z_next_in z)%Z; (0 <= z_avail_in z)%Z;
          (0 <= srcleft)%Z; (Zlength out + z_avail_out z + left = cap)%Z; (0 <= z_avail_out z)%Z; (0 <= left)%Z;
          left = 0 \/ z_avail_out z = 0; srcleft = 0 \/ z_avail_in z = 0; msg_ok (z_msg z) msgv)
    LOCAL (temp _left (vl left); temp _sourceLen (vl srcleft); temp _max (Vint (Int.neg (Int.repr 1)));
           lvar _stream (Tstruct _z_stream_s noattr) v_stream; gvars gv; temp _dest dp; temp _destLen dlp;
           temp _source sp)
    SEP (@data_at_ CCS (Share.comp Ews) t_strm v_stream; dstream 2 (Some s0) v_stream nullval gv;
         api_fields v_stream (offset_val (z_next_in z) sp) (z_avail_in z) (z_total_in z)
           (offset_val (Zlength out) dp) (z_avail_out z) (z_total_out z) msgv (z_adler z);
         strm_pad v_stream;
         data_at Ews (tarray tuchar cap) (map vi out ++ sublist (Zlength out) cap dc) dp;
         data_at Tsh tulong (vl 0) dlp;
         data_at ssh (tarray tuchar (Zlength src)) (map vi src) sp;
         cversion_lit gv; deflate_globals gv; mem_mgr gv))
  break: (EX msgv : val,
    PROP (E <> Z_OK; DeflateParams8.rc_ok E; (Zlength OUT <= cap)%Z; msg_ok (z_msg ZF) msgv)
    LOCAL (temp _err (vi E); temp _dest dp; temp _destLen dlp;
           lvar _stream (Tstruct _z_stream_s noattr) v_stream; gvars gv)
    SEP (@data_at_ CCS (Share.comp Ews) t_strm v_stream; dstream 2 (Some SF) v_stream nullval gv;
         api_fields v_stream (offset_val (z_next_in ZF) sp) (z_avail_in ZF) (z_total_in ZF)
           (offset_val (Zlength OUT) dp) (z_avail_out ZF) (z_total_out ZF) msgv (z_adler ZF);
         strm_pad v_stream;
         data_at Ews (tarray tuchar cap) (map vi OUT ++ sublist (Zlength OUT) cap dc) dp;
         data_at Tsh tulong (vl 0) dlp;
         data_at ssh (tarray tuchar (Zlength src)) (map vi src) sp;
         cversion_lit gv; deflate_globals gv; mem_mgr gv)).
  { (* entry *)
    Exists s (mkST src 0 0 (z_total_in z1) [] 0 (z_total_out z1) (z_adler z1) (z_msg z1)) cap (Zlength src)
      (@nil Z) nullval.
    thaw FCOMP. unfold cversion_lit. rewrite tschar_cd. unfold api_fields, reset_fields. cbn [DS.z_next_in DS.z_avail_in DS.z_total_in DS.z_avail_out DS.z_total_out DS.z_adler DS.z_msg].
    rewrite Hti, Hto, Hmsg.
    entailer!.
    - unfold u32_ok, u64_ok. destruct Had as [-> | ->]; rep_lia.
    - rewrite Zlength_nil, app_nil_l, sublist_same by lia. cancel. }
  { (* the loop body *)
    Intros s0 z left srcleft out msgv.
    freeze FC2 := (@data_at_ CCS (Share.comp Ews) t_strm v_stream).
    unfold api_fields. Intros. fa_to_ccs.
    forward.
    freeze FR := - (field_at _ _ (DOT deflate.code._avail_out) _ _) (field_at _ _ (DOT deflate.code._avail_in) _ _).
    forward_if (PROP () LOCAL (temp _left (vl 0); temp _sourceLen (vl srcleft);
        temp _max (Vint (Int.neg (Int.repr 1))); lvar _stream (Tstruct _z_stream_s noattr) v_stream; gvars gv;
        temp _dest dp; temp _destLen dlp; temp _source sp)
      SEP (FRZL FR; field_at Ews t_strm (DOT deflate.code._avail_out) (vi (z_avail_out z + left)) v_stream;
           field_at Ews t_strm (DOT deflate.code._avail_in) (vi (z_avail_in z)) v_stream)).
    { unfold MORE_COMMANDS, abbreviate. apply -> seq_assoc. apply semax_if_seq. forward_if.
      { assert (Hm : Int.unsigned (Int.neg (Int.repr 1)) = 4294967295) by reflexivity. rewrite Hm in *. pose proof (Zlength_nonneg out). lia. }
      assert (Hlc : left <= 4294967295) by (pose proof (Zlength_nonneg out); lia).
      forward. forward. forward. forward. entailer!.
      - rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia. rewrite Int.unsigned_repr by rep_lia.
        unfold vl. rewrite Z.sub_diag. reflexivity.
      - rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia. rewrite H26. unfold vi. rewrite Z.add_0_l. cancel. }
    { destruct H18 as [-> | ?]; [| contradiction].
      forward. rewrite Z.add_0_r. entailer!. }
    forward.
    forward_if (PROP () LOCAL (temp _left (vl 0); temp _sourceLen (vl 0);
        temp _max (Vint (Int.neg (Int.repr 1))); lvar _stream (Tstruct _z_stream_s noattr) v_stream; gvars gv;
        temp _dest dp; temp _destLen dlp; temp _source sp)
      SEP (FRZL FR; field_at Ews t_strm (DOT deflate.code._avail_out) (vi (z_avail_out z + left)) v_stream;
           field_at Ews t_strm (DOT deflate.code._avail_in) (vi (z_avail_in z + srcleft)) v_stream)).
    { unfold MORE_COMMANDS, abbreviate. apply -> seq_assoc. apply semax_if_seq. forward_if.
      { assert (Hm : Int.unsigned (Int.neg (Int.repr 1)) = 4294967295) by reflexivity. rewrite Hm in *. lia. }
      assert (Hsc : srcleft <= 4294967295) by lia.
      forward. forward. forward. forward. entailer!.
      - rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia. rewrite Int.unsigned_repr by rep_lia.
        unfold vl. rewrite Z.sub_diag. reflexivity.
      - rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia.
        rewrite H26. unfold vi. rewrite Z.add_0_l. cancel. }
    { destruct H19 as [-> | ?]; [| contradiction].
      forward. rewrite Z.add_0_r. entailer!. }
    unfold MORE_COMMANDS, abbreviate. repeat apply -> seq_assoc. apply semax_if_seq. forward_if.
    { match goal with Hx : _ <> _ |- _ => contradiction Hx; reflexivity end. }
    forward.
    thaw FR. fa_to_dcs.
    (* the model: this iteration's deflate call *)
    assert (Hk : 0 <= Zlength out) by apply Zlength_nonneg.
    assert (HG := give_eq src z left srcleft ltac:(unfold umax; lia) ltac:(unfold umax; lia) H18 H19).
    destruct (c2_run_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ H9 HG) as (s' & z' & e & Hdf & Hgz' & Hst & Hnext).
    rewrite dstream_sp_eq. Intros ssp.
    rewrite (bytes_cd Ews cap), (bytes_cd ssh (Zlength src)).
    assert_PROP (@field_compatible DCS.CS (tarray tuchar cap) [] dp) as FCd by entailer!.
    sep_apply (dest_open (Zlength out) cap (map vi out ++ sublist (Zlength out) cap dc) dp ltac:(lia) ltac:(lia)
                 ltac:(rewrite Zlength_app, Zlength_map, Zlength_sublist by lia; lia)).
    assert (HR1 : sublist (Zlength out) cap (map vi out ++ sublist (Zlength out) cap dc) = sublist (Zlength out) cap dc)
      by list_solve.
    assert (HL1 : Zlength (sublist (Zlength out) cap dc) = z_avail_out z + left) by (rewrite Zlength_sublist; lia).
    assert (HL2 : Zlength (sublist (Zlength out) cap dc) = cap - Zlength out) by (rewrite Zlength_sublist; lia).
    rewrite HR1.
    forward_call (Some s0, v_stream, nullval, ssp, (Ews, nullval, nullval, nullval), sp, ssh, src, z_next_in z,
                  z_avail_in z + srcleft, z_total_in z, offset_val (Zlength out) dp,
                  sublist (Zlength out) cap dc,
                  wv_of (Zlength out) cap (map vi out ++ sublist (Zlength out) cap dc), z_total_out z, msgv,
                  z_msg z, z_adler z, 4, (Some s', z', e), gv).
    { rewrite HL2. replace (z_avail_out z + left) with (cap - Zlength out) by lia.
      unfold hdr_at. rewrite H10. unfold api_fields. entailer!. unfold u32_ok. split; rep_lia. }
    { split; [intros Hz; apply wv_of_ok; lia |].
      split; [unfold s32_ok; rep_lia |].
      split.
      - unfold strm_ranges, zmk. cbn. rewrite HL1. unfold u32_ok, u64_ok in *.
        repeat split; try rep_lia; auto.
      - exists (fun f => f). split; [apply ef_ok_id |].
        unfold on_state, c_on_state. rewrite c_deflate_g_id. rewrite HL1. unfold zmk. unfold Z_FINISH in Hdf. rewrite Hdf. reflexivity. }
    cbn [fst snd]. Intros msgv'.
    forward.
    unfold hdr_at. rewrite H10. Intros.
    pose proof (DeflateParams8.c_deflate_rc _ _ _ _ _ _ Hdf) as Hrc.
    destruct Hst as (Hs1 & Hs2 & Hs3 & Hs4); cbn [DS.z_avail_in DS.z_next_in DS.z_avail_out DS.z_out] in Hs1, Hs2, Hs3, Hs4.
    rewrite HL2, H0.
    assert (HRl : Zlength (map vi (z_out z') ++ sublist (Zlength (z_out z')) (cap - Zlength out)
                            (sublist (Zlength out) cap dc)) = cap - Zlength out) by list_solve.
    assert (HDl : Zlength (map vi out ++ sublist (Zlength out) cap dc) = cap) by list_solve.
    sep_apply (dest_close (Zlength out) cap (map vi out ++ sublist (Zlength out) cap dc)
                 (map vi (z_out z') ++ sublist (Zlength (z_out z')) (cap - Zlength out) (sublist (Zlength out) cap dc))
                 dp ltac:(lia) ltac:(lia) HDl HRl FCd).
    assert (HD : sublist 0 (Zlength out) (map vi out ++ sublist (Zlength out) cap dc) ++
                 (map vi (z_out z') ++ sublist (Zlength (z_out z')) (cap - Zlength out) (sublist (Zlength out) cap dc)) =
                 map vi (out ++ z_out z') ++ sublist (Zlength (out ++ z_out z')) cap dc)
      by (rewrite map_app, Zlength_app; list_solve).
    rewrite HD. clear HD.
    rewrite <- (bytes_cd Ews cap), <- (bytes_cd ssh (Zlength src)).
    sep_apply (dstream_sp_fold' 2 (Some s') v_stream nullval ssp gv).
    rewrite offset_offset_val.
    forward_if.
    { (* Z_OK: the next iteration *)
      assert (He : e = Z_OK).
      { unfold DeflateParams8.rc_ok in Hrc.
        destruct Hrc as [-> | [-> | [-> | ->]]]; auto;
          apply repr_inj_signed in H28; try discriminate; rep_lia. }
      destruct Hnext as [[_ Hrun'] | [Hne _]]; [| contradiction].
      forward.
      Exists s' z' 0 0 (out ++ z_out z') msgv'. thaw FC2. rewrite Zlength_app.
      entailer!. }
    { (* the end of the loop *)
      destruct Hnext as [[-> _] | [Hne (-> & -> & -> & ->)]]; [exfalso; apply H28; reflexivity |].
      forward.
      Exists msgv'. thaw FC2. rewrite Zlength_app.
      entailer!. }
    }
  (* after the loop: *destLen, deflateEnd, the return value *)
  Intros msgv.
  freeze FC3 := (@data_at_ CCS (Share.comp Ews) t_strm v_stream).
  unfold api_fields. Intros. fa_to_ccs.
  forward.
  assert_PROP (field_compatible (tarray tuchar cap) [] dp) as FCd by entailer!.
  forward.
  { entailer!. destruct dp; try contradiction. simpl. unfold denote_tc_samebase. simpl. entailer!. }
  rewrite (sub_pp_val0 cap dp (Zlength OUT) FCd ltac:(pose proof (Zlength_nonneg OUT); lia)).
  fa_to_dcs.
  destruct (c_deflateEnd SF ZF) as [rr|] eqn:Hend; [| unfold c_deflateEnd in Hend; destruct (bad_state SF); discriminate].
  sep_apply (HDE (Some SF) v_stream nullval gv).
  forward_call (Some SF, v_stream, offset_val (z_next_in ZF) sp, ZF, rr, gv).
  sep_apply (end_fields (fst (fst rr)) SF v_stream gv).
  Intros st za zf op dt.
  thaw FC3.
  sep_apply (strm_close v_stream).
  apply semax_if_seq. forward_if.
  { forward. forward.
    assert (HE1 : E = Z_STREAM_END).
    { unfold DeflateParams8.rc_ok in *.
      destruct H10 as [-> | [-> | [-> | ->]]]; auto;
        match goal with Hx : Int.repr _ = Int.repr 1 |- _ => apply repr_inj_signed in Hx; try discriminate; rep_lia end. }
    Exists a1 a2 a3 a4 a5 Z_OK OUT.
    entailer!.
    exists (Some s), z1, Z_OK. split; [exact HI |]. right. split; [reflexivity |].
    exists s, Z_STREAM_END, SF, ZF. split; [reflexivity |]. split; [exact Hgz |]. split; [exact Hrun | reflexivity]. }
  { forward. forward.
    assert (HE1 : (E =? Z_STREAM_END) = false).
    { apply Z.eqb_neq. intros ->. match goal with Hx : Int.repr _ <> Int.repr 1 |- _ => apply Hx; reflexivity end. }
    Exists a1 a2 a3 a4 a5 E OUT.
    entailer!.
    exists (Some s), z1, Z_OK. split; [exact HI |]. right. split; [reflexivity |].
    exists s, E, SF, ZF. split; [reflexivity |]. split; [exact Hgz |]. split; [exact Hrun |]. rewrite HE1. reflexivity. }
Qed.
