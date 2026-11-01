(* Law rj_bad_dictionary, main (RDMain.v), statements 14-16: gp_assume on the dictionary's Adler-32,
   new_stream, inflateInit2 and its check *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.adler32.Spec.
Require Import Zlib.proof.harness.rj_bad_dictionary.RDLawCS.
Require Import Zlib.proof.harness.rj_bad_dictionary.RDGlobals.
Require Import Zlib.proof.harness.rj_bad_dictionary.RDFacts.
Require Import Zlib.proof.harness.rj_bad_dictionary.RDKit.
Require Import Zlib.harness.rj_bad_dictionary.code.
Local Open Scope Z_scope.

Lemma seg_init_ok : seg_init_stmt.
Proof.
  intros Espec gv v_strm t1 t2 room dlen streamp s3 outp dictp dict cinfo x K.
  unfold rd_seg14, rd_A14, POST_B, POST_rd, t_zsl. abbreviate_semax.
  Intros. rename H3 into Ns, H4 into No, H5 into Nd. rename H2 into H6', H1 into H5'.
  destruct H0 as (Hs3 & Hb3 & H7 & Hx & S30 & S31).
  destruct H as (H & H0 & H1 & H2). rename H5' into H5, H6' into H6.
  assert (Hid: 0 <= rbd_dictid s3 < 2 ^ 32).
  { pose proof (rbd_byte_range 2 s3 Hb3 ltac:(lia)). pose proof (rbd_byte_range 3 s3 Hb3 ltac:(lia)).
    pose proof (rbd_byte_range 4 s3 Hb3 ltac:(lia)). pose proof (rbd_byte_range 5 s3 Hb3 ltac:(lia)).
    unfold rbd_dictid; lia. }
  pose proof (Zlib.proof.adler32.Model.adler32_z_val_range 1 dict H6) as [Had _].
  assert_PROP (isptr dictp) as Pd by entailer!.
  rewrite <- (rbd_bytes_adler_cs Ews dlen (bytes_rep dict) dictp), <- (rbd_tok_adler_cs Ews dlen dictp).
  forward_call (1, dictp, dlen, false, Ews, dictp, 0, dlen, bytes_rep dict, dict, true, Ews).
  { split; [destruct dictp; try contradiction; simpl; rewrite Ptrofs.add_zero; reflexivity | ].
    split; [auto | ]. split; [lia | ]. split; [lia | ]. split; [lia | ]. split; [auto | ].
    rewrite Z.add_0_l, sublist_same; auto. unfold bytes_rep; rewrite Zlength_map; lia. }
  forward_call (Int.repr (if negb (adler32_z_val 1 dict =? rbd_dictid s3) then 1 else 0)).
  { entailer!. arg_cmp. }
  assumed.
  (* new_stream(&strm) on the local z_stream, then inflateInit2(&strm, window_bits) *)
  assert (U: @data_at_ CS Tsh (Tstruct _z_stream_s noattr) v_strm =
    @data_at Zlib.units.Compress.CS Tsh t_zs
      (zs_val Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef) v_strm).
  { unfold data_at_. rewrite rbd_zs_cs. reflexivity. }
  rewrite U. clear U.
  forward_call (v_strm, Tsh, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef,
                Vundef, Vundef, Vundef).
  match goal with |- context [@data_at _ Tsh t_zs ?v v_strm] => rewrite (rbd_zs_cs Tsh v v_strm) end.
  rewrite <- rbd_strm_cs.
  set (r0 := RF nullval (Vint (Int.repr 0)) Vundef nullval (Vint (Int.repr 0)) Vundef Vundef Vundef Vundef).
  match goal with |- context [@data_at Zlib.units.Inflate.CS Tsh Rep.t_strm ?v v_strm] =>
    change (@data_at Zlib.units.Inflate.CS Tsh Rep.t_strm v v_strm)
      with (raw_strm gv Tsh v_strm r0 Vundef Vundef nullval nullval nullval) end.
  assert_PROP (isptr (gv ___stringlit_rj_bad_dictionary_1)) as Pv by (unfold rbd_hversion_lit; entailer!).
  unfold rbd_hversion_lit. rewrite <- rbd_schar_inflate_cs.
  assert_PROP (isptr v_strm) as Ps by entailer!.
  assert (Ns': v_strm <> nullval) by (destruct v_strm; try contradiction; discriminate).
  forward_call (gv, Tsh, v_strm, r0, Vundef, Vundef, nullval, 8 + t1, gv ___stringlit_rj_bad_dictionary_1, Ers,
                map (fun c => Vint (Int.repr c)) [49; 46; 51; 46; 50; 0], 49, 112).
  { rewrite if_false by auto. cancel. }
  { cbn; rep_lia. }
  Intros vret. destruct vret as [aok sp]. simpl fst in *; simpl snd in *.
  destruct (rbd_init_facts sp (8 + t1) ltac:(lia)) as (Wok & Wrap & Hd).
  replace (init_ret v_strm 49 112 (8 + t1) aok) with (if aok then Z_OK else Z_MEM_ERROR)
    by (unfold init_ret; simpl; rewrite if_false by auto; rewrite Wok; destruct aok; reflexivity).
  destruct aok.
  2: { (* the allocation failed: return 0 *)
       replace (init_mem gv Tsh v_strm r0 Vundef Vundef nullval Z_MEM_ERROR sp (8 + t1))
         with (raw_strm gv Tsh v_strm r0 nullval Vundef (gv Zlib.inflate.code._zcalloc)
                 (gv Zlib.inflate.code._zcfree) nullval)
         by (unfold init_mem; rewrite if_false by auto; reflexivity).
       unfold raw_strm. rewrite rbd_strm_cs.
       change Z_MEM_ERROR with (-4).
       forward_if; [ | discriminate].
       rbd_ret. }
  set (L := init_live sp (8 + t1)) in *.
  replace (init_mem gv Tsh v_strm r0 Vundef Vundef nullval Z_OK sp (8 + t1))
    with (istream_raw gv Tsh v_strm (raw_after_init r0 (l_s L)) L)
    by (unfold init_mem; rewrite if_false by auto; reflexivity).
  change Z_OK with 0.
  forward_if; [rbd_nob | ].
  unfold istream_raw, raw_strm. Intros.
  unfold raw_after_init. rewrite Wrap. simpl rf_ni. simpl rf_ai. simpl rf_no. simpl rf_ao. simpl rf_res.
  change (5 =? 0) with false. cbv iota. change (Z.land 5 1) with 1.
  rewrite rbd_strm_cs.
  match goal with |- context [@data_at CS Tsh (Tstruct _z_stream_s noattr) ?v v_strm] =>
    rewrite <- (rbd_zs_cs Tsh v v_strm) end.
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  assert (Hne: adler32_z_val 1 dict <> rbd_dictid s3) by (intro X; rewrite X, Z.eqb_refl in E; discriminate).
  assert (Hh: rd_hdr t1 t2 s3 cinfo x) by (unfold rd_hdr; auto 7).
  eapply semax_pre; [ | apply (K sp)].
  unfold rd_A17, rd_in. subst L.
  rewrite ?(rbd_bytes_adler_cs Ews dlen (bytes_rep dict) dictp), ?(rbd_tok_adler_cs Ews dlen dictp).
  entailer!.
Qed.
