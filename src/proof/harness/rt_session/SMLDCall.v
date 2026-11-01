(* Law rt_session (harness/rt_session.c), main's deflate loop (SMKit.loopD): the deflate() call, from DP_s to DA_s
   against DSpecV.deflate_specV (SMLDKit.callD_s_stmt), as rt_stream_trailing's TLoopDCall.v.  The call is offered
   the bytes [inb] of data from next_in = data + |D| on, clip(offered - |D|) of them, and avail_out bytes of
   compressed from next_out = compressed + |O| on; SDFacts.sd_deflate, with the session's dictionary and header,
   gives its run.  The compressor's gzhead pointer is SMKit.ghp and the header part of its state is in the frame:
   deflate keeps the state's gzhead, so the header part of the new state is the same predicate and hclose still
   holds (SMLDLib.hdr_at_gz, hclose_gz).  main's objects data and compressed are rt_stream's (SMLDLib.dobj_tu,
   cobj_tu), cut by rt_stream's ULoopDCallLib.  A call offered no output space returns Z_BUF_ERROR without
   consuming or writing anything, so the stream's members after it are those position_of recorded in [at]; by the
   run's rcall_ok the call consumed exactly what it took off avail_in and wrote exactly what it took off avail_out,
   so next_in + avail_in and next_out + avail_out are those at records ([acc_ok_of_s]: accounted() holds). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.deflate.DCS.
Require Zlib.proof.deflate.DSpecV.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.laws_session.Spec.
Require Zlib.proof.harness.laws_session.Facts.
Require Zlib.proof.harness.rt_stream.ULoopDLib.
Require Zlib.proof.harness.rt_stream.ULoopDCallLib.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SDFacts.
Require Import Zlib.proof.harness.rt_session.SMainStmt.
Require Import Zlib.proof.harness.rt_session.SMKit.
Require Import Zlib.proof.harness.rt_session.SMLDLib.
Require Import Zlib.proof.harness.rt_session.SMLDKit.
Require Import Zlib.harness.rt_session.code.
Require Zlib.deflate.code.
#[local] Existing Instance SCS.CS.
Local Open Scope logic.

Module LS := Zlib.proof.harness.laws_session.Spec.
Module DC := Zlib.deflate.code.

(* VST's after_forward_call simplifies remove_localdef_temp with `simpl rlt_ident_eq`, which runs away on main's
   identifiers; each identifier comparison is decided by vm_compute instead. *)
Ltac cd_rlt_fix u :=
  lazymatch u with
  | context C [rlt_ident_eq ?a ?b] =>
      let v := eval vm_compute in (rlt_ident_eq a b) in
      let u2 := context C [v] in cd_rlt_fix u2
  | _ => u
  end.

Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u := constr:(remove_localdef_temp i L) in
    let u' := eval lazy delta [remove_localdef_temp] beta iota in u in
    let u' := cd_rlt_fix u' in
    let u' := eval lazy beta iota in u' in
    let u' := eval lazy zeta in u' in
    change u with u'
  end.

(* the model's loops have 2^40 iterations of fuel: the kernel must never unfold them *)
Local Strategy opaque [Zlib.proof.deflate.DLoop.loop Zlib.proof.deflate.DLoop.loop2 Zlib.proof.deflate.DLoop.FUEL].

(* the facts of the setup the call uses *)
Lemma su_ok_call (u : setup) :
  su_ok u -> Zlength (su_data u) <= max_size /\ rbytes (su_data u) /\ 0 <= su_cap u <= max_size /\
             isptr (su_dp u) /\ isptr (su_cp u).
Proof.
  intros (Hd & _ & _ & _ & _ & _ & Pc & _).
  unfold su_dok in Hd. tauto.
Qed.

(* data cut around the bytes offered, as rt_stream's cut of the same objects *)
Lemma dobj_split_s (u : setup) (a b : Z) :
  0 <= a <= b -> b <= Zlength (su_data u) ->
  dobj u = ULoopDCallLib.din_rest (tu u) a b *
    @data_at DCS.CS Ews (tarray tuchar (Zlength (sublist a b (su_data u)))) (map vi (sublist a b (su_data u)))
      (offset_val a (su_dp u)).
Proof. intros. rewrite dobj_tu. apply (ULoopDCallLib.dobj_split (tu u)); auto. Qed.

Lemma dobj_join_s (u : setup) (a b : Z) :
  0 <= a <= b -> b <= Zlength (su_data u) ->
  ULoopDCallLib.din_rest (tu u) a b *
    @data_at DCS.CS Ews (tarray tuchar (Zlength (sublist a b (su_data u)))) (map vi (sublist a b (su_data u)))
      (offset_val a (su_dp u))
  |-- dobj u.
Proof. intros. rewrite (dobj_split_s u a b) by lia. apply derives_refl. Qed.

(* compressed: the output space offered, its frame [Fo] and deflate_specV's witness [W] (rt_stream's out_ok) *)
Lemma out_ok_ex_s (u : setup) (O : list Z) (aout : Z) :
  isptr (su_cp u) -> 0 <= aout -> Zlength O + aout <= su_cap u ->
  exists Fo W,
  (Zlength (Zrepeat Vundef aout) = 0 -> DSpecV.wv2_ok W) /\
  (cobj u O |-- Fo *
     @data_at DCS.CS Ews (tarray tuchar (Zlength (Zrepeat Vundef aout))) (Zrepeat Vundef aout)
       (offset_val (Zlength O) (su_cp u)) * DSpecV.wv2_at W (offset_val (Zlength O) (su_cp u))) /\
  (forall z, Zlength z <= aout ->
     Fo * @data_at DCS.CS Ews (tarray tuchar (Zlength (Zrepeat Vundef aout)))
            (map vi z ++ sublist (Zlength z) (Zlength (Zrepeat Vundef aout)) (Zrepeat Vundef aout))
            (offset_val (Zlength O) (su_cp u)) *
     DSpecV.wv2_at W (offset_val (Zlength O) (su_cp u))
     |-- cobj u (O ++ z)).
Proof.
  intros Pc Ha Hc.
  destruct (ULoopDCallLib.out_ok_ex (tu u) O aout Pc Ha Hc) as (Fo & W & H1 & H2 & H3).
  exists Fo, W. rewrite !cobj_tu. split; [exact H1 | split; [exact H2 | intros z Hz; rewrite cobj_tu; exact (H3 z Hz)]].
Qed.

(* accounted() after a call offered [cs_ain] bytes ending at data + ki and [cs_aout] bytes of room ending at
   compressed + ko (the members [a] before the call), which left [c]: next_in + avail_in and next_out + avail_out
   are still data + ki and compressed + ko, and avail_in and avail_out did not grow *)
Lemma acc_ok_of_s (u : setup) (c : cst) (a : LS.posz) (ki ko : Z) :
  isptr (su_dp u) -> isptr (su_cp u) ->
  0 <= ki <= Zlength (su_data u) -> 0 <= ko <= su_cap u ->
  cs_ain c <= LS.pz_avail_in a -> cs_aout c <= LS.pz_avail_out a ->
  cs_ni c = offset_val (ki - cs_ain c) (su_dp u) -> cs_no c = offset_val (ko - cs_aout c) (su_cp u) ->
  LS.pz_next_in a = offset_val (ki - LS.pz_avail_in a) (su_dp u) ->
  LS.pz_next_out a = offset_val (ko - LS.pz_avail_out a) (su_cp u) ->
  acc_ok_s u c a.
Proof.
  intros Pd Pc Hki Hko Hi Ho Eci Eco Eai Eao.
  assert (Ei : offset_val (cs_ain c) (cs_ni c) = offset_val ki (su_dp u))
    by (rewrite Eci, offset_offset_val; f_equal; lia).
  assert (Eo : offset_val (cs_aout c) (cs_no c) = offset_val ko (su_cp u))
    by (rewrite Eco, offset_offset_val; f_equal; lia).
  assert (Ei' : offset_val (LS.pz_avail_in a) (LS.pz_next_in a) = offset_val ki (su_dp u))
    by (rewrite Eai, offset_offset_val; f_equal; lia).
  assert (Eo' : offset_val (LS.pz_avail_out a) (LS.pz_next_out a) = offset_val ko (su_cp u))
    by (rewrite Eao, offset_offset_val; f_equal; lia).
  unfold acc_ok_s.
  split.
  { unfold LS.accounted_b, cpos_s.
    cbn [LS.pz_next_in LS.pz_avail_in LS.pz_total_in LS.pz_next_out LS.pz_avail_out LS.pz_total_out].
    rewrite Ei, Eo, Ei', Eo'. unfold LS.ptr_eqb.
    destruct (Val.eq (offset_val ki (su_dp u)) (offset_val ki (su_dp u))); [ | congruence].
    destruct (Val.eq (offset_val ko (su_cp u)) (offset_val ko (su_cp u))); [ | congruence].
    rewrite (proj2 (Z.leb_le _ _) Hi), (proj2 (Z.leb_le _ _) Ho). reflexivity. }
  split; [rewrite Eci, isptr_offset_val; auto|]. split; [rewrite Eco, isptr_offset_val; auto|].
  split; [rewrite Eai, isptr_offset_val; auto|]. split; [rewrite Eao, isptr_offset_val; auto|].
  exists ki, ko. repeat split; auto; lia.
Qed.

Lemma scall_d : callD_s_stmt.
Proof.
  intros Espec J gv vh vg vc va vd u hx Hr l HJ.
  destruct l as [D O fin off flush msg [s ni ain tin no aout tout msgv adler]].
  unfold Delta_s. simplify_func_tycontext.
  unfold DP_s, callD_s.
  cbn [dl_D dl_O dl_fin dl_off dl_flush dl_msg dl_c cs_s cs_ni cs_ain cs_tin cs_no cs_aout cs_tout cs_msgv cs_adler].
  Intros.
  destruct (su_ok_call u H) as (Hdb & Hdat & Hcap & Pd & Pc).
  destruct H0 as (HJl & HD & Hoff & Hfl & Hfl4 & Hfin & HO & HOb & Hmsg & Hni & Hno).
  cbn [dl_D dl_O dl_fin dl_off dl_flush dl_msg dl_c cs_s cs_ni cs_ain cs_tin cs_no cs_aout cs_tout cs_msgv cs_adler]
    in *.
  assert (HD0 := Zlength_nonneg D). assert (HO0 := Zlength_nonneg O).
  destruct (sd_range J HJ _ _ _ _ _ _ _ _ _ _ HJl) as (Htin & Htout & Hadl & Hgz).
  (* the bytes offered: clip(offered - |D|) of them, all of the rest under Z_FINISH *)
  assert (Hain : 0 <= ain <= off - Zlength D /\ ain <= 4294967295) by (rewrite H2; rep_lia).
  assert (Hain4 : flush = Z_FINISH -> Zlength D + ain = Zlength (su_data u)).
  { intros E. destruct (Hfl4 E) as [Eo Hr']. rewrite H2, Z.min_l by rep_lia. lia. }
  set (inb := sublist (Zlength D) (Zlength D + ain) (su_data u)).
  assert (Hinb : Zlength inb = ain) by (subst inb; rewrite Zlength_sublist; lia).
  assert (Hib : rbytes inb) by (apply Forall_sublist; auto).
  destruct (sd_deflate J HJ (su_wbits u) (sdict u) (sgh u) D O fin s tin tout adler inb aout flush msg HJl)
    as (s' & z' & code & Hrun & Hok & Hgz' & Hz0 & Hend & Hnext);
    [ lia | exact Hib | lia | unfold max_size in *; lia | rep_lia | unfold max_size in *; rep_lia | | ].
  { intros R HR. destruct (Hfin R HR) as [H4 HRe]. split; [exact H4|].
    rewrite HRe. subst inb. rewrite (Hain4 H4). reflexivity. }
  destruct (out_ok_ex_s u O aout Pc) as (Fo & W & HW & Hsplit & Hjoin); [rep_lia | rep_lia |].
  unfold cstream. cbn [cs_s cs_ni cs_ain cs_tin cs_no cs_aout cs_tout cs_msgv cs_adler].
  rewrite dstream_sp_eq. Intros sp.
  unfold Rm, c_locals, d_locals, lvs, lv_locals. simpl app.
  rewrite (dobj_split_s u (Zlength D) (Zlength D + ain)) by lia.
  sep_apply Hsplit.
  replace (api_fields vc ni ain tin no aout tout msgv adler)
    with (api_fields vc (offset_val 0 (offset_val (Zlength D) (su_dp u))) (Zlength inb)
            tin (offset_val (Zlength O) (su_cp u)) (Zlength (Zrepeat Vundef aout)) tout msgv adler)
    by (rewrite isptr_offset_val_zero, Hinb, Zlength_Zrepeat, <- Hni, <- Hno by (auto; lia); reflexivity).
  fold inb.
  assert (Hrg : strm_ranges (zmk inb 0 (Zlength inb) tin (Zlength (Zrepeat Vundef aout)) tout adler msg)).
  { unfold strm_ranges, zmk; simpl. rewrite Zlength_nil, Zlength_Zrepeat by lia. unfold u32_ok, u64_ok in *.
    repeat split; auto; try rep_lia. }
  forward_call (Some s, vc, ghp vh u, sp, hx, offset_val (Zlength D) (su_dp u), Ews,
                inb, 0, Zlength inb, tin, offset_val (Zlength O) (su_cp u), Zrepeat Vundef aout, W, tout, msgv, msg,
                adler, flush, (Some s', z', code), gv).
  { cancel. }
  { split.
    - unfold s32_ok. rep_lia.
    - exists (fun f => f). split; [ apply ef_ok_id | ].
      unfold on_state, c_on_state. rewrite c_deflate_g_id. rewrite Zlength_Zrepeat by lia.
      change (zmk ?a ?c ?e ?f ?g ?h ?i ?j) with (rzcall a c e f g h i j). rewrite Hrun. reflexivity. }
  simpl fst; simpl snd. Intros msgv'.
  forward.
  pose proof (ULoopDCallLib.cd_deflate_code _ _ _ _ _ _ Hrun) as Hcode.
  destruct Hok as (Hin & Hai & Hni' & Hti & Hao & Hlo & Hto & Hro).
  cbv zeta in Hnext.
  set (used := Zlength inb - z_avail_in z') in *.
  assert (Hused : 0 <= used <= ain) by lia.
  assert (HDl : D ++ sublist 0 used inb = sublist 0 (Zlength D + used) (su_data u)).
  { subst inb. rewrite HD at 1. list_solve. }
  set (l' := mkDL (D ++ sublist 0 used inb) (O ++ z_out z')
               (if flush =? Z_FINISH then Some (sublist used (Zlength inb) inb) else None) off flush (z_msg z')
               (mkCS s' (offset_val (z_next_in z') (offset_val (Zlength D) (su_dp u))) (z_avail_in z')
                  (z_total_in z') (offset_val (Zlength (z_out z')) (offset_val (Zlength O) (su_cp u)))
                  (z_avail_out z') (z_total_out z') msgv' (z_adler z'))).
  assert (Hl' : if code =? Z_STREAM_END
                then dfinal (sdict u) (rwrap_of (su_wbits u)) (rwbe (su_wbits u)) (sgh u) (su_data u)
                       (O ++ z_out z')
                else dl_ok J u l').
  { destruct (code =? Z_STREAM_END) eqn:Ec.
    - apply Z.eqb_eq in Ec. destruct (Hend Ec) as [Hf4 Ha0]. specialize (Hain4 Hf4).
      replace (su_data u) with (D ++ sublist 0 used inb). exact Hnext.
      rewrite HDl. subst used. rewrite Ha0, Hinb, Z.sub_0_r, Hain4. apply sublist_same; lia.
    - unfold dl_ok, l'.
      cbn [dl_D dl_O dl_fin dl_off dl_flush dl_msg dl_c cs_s cs_ni cs_ain cs_tin cs_no cs_aout cs_tout cs_msgv cs_adler].
      rewrite HDl in Hnext |- *. rewrite Zlength_sublist by lia. rewrite Z.sub_0_r.
      split; [exact Hnext|]. split; [reflexivity|]. split; [lia|].
      split; [lia|].
      split; [intros E; destruct (Hfl4 E); lia|].
      split.
      { intros R HR. destruct (flush =? Z_FINISH) eqn:Ef; [|discriminate]. apply Z.eqb_eq in Ef.
        injection HR as <-. split; [exact Ef|]. specialize (Hain4 Ef).
        subst inb. rewrite Hinb, sublist_sublist by lia. f_equal; lia. }
      split; [rewrite Zlength_app; lia|]. split; [apply Forall_app; auto|]. split; [auto|].
      split; rewrite offset_offset_val; f_equal; rewrite ?Zlength_app; lia. }
  (* no output space: Z_BUF_ERROR, and the six members are those before the call *)
  assert (Hbuf : aout = 0 -> code = Z_BUF_ERROR /\
                 cpos_s (dl_c l') = cpos_s (mkCS s ni ain tin no aout tout msgv adler)).
  { intros E. destruct (Hz0 E) as [Ec Ea]. split; [exact Ec|].
    assert (Ezo : Zlength (z_out z') = 0) by lia. assert (Ezn : z_next_in z' = 0) by lia.
    unfold cpos_s, l'; cbn [cs_ni cs_ain cs_tin cs_no cs_aout cs_tout dl_c].
    rewrite Ezo, Ezn, !isptr_offset_val_zero, <- Hni, <- Hno by (rewrite isptr_offset_val; auto).
    f_equal; lia. }
  (* the six members before the call are well typed *)
  assert (Hpz : LS.posz_ok (cpos_s (mkCS s ni ain tin no aout tout msgv adler))).
  { assert (Pni : isptr ni) by (rewrite Hni, isptr_offset_val; auto).
    assert (Pno : isptr no) by (rewrite Hno, isptr_offset_val; auto).
    unfold LS.posz_ok, cpos_s; cbn [LS.pz_next_in LS.pz_avail_in LS.pz_total_in LS.pz_next_out LS.pz_avail_out
                                    LS.pz_total_out cs_ni cs_ain cs_tin cs_no cs_aout cs_tout].
    split; [apply isptr_is_pointer_or_null; auto|].
    split; [apply isptr_is_pointer_or_null; auto|]. unfold u32_ok, u64_ok. rep_lia. }
  (* the call accounted for what it moved *)
  assert (Hacc : acc_ok_s u (dl_c l') (cpos_s (mkCS s ni ain tin no aout tout msgv adler))).
  { apply (acc_ok_of_s u _ _ (Zlength D + ain) (Zlength O + aout)); auto;
      unfold l', cpos_s;
      cbn [cs_ni cs_ain cs_tin cs_no cs_aout cs_tout dl_c LS.pz_next_in LS.pz_avail_in LS.pz_next_out
           LS.pz_avail_out]; try lia.
    - rewrite offset_offset_val. f_equal. lia.
    - rewrite offset_offset_val. f_equal. lia.
    - rewrite Hni. f_equal. lia.
    - rewrite Hno. f_equal. lia. }
  (* the header part: the state's gzhead is unchanged *)
  assert (Hgzs : d_gzhead s' = d_gzhead s) by congruence.
  assert (Hcl : hclose vh u s' hx Hr) by exact (hclose_gz vh u s s' hx Hr Hgzs H1).
  rewrite <- (hdr_at_gz s s' (ghp vh u) hx Hgzs).
  assert (HOl : Zlength (O ++ z_out z') <= su_cap u) by (rewrite Zlength_app; lia).
  assert (HOb' : rbytes (O ++ z_out z')) by (apply Forall_app; auto).
  assert (Hno' : offset_val (Zlength (z_out z')) (offset_val (Zlength O) (su_cp u)) =
                 offset_val (Zlength (O ++ z_out z')) (su_cp u))
    by (rewrite offset_offset_val, Zlength_app; f_equal; lia).
  sep_apply (ULoopDCallLib.cd_dstream_sp_fold 2 (Some s') vc (ghp vh u) sp gv).
  sep_apply (Hjoin (z_out z')); [lia|].
  sep_apply (dobj_join_s u (Zlength D) (Zlength D + ain)); [lia | lia |].
  Exists code l'.
  unfold DA_s, cstream, Rm, c_locals, d_locals, lvs, lv_locals. simpl app.
  change (dl_off l') with off. change (dl_flush l') with flush. change (dl_O l') with (O ++ z_out z').
  change (cs_no (dl_c l')) with (offset_val (Zlength (z_out z')) (offset_val (Zlength O) (su_cp u))).
  change (cs_s (dl_c l')) with s'.
  change (cs_ni (dl_c l')) with (offset_val (z_next_in z') (offset_val (Zlength D) (su_dp u))).
  change (cs_ain (dl_c l')) with (z_avail_in z'). change (cs_tin (dl_c l')) with (z_total_in z').
  change (cs_aout (dl_c l')) with (z_avail_out z'). change (cs_tout (dl_c l')) with (z_total_out z').
  change (cs_msgv (dl_c l')) with msgv'. change (cs_adler (dl_c l')) with (z_adler z').
  change (LS.pz_avail_out (cpos_s (mkCS s ni ain tin no aout tout msgv adler))) with aout.
  (* the records stay opaque to entailer! *)
  clearbody l'. set (a := cpos_s (mkCS s ni ain tin no aout tout msgv adler)) in *. clearbody a.
  entailer!.
Qed.
