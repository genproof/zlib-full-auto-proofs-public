(* Law rt_session (harness/rt_session.c): main's statements 63-72 without a header: inflateInit2_, a raw inflateSetDictionary and the inflate loop's start (SMKit.v, [segC_W_stmt]). *)
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
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SDFacts.
Require Import Zlib.proof.harness.rt_session.SIFacts.
Require Import Zlib.proof.harness.rt_session.SMainStmt.
Require Import Zlib.proof.harness.rt_session.SMKit.
Require Import Zlib.proof.harness.rt_session.SMCWKit.
Require Import Zlib.proof.harness.rt_session.SMCWTail.
Require Import Zlib.harness.rt_session.code.
#[local] Existing Instance SCS.CS.
Local Open Scope logic.

(* VST's after_forward_call simplifies remove_localdef_temp with `simpl rlt_ident_eq`, which runs away on main's
   identifiers (_i against _input); each identifier comparison is decided by vm_compute instead. *)
Ltac scw_rlt_fix u :=
  lazymatch u with
  | context C [rlt_ident_eq ?a ?b] =>
      let v := eval vm_compute in (rlt_ident_eq a b) in
      let u2 := context C [v] in scw_rlt_fix u2
  | _ => u
  end.

Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u := constr:(remove_localdef_temp i L) in
    let u' := eval lazy delta [remove_localdef_temp] beta iota in u in
    let u' := scw_rlt_fix u' in
    let u' := eval lazy beta iota in u' in
    let u' := eval lazy zeta in u' in
    change u with u'
  end.

(* the branch of a test whose value is known *)
Ltac scw_absurd :=
  exfalso;
  repeat match goal with
         | H : with_dict _ = _ |- _ => rewrite H in * |-; clear H
         | H : with_head _ = _ |- _ => rewrite H in * |-; clear H
         end;
  cbn [Z.b2z] in * |-;
  first [ lia
        | match goal with H : Int.repr _ = Int.zero |- _ =>
            apply (f_equal Int.unsigned) in H; vm_compute in H; discriminate end
        | match goal with H : Int.repr _ = Int.repr _ |- _ =>
            apply (f_equal Int.unsigned) in H; vm_compute in H; discriminate end
        | match goal with H : Int.repr _ <> _ |- _ => apply H; reflexivity end ].

Lemma sm_segC_W : segC_W_stmt.
Proof.
  intros Espec P PN gv vh vg vc va vd u O c src ip PF NH.
  unfold DB, II_W, segC, POST_s, c_locals, d_locals, lvs, lv_locals. cbn [app]. abbreviate_semax.
  Intros.
  match goal with H : su_ok u |- _ => pose proof H as [Hd Hp] end.
  pose proof Hd as (Hlv & Hwb & Hmem & Hstr & Hrp & Hch & Hdl & Hdb & _).
  rewrite (scw_undef vd).
  forward_call (vd, Tsh, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef,
                Vundef, Vundef, Vundef).
  rewrite (scw_ns_raw gv vd).
  (* if (window_bits == 8) window_bits = 9 *)
  match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
    forward_if (PROPx [] (LOCALx
      (temp _compressed_len (vl (Zlength O)) :: temp _after (vl (Zlength src - Zlength O)) :: temp _input ip ::
       c_locals u ++ d_locals u (rts_iw (su_wbits u)) ++ lvs gv vh vg vc va vd) (SEPx R))) end.
  { forward. unfold c_locals, d_locals, lvs, lv_locals. cbn [app]. entailer!. symmetry; apply scw_iw_8; auto. }
  { forward. unfold c_locals, d_locals, lvs, lv_locals. cbn [app]. entailer!.
    first [apply scw_iw_n8; auto | symmetry; apply scw_iw_n8; auto]. }
  unfold c_locals, d_locals, lvs, lv_locals. cbn [app].
  make_func_ptr Zlib.inflate.code._zcalloc. make_func_ptr Zlib.inflate.code._zcfree.
  gather_SEP (func_ptr' _ (gv Zlib.inflate.code._zcalloc)) (func_ptr' _ (gv Zlib.inflate.code._zcfree)).
  fold (zfuncs gv).
  unfold Rm at 1. Intros. rewrite scw_version.
  assert_PROP (isptr (gv ___stringlit_rt_session_1)) as Pv by entailer!.
  assert_PROP (isptr vd) as Pvd by entailer!.
  assert (Nd : vd <> nullval) by (intro; subst; contradiction).
  assert (Hw : Int.min_signed <= rts_iw (su_wbits u) <= Int.max_signed)
    by (unfold rts_iw, rs32 in *; destruct (su_wbits u =? 8); rep_lia).
  forward_call (gv, Tsh, vd, scw_ns, Vundef, Vundef, nullval, rts_iw (su_wbits u), gv ___stringlit_rt_session_1,
                Ers, scw_hv, 49, 112).
  { rewrite if_false by auto. cancel. }
  { change (Zlength scw_hv) with 6. repeat split; auto; rep_lia. }
  Intros vret. destruct vret as [aok sp]. cbn [fst snd] in *.
  (* the window bits deflateInit2_ accepted are valid for inflateInit2_: Z_OK unless Z_MEM_ERROR *)
  destruct (si_init _ _ _ PF (scase_of u) (su_data u) O src sp I H0 H4) as (WB & SW & P0).
  cbn [sc_wbits scase_of] in WB, SW, P0.
  replace (init_ret vd 49 112 (rts_iw (su_wbits u)) aok)
    with (if aok then Z_OK else Z_MEM_ERROR)
    by (unfold init_ret; simpl; rewrite if_false by auto; rewrite WB; destruct aok; reflexivity).
  destruct aok; cbv iota.
  2: (* Z_MEM_ERROR: return 0, the locals given back *)
    forward_if; [ | exfalso; match goal with H : Int.repr _ <> _ |- _ => apply H; reflexivity end];
    sep_apply (scw_init_fail gv vd scw_ns Z_MEM_ERROR sp (rts_iw (su_wbits u)) Pvd ltac:(cbv; congruence));
    sep_apply (scw_comp_back gv vc (ghp vh u) c);
    forward; Exists (Int.repr 0); entailer!;
    unfold hobj, graw; sep_apply (data_at_data_at_ Tsh t_g (hvals u) vh);
    sep_apply (data_at_data_at_ Tsh t_g (gval u) vg); cancel.
  (* Z_OK: a live stream *)
  set (L := init_live sp (rts_iw (su_wbits u))) in *.
  replace (init_mem gv Tsh vd scw_ns Vundef Vundef nullval Z_OK sp (rts_iw (su_wbits u)))
    with (istream_raw gv Tsh vd (raw_after_init scw_ns (l_s L)) L)
    by (unfold init_mem; rewrite if_false by auto; reflexivity).
  forward_if; [exfalso; match goal with H : Int.repr _ = _ |- _ =>
                  apply (f_equal Int.unsigned) in H; vm_compute in H; discriminate end | ].
  forward_call (Int.repr 1).
  assert_PROP (live_ok L) as LV by (unfold istream_raw; entailer!).
  sep_apply (scw_raw_istreamA gv vd L).
  (* without a header: if (with_head) skip *)
  apply semax_if_seq. forward_if; [scw_absurd | ].
  rewrite <- seq_assoc.
  destruct (Bool.bool_dec (with_dict u) true) as [WD | WD%Bool.not_true_is_false].
  - apply semax_if_seq. forward_if; [ | scw_absurd].
    forward.
    assert (NG : sc_gh (scase_of u) = None) by (unfold scase_of, sgh; cbn [sc_gh]; rewrite NH; reflexivity).
    assert (HT : tycontext_sub Delta_s Delta) by (unfold Delta, abbreviate; apply tycontext_sub_refl).
    destruct (zlt (rts_iw (su_wbits u)) 0) as [Neg | NNeg]; cbn [proj_sumbool bool2val].
    + (* a raw stream: inflateSetDictionary(&decompressor, dict_copy, (uInt) dict_len) *)
      apply semax_if_seq. forward_if; [ | scw_absurd].
      assert (SKR : sk_raw (scase_of u)).
      { split.
        - unfold scase_of, sdict; cbn [sc_dict]. rewrite WD. intro E. rewrite E, Zlength_nil in Hdl. lia.
        - unfold sc_wrap, scase_of, rwrap_of; cbn [sc_wbits].
          assert (su_wbits u < 0) by (unfold rts_iw in Neg; destruct (su_wbits u =? 8); lia).
          destruct (su_wbits u <? 0) eqn:E1; [reflexivity | apply Z.ltb_ge in E1; lia]. }
      assert (Esd : sc_dict (scase_of u) = su_dict u)
        by (unfold scase_of, sdict; cbn [sc_dict]; rewrite WD; reflexivity).
      rewrite <- !seq_assoc.
      unfold dcopy, bobj. flatten_sepcon_in_SEP.
      rewrite <- (scw_bytes_i Ews (Zlength (su_dict u)) (map vi (su_dict u)) (su_dcp u)),
              <- (scw_tok_i Ews (Zlength (su_dict u)) (su_dcp u)).
      rewrite <- (scw_istreamA_opt_ptr gv Tsh vd (scw_z nullval nullval L) Vundef (Some L)) by auto.
      forward_call (gv, Tsh, vd, scw_z nullval nullval L, Vundef, Some L, Ews, su_dcp u, 0, Zlength (su_dict u),
                    map vi (su_dict u), su_dict u, true).
      { entailer!. simpl. rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia.
        destruct (su_dcp u); try (exfalso; tauto). simpl. rewrite ?Ptrofs.add_zero. reflexivity. }
      { split; [tauto | split; [rewrite Zlength_map; reflexivity | split]].
        - rewrite sublist_same by (rewrite ?Zlength_map; lia). reflexivity.
        - unfold bytes_ok. eapply Forall_impl; [ | exact Hdb]. intros b Hb; simpl in *; rep_lia. }
      Intros vret. destruct vret as [aok winp]. cbn [fst snd] in *.
      unfold on_live. rewrite scw_is_live_ptr by auto.
      pose proof (si_rawdict _ _ _ PF (scase_of u) (su_data u) O src sp (scw_z nullval nullval L) aok winp I H0 H4
                    SKR eq_refl LV) as RD.
      cbv zeta in RD. change (sc_wbits (scase_of u)) with (su_wbits u) in RD. fold L in RD. rewrite Esd in RD.
      destruct RD as [Hr Hok].
      destruct (setdict_f (su_dict u) aok winp (scw_z nullval nullval L) L) as [[r z2] L2] eqn:Esdf.
      unfold fst3, snd3, thd3 in Hr, Hok |- *. cbn [fst snd] in Hr, Hok |- *.
      rewrite scw_istreamA_opt_ptr by auto.
      forward.
      (* if (code == Z_MEM_ERROR) return 0 *)
      forward_if.
      { sep_apply (scw_dec_back gv vd z2 Vundef L2). sep_apply (scw_comp_back gv vc (ghp vh u) c).
        forward. Exists (Int.repr 0). entailer!.
        unfold hobj, graw. sep_apply (data_at_data_at_ Tsh t_g (hvals u) vh).
        sep_apply (data_at_data_at_ Tsh t_g). cancel. }
      assert (R1 : r = Z_OK) by (destruct Hr as [-> | ->]; [reflexivity | scw_absurd]).
      destruct (Hok R1) as (-> & SW2 & HP2). subst r.
      (* gp_assert(code == Z_OK) *)
      forward_call (Int.repr 1).
      pose proof (si_shape _ _ _ PF _ _ _ _ _ _ _ _ _ I HP2) as NHd. rewrite NG in NHd.
      unfold abbreviate in MORE_COMMANDS; subst MORE_COMMANDS.
      drop_LOCAL 0%nat. drop_LOCAL 0%nat. drop_LOCAL 0%nat.
      eapply scw_sep_pre.
      2: { eapply (semax_Delta_subsumption Delta_s _ _ _ _ HT).
           apply (scw_tail_ok P gv vh vg vc va vd u O c src ip (scw_z nullval nullval L) L2); auto. }
      unfold dcopy, bobj. rewrite ?scw_bytes_i, ?scw_tok_i. cbn [fold_right_sepcon].
      rewrite <- (scw_bytes_i Ews (Zlength (su_dict u)) (map vi (su_dict u)) (su_dcp u)),
              <- (scw_tok_i Ews (Zlength (su_dict u)) (su_dcp u)).
      cancel.
    + (* a zlib stream: its dictionary is set when inflate() asks for it *)
      apply semax_if_seq. forward_if; [scw_absurd | ].
      assert (NR : ~ sk_raw (scase_of u)).
      { assert (Wnn : 0 <= su_wbits u)
          by (unfold rts_iw in NNeg; destruct (su_wbits u =? 8) eqn:E8; [apply Z.eqb_eq in E8 | ]; lia).
        intros [_ E]. unfold sc_wrap, scase_of, rwrap_of in E; cbn [sc_wbits] in E.
        destruct (su_wbits u <? 0) eqn:E1; [apply Z.ltb_lt in E1; lia | ].
        destruct (su_wbits u >? 15); discriminate. }
      specialize (P0 NG NR).
      pose proof (si_shape _ _ _ PF _ _ _ _ _ _ _ _ _ I P0) as NHd. rewrite NG in NHd.
      unfold abbreviate in MORE_COMMANDS; subst MORE_COMMANDS.
      drop_LOCAL 0%nat. drop_LOCAL 0%nat.
      eapply (semax_Delta_subsumption Delta_s _ _ _ _ HT).
      apply (scw_tail_ok P gv vh vg vc va vd u O c src ip (scw_z nullval nullval L) L); auto.
  - apply semax_if_seq. forward_if; [scw_absurd | ].
    forward.
    apply semax_if_seq. forward_if; [scw_absurd | ].
    assert (NR : ~ sk_raw (scase_of u)).
    { unfold sk_raw, scase_of, sdict; cbn [sc_dict]. rewrite WD. tauto. }
    assert (NG : sc_gh (scase_of u) = None) by (unfold scase_of, sgh; cbn [sc_gh]; rewrite NH; reflexivity).
    specialize (P0 NG NR).
    pose proof (si_shape _ _ _ PF _ _ _ _ _ _ _ _ _ I P0) as NHd. rewrite NG in NHd.
    assert (HT : tycontext_sub Delta_s Delta) by (unfold Delta, abbreviate; apply tycontext_sub_refl).
    unfold abbreviate in MORE_COMMANDS; subst MORE_COMMANDS.
    drop_LOCAL 0%nat. drop_LOCAL 0%nat.
    eapply (semax_Delta_subsumption Delta_s _ _ _ _ HT).
    apply (scw_tail_ok P gv vh vg vc va vd u O c src ip (scw_z nullval nullval L) L); auto.
Qed.
