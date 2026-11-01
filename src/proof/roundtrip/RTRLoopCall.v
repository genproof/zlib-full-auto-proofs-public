(* Law deflate_api, deflate_run's loop body: the call of deflateParams or deflate (RunKit.v). *)
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

(* the call's witness that next_out is weakly valid: the 0-byte object's token *)
Definition wtok (n : Z) : wvw := if n =? 0 then WVtok (tarray tuchar 0) else WVnone.
Definition tok_rest (n : Z) (p : val) : mpred :=
  if n =? 0 then emp else malloc_token Ews (tarray tuchar n) p.

Lemma tok_split n p :
  malloc_token Ews (tarray tuchar n) p = tok_rest n p * wv_at (wtok n) p.
Proof.
  unfold tok_rest, wtok, wv_at. destruct (n =? 0) eqn:E.
  - apply Z.eqb_eq in E. subst n. rewrite emp_sepcon. rewrite tok_tuchar_cs. reflexivity.
  - rewrite sepcon_emp. reflexivity.
Qed.

Lemma wtok_ok' n : n = 0 -> wv_ok (wtok n).
Proof. intros ->. simpl. reflexivity. Qed.

Lemma obj_dcs p l :
  obj p l = malloc_token Ews (tarray tuchar (Zlength l)) p *
            @data_at DCS.CS Ews (tarray tuchar (Zlength l)) (map vi l) p.
Proof. unfold obj. rewrite (bytes_cs CS DCS.CS). reflexivity. Qed.

Lemma dstream_sp_fold lvl os strmp ghp sp gv :
  dstream_sp lvl os strmp ghp sp gv |-- dstream lvl os strmp ghp gv.
Proof. rewrite dstream_sp_eq. Exists sp. cancel. Qed.

Lemma hdr_at_gz s s' ghp hx :
  d_gzhead s' = d_gzhead s -> hdr_at (Some s) ghp hx = hdr_at (Some s') ghp hx.
Proof. intros E. unfold hdr_at. rewrite E. reflexivity. Qed.

Lemma loop_call_ok {Espec : OracleKind} I Iend Rp sp api vosn gv rs ls ci :
  (forall s' z' code msgv',
     semax Delta_r (B2 I Iend Rp sp api vosn gv rs ls ci s' z' code msgv') lsuf22 (Rbody I Iend Rp sp api vosn gv rs)) ->
  semax Delta_r (B1 I Iend Rp sp api vosn gv rs ls ci) lsuf21 (Rbody I Iend Rp sp api vosn gv rs).
Proof.
  intros HK. unfold B1, B_loc, lsuf21.
  Intros.
  forward_if (EX s' : dstate, EX z' : strm, EX code : Z, EX msgv' : val,
                B2 I Iend Rp sp api vosn gv rs ls ci s' z' code msgv').
  - assert (Hp : ci_params ci = true) by (destruct (ci_params ci); auto; contradiction).
    pose proof H as Hci.
    destruct Hci as [HJ [Hlim [Hfin' [Hfl [Haout [HOa [Hpar [Hplev [Hpstrat [Hbs [Hbsb [Pib [Pob Pq]]]]]]]]]]]]].
    pose proof HJ as HJ'.
    destruct HJ' as [RS [AF [S32 [HI [Hpos [Hnf [HO [HOb [Hfin [Hd [Hh [Hmsg [RX [Hwb Hhw]]]]]]]]]]]]]].
    destruct (Hpar Hp) as [Hfn Hflf].
    rewrite Hfn in HI.
    assert (RS' := RS). unfold rs_ok in RS'.
    assert (Hinb : Zlength (ci_inb rs ls ci) = ci_lim ci - ls_pos ls)
      by (unfold ci_inb; rewrite Zlength_sublist; lia).
    assert (Hinbb : bytes (ci_inb rs ls ci)) by (unfold ci_inb; apply Forall_sublist; tauto).
    destruct (af_params _ _ AF (ls_dict ls) (wrap_of (rs_wbits rs)) (sublist 0 (ls_pos ls) (rs_data rs)) (ls_O ls)
                (ls_s ls) (ls_tin ls) (ls_tout ls) (ls_adler ls) (ci_inb rs ls ci) (ci_aout ci) (ci_plev ci)
                (ci_pstrat ci) (ls_msg ls)) as (s' & z' & code & Hrun & Hgz & Hcall & Hcode & Hiff & HI')
      ; auto; try (rewrite Zlength_sublist; lia); try lia.
    unfold lsep. rewrite dstream_sp_eq. Intros sp'.
    assert_PROP (u32_ok (ci_lim ci - ls_pos ls) /\ u64_ok (ls_tin ls) /\ u32_ok (ci_aout ci) /\
                 u64_ok (ls_tout ls) /\ u64_ok (ls_adler ls)) as HAF.
    { unfold api_fields. entailer!. }
    rewrite (obj_dcs (ci_ib ci)). unfold obj at 1. rewrite (tok_split (Zlength (ci_bs ci))).
    rewrite (bytes_cs CS DCS.CS Ews (Zlength (ci_bs ci))).
    rewrite <- (Zlength_map _ _ vi (ci_bs ci)).
    replace (api_fields sp (ci_ib ci) (ci_lim ci - ls_pos ls) (ls_tin ls) (ci_ob ci) (ci_aout ci) (ls_tout ls)
               (ls_msgv ls) (ls_adler ls))
      with (api_fields sp (offset_val 0 (ci_ib ci)) (Zlength (ci_inb rs ls ci)) (ls_tin ls) (ci_ob ci)
              (Zlength (map vi (ci_bs ci))) (ls_tout ls) (ls_msgv ls) (ls_adler ls))
      by (rewrite isptr_offset_val_zero, Hinb, Zlength_map, Hbs by auto; reflexivity).
    flatten_sepcon_in_SEP.
    forward_call (Some (ls_s ls), sp, ls_ghp ls, sp', hx_of rs, ci_ib ci, Ews, ci_inb rs ls ci, 0,
                  Zlength (ci_inb rs ls ci), ls_tin ls, ci_ob ci, map vi (ci_bs ci),
                  wtok (Zlength (map vi (ci_bs ci))), ls_tout ls, ls_msgv ls, ls_msg ls, ls_adler ls,
                  ci_plev ci, ci_pstrat ci, (Some s', z', code), gv).
    { rewrite !sepcon_assoc. cancel. }
    { split3.
      - intros; apply wtok_ok'; auto.
      - unfold strm_ranges, zmk; simpl. try rewrite Zlength_map, Hbs; try rewrite Hinb.
        unfold bytes in Hinbb. rewrite Zlength_nil. unfold u32_ok, u64_ok in *.
        repeat split; auto; try rep_lia.
      - exists (fun f => f). split; [ apply ef_ok_id | ].
        unfold on_state, c_on_state. rewrite c_deflateParams_g_id. rewrite Zlength_map, Hbs.
        change (zmk ?a ?b ?c ?d ?e ?f ?g ?h) with (zcall a b c d e f g h). rewrite Hrun. reflexivity. }
    simpl fst; simpl snd.
    Intros msgv'.
    forward.
    Exists s' z' code msgv'. unfold B2, B_sep, B_loc, lsep.
    rewrite (hdr_at_gz (ls_s ls) s' _ _ Hgz).
    sep_apply (dstream_sp_fold 2 (Some s') sp (ls_ghp ls) sp' gv).
    rewrite (obj_dcs (ci_ib ci)). rewrite (tok_split (ci_aout ci)).
    rewrite (bytes_cs CS DCS.CS Ews (ci_aout ci)).
    rewrite Zlength_map, Hbs.
    assert (Hst : step_ok I Iend rs ls ci s' z' code).
    { unfold step_ok. rewrite Hp. auto. }
    assert (Hsx : stepx rs ls ci s' z' code).
    { split; [ | intros Hp'; congruence ].
      eapply (rx_params _ RX (ls_dict ls) (wrap_of (rs_wbits rs)) (sublist 0 (ls_pos ls) (rs_data rs)) (ls_O ls)
                (ls_s ls) (ls_tin ls) (ls_tout ls) (ls_adler ls) (ci_inb rs ls ci) (ci_aout ci) (ci_plev ci)
                (ci_pstrat ci) (ls_msg ls)); eauto; try (rewrite Zlength_sublist; lia); try lia. }
    cbn [ls_s ls_hset ls_ghp ls_O].
    entailer!.
  - assert (Hp : ci_params ci = false) by (destruct (ci_params ci); auto; discriminate).
    pose proof H as Hci.
    destruct Hci as [HJ [Hlim [Hfin' [Hfl [Haout [HOa [Hpar [Hplev [Hpstrat [Hbs [Hbsb [Pib [Pob Pq]]]]]]]]]]]]].
    pose proof HJ as HJ'.
    destruct HJ' as [RS [AF [S32 [HI [Hpos [Hnf [HO [HOb [Hfin [Hd [Hh [Hmsg [RX [Hwb Hhw]]]]]]]]]]]]]].
    assert (RS' := RS). unfold rs_ok in RS'.
    assert (Hinb : Zlength (ci_inb rs ls ci) = ci_lim ci - ls_pos ls)
      by (unfold ci_inb; rewrite Zlength_sublist; lia).
    assert (Hinbb : bytes (ci_inb rs ls ci)) by (unfold ci_inb; apply Forall_sublist; tauto).
    assert (HR : forall R, ls_fin ls = Some R -> ci_flush ci = Z_FINISH /\ ci_inb rs ls ci = R).
    { intros R0 HR0. destruct (Hfin' R0 HR0) as [Hf Hl]. split; auto.
      destruct Hfin as [[Hn _] | Hs]; [congruence |].
      rewrite HR0 in Hs. inversion Hs. unfold ci_inb. rewrite Hl. reflexivity. }
    destruct (af_deflate _ _ AF (ls_dict ls) (wrap_of (rs_wbits rs)) (sublist 0 (ls_pos ls) (rs_data rs)) (ls_O ls)
                (ls_fin ls) (ls_s ls) (ls_tin ls) (ls_tout ls) (ls_adler ls) (ci_inb rs ls ci) (ci_aout ci)
                (ci_flush ci) (ls_msg ls))
      as (s' & z' & code & Hrun & Hgz & Hcall & Hcode & Hend & Hbuf & HI')
      ; auto; try (rewrite Zlength_sublist; lia); try lia.
    unfold lsep. rewrite dstream_sp_eq. Intros sp'.
    assert_PROP (u32_ok (ci_lim ci - ls_pos ls) /\ u64_ok (ls_tin ls) /\ u32_ok (ci_aout ci) /\
                 u64_ok (ls_tout ls) /\ u64_ok (ls_adler ls)) as HAF.
    { unfold api_fields. entailer!. }
    rewrite (obj_dcs (ci_ib ci)). unfold obj at 1. rewrite (tok_split (Zlength (ci_bs ci))).
    rewrite (bytes_cs CS DCS.CS Ews (Zlength (ci_bs ci))).
    rewrite <- (Zlength_map _ _ vi (ci_bs ci)).
    replace (api_fields sp (ci_ib ci) (ci_lim ci - ls_pos ls) (ls_tin ls) (ci_ob ci) (ci_aout ci) (ls_tout ls)
               (ls_msgv ls) (ls_adler ls))
      with (api_fields sp (offset_val 0 (ci_ib ci)) (Zlength (ci_inb rs ls ci)) (ls_tin ls) (ci_ob ci)
              (Zlength (map vi (ci_bs ci))) (ls_tout ls) (ls_msgv ls) (ls_adler ls))
      by (rewrite isptr_offset_val_zero, Hinb, Zlength_map, Hbs by auto; reflexivity).
    flatten_sepcon_in_SEP.
    forward_call (Some (ls_s ls), sp, ls_ghp ls, sp', hx_of rs, ci_ib ci, Ews, ci_inb rs ls ci, 0,
                  Zlength (ci_inb rs ls ci), ls_tin ls, ci_ob ci, map vi (ci_bs ci),
                  wtok (Zlength (map vi (ci_bs ci))), ls_tout ls, ls_msgv ls, ls_msg ls, ls_adler ls,
                  ci_flush ci, (Some s', z', code), gv).
    { rewrite !sepcon_assoc. cancel. }
    { split; [| split; [| split]].
      - intros; apply wtok_ok'; auto.
      - unfold s32_ok. rep_lia.
      - unfold strm_ranges, zmk; simpl. try rewrite Zlength_map, Hbs; try rewrite Hinb.
        unfold bytes in Hinbb. rewrite Zlength_nil. unfold u32_ok, u64_ok in *.
        repeat split; auto; try rep_lia.
      - exists (fun f => f). split; [ apply ef_ok_id | ].
        unfold on_state, c_on_state. rewrite c_deflate_g_id. rewrite Zlength_map, Hbs.
        change (zmk ?a ?b ?c ?d ?e ?f ?g ?h) with (zcall a b c d e f g h). rewrite Hrun. reflexivity. }
    simpl fst; simpl snd.
    Intros msgv'.
    forward.
    Exists s' z' code msgv'. unfold B2, B_sep, B_loc, lsep.
    rewrite (hdr_at_gz (ls_s ls) s' _ _ Hgz).
    sep_apply (dstream_sp_fold 2 (Some s') sp (ls_ghp ls) sp' gv).
    rewrite (obj_dcs (ci_ib ci)). rewrite (tok_split (ci_aout ci)).
    rewrite (bytes_cs CS DCS.CS Ews (ci_aout ci)).
    rewrite Zlength_map, Hbs.
    assert (Hst : step_ok I Iend rs ls ci s' z' code).
    { unfold step_ok. rewrite Hp. auto 10. }
    assert (Hsx : stepx rs ls ci s' z' code).
    { destruct (rx_deflate _ RX (ls_dict ls) (wrap_of (rs_wbits rs)) (sublist 0 (ls_pos ls) (rs_data rs)) (ls_O ls)
                (ls_fin ls) (ls_s ls) (ls_tin ls) (ls_tout ls) (ls_adler ls) (ci_inb rs ls ci) (ci_aout ci)
                (ci_flush ci) (ls_msg ls) s' z' code) as [Hw Hdf]; auto; try (rewrite Zlength_sublist; lia);
        try lia.
      split; [ exact Hw | intros _ Hc; exact (Hdf Hc) ]. }
    cbn [ls_s ls_hset ls_ghp ls_O].
    entailer!.
  - Intros s' z' code msgv'. apply HK.
Qed.
