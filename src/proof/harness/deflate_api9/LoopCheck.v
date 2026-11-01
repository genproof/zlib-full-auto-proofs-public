(* Law deflate_api, deflate_run's loop body: used, made and the API checks after the call (RunKit.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.harness.deflate_api.ApiCS Zlib.proof.harness.deflate_api9.RunSpec
               Zlib.proof.harness.deflate_api9.ApiConv Zlib.proof.harness.deflate_api9.RunKit.
Require Import Zlib.harness.x_deflate_api.code.
#[local] Existing Instance ApiCS.CS.
Local Open Scope logic.

(* an object of n bytes with its token: p + k is weakly valid for 0 <= k <= n (also for n = 0) *)
Lemma arr_wvp n (v : list val) p k :
  0 <= k <= n ->
  malloc_token Ews (tarray tuchar n) p * data_at Ews (tarray tuchar n) v p |-- weak_valid_pointer (offset_val k p).
Proof.
  intros Hk.
  assert_PROP (isptr p) as Pp by entailer!.
  destruct (Z.eq_dec n 0) as [E | E].
  - subst n. assert (k = 0) by lia. subst k. rewrite isptr_offset_val_zero by auto.
    eapply derives_trans; [ | apply valid_pointer_weak ].
    assert (Hs : sizeof (tarray tuchar 0) <= 0) by (simpl; lia).
    apply sepcon_valid_pointer1. apply malloc_token_valid_pointer; auto.
  - apply sepcon_weak_valid_pointer2.
    sep_apply (data_at_memory_block Ews (tarray tuchar n) v p).
    apply (memory_block_weak_valid_pointer Ews (sizeof (tarray tuchar n)) p k).
    + simpl. rewrite Z.max_r by lia. lia.
    + simpl. rewrite Z.max_r by lia. lia.
    + apply readable_nonidentity. apply writable_readable. apply writable_Ews.
Qed.

Transparent denote_tc_test_eq.
Lemma arr_tc_eq n (v : list val) p k F :
  0 <= k <= n ->
  F * (malloc_token Ews (tarray tuchar n) p * data_at Ews (tarray tuchar n) v p) |--
  denote_tc_test_eq (offset_val k p) (offset_val k p).
Proof.
  intros Hk.
  assert_PROP (isptr p) as Pp by entailer!.
  destruct p; try contradiction.
  unfold denote_tc_test_eq, test_eq_ptrs, sameblock. simpl. destruct (peq b b); [ | congruence]. simpl.
  change (Vptr b (Ptrofs.add i (Ptrofs.repr k))) with (offset_val k (Vptr b i)).
  apply andp_right; apply sepcon_weak_valid_pointer2; apply arr_wvp; auto.
Qed.
Opaque denote_tc_test_eq.

Lemma bytes_is l : bytes l -> is_bytes l.
Proof. unfold bytes, is_bytes. intros H. eapply Forall_impl; [ | exact H ]. intros a Ha. simpl. rep_lia. Qed.

Ltac bsolve :=
  unfold s32 in *; unfold vi, bool2val, Int.lt in *;
  try change (Int.neg (Int.repr 1)) with (Int.repr (-1)) in *;
  try change (Int.neg (Int.repr 2)) with (Int.repr (-2)) in *;
  try change (Int.neg (Int.repr 5)) with (Int.repr (-5)) in *;
  rewrite ?Int.signed_repr in * by rep_lia;
  repeat match goal with H : context [Z.leb _ _] |- _ => revert H end;
  repeat match goal with
         | |- context [zlt ?a ?b] => destruct (zlt a b)
         | |- context [?a <=? ?b] => destruct (Z.leb_spec a b)
         end; simpl; intros; try reflexivity; try lia;
  try (exfalso; match goal with H : Int.repr _ <> Int.zero |- _ => apply H; reflexivity end).

Lemma pok_of_iff c p s :
  (c = -2 <-> ~ (-1 <= p <= 9 /\ 0 <= s <= 4)) ->
  ((-1 <=? p) && (p <=? 9) && (0 <=? s) && (s <=? 4))%bool = negb (c =? -2).
Proof.
  intros [H1 H2].
  destruct (Z.leb_spec (-1) p), (Z.leb_spec p 9), (Z.leb_spec 0 s), (Z.leb_spec s 4);
    destruct (Z.eqb_spec c (-2)) as [E | E]; simpl; try reflexivity; exfalso;
    first [ apply (H1 E); lia | apply E; apply H2; intros [? ?]; lia ].
Qed.

Ltac contra :=
  exfalso; first [ contradiction | discriminate | lia
                 | match goal with H : _ <> _ |- _ => apply H; reflexivity end
                 | match goal with H : Int.repr _ <> Int.repr _ |- _ => apply H; f_equal; lia end
                 | match goal with H : Int.repr _ = Int.repr _ |- _ =>
                     apply repr_inj_signed in H; [ lia | rep_lia | rep_lia ] end ].

Ltac br := first [ solve [ contra ] | (forward; entailer!; try bsolve) ].

Ltac rb := unfold Rbody, loop1_ret_assert, overridePost, POST_r, frame_ret_assert; simpl RA_normal.

Lemma loop_check_ok {Espec : OracleKind} I Iend Rp sp api vosn gv rs ls ci s' z' code msgv' :
  semax Delta_r (B3 I Iend Rp sp api vosn gv rs ls ci s' z' code msgv') lsuf25 (Rbody I Iend Rp sp api vosn gv rs) ->
  semax Delta_r (B2 I Iend Rp sp api vosn gv rs ls ci s' z' code msgv') lsuf22 (Rbody I Iend Rp sp api vosn gv rs).
Proof.
  intros HK. unfold B2, B_loc, B_sep, lsuf22. abbreviate_semax. Intros.
  rename H into Hci, H0 into Hst, H1 into Hmsg.
  rewrite api_fields_L. unfold api_fieldsL. Intros.
  rename H into Uai, H0 into Uti, H1 into Uao, H2 into Uto, H3 into Uad.
  pose proof Hci as Hci'.
  destruct Hci' as [HJ [Hlim [Hfin' [Hfl [Haout [HOa [Hpar [Hplev [Hpstrat [Hbs [Hbsb [Pib [Pob Pq]]]]]]]]]]]]].
  pose proof HJ as HJ'.
  destruct HJ' as [RS [AF [S32 [HI [Hpos [Hnf [HO [HOb [Hfin [Hd [Hh Hmsg0]]]]]]]]]]].
  assert (RS' := RS). unfold rs_ok in RS'.
  assert (Hdl : Zlength (rs_data rs) <= 1048576) by tauto.
  assert (Hdb : bytes (rs_data rs)) by tauto.
  assert (Pdp : isptr (rs_datap rs)) by tauto.
  clear RS' HI Hd Hh Hmsg0 AF HJ Hfin.
  assert (Hinb : Zlength (ci_inb rs ls ci) = ci_lim ci - ls_pos ls)
    by (unfold ci_inb; rewrite Zlength_sublist; lia).
  pose proof Hst as Hst'. destruct Hst' as [Hgz [Hcall Hcodes]].
  destruct Hcall as (Hzin & Hai & Hni & Hti & Hao & Hzo & Hto & Hob).
  forward. forward. forward. forward. rewrite !sub_repr.
  rewrite Hni, Hinb. rewrite Hzo.
  match goal with |- semax _ ?P _ _ => forward_if P end.
  2: { forward. rb. entailer!. }
  2: { eapply semax_pre; [ | apply HK ].
       unfold B3, B_sep, B_loc. rewrite api_fields_L; unfold api_fieldsL. rewrite Hinb, Hzo, Hni, Hinb.
       entailer!. }
  (* avail_in <= ain && avail_out <= aout *)
  forward. forward_if (temp _t'65 (vi 1)).
  { forward. forward. entailer!. destruct (zlt (ci_aout ci) (z_avail_out z')); [lia | reflexivity]. }
  { exfalso. lia. }
  forward_call (Int.repr 1).
  (* next_in == ib + used && next_out == ob + made *)
  forward.
  assert (Hsi : force_val (sem_add_ptr_int tuchar Unsigned (ci_ib ci)
                  (Vint (Int.repr (ci_lim ci - ls_pos ls - z_avail_in z')))) =
                offset_val (ci_lim ci - ls_pos ls - z_avail_in z') (ci_ib ci)).
  { rewrite sem_add_pi_ptr_special by (auto; rep_lia). simpl force_val. change (sizeof tuchar) with 1.
    rewrite Z.mul_1_l. reflexivity. }
  assert (Hso : force_val (sem_add_ptr_int tuchar Unsigned (ci_ob ci)
                  (Vint (Int.repr (ci_aout ci - z_avail_out z')))) =
                offset_val (ci_aout ci - z_avail_out z') (ci_ob ci)).
  { rewrite sem_add_pi_ptr_special by (auto; rep_lia). simpl force_val. change (sizeof tuchar) with 1.
    rewrite Z.mul_1_l. reflexivity. }
  forward_if (temp _t'66 (vi 1)).
  { try rewrite Hsi. unfold obj. rewrite Hinb.
    eapply derives_trans; [ | apply (arr_tc_eq (ci_lim ci - ls_pos ls) (map vi (ci_inb rs ls ci)) (ci_ib ci) _ TT); lia ].
    cancel. }
  { forward. forward.
    { entailer!. try rewrite Hso.
      eapply derives_trans; [ | apply (arr_tc_eq (ci_aout ci)
        (map vi (z_out z') ++ sublist (ci_aout ci - z_avail_out z') (ci_aout ci) (map vi (ci_bs ci)))
        (ci_ob ci) _ TT); lia ].
      cancel. }
    entailer!. rewrite if_true by auto. reflexivity. }
  { exfalso. match goal with H : _ <> _ |- _ => rewrite Hsi in H; contradiction end. }
  forward_call (Int.repr 1).
  (* total_in == tin + used && total_out == tout + made *)
  forward.
  forward_if (temp _t'67 (vi 1)).
  { forward. forward. entailer!. rewrite Hto. unfold Int64.cmpu. rewrite Int64.eq_true. reflexivity. }
  { exfalso. match goal with H : Int64.repr _ <> _ |- _ => apply H end.
    rewrite Int.unsigned_repr by rep_lia. rewrite add64_repr. f_equal. lia. }
  forward_call (Int.repr 1).
  (* bytes_same(ib, R->data + pos, ain) *)
  unfold drun_rest. Intros.
  forward.
  assert (Hinbb : bytes (ci_inb rs ls ci)) by (unfold ci_inb; apply Forall_sublist; auto).
  unfold lsep, obj. Intros.
  rewrite (bytes_cs CS Zlib.units.Adler32.CS Ews (Zlength (ci_inb rs ls ci)) _ (ci_ib ci)).
  rewrite (bytes_cs CS Zlib.units.Adler32.CS Ews (Zlength (rs_data rs)) _ (rs_datap rs)).
  assert (CB1 : cbuf_ok false (ci_ib ci) Ews (ci_ib ci) 0 (Zlength (ci_inb rs ls ci)) (ci_lim ci - ls_pos ls)
                  (map vi (ci_inb rs ls ci)) (ci_inb rs ls ci)).
  { unfold cbuf_ok. rewrite isptr_offset_val_zero by auto. split3; [ reflexivity | auto with share | ].
    split3; [ lia | lia | ]. split3; [ lia | apply bytes_is; auto | ].
    rewrite sublist_same by (rewrite ?Zlength_map; lia). reflexivity. }
  assert (CB2 : cbuf_ok false (offset_val (ls_pos ls) (rs_datap rs)) Ews (rs_datap rs) (ls_pos ls)
                  (Zlength (rs_data rs)) (ci_lim ci - ls_pos ls) (map vi (rs_data rs)) (ci_inb rs ls ci)).
  { unfold cbuf_ok. split3; [ reflexivity | auto with share | ].
    split3; [ lia | lia | ]. split3; [ lia | apply bytes_is; auto | ].
    rewrite sublist_map. unfold ci_inb.
    replace (ls_pos ls + (ci_lim ci - ls_pos ls)) with (ci_lim ci) by lia. reflexivity. }
  forward_call (ci_ib ci, Ews, ci_ib ci, 0, Zlength (ci_inb rs ls ci), map vi (ci_inb rs ls ci), ci_inb rs ls ci,
                offset_val (ls_pos ls) (rs_datap rs), Ews, rs_datap rs, ls_pos ls, Zlength (rs_data rs),
                map vi (rs_data rs), ci_inb rs ls ci, ci_lim ci - ls_pos ls).
  { entailer!. unfold vi. rewrite sem_add_pi_ptr_special by (auto; rep_lia). change (sizeof tuchar) with 1.
    rewrite Z.mul_1_l. destruct (ci_ib ci); try contradiction. destruct (rs_datap rs); try contradiction.
    simpl. rewrite Int.unsigned_repr by rep_lia. reflexivity. }
  rewrite if_true by auto.
  forward_call (Int.repr 1).
  (* bytes_same(ob + made, osnap + made, aout - made) *)
  forward.
  rewrite (bytes_cs CS Zlib.units.Adler32.CS Ews (ci_aout ci) _ (ci_ob ci)).
  rewrite (bytes_cs CS Zlib.units.Adler32.CS Ews (Zlength (ci_bs ci)) _ (ci_q ci)).
  set (made := ci_aout ci - z_avail_out z') in *.
  assert (CB3 : cbuf_ok false (offset_val made (ci_ob ci)) Ews (ci_ob ci) made (ci_aout ci) (ci_aout ci - made)
                  (map vi (z_out z') ++ sublist made (ci_aout ci) (map vi (ci_bs ci)))
                  (sublist made (ci_aout ci) (ci_bs ci))).
  { unfold cbuf_ok. split3; [ reflexivity | auto with share | ].
    split3; [ lia | lia | ]. split3; [ rewrite Zlength_sublist; lia | apply bytes_is; apply Forall_sublist; auto | ].
    rewrite sublist_app2 by (rewrite Zlength_map; lia). rewrite Zlength_map, Hzo.
    rewrite Z.sub_diag. replace (made + (ci_aout ci - made) - made) with (ci_aout ci - made) by lia.
    rewrite sublist_same; [ | lia | rewrite Zlength_sublist; rewrite ?Zlength_map; lia ].
    rewrite sublist_map. reflexivity. }
  assert (CB4 : cbuf_ok false (offset_val made (ci_q ci)) Ews (ci_q ci) made (Zlength (ci_bs ci)) (ci_aout ci - made)
                  (map vi (ci_bs ci)) (sublist made (ci_aout ci) (ci_bs ci))).
  { unfold cbuf_ok. split3; [ reflexivity | auto with share | ].
    split3; [ lia | lia | ]. split3; [ rewrite Zlength_sublist; lia | apply bytes_is; apply Forall_sublist; auto | ].
    rewrite sublist_map. replace (made + (ci_aout ci - made)) with (ci_aout ci) by lia. reflexivity. }
  forward_call (offset_val made (ci_ob ci), Ews, ci_ob ci, made, ci_aout ci,
                map vi (z_out z') ++ sublist made (ci_aout ci) (map vi (ci_bs ci)),
                sublist made (ci_aout ci) (ci_bs ci),
                offset_val made (ci_q ci), Ews, ci_q ci, made, Zlength (ci_bs ci), map vi (ci_bs ci),
                sublist made (ci_aout ci) (ci_bs ci), ci_aout ci - made).
  rewrite if_true by auto.
  forward_call (Int.repr 1).
  rewrite <- (bytes_cs CS Zlib.units.Adler32.CS Ews (ci_aout ci) _ (ci_ob ci)).
  rewrite <- (bytes_cs CS Zlib.units.Adler32.CS Ews (Zlength (ci_bs ci)) _ (ci_q ci)).
  rewrite <- (bytes_cs CS Zlib.units.Adler32.CS Ews (Zlength (ci_inb rs ls ci)) _ (ci_ib ci)).
  rewrite <- (bytes_cs CS Zlib.units.Adler32.CS Ews (Zlength (rs_data rs)) _ (rs_datap rs)).
  forward_if.
  - (* deflateParams *)
    assert (Hp : ci_params ci = true) by (destruct (ci_params ci); auto; contradiction).
    rewrite Hp in Hcodes. destruct Hcodes as [Hc [Hiff _]].
    forward_if (temp _t'70 (vi (Z.b2z ((-1 <=? ci_plev ci) && (ci_plev ci <=? 9))%bool))).
    { forward. entailer!. bsolve. }
    { forward. entailer!. bsolve. }
    forward_if (temp _t'71 (vi (Z.b2z ((-1 <=? ci_plev ci) && (ci_plev ci <=? 9) && (0 <=? ci_pstrat ci))%bool))).
    { forward. entailer!. bsolve. }
    { forward. entailer!. bsolve. }
    forward_if (temp _t'72 (vi (Z.b2z ((-1 <=? ci_plev ci) && (ci_plev ci <=? 9) && (0 <=? ci_pstrat ci) &&
                                      (ci_pstrat ci <=? 4))%bool))).
    { forward. entailer!. bsolve. }
    { forward. entailer!. bsolve. }
    forward.
    destruct Hc as [Hc | [Hc | Hc]];
      [ assert (Ec : code = 0) by (rewrite Hc; reflexivity)
      | assert (Ec : code = -5) by (rewrite Hc; reflexivity)
      | assert (Ec : code = -2) by (rewrite Hc; reflexivity) ]; clear Hc; subst code.
    + forward_if (temp _t'73 (vi 1)); [ br | br | ].
      forward_if (temp _t'74 (vi 1)); [ br | br | ].
      forward_call (Int.repr 1).
      pose proof (pok_of_iff _ _ _ Hiff) as Hpk. simpl in Hpk. rewrite Hpk.
      forward_call (Int.repr 1).
      rb. unfold drun_rest, lsep, obj. entailer!.
    + forward_if (temp _t'73 (vi 1)); [ br | br | ].
      forward_if (temp _t'74 (vi 1)); [ br | br | ].
      forward_call (Int.repr 1).
      pose proof (pok_of_iff _ _ _ Hiff) as Hpk. simpl in Hpk. rewrite Hpk.
      forward_call (Int.repr 1).
      rb. unfold drun_rest, lsep, obj. entailer!.
    + forward_if (temp _t'73 (vi 0)); [ br | br | ].
      forward_if (temp _t'74 (vi 1)); [ br | br | ].
      forward_call (Int.repr 1).
      pose proof (pok_of_iff _ _ _ Hiff) as Hpk. simpl in Hpk. rewrite Hpk.
      forward_call (Int.repr 1).
      rb. unfold drun_rest, lsep, obj. entailer!.
  - (* deflate *)
    assert (Hp : ci_params ci = false) by (destruct (ci_params ci); auto; discriminate).
    rewrite Hp in Hcodes. destruct Hcodes as [Hc [Hend [Hbuf _]]].
    destruct Hc as [Hc | [Hc | Hc]];
      [ assert (Ec : code = 0) by (rewrite Hc; reflexivity)
      | assert (Ec : code = 1) by (rewrite Hc; reflexivity)
      | assert (Ec : code = -5) by (rewrite Hc; reflexivity) ]; clear Hc; subst code.
    + (* Z_OK *)
      forward_if (temp _t'75 (vi 1)); [ br | br | ].
      forward_if (temp _t'76 (vi 1)); [ br | br | ].
      forward_call (Int.repr 1).
      match goal with |- semax _ ?P _ _ => forward_if P end; [ contra | forward; entailer! | ].
      forward_if; [ contra | forward; rb; unfold drun_rest, lsep, obj; entailer! ].
    + (* Z_STREAM_END *)
      destruct (Hend eq_refl) as [Hf Hai0].
      assert (Hf4 : ci_flush ci = 4) by (rewrite Hf; reflexivity).
      assert (Hnf' : ci_nf ls ci = ci_lim ci) by (unfold ci_nf; rewrite Hf; reflexivity).
      forward_if (temp _t'75 (vi 1)); [ br | br | ].
      forward_if (temp _t'76 (vi 1)); [ br | br | ].
      forward_call (Int.repr 1).
      match goal with |- semax _ ?P _ _ => forward_if P end; [ | contra | ].
      { forward_if (temp _t'77 (vi 1)).
        { forward. forward. entailer!. all: rewrite Hnf', Hai0; destruct (zeq _ _); [ reflexivity | lia ]. }
        { contra. }
        forward_if (temp _t'78 (vi 1)).
        { forward. forward. entailer!. all: rewrite Hai0; reflexivity. }
        { contra. }
        forward_call (Int.repr 1). entailer!. }
      forward_if; [ contra | forward; rb; unfold drun_rest, lsep, obj; entailer! ].
    + (* Z_BUF_ERROR *)
      destruct (Hbuf eq_refl) as [Hai0 Hao0].
      assert (Hm0 : made = 0) by (unfold made; lia).
      forward_if (temp _t'75 (vi 0)); [ br | br | ].
      forward_if (temp _t'76 (vi 1)); [ br | br | ].
      forward_call (Int.repr 1).
      match goal with |- semax _ ?P _ _ => forward_if P end; [ contra | forward; entailer! | ].
      forward_if; [ | contra ].
      forward_if (temp _t'79 (vi 1)).
      { forward. entailer!. all: rewrite Hm0; reflexivity. }
      { contra. }
      forward_call (Int.repr 1).
      rb. unfold drun_rest, lsep, obj. entailer!.
Qed.
