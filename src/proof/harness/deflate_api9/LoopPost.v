(* Law deflate_api, deflate_run's loop body: the output into comp, pos, the frees, the break (RunKit.v). *)
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

(* comp's array cut at clen and clen + m, and joined back with m more bytes *)
Lemma comp_split O m p :
  0 <= m -> Zlength O + m <= COMP_MAX ->
  data_at Ews (tarray tuchar COMP_MAX) (map vi O ++ Zrepeat Vundef (COMP_MAX - Zlength O)) p |--
  !! field_compatible (tarray tuchar COMP_MAX) [] p &&
  (data_at Ews (tarray tuchar (Zlength O)) (map vi O) p *
   data_at_ Ews (tarray tuchar m) (offset_val (Zlength O) p) *
   data_at Ews (tarray tuchar (COMP_MAX - (Zlength O + m))) (Zrepeat Vundef (COMP_MAX - (Zlength O + m)))
     (offset_val (Zlength O + m) p)).
Proof.
  intros Hm HO. pose proof (Zlength_nonneg O).
  assert_PROP (field_compatible (tarray tuchar COMP_MAX) [] p) as FC by entailer!.
  rewrite (split3_data_at_Tarray_tuchar Ews COMP_MAX (Zlength O) (Zlength O + m))
    by (try lia; unfold COMP_MAX in *; list_solve).
  rewrite !field_address0_offset by auto with field_compatible.
  simpl. rewrite !Z.mul_1_l.
  replace (Zlength O + m - Zlength O) with m by lia.
  set (v := map vi O ++ Zrepeat Vundef (COMP_MAX - Zlength O)).
  assert (E1 : sublist 0 (Zlength O) v = map vi O) by (subst v; list_solve).
  assert (E2 : sublist (Zlength O) (Zlength O + m) v = Zrepeat Vundef m) by (subst v; unfold COMP_MAX in *; list_solve).
  assert (E3 : sublist (Zlength O + m) COMP_MAX v = Zrepeat Vundef (COMP_MAX - (Zlength O + m)))
    by (subst v; unfold COMP_MAX in *; list_solve).
  rewrite E1, E2, E3. unfold data_at_, field_at_. simpl default_val.
  entailer!.
Qed.

Lemma comp_join O l p :
  field_compatible (tarray tuchar COMP_MAX) [] p -> Zlength O + Zlength l <= COMP_MAX ->
  data_at Ews (tarray tuchar (Zlength O)) (map vi O) p *
  data_at Ews (tarray tuchar (Zlength l)) (map vi l) (offset_val (Zlength O) p) *
  data_at Ews (tarray tuchar (COMP_MAX - (Zlength O + Zlength l)))
    (Zrepeat Vundef (COMP_MAX - (Zlength O + Zlength l))) (offset_val (Zlength O + Zlength l) p) |--
  data_at Ews (tarray tuchar COMP_MAX) (map vi (O ++ l) ++ Zrepeat Vundef (COMP_MAX - Zlength (O ++ l))) p.
Proof.
  intros FC HO. pose proof (Zlength_nonneg O). pose proof (Zlength_nonneg l).
  rewrite (split3_data_at_Tarray_tuchar Ews COMP_MAX (Zlength O) (Zlength O + Zlength l))
    by (try lia; unfold COMP_MAX in *; list_solve).
  rewrite !field_address0_offset by auto with field_compatible.
  simpl. rewrite !Z.mul_1_l.
  replace (Zlength O + Zlength l - Zlength O) with (Zlength l) by lia.
  set (v := map vi (O ++ l) ++ Zrepeat Vundef (COMP_MAX - Zlength (O ++ l))).
  assert (E1 : sublist 0 (Zlength O) v = map vi O) by (subst v; list_solve).
  assert (E2 : sublist (Zlength O) (Zlength O + Zlength l) v = map vi l) by (subst v; unfold COMP_MAX in *; list_solve).
  assert (E3 : sublist (Zlength O + Zlength l) COMP_MAX v = Zrepeat Vundef (COMP_MAX - (Zlength O + Zlength l)))
    by (subst v; unfold COMP_MAX in *; list_solve).
  rewrite E1, E2, E3. cancel.
Qed.

Lemma add_ptr_long0 p z :
  isptr p -> 0 <= z <= Int64.max_unsigned ->
  force_val (sem_add_ptr_long tuchar p (Vlong (Int64.repr z))) = offset_val z p.
Proof.
  intros Pp Hz. destruct p; try contradiction. unfold sem_add_ptr_long. simpl. f_equal. f_equal.
  unfold Ptrofs.of_int64. rewrite Int64.unsigned_repr by rep_lia.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one. reflexivity.
Qed.

Lemma lp_sub_D (data : list Z) pos lim u :
  0 <= pos <= lim -> lim <= Zlength data -> 0 <= u <= lim - pos ->
  sublist 0 pos data ++ sublist 0 u (sublist pos lim data) = sublist 0 (pos + u) data.
Proof. intros. list_solve. Qed.

Lemma lp_sub_R (data : list Z) pos lim u :
  0 <= pos <= lim -> lim <= Zlength data -> 0 <= u <= lim - pos ->
  sublist u (lim - pos) (sublist pos lim data) = sublist (pos + u) lim data.
Proof. intros. list_solve. Qed.

(* the loop state after an iteration that does not break, and the final record after the break *)
Definition lp_used (rs : rsetup) (ls : lstate) (ci : citer) (z' : strm) : Z :=
  Zlength (ci_inb rs ls ci) - z_avail_in z'.

Definition lp_next (rs : rsetup) (ls : lstate) (ci : citer) (s' : dstate) (z' : strm) (msgv' : val) : lstate :=
  mkLS (ls_dict ls) (ls_pos ls + lp_used rs ls ci z') (ls_O ls ++ z_out z')
       (if ci_flush ci =? Z_FINISH then Some (sublist (ls_pos ls + lp_used rs ls ci z') (ci_lim ci) (rs_data rs))
        else None)
       s' (z_total_in z') (z_total_out z') (z_adler z') (offset_val (z_next_in z') (ci_ib ci)) (z_avail_in z')
       (offset_val (Zlength (z_out z')) (ci_ob ci)) (z_avail_out z') (z_msg z') msgv' (ci_nf ls ci)
       (ls_dset ls) (ls_hset ls) (ls_ghp ls).

Definition lp_final (rs : rsetup) (ls : lstate) (ci : citer) (s' : dstate) (z' : strm) (msgv' : val) : rfinal :=
  mkRF rs (ls_dict ls) (ci_nf ls ci) (ls_dset ls) (ls_hset ls) (ls_O ls ++ z_out z') s'
       (z_total_in z') (z_total_out z') (z_adler z') (offset_val (z_next_in z') (ci_ib ci)) (z_avail_in z')
       (offset_val (Zlength (z_out z')) (ci_ob ci)) (z_avail_out z') msgv' (ls_ghp ls).

Lemma lp_next_ok I Iend Rp api rs ls ci s' z' code msgv' :
  ci_ok I Iend Rp api rs ls ci -> step_ok I Iend rs ls ci s' z' code -> msg_ok (z_msg z') msgv' ->
  andb (negb (ci_params ci)) (code =? Z_STREAM_END) = false ->
  J_ok I Iend Rp api rs (lp_next rs ls ci s' z' msgv').
Proof.
  intros Hci Hst Hm Hnb.
  destruct Hci as [HJ [Hlim [Hfin' [Hfl [Haout [HOa [Hpar _]]]]]]].
  destruct HJ as [RS [AF [S32 [HI [Hpos [Hnf [HO [HOb [Hfin [Hd [Hh Hmsg]]]]]]]]]]].
  destruct Hst as [Hgz [Hcall Hstep]].
  destruct Hcall as (Hzin & Hain & Hnin & Htin & Haout' & Hzout & Htout & Hzb).
  assert (Hinb : Zlength (ci_inb rs ls ci) = ci_lim ci - ls_pos ls)
    by (unfold ci_inb; rewrite Zlength_sublist; lia).
  assert (HD : sublist 0 (ls_pos ls) (rs_data rs) ++ sublist 0 (lp_used rs ls ci z') (ci_inb rs ls ci) =
               sublist 0 (ls_pos ls + lp_used rs ls ci z') (rs_data rs)).
  { unfold lp_used. rewrite Hinb. unfold ci_inb. apply lp_sub_D; lia. }
  assert (HR : sublist (lp_used rs ls ci z') (Zlength (ci_inb rs ls ci)) (ci_inb rs ls ci) =
               sublist (ls_pos ls + lp_used rs ls ci z') (ci_lim ci) (rs_data rs)).
  { unfold lp_used. rewrite Hinb. unfold ci_inb. apply lp_sub_R; lia. }
  fold (lp_used rs ls ci z') in Hstep.
  assert (Hu : 0 <= lp_used rs ls ci z' <= ci_lim ci - ls_pos ls) by (unfold lp_used; lia).
  assert (HI' : I (ls_dict ls) (wrap_of (rs_wbits rs)) (sublist 0 (ls_pos ls + lp_used rs ls ci z') (rs_data rs))
                  (ls_O ls ++ z_out z')
                  (if ci_flush ci =? Z_FINISH
                   then Some (sublist (ls_pos ls + lp_used rs ls ci z') (ci_lim ci) (rs_data rs)) else None)
                  s' (z_total_in z') (z_total_out z') (z_adler z')).
  { rewrite <- HD. destruct (ci_params ci) eqn:Hp.
    - destruct Hstep as (_ & _ & HI'). destruct (Hpar eq_refl) as [_ Hf].
      replace (ci_flush ci =? Z_FINISH) with false by (symmetry; apply Z.eqb_neq; exact Hf). exact HI'.
    - cbn [negb andb] in Hnb. destruct Hstep as (_ & _ & _ & HI'). rewrite Hnb in HI'.
      rewrite <- HR. exact HI'. }
  unfold J_ok, lp_next. cbn [ls_dict ls_pos ls_O ls_fin ls_s ls_tin ls_tout ls_adler ls_nin ls_ain ls_nout ls_aout
                              ls_msg ls_msgv ls_nf ls_dset ls_hset ls_ghp].
  unfold ci_nf. rewrite Hgz.
  assert (HOz : Zlength (ls_O ls ++ z_out z') <= COMP_MAX) by (rewrite Zlength_app; lia).
  assert (HOzb : bytes (ls_O ls ++ z_out z')) by (apply Forall_app; auto).
  refine (conj RS (conj AF (conj S32 (conj _ _)))).
  { destruct (ci_flush ci =? Z_FINISH); exact HI'. }
  refine (conj _ (conj _ (conj HOz (conj HOzb (conj _ (conj Hd (conj Hh Hm))))))).
  all: destruct (ci_flush ci =? Z_FINISH) eqn:Ef;
    [ apply Z.eqb_eq in Ef
    | apply Z.eqb_neq in Ef;
      assert (Hn : ls_fin ls = None)
        by (destruct (ls_fin ls) as [R0|] eqn:E; auto; destruct (Hfin' R0 eq_refl); contradiction);
      assert (Hn' : ls_nf ls = Zlength (rs_data rs)) by (destruct Hfin as [[_ ?] | ?]; congruence) ].
  all: first [ lia | (right; reflexivity) | (left; split; auto) ].
Qed.

Lemma lp_final_ok I Iend Rp api rs ls ci s' z' code msgv' :
  ci_ok I Iend Rp api rs ls ci -> step_ok I Iend rs ls ci s' z' code -> msg_ok (z_msg z') msgv' ->
  ci_params ci = false -> code = Z_STREAM_END ->
  rf_ok Iend Rp (lp_final rs ls ci s' z' msgv').
Proof.
  intros Hci Hst HM Hp Hc.
  assert (HMv : is_pointer_or_null msgv')
    by (unfold msg_ok in HM; destruct (z_msg z'); [exact HM | subst; cbv; auto]).
  destruct Hci as [HJ [Hlim [Hfin' [Hfl [Haout [HOa [Hpar _]]]]]]].
  destruct HJ as [RS [AF [S32 [HI [Hpos [Hnf [HO [HOb [Hfin [Hd [Hh Hmsg]]]]]]]]]]].
  destruct Hst as [Hgz [Hcall Hstep]].
  destruct Hcall as (Hzin & Hain & Hnin & Htin & Haout' & Hzout & Htout & Hzb).
  rewrite Hp in Hstep. destruct Hstep as (_ & Hend & _ & Hfo). subst code.
  destruct (Hend eq_refl) as [Hf Ha0]. rewrite Z.eqb_refl in Hfo. destruct Hfo as [Hie Hfo].
  assert (Hinb : Zlength (ci_inb rs ls ci) = ci_lim ci - ls_pos ls)
    by (unfold ci_inb; rewrite Zlength_sublist; lia).
  rewrite Ha0, Z.sub_0_r, Hinb in Hfo. unfold ci_inb in Hfo.
  rewrite lp_sub_D in Hfo by lia. replace (ls_pos ls + (ci_lim ci - ls_pos ls)) with (ci_lim ci) in Hfo by lia.
  unfold rf_ok, lp_final, rf_wrap. cbn [rf_rs rf_dict rf_nf rf_dset rf_hset rf_O rf_s rf_adler rf_ghp].
  unfold ci_nf. rewrite Hf, Z.eqb_refl. rewrite Hgz.
  assert (HOz : Zlength (ls_O ls ++ z_out z') <= COMP_MAX) by (rewrite Zlength_app; lia).
  refine (conj RS (conj Hie (conj HMv (conj Hfo (conj _ (conj HOz (conj Hd Hh))))))). lia.
Qed.

Lemma loop_post_ok {Espec : OracleKind} I Iend Rp sp api vosn gv rs ls ci s' z' code msgv' :
  semax Delta_r (B3 I Iend Rp sp api vosn gv rs ls ci s' z' code msgv') lsuf25 (Rbody I Iend Rp sp api vosn gv rs).
Proof.
  unfold B3, B_sep, B_loc, lsuf25, Rbody, POST_r.
  Intros.
  match goal with H : ci_ok _ _ _ _ _ _ _ |- _ => pose proof H as Hci;
    destruct Hci as [HJ [Hlim [Hfin' [Hfl [Haout [HOa [Hpar [Hplev [Hpstrat [Hbs [Hbsb [Pib [Pob Pq]]]]]]]]]]]]] end.
  pose proof HJ as HJ'.
  destruct HJ' as [RS [AF [S32 [HI [Hpos [Hnf [HO [HOb [Hfin [Hd [Hh Hmsg]]]]]]]]]]].
  match goal with H : step_ok _ _ _ _ _ _ _ _ |- _ => pose proof H as Hst; destruct Hst as [Hgz [Hcall Hstep]] end.
  destruct Hcall as (Hzin & Hain & Hnin & Htin & Haout' & Hzout & Htout & Hzb).
  assert (Pc : isptr (rs_compp rs)) by (unfold rs_ok in RS; tauto).
  set (m := Zlength (z_out z')).
  assert (Hm : ci_aout ci - z_avail_out z' = m) by (subst m; lia).
  rewrite Hm.
  unfold drun_rest. Intros.
  forward. forward.
  unfold lsep, comp_at. cbn [ls_O ls_s ls_hset ls_ghp ls_dict]. Intros.
  sep_apply (comp_split (ls_O ls) m (rs_compp rs)); [subst m; lia | subst m; lia |].
  Intros.
  rewrite (bytes_cs CS Zlib.units.Adler32.CS Ews (ci_aout ci) _ (ci_ob ci)).
  replace (@data_at_ CS Ews (tarray tuchar m)) with (@data_at_ Zlib.units.Adler32.CS Ews (tarray tuchar m))
    by (extensionality q; unfold data_at_; apply bytes_cs).
  forward_call (offset_val (Zlength (ls_O ls)) (rs_compp rs), Ews, ci_ob ci, Ews, ci_ob ci, 0, ci_aout ci,
                map vi (z_out z') ++ sublist m (ci_aout ci) (map vi (ci_bs ci)), m, z_out z').
  { entailer!. unfold vl. rewrite add_ptr_long0 by (auto; unfold COMP_MAX in *; rep_lia).
    destruct (rs_compp rs); try contradiction. unfold vi. simpl.
    rewrite Int.unsigned_repr by (unfold COMP_MAX in *; rep_lia). reflexivity. }
  { unfold cbuf_ok. assert (0 <= m) by (subst m; apply Zlength_nonneg).
    split; [rewrite isptr_offset_val_zero by auto; reflexivity|].
    split; [auto|]. split; [lia|]. split; [lia|]. split; [reflexivity|]. split.
    - unfold is_bytes, bytes in *. eapply Forall_impl; [|exact Hzb]. simpl; intros; rep_lia.
    - unfold bytes_rep. replace (0 + m) with (Zlength (map vi (z_out z'))) by (rewrite Zlength_map; subst m; lia).
      pose proof (Zlength_nonneg (map vi (z_out z'))).
      rewrite sublist0_app1 by lia. rewrite sublist_same by lia. reflexivity. }
  forward. forward. forward.
  rewrite <- (bytes_cs CS Zlib.units.Adler32.CS Ews (ci_aout ci) _ (ci_ob ci)).
  rewrite <- (bytes_cs CS Zlib.units.Adler32.CS Ews m _ (offset_val (Zlength (ls_O ls)) (rs_compp rs))).
  unfold obj at 1.
  sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength (ci_inb rs ls ci))) (map vi (ci_inb rs ls ci)) (ci_ib ci)).
  forward_call (tarray tuchar (Zlength (ci_inb rs ls ci)), ci_ib ci, gv).
  { rewrite if_false by (intro; subst; destruct (ci_ib ci); try contradiction; discriminate). cancel. }
  sep_apply (data_at_data_at_ Ews (tarray tuchar (ci_aout ci))
    (map vi (z_out z') ++ sublist m (ci_aout ci) (map vi (ci_bs ci))) (ci_ob ci)).
  forward_call (tarray tuchar (ci_aout ci), ci_ob ci, gv).
  { rewrite if_false by (intro; subst; destruct (ci_ob ci); try contradiction; discriminate). cancel. }
  forward.
  unfold obj at 1.
  sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength (ci_bs ci))) (map vi (ci_bs ci)) (ci_q ci)).
  forward_call (tarray tuchar (Zlength (ci_bs ci)), ci_q ci, gv).
  { rewrite if_false by (intro; subst; destruct (ci_q ci); try contradiction; discriminate). cancel. }
  assert (Hinb : Zlength (ci_inb rs ls ci) = ci_lim ci - ls_pos ls)
    by (unfold ci_inb; rewrite Zlength_sublist; lia).
  assert (Eclen : Vlong (Int64.add (Int64.repr (Zlength (ls_O ls))) (Int64.repr (Int.unsigned (Int.repr m)))) =
                  vl (Zlength (ls_O ls ++ z_out z'))).
  { rewrite Int.unsigned_repr by (subst m; unfold COMP_MAX in *; rep_lia).
    rewrite add64_repr, Zlength_app. reflexivity. }
  rewrite Eclen. clear Eclen.
  assert (Epos : Vint (Int.add (Int.repr (ls_pos ls)) (Int.repr (Zlength (ci_inb rs ls ci) - z_avail_in z'))) =
                 vi (ls_pos ls + (Zlength (ci_inb rs ls ci) - z_avail_in z'))).
  { unfold vi. rewrite add_repr. reflexivity. }
  rewrite Epos. clear Epos.
  change (bytes_rep (z_out z')) with (map vi (z_out z')).
  subst m.
  sep_apply (comp_join (ls_O ls) (z_out z') (rs_compp rs) ltac:(assumption) ltac:(lia)).
  sep_apply (data_at_data_at_ Tsh (tptr tuchar) (ci_q ci) vosn).
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'80 (Vint (if andb (negb (ci_params ci)) (code =? Z_STREAM_END)
                                                    then Int.one else Int.zero)) :: Q) (SEPx R))) end.
  { forward. entailer!. destruct (ci_params ci); [discriminate|].
    destruct Hstep as [Hc _]. destruct Hc as [-> | [-> | ->]]; reflexivity. }
  { forward. entailer!. destruct (ci_params ci) eqn:Hpp; [reflexivity|]. exfalso. auto. }
  match goal with Hc : ci_ok _ _ _ _ _ _ _, Hs : step_ok _ _ _ _ _ _ _ _ |- _ =>
    rename Hc into Hci0; rename Hs into Hst0 end.
  forward_if.
  { assert (Hbr : andb (negb (ci_params ci)) (code =? Z_STREAM_END) = true).
    { destruct (andb (negb (ci_params ci)) (code =? Z_STREAM_END)) eqn:E; auto;
      exfalso; first [discriminate | contradiction | auto]. }
    apply andb_prop in Hbr. destruct Hbr as [Hp Hc]. apply negb_true_iff in Hp. apply Z.eqb_eq in Hc.
    pose proof (lp_final_ok I Iend Rp api rs ls ci s' z' code msgv' Hci0 Hst0
                  ltac:(match goal with H : msg_ok (z_msg z') msgv' |- _ => exact H end) Hp Hc) as Hrf.
    forward.
    unfold E_inv. Exists (lp_final rs ls ci s' z' msgv').
    unfold E_at, comp_at, drun_rest.
    unfold lp_final in *. unfold rf_wrap in *.
    cbn [rf_rs rf_dict rf_nf rf_dset rf_hset rf_O rf_s rf_tin rf_tout rf_adler rf_nin rf_ain rf_nout rf_aout
         rf_msgv rf_ghp] in *.
    entailer!. }
  { assert (Hnb : andb (negb (ci_params ci)) (code =? Z_STREAM_END) = false).
    { destruct (andb (negb (ci_params ci)) (code =? Z_STREAM_END)) eqn:E; auto;
      exfalso; first [discriminate | contradiction | auto]. }
    pose proof (lp_next_ok I Iend Rp api rs ls ci s' z' code msgv' Hci0 Hst0 ltac:(assumption) Hnb) as HJn.
    forward.
    unfold J_inv. Exists (lp_next rs ls ci s' z' msgv').
    unfold J_at, lsep, comp_at, drun_rest.
    unfold lp_next in *. unfold lp_used in *.
    cbn [ls_dict ls_pos ls_O ls_fin ls_s ls_tin ls_tout ls_adler ls_nin ls_ain ls_nout ls_aout
         ls_msg ls_msgv ls_nf ls_dset ls_hset ls_ghp] in *.
    replace (fin_flag (if ci_flush ci =? Z_FINISH
                       then Some (sublist (ls_pos ls + (Zlength (ci_inb rs ls ci) - z_avail_in z')) (ci_lim ci)
                                    (rs_data rs)) else None)) with (ci_fin ci)
      by (unfold ci_fin; destruct (ci_flush ci =? Z_FINISH); reflexivity).
    entailer!. }
Qed.