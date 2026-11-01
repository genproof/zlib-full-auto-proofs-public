(* Law rt_session (harness/rt_session.c), main's deflate loop (SMKit.loopD): the first two statements of its body, read = next_in - data and the draws of offered and flush (when flush is not yet Z_FINISH), from the invariant DI to DR_s (SMLDKit.drawD_s_stmt). *)
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

(* read = (size_t) (data + k - data): the bytes consumed, k <= PTRDIFF_MAX *)
Lemma dd_read (p : val) k : isptr p -> 0 <= k <= Ptrofs.max_signed ->
  force_val (sem_binary_operation' Osub (tptr tuchar) (tptr tuchar) (offset_val k p) p) = vl k.
Proof.
  intros Pp Hk. destruct p; try contradiction. simpl.
  unfold sem_sub_pp. simpl. destruct (eq_block b b); [ | congruence]. simpl.
  rewrite Ptrofs.sub_add_l, Ptrofs.sub_idem, Ptrofs.add_zero_l.
  change (Ptrofs.repr 1) with Ptrofs.one. rewrite Ptrofs.divs_one by (cbv; congruence).
  unfold Vptrofs. simpl. f_equal. unfold Ptrofs.to_int64. rewrite Ptrofs.unsigned_repr by rep_lia.
  reflexivity.
Qed.

(* the end of the draws: DR_s for the new state [l1], whose invariant SMLDLib.dl_redraw_s gives *)
Ltac dd_fin l1 :=
  match goal with DL : dl_ok ?J ?u ?l |- context [loopD_post_s ?J' ?gv ?vh ?vg ?vc ?va ?vd ?u' ?hx' ?Hr'] =>
    assert (dl_ok J u l1)
      by (apply (dl_redraw_s J u l); cbn [dl_D dl_O dl_fin dl_off dl_flush dl_msg dl_c]; auto; try lia;
          intro; first [discriminate | split; lia | match goal with H : ?f <> 4, E : ?f = _ |- _ => destruct (H E) end]);
    destruct (loopD_post_s J' gv vh vg vc va vd u' hx' Hr'); cbv beta iota
  end;
  Exists l1; unfold DR_s, c_locals, d_locals, lvs, lv_locals; simpl app;
  cbn [dl_D dl_O dl_fin dl_off dl_flush dl_msg dl_c cs_s];
  entailer!.

Lemma sdraw_d : drawD_s_stmt.
Proof.
  intros Espec J gv vh vg vc va vd u hx Hr l HP.
  unfold bodyD_s, Delta_s; simplify_func_tycontext.
  unfold DI. Intros.
  match goal with H: su_ok u |- _ => rename H into SU end.
  match goal with H: dl_ok J u l |- _ => rename H into DL end.
  pose proof SU as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hn & _ & Hcap & _ & _ & _ & _ & _ & _ & _ & _ & Pdp) & _).
  pose proof DL as (HJ & ED & HDoff & Hfl & Hfin4 & Hfin & HO & BO & Hmsg & Eni & Eno).
  destruct l as [D O fin off flush msg c]. cbn [dl_D dl_O dl_fin dl_off dl_flush dl_msg dl_c] in *.
  destruct c as [s ni ain tin no aout tout msgv adler].
  cbn [cs_s cs_ni cs_ain cs_tin cs_no cs_aout cs_tout cs_msgv cs_adler] in *.
  subst ni.
  unfold cstream, api_fields. Intros. cbn [cs_s cs_ni cs_ain cs_tin cs_no cs_aout cs_tout cs_msgv cs_adler] in *.
  rewrite next_in_s.
  unfold c_locals, d_locals, lvs, lv_locals. simpl app.
  forward.
  forward.
  { entailer!. apply prop_right, ULoopDLib.ld_sameblock_off; auto. }
  rewrite dd_read by (auto; unfold max_size in *; rep_lia).
  rewrite <- next_in_s.
  sep_apply (cstream_fold_s gv vc (ghp vh u) s (offset_val (Zlength D) (su_dp u)) ain tin no aout tout msgv adler); auto.
  set (n := Zlength (su_data u)) in *.
  forward_if (EX l1 : dls, DR_s gv vh vg vc va vd J u l1 hx Hr).
  { assert (Hnf : flush <> Z_FINISH) by (intro E; rewrite E in *; contradiction).
    forward_call (n - off). { unfold max_size in *; rep_lia. } Intros t.
    forward.
    rewrite <- !seq_assoc.
    forward_call 5. Intros fl.
    forward.
    rewrite Int64.unsigned_repr by (unfold max_size in *; rep_lia).
    rewrite add64_repr.
    set (b := andb (fl =? 4) (4294967295 <? n - Zlength D)).
    forward_if (PROPx [] (LOCALx (temp _t'54 (Vint (if b then Int.one else Int.zero)) :: temp _flush (vi fl) ::
      temp _offered (vl (off + t)) :: temp _read (vl (Zlength D)) ::
      c_locals u ++ d_locals u (su_wbits u) ++ lvs gv vh vg vc va vd)
      (SEPx [cstream gv vc (ghp vh u) (mkCS s (offset_val (Zlength D) (su_dp u)) ain tin no aout tout msgv adler);
           data_at_ Tsh t_z vd; mem_mgr gv; Rm gv; dobj u; cobj u O; oobj u []; data_at_ Tsh t_p va;
           hdr_at (Some s) (ghp vh u) hx; Hr; graw vg u; dictobj u; dcopy u]))).
    { forward. unfold c_locals, d_locals, lvs, lv_locals; simpl app. entailer!.
      unfold b, bool2val; rewrite Z.eqb_refl; cbn [andb]. unfold Int64.cmpu, Int64.ltu.
      rewrite !Int64.unsigned_repr by (unfold max_size in *; rep_lia).
      destruct (zlt _ _), (Z.ltb_spec 4294967295 (n - Zlength D)); try reflexivity; lia. }
    { forward. unfold c_locals, d_locals, lvs, lv_locals; simpl app. entailer!.
      unfold b. match goal with E : fl <> 4 |- _ => rewrite (proj2 (Z.eqb_neq _ _) E) end. reflexivity. }
    unfold c_locals, d_locals, lvs, lv_locals; simpl app.
    forward_if (PROPx [] (LOCALx (temp _flush (vi (if b then 0 else fl)) ::
      temp _offered (vl (off + t)) :: temp _read (vl (Zlength D)) ::
      c_locals u ++ d_locals u (su_wbits u) ++ lvs gv vh vg vc va vd)
      (SEPx [cstream gv vc (ghp vh u) (mkCS s (offset_val (Zlength D) (su_dp u)) ain tin no aout tout msgv adler);
           data_at_ Tsh t_z vd; mem_mgr gv; Rm gv; dobj u; cobj u O; oobj u []; data_at_ Tsh t_p va;
           hdr_at (Some s) (ghp vh u) hx; Hr; graw vg u; dictobj u; dcopy u]))).
    { forward. unfold c_locals, d_locals, lvs, lv_locals; simpl app. entailer!.
      destruct b; [reflexivity | contradiction]. }
    { forward. unfold c_locals, d_locals, lvs, lv_locals; simpl app. entailer!.
      destruct b; [discriminate | reflexivity]. }
    unfold c_locals, d_locals, lvs, lv_locals; simpl app.
    unfold b; destruct (Z.eqb_spec fl 4) as [Ef | Ef]; destruct (Z.ltb_spec 4294967295 (n - Zlength D)) as [Eg | Eg];
      cbn [andb].
    - (* Z_FINISH drawn but the rest does not fit in one call: flush becomes Z_NO_FLUSH *)
      forward_if; [ exfalso; lia | ].
      forward. dd_fin (mkDL D O fin (off + t) 0 msg (mkCS s (offset_val (Zlength D) (su_dp u)) ain tin no aout tout msgv adler)).
    - (* Z_FINISH drawn, the rest fits: all the data is offered *)
      subst fl. forward_if; [ | exfalso; lia ].
      forward. dd_fin (mkDL D O fin n 4 msg (mkCS s (offset_val (Zlength D) (su_dp u)) ain tin no aout tout msgv adler)).
    - forward_if; [ exfalso; lia | ].
      forward. dd_fin (mkDL D O fin (off + t) fl msg (mkCS s (offset_val (Zlength D) (su_dp u)) ain tin no aout tout msgv adler)).
    - forward_if; [ exfalso; lia | ].
      forward. dd_fin (mkDL D O fin (off + t) fl msg (mkCS s (offset_val (Zlength D) (su_dp u)) ain tin no aout tout msgv adler)). }
  { forward. Exists (mkDL D O fin off flush msg (mkCS s (offset_val (Zlength D) (su_dp u)) ain tin no aout tout msgv adler)).
    unfold DR_s, c_locals, d_locals, lvs, lv_locals. simpl app. cbn [dl_D dl_O dl_fin dl_off dl_flush dl_msg dl_c cs_s].
    entailer!. }
  Intros l1. unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
  eapply semax_pre; [ | apply (HP l1) ].
  apply ENTAIL_refl.
Qed.
