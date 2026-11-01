(* Law rt_session (harness/rt_session.c), main's deflate loop (SMKit.loopD): the out-of-room test at the end of the body, from DK_s to the loop's test or main's return (SMLDKit.testD_s_stmt). *)
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

(* next_out == compressed + out_size, cast to _Bool, at the law's compspecs: a boolean (rt_stream's ld_cmp_bool) *)
Lemma cmp_bool_s (p : val) a n : isptr p ->
  exists b : bool,
  force_val (sem_cast tint tbool (eval_binop Oeq (tptr tuchar) (tptr tuchar) (offset_val a p)
                                    (eval_binop Oadd (tptr tuchar) tulong p (vl n))))
  = Vint (if b then Int.one else Int.zero).
Proof.
  intros Pp. destruct p; try contradiction.
  simpl. unfold sem_cmp_pp; simpl. rewrite peq_true. simpl.
  destruct (Ptrofs.eq _ _); [exists true | exists false]; reflexivity.
Qed.

(* the end of the body, to the loop's test: DK_s with the deflate result [code] and the state [l] *)
Ltac ld_cont_s code l :=
  forward; Exists code l;
  unfold DK_s, c_locals, d_locals, lvs, lv_locals; simpl app;
  cbn [dl_D dl_O dl_fin dl_off dl_flush dl_msg dl_c cs_s cs_ni cs_ain cs_tin cs_no cs_aout cs_tout cs_msgv cs_adler];
  entailer!.

Lemma stest_d : testD_s_stmt.
Proof.
  intros Espec J gv vh vg vc va vd u off flush code l hx Hr.
  unfold testD_s, Delta_s; simplify_func_tycontext.
  unfold DK_s. Intros.
  match goal with H: su_ok u |- _ => rename H into SU end.
  match goal with H: hclose _ _ _ _ _ |- _ => rename H into HC end.
  pose proof SU as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hn & _ & Hcap & _) & _ & _ & _ & _ &
                    _ & Pcp & _).
  subst off flush.
  match goal with H: if code =? Z_STREAM_END then _ else _ |- _ => rename H into HK end.
  destruct l as [D O fin off flush msg c]. cbn [dl_D dl_O dl_fin dl_off dl_flush dl_msg dl_c] in *.
  destruct c as [s ni ain tin no aout tout msgv adler].
  cbn [cs_s cs_ni cs_ain cs_tin cs_no cs_aout cs_tout cs_msgv cs_adler] in *.
  subst no.
  unfold cstream, api_fields. Intros. cbn [cs_s cs_ni cs_ain cs_tin cs_no cs_aout cs_tout cs_msgv cs_adler] in *.
  rewrite next_out_s.
  unfold c_locals, d_locals, lvs, lv_locals. simpl app.
  apply semax_if_seq.
  forward_if.
  { forward. forward.
    { entailer!. rewrite ULoopDLib.ld_add_ptr_long_tuchar by (auto; unfold max_size in *; rep_lia). unfold cobj.
      eapply derives_trans;
        [ | apply (test_eq_s TT (su_cp u) (Zlength O) (su_cap u) (su_cap u) (cbytes (su_cap u) O))];
        [cancel | pose proof (Zlength_nonneg O); lia | lia | auto]. }
    destruct (cmp_bool_s (su_cp u) (Zlength O) (su_cap u) Pcp) as [b Eb]. rewrite Eb.
    rewrite <- next_out_s.
    sep_apply (cstream_fold_s gv vc (ghp vh u) s ni ain tin (offset_val (Zlength O) (su_cp u))
                 aout tout msgv adler); auto.
    forward_if.
    - (* out of room: return 0; the frame back from the compressor, head (by hclose) and got *)
      forward. Exists (Int.repr 0). sep_apply cstream_frame_s.
      sep_apply (HC s eq_refl). unfold hobj, graw.
      sep_apply (data_at_data_at_ Tsh t_g (hvals u) vh). sep_apply (data_at_data_at_ Tsh t_g (gval u) vg).
      entailer!.
    - ld_cont_s code (mkDL D O fin off flush msg
                       (mkCS s ni ain tin (offset_val (Zlength O) (su_cp u)) aout tout msgv adler)). }
  { forward. forward_if; [ exfalso; lia | ].
    rewrite <- next_out_s.
    sep_apply (cstream_fold_s gv vc (ghp vh u) s ni ain tin (offset_val (Zlength O) (su_cp u))
                 aout tout msgv adler); auto.
    ld_cont_s code (mkDL D O fin off flush msg
                    (mkCS s ni ain tin (offset_val (Zlength O) (su_cp u)) aout tout msgv adler)). }
Qed.
