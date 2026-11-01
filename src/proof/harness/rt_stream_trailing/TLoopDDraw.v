(* Law rt_stream_trailing (harness/rt_stream_trailing.c), main's deflate loop (TMainKit.loopD_t), ported from rt_stream's
   rt_stream/ULoopDDraw.v: the first two statements of its body, read = next_in - data and the draws of offered and flush (when
   flush is not yet Z_FINISH), from the invariant DI_t to DR_t (TLoopDKit.drawD_t_stmt). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.deflate.Obligations.
Require Zlib.proof.deflate.Api_toend.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.rt_stream.UDFacts.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_stream.LawCS.
Require Import Zlib.proof.harness.rt_stream.UMainStmt.
Require Import Zlib.proof.harness.rt_stream.UMainKit.
Require Zlib.proof.harness.rt_stream.ULoopDKit.
Require Import Zlib.proof.harness.rt_stream.ULoopDLib.
Require Zlib.deflate.code.
Require Import Zlib.proof.harness.rt_stream_trailing.TMainStmt.
Require Import Zlib.proof.harness.rt_stream_trailing.TMainKit.
Require Import Zlib.proof.harness.rt_stream_trailing.TLoopDKit.
Require Import Zlib.harness.rt_stream_trailing.code.
#[local] Existing Instance LawCS.CS.
Local Open Scope logic.

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

(* the end of the draws: DR_t for the new state [l1], whose invariant ULoopDLib.dl_redraw gives *)
Ltac dd_fin l1 :=
  match goal with DL : dl_ok ?J ?u ?l |- context [loopD_post_t ?J' ?gv ?vc ?vd ?va ?u'] =>
    assert (dl_ok J u l1)
      by (apply (dl_redraw J u l); cbn [dl_D dl_O dl_fin dl_off dl_flush dl_msg dl_c]; auto; try lia;
          intro; first [discriminate | split; lia | match goal with H : ?f <> 4, E : ?f = _ |- _ => destruct (H E) end]);
    destruct (loopD_post_t J' gv vc vd va u'); cbv beta iota
  end;
  Exists l1; unfold DR_t, su_locals, lv_locals; simpl app;
  cbn [dl_D dl_O dl_fin dl_off dl_flush dl_msg dl_c];
  entailer!.

Lemma tdraw_d : drawD_t_stmt.
Proof.
  intros Espec J gv vc vd va u l HP.
  unfold bodyD_t, Delta_t; simplify_func_tycontext.
  unfold DI_t. Intros.
  match goal with H: su_ok u |- _ => rename H into SU end.
  match goal with H: dl_ok J u l |- _ => rename H into DL end.
  pose proof SU as (_ & _ & _ & _ & Hn & _ & Hcap & Pdp & Pcp & Pop).
  pose proof DL as (HJ & ED & HDoff & Hfl & Hfin4 & Hfin & HO & BO & Hmsg & Eni & Eno).
  destruct l as [D O fin off flush msg c]. cbn [dl_D dl_O dl_fin dl_off dl_flush dl_msg dl_c] in *.
  destruct c as [s ni ain tin no aout tout msgv adler].
  cbn [cs_s cs_ni cs_ain cs_tin cs_no cs_aout cs_tout cs_msgv cs_adler] in *.
  subst ni.
  unfold cstream, api_fields. Intros. cbn [cs_s cs_ni cs_ain cs_tin cs_no cs_aout cs_tout cs_msgv cs_adler] in *.
  rewrite ld_next_in_cs.
  unfold su_locals, lv_locals. simpl app.
  forward.
  forward.
  { entailer!. apply prop_right, ld_sameblock_off; auto. }
  rewrite dd_read by (auto; unfold max_size in *; rep_lia).
  rewrite <- ld_next_in_cs.
  sep_apply (ld_cstream_fold gv vc s (offset_val (Zlength D) (su_dp u)) ain tin no aout tout msgv adler); auto.
  set (c := mkCS s (offset_val (Zlength D) (su_dp u)) ain tin no aout tout msgv adler).
  set (n := Zlength (su_data u)) in *.
  forward_if (EX l1 : dls, DR_t gv vc vd va J u l1).
  { assert (Hnf : flush <> Z_FINISH) by (intro E; rewrite E in *; contradiction).
    forward_call (n - off). { unfold max_size in *; rep_lia. } Intros t.
    forward.
    rewrite <- !seq_assoc.
    forward_call 5. Intros fl.
    forward.
    rewrite Int64.unsigned_repr by (unfold max_size in *; rep_lia).
    rewrite add64_repr.
    set (b := andb (fl =? 4) (4294967295 <? n - Zlength D)).
    forward_if (PROP () LOCAL (temp _t'17 (Vint (if b then Int.one else Int.zero)); temp _flush (vi fl);
      temp _offered (vl (off + t)); temp _read (vl (Zlength D));
      temp _level (vi (su_level u)); temp _window_bits (vi (su_wbits u));
      temp _mem_level (vi (su_mem u)); temp _strategy (vi (su_strategy u));
      temp _data_len (vl n); temp _out_size (vl (su_cap u));
      temp _data (su_dp u); temp _expected (su_ep u); temp _compressed (su_cp u); temp _out (su_op u);
      lvar _decompressor t_z vd; lvar _at t_p va; lvar _compressor t_z vc; gvars gv)
      SEP (cstream gv vc c; data_at_ Tsh t_z vd; mem_mgr gv; Rm_t gv; dobj u; cobj u O; oobj u []; data_at_ Tsh t_p va)).
    { forward. entailer!.
      unfold b, bool2val; rewrite Z.eqb_refl; cbn [andb]. unfold Int64.cmpu, Int64.ltu.
      rewrite !Int64.unsigned_repr by (unfold max_size in *; rep_lia).
      destruct (zlt _ _), (Z.ltb_spec 4294967295 (n - Zlength D)); try reflexivity; lia. }
    { forward. entailer!. unfold b. rewrite (proj2 (Z.eqb_neq _ _) H8). reflexivity. }
    forward_if (PROP () LOCAL (temp _flush (vi (if b then 0 else fl));
      temp _offered (vl (off + t)); temp _read (vl (Zlength D));
      temp _level (vi (su_level u)); temp _window_bits (vi (su_wbits u));
      temp _mem_level (vi (su_mem u)); temp _strategy (vi (su_strategy u));
      temp _data_len (vl n); temp _out_size (vl (su_cap u));
      temp _data (su_dp u); temp _expected (su_ep u); temp _compressed (su_cp u); temp _out (su_op u);
      lvar _decompressor t_z vd; lvar _at t_p va; lvar _compressor t_z vc; gvars gv)
      SEP (cstream gv vc c; data_at_ Tsh t_z vd; mem_mgr gv; Rm_t gv; dobj u; cobj u O; oobj u []; data_at_ Tsh t_p va)).
    { forward. entailer!. destruct b; [reflexivity | contradiction]. }
    { forward. entailer!. destruct b; [discriminate | reflexivity]. }
    unfold b; destruct (Z.eqb_spec fl 4) as [Ef | Ef]; destruct (Z.ltb_spec 4294967295 (n - Zlength D)) as [Eg | Eg];
      cbn [andb].
    - (* Z_FINISH drawn but the rest does not fit in one call: flush becomes Z_NO_FLUSH *)
      forward_if; [ exfalso; lia | ].
      forward. dd_fin (mkDL D O fin (off + t) 0 msg c).
    - (* Z_FINISH drawn, the rest fits: all the data is offered *)
      subst fl. forward_if; [ | exfalso; lia ].
      forward. dd_fin (mkDL D O fin n 4 msg c).
    - forward_if; [ exfalso; lia | ].
      forward. dd_fin (mkDL D O fin (off + t) fl msg c).
    - forward_if; [ exfalso; lia | ].
      forward. dd_fin (mkDL D O fin (off + t) fl msg c). }
  { forward. Exists (mkDL D O fin off flush msg c).
    unfold DR_t, su_locals, lv_locals. simpl app. cbn [dl_D dl_O dl_fin dl_off dl_flush dl_msg dl_c].
    entailer!. }
  Intros l1. unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
  eapply semax_pre; [ | apply (HP l1) ].
  apply ENTAIL_refl.
Qed.
