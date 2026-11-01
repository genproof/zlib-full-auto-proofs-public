(* Law api_deterministic (data of any length): maybe deflateParams on both streams (DetKit2.det_params_stmt): the same model run
   (DetFacts2.df2_params), so the same code. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Rep.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.deflate.DetFacts2.
Require Zlib.proof.deflate.DModel5.
Require Import Zlib.proof.deflate.DetGz.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.api_deterministic.DetCS2.
Require Import Zlib.proof.harness.api_deterministic.DetMainStmt2.
Require Import Zlib.proof.harness.api_deterministic.DetKit2.
Require Import Zlib.harness.api_deterministic.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.


(* VST's after_forward_call simplifies [remove_localdef_temp i L] with [simpl], which takes about a minute when the
   identifiers are built by $"name": the same list built syntactically, comparing the identifiers by vm_compute *)
Ltac rlt_list i L :=
  lazymatch L with
  | temp ?j ?v :: ?L' =>
      let r := rlt_list i L' in
      let b := eval vm_compute in (Pos.eqb i j) in
      lazymatch b with true => r | false => constr:(temp j v :: r) end
  | ?d :: ?L' => let r := rlt_list i L' in constr:(d :: r)
  | nil => constr:(@nil localdef)
  end.
Local Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u' := rlt_list i L in change (remove_localdef_temp i L) with u' end.

(* deflateParams' witness that next_out is weakly valid when there is no output space: the token of the 0-byte
   output object *)
Definition dp_wtok (n : Z) : wvw := if n =? 0 then WVtok (tarray tuchar 0) else WVnone.
Definition dp_tok_rest (n : Z) (p : val) : mpred := if n =? 0 then emp else malloc_token Ews (tarray tuchar n) p.

Lemma dp_tok_split n p : malloc_token Ews (tarray tuchar n) p = dp_tok_rest n p * wv_at (dp_wtok n) p.
Proof.
  unfold dp_tok_rest, dp_wtok, wv_at. destruct (n =? 0) eqn:E.
  - apply Z.eqb_eq in E. subst n. rewrite emp_sepcon. reflexivity.
  - rewrite sepcon_emp. reflexivity.
Qed.

Lemma dp_wtok_ok n : n = 0 -> wv_ok (dp_wtok n).
Proof. intros ->. simpl. reflexivity. Qed.

(* a stream without a gzip header: deflateParams' header resource is empty *)
Lemma dp_hdr_none s hx : d_gzhead s = None -> hdr_at (Some s) nullval hx = emp.
Proof. intros E. unfold hdr_at. rewrite E. apply pred_ext; entailer!. Qed.

(* the output space after deflateParams wrote [o] into the fresh space *)
Lemma dp_out_after (room : Z) (o : list Z) :
  0 <= Zlength o <= room ->
  map vi o ++ sublist (Zlength o) (Zlength (Zrepeat Vundef room)) (Zrepeat Vundef room) = out_vals room o.
Proof.
  intros H. unfold out_vals. rewrite Zlength_Zrepeat by lia. rewrite sublist_Zrepeat by lia. reflexivity.
Qed.

(* the PROP part of deflateParams' precondition at main's two calls *)
Ltac pre_tac :=
  match goal with
  | Hinb : Zlength _ = _, Hinbb : bytes _, Hrun : c_deflateParams _ _ _ _ = _ |- _ =>
    rewrite Zlength_Zrepeat by lia;
    split; [| split; [| split; [| split]]];
    [ intros; apply dp_wtok_ok; lia
    | unfold s32_ok; rep_lia
    | unfold s32_ok; rep_lia
    | unfold strm_ranges, zmk; simpl; rewrite Zlength_nil, Hinb; unfold bytes in Hinbb; unfold ci_take in *;
      unfold u32_ok, u64_ok, u64r in *; repeat split; auto; try rep_lia
    | exists (fun f => f); split; [apply ef_ok_id |]; unfold on_state, c_on_state;
      rewrite DModel5.c_deflateParams_g_id; change (zmk ?a ?b ?c ?d ?e ?f ?g ?h) with (zcall a b c d e f g h);
      rewrite Hrun; reflexivity ]
  end.

Lemma det_params : det_params_stmt.
Proof.
  intros Espec J n data datap v1 v2 sp1 sp2 gv ls ci HK.
  (* the two calls (or none) end in C_at for some configuration; the rest is the continuation *)
  unfold lsuf10.
  eapply semax_seq' with (P' := EX c : cstate, C_at J n data datap v1 v2 sp1 sp2 gv ls ci c).
  2: { apply extract_exists_pre; intro c. apply HK. }
  clear HK.
  unfold C_at, B_loc.
  Intros.
  (* abbreviate the rest of the body first: forward_call on the whole statement is slow *)
  abbreviate_semax.
  forward_call tt. Intros b.
  forward_if.
  2: { forward. Exists (c0 ls). entailer!. }
  forward_call tt. Intros lv.
  forward_call tt. Intros st.
  pose proof H as [[Hdf [Hn [Hlen [Hbytes Hdp]]]] [HJ [Hgz [Hrd [Hoffn [Hlfl [Hfinm [Htout [Hm1 Hm2]]]]]]]]].
  pose proof H0 as (Hoff & Hfl & Hfl4 & Hfin & Hroom & Pi1 & Pi2 & Po1 & Po2).
  pose proof (df2_adler J Hdf _ _ _ _ HJ) as Had.
  set (level := Int.signed (Int.repr lv)).
  set (strategy := Int.signed (Int.repr st)).
  assert (Hlv : Vint (Int.repr lv) = vi level) by (unfold level, vi; rewrite Int.repr_signed; reflexivity).
  assert (Hst : Vint (Int.repr st) = vi strategy) by (unfold strategy, vi; rewrite Int.repr_signed; reflexivity).
  assert (Hinb : Zlength (ci_inb data ls ci) = ci_take ls ci)
    by (unfold ci_inb, ci_take; rewrite Zlength_sublist; lia).
  assert (Hinbb : bytes (ci_inb data ls ci)) by (apply Forall_sublist; auto).
  destruct (df2_params J Hdf (ls_fin ls) (ls_s ls) (ls_read ls) (ls_adler ls) (ci_inb data ls ci) 0 (ci_room ci)
              (ls_tout ls) level strategy (ls_msg ls))
    as (s' & z' & code & Hrun & Hcall & HJ');
    try solve [auto | unfold level, strategy, s32; rep_lia | rewrite Hinb; unfold ci_take; lia | lia].
  { intros R HR. rewrite sublist_same by lia.
    rewrite HR in Hfinm. destruct Hfinm as (_ & _ & -> & Hrest).
    assert (Hf4 : ci_flush ci = 4) by (apply Hfin; congruence).
    destruct (Hfl4 Hf4) as [Ho _].
    (* after Z_FINISH the rest fits in one call: the piece is the whole rest *)
    unfold ci_inb, ci_take. rewrite Ho. f_equal. lia. }
  rewrite Hinb, Z.sub_0_r in Hrun. rewrite Hinb in HJ'.
  unfold C_sep, c0, out_at, out_vals, strm_at, BoundKit.obj.
  cbn [cs_s cs_fin cs_nin cs_out cs_tout cs_adler cs_msg cs_msgv1 cs_msgv2].
  rewrite Zlength_nil, !Z.sub_0_r, !Z.add_0_r. simpl map. rewrite !app_nil_l.
  rewrite (isptr_offset_val_zero (ci_out1 ci) Po1), (isptr_offset_val_zero (ci_out2 ci) Po2).
  rewrite (dp_tok_split (ci_room ci) (ci_out1 ci)), (dp_tok_split (ci_room ci) (ci_out2 ci)).
  flatten_sepcon_in_SEP.
  forward_call (Some (ls_s ls), v1, nullval, sp1, (Ews, nullval, nullval, nullval), ci_in1 ci, Ews,
                ci_inb data ls ci, 0, ci_take ls ci, ls_read ls,
                ci_out1 ci, Zrepeat Vundef (ci_room ci),
                dp_wtok (ci_room ci), ls_tout ls, ls_msgv1 ls, ls_msg ls, ls_adler ls, level, strategy,
                (Some s', z', code), gv).
  { rewrite (dp_hdr_none (ls_s ls)) by auto. rewrite Zlength_Zrepeat by lia. cancel. }
  { pre_tac. }
  cbn [fst snd]. Intros msgv1'.
  forward_call (Some (ls_s ls), v2, nullval, sp2, (Ews, nullval, nullval, nullval), ci_in2 ci, Ews,
                ci_inb data ls ci, 0, ci_take ls ci, ls_read ls,
                ci_out2 ci, Zrepeat Vundef (ci_room ci),
                dp_wtok (ci_room ci), ls_tout ls, ls_msgv2 ls, ls_msg ls, ls_adler ls, level, strategy,
                (Some s', z', code), gv).
  { rewrite Zlength_Zrepeat by lia. cancel. }
  { pre_tac. }
  cbn [fst snd]. Intros msgv2'.
  forward_call (Int.one).
  { entailer!. simpl. rewrite Int.eq_true. reflexivity. }
  (* the configuration after the calls: the call's stream fields and output, Z_FINISH's rest from next_in on *)
  pose proof Hcall as (Hzin & Hnx & Hav & Htin & Haout & Hzout & Htot & Hzb).
  rewrite Hinb in Hnx, Hav.
  assert (Hsr : strm_ranges (zcall (ci_inb data ls ci) 0 (ci_take ls ci) (ls_read ls) (ci_room ci) (ls_tout ls)
                               (ls_adler ls) (ls_msg ls))).
  { unfold strm_ranges, zcall; simpl. rewrite Zlength_nil, Hinb. unfold bytes in Hinbb. unfold ci_take in *.
    unfold u32_ok, u64_ok, u64r in *. repeat split; auto; try rep_lia. }
  set (fin' := match ls_fin ls with
               | None => None
               | Some _ => Some (sublist (z_next_in z') (ci_take ls ci) (ci_inb data ls ci))
               end).
  set (c := mkCS s' fin' (z_next_in z') (z_out z') (z_total_out z') (z_adler z') (z_msg z') msgv1' msgv2').
  assert (Hcs : cs_ok J data ls ci c).
  { unfold cs_ok, c. cbn [cs_s cs_fin cs_nin cs_out cs_tout cs_adler cs_msg cs_msgv1 cs_msgv2].
    split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]].
    - rewrite Htin in HJ'. replace (ls_read ls + (z_next_in z' - 0)) with (ls_read ls + z_next_in z') in HJ'
        by lia. exact HJ'.
    - rewrite (det_gz_params _ _ _ _ _ _ _ Hsr Hrun). exact Hgz.
    - lia.
    - lia.
    - exact Hzb.
    - intros R HR. unfold fin' in HR. destruct (ls_fin ls) eqn:Ef; [| discriminate].
      split; [apply Hfin; congruence | congruence].
    - rewrite Htot. unfold u64r, u64. pose proof (Z.mod_pos_bound (ls_tout ls + (ci_room ci - z_avail_out z'))
        18446744073709551616 ltac:(lia)). lia.
    - auto. }
  Exists c.
  unfold C_sep, out_at, out_vals, strm_at, BoundKit.obj, c.
  cbn [cs_s cs_fin cs_nin cs_out cs_tout cs_adler cs_msg cs_msgv1 cs_msgv2].
  rewrite (dp_hdr_none (ls_s ls)) by auto.
  rewrite Zlength_Zrepeat by lia.
  rewrite sublist_Zrepeat by lia.
  rewrite (dp_tok_split (ci_room ci) (ci_out1 ci)), (dp_tok_split (ci_room ci) (ci_out2 ci)).
  replace (ci_take ls ci - z_next_in z') with (z_avail_in z') by lia.
  replace (ls_read ls + z_next_in z') with (z_total_in z') by lia.
  replace (ci_room ci - Zlength (z_out z')) with (z_avail_out z') by lia.
  entailer!.
Qed.


