(* Law api_deflate_any: the check of the output space (AnyCheck.any_check): wrote = out_size - strm.avail_out;
   gp_assert(strm.avail_out <= out_size && bytes_eq(out + wrote, before + wrote, strm.avail_out)).  deflate wrote
   [cs_out ++ z_out] at the start of the output space (wrote bytes: call_okw), so the space holds
   [ovals bs (cs_out ++ z_out)]: its last avail_out bytes are those of [bs], as in the copy [before].  The check
   does not change the memory, so the assertion after it is D_at again. *)
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
Require Import Zlib.proof.harness.api_deflate_any.AnyFacts.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.api_deterministic.DetMem2.
Require Zlib.proof.harness.api_deterministic.DetKit2.
Require Import Zlib.proof.harness.api_deflate_any.AnyCS.
Require Import Zlib.proof.harness.api_deflate_any.AnyMainStmt.
Require Import Zlib.proof.harness.api_deflate_any.AnyKit.
Require Import Zlib.proof.harness.api_deflate_any.AnyCheckNext.
Require Import Zlib.proof.harness.api_deflate_any.AnyCheckCode.
Require Import Zlib.harness.api_deflate_any.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.
Module DM := Zlib.proof.harness.api_deterministic.DetMem2.

Ltac simplify_remove_localdef_temp ::=
  repeat first [ rewrite rlt_nil | rewrite rlt_gvars | rewrite rlt_lvar | rewrite rlt_same
               | rewrite rlt_cons by (let X := fresh in intro X; discriminate X) ].


(* the output space past the [o] bytes written at its start holds the bytes of [bs] there *)
Lemma ovals_tail (bs o : list Z) :
  Zlength o <= Zlength bs ->
  sublist (Zlength o) (Zlength bs) (map vi (ovals bs o)) = bytes_rep (sublist (Zlength o) (Zlength bs) bs).
Proof.
  intros Hl. pose proof (Zlength_nonneg o). unfold ovals, bytes_rep.
  rewrite map_app, sublist_app2 by (rewrite Zlength_map; lia).
  rewrite Zlength_map, Z.sub_diag.
  rewrite sublist_same; [ reflexivity | reflexivity | ].
  rewrite Zlength_map, Zlength_sublist; lia.
Qed.

Lemma bs_tail (bs : list Z) (lo : Z) :
  0 <= lo <= Zlength bs ->
  sublist lo (Zlength bs) (map vi bs) = bytes_rep (sublist lo (Zlength bs) bs).
Proof. intros Hl. unfold bytes_rep. rewrite sublist_map. reflexivity. Qed.

(* out + wrote, before + wrote: a byte pointer plus an unsigned long (at any compspecs: main's body is proved at
   the law's) *)
Lemma add_ptr_long_uchar (cs : compspecs) (p : val) (k : Z) :
  isptr p -> 0 <= k <= Int64.max_signed -> force_val (@sem_add_ptr_long cs tuchar p (vl k)) = offset_val k p.
Proof.
  intros Pp Hk. destruct p; try contradiction. unfold sem_add_ptr_long, vl. simpl.
  unfold Ptrofs.of_int64. rewrite Int64.unsigned_repr by rep_lia. f_equal.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one. reflexivity.
Qed.

Lemma any_check_bytes : any_check_bytes_stmt.
Proof.
  intros Espec J n data datap v sp gv ap ls ci c d HK.
  unfold lsuf17. apply (@seq_assoc AnyCS.CS).
  eapply semax_seq' with (P' := D_at J n data datap v sp gv ap ls ci c d); [ | exact HK ].
  clear HK.
  unfold D_at, D_sep, B_loc, Rbody, POST_m, Delta_m, Gmain. simplify_func_tycontext.
  abbreviate_semax. Intros.
  unfold DK.strm_at, api_fields. Intros.
  pose proof H0 as (_ & _ & _ & _ & Hroom & Hbsl & Hbs & _ & Po & Pb).
  pose proof H1 as (_ & _ & Hcout & Hcb & _).
  pose proof H2 as (_ & Hok & _).
  pose proof Hok as (_ & _ & _ & _ & Hao & Hzo & _ & Hzb).
  assert (Hol : Zlength (cs_out c ++ z_out (dr_z d)) = ci_room ci - z_avail_out (dr_z d))
    by (rewrite Zlength_app; lia).
  set (W := ci_room ci - z_avail_out (dr_z d)) in *.
  assert (HW : W = ci_room ci - z_avail_out (dr_z d)) by reflexivity.
  pose proof (Zlength_nonneg (cs_out c)).
  assert (Hw : Vlong (Int64.sub (Int64.repr (ci_room ci)) (Int64.repr (Int.unsigned (Int.repr (z_avail_out (dr_z d))))))
               = vl W).
  { unfold vl, W. rewrite Int.unsigned_repr by (unfold u32_ok in H5; rep_lia).
    rewrite sub64_repr. reflexivity. }
  rewrite any_field_cs_avail_out.
  forward. forward. rewrite Hw.
  forward.
  (* the slices [W, room) of the output space and of the copy, avail_out bytes, hold the same bytes *)
  assert (CBo : cbuf_ok false (offset_val W (ci_out ci)) Ews (ci_out ci) W (ci_room ci) (z_avail_out (dr_z d))
                  (map vi (ovals (ci_bs ci) (cs_out c ++ z_out (dr_z d)))) (sublist W (ci_room ci) (ci_bs ci))).
  { unfold cbuf_ok. split3; [ reflexivity | auto with share | ]. split3; [ lia | lia | ].
    split3; [ rewrite Zlength_sublist; lia | | ].
    { unfold is_bytes. apply Forall_sublist. eapply Forall_impl; [ | exact Hbs ]. intros b Hb. simpl. rep_lia. }
    replace (W + z_avail_out (dr_z d)) with (Zlength (ci_bs ci)) by lia.
    rewrite <- Hbsl. replace W with (Zlength (cs_out c ++ z_out (dr_z d))) by lia.
    apply ovals_tail. lia. }
  assert (CBb : cbuf_ok false (offset_val W (ci_before ci)) Ews (ci_before ci) W (ci_room ci) (z_avail_out (dr_z d))
                  (map vi (ci_bs ci)) (sublist W (ci_room ci) (ci_bs ci))).
  { unfold cbuf_ok. split3; [ reflexivity | auto with share | ]. split3; [ lia | lia | ].
    split3; [ rewrite Zlength_sublist; lia | | ].
    { unfold is_bytes. apply Forall_sublist. eapply Forall_impl; [ | exact Hbs ]. intros b Hb. simpl. rep_lia. }
    replace (W + z_avail_out (dr_z d)) with (Zlength (ci_bs ci)) by lia.
    rewrite <- Hbsl. apply bs_tail. lia. }
  forward_if (temp _t'39 (vi 1)).
  { forward.
    unfold DK.out_at, BoundKit.obj. rewrite Hbsl.
    rewrite <- (DM.det_bytes_cs Ews (ci_room ci) _ (ci_out ci)).
    rewrite <- (DM.det_bytes_cs Ews (ci_room ci) _ (ci_before ci)).
    forward_call (offset_val W (ci_out ci), Ews, ci_out ci, W, ci_room ci,
                  map vi (ovals (ci_bs ci) (cs_out c ++ z_out (dr_z d))), sublist W (ci_room ci) (ci_bs ci),
                  offset_val W (ci_before ci), Ews, ci_before ci, W, ci_room ci,
                  map vi (ci_bs ci), sublist W (ci_room ci) (ci_bs ci), z_avail_out (dr_z d)).
    { entailer!. rewrite !(add_ptr_long_uchar AnyCS.CS) by (auto; rep_lia). simpl.
      rewrite Int.unsigned_repr by (unfold u32_ok in H5; rep_lia). reflexivity. }
    { cancel. }
    rewrite (DM.det_bytes_cs Ews (ci_room ci) _ (ci_out ci)).
    rewrite (DM.det_bytes_cs Ews (ci_room ci) _ (ci_before ci)).
    destruct (list_eq_dec Z.eq_dec (sublist W (ci_room ci) (ci_bs ci)) (sublist W (ci_room ci) (ci_bs ci)))
      as [_ | E]; [ | contradiction ].
    forward. entailer!. unfold DK.out_at, BoundKit.obj. rewrite Hbsl. cancel. }
  { exfalso. rewrite Int.unsigned_repr in * by (unfold u32_ok in H5; rep_lia).
    match goal with Hlt : _ < _ |- _ => lia end. }
  forward_call (Int.repr 1).
  rewrite <- any_field_cs_avail_out.
  unfold DK.out_at, BoundKit.obj, DK.strm_at, api_fields. rewrite Hbsl. entailer!.
Qed.
