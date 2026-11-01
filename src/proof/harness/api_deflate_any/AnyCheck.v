(* Law api_deflate_any: the checks after deflate (AnyKit.any_check_stmt): the three gp_asserts on the code, the
   output space past what was written still holds its bytes (bytes_eq against the copy), read, left, finishing,
   the three frees; the loop invariant for the next iteration unless the code is Z_STREAM_END (T_at).  The checks
   of the code are proved in AnyCheckCode.v, the check of the output space in AnyCheckBytes.v (each from D_at at
   its first statement to D_at at the next one), the next loop head and its invariant in AnyCheckNext.v; this
   file proves the rest of the body and puts the parts together. *)
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
Require Zlib.proof.harness.api_deflate_any.AnyCodes.
Require Zlib.proof.deflate.DModel5.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.api_deterministic.DetMem2.
Require Zlib.proof.harness.api_deterministic.DetMem2b.
Require Zlib.proof.harness.api_deterministic.DetKit2.
Require Import Zlib.proof.harness.api_deflate_any.AnyCS.
Require Import Zlib.proof.harness.api_deflate_any.AnyMainStmt.
Require Import Zlib.proof.harness.api_deflate_any.AnyKit.
Require Import Zlib.proof.harness.api_deflate_any.AnyCheckNext.
Require Zlib.proof.harness.api_deflate_any.AnyAt.
Require Import Zlib.proof.harness.api_deflate_any.AnyCheckCode.
Require Import Zlib.proof.harness.api_deflate_any.AnyCheckBytes.
Require Import Zlib.proof.harness.api_deflate_any.AnyCheckUnmoved.
Require Import Zlib.harness.api_deflate_any.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

Ltac simplify_remove_localdef_temp ::=
  repeat first [ rewrite rlt_nil | rewrite rlt_gvars | rewrite rlt_lvar | rewrite rlt_same
               | rewrite rlt_cons by (let X := fresh in intro X; discriminate X) ].

(* the end of the loop body: read += take - strm.avail_in, left = strm.avail_in, finishing = finishing || flush ==
   Z_FINISH, the three frees, and the loop test's precondition T_inv with the next loop head any_next *)
Lemma any_check_tail : any_check_tail_stmt.
Proof.
  unfold any_check_tail_stmt. intros.
  pose proof (any_next_ok J n data datap ls ci c d) as HJ'.
  unfold D_at, D_sep, B_loc, lsuf19, Rbody, POST_m, Delta_m, Gmain. simplify_func_tycontext.
  abbreviate_semax. Intros.
  specialize (HJ' H H0 H1 H2).
  pose proof H as (Hsetup & _ & Hrd & _ & _).
  pose proof Hsetup as (_ & _ & Hdl & _).
  pose proof H0 as (Htk & Htkn & Hfl & Hcfin & Hroom & Hbsl & _ & Pp & Po & Pb).
  pose proof H2 as (_ & Hok & _).
  pose proof Hok as (_ & Hni & Hai & Hti & _).
  assert (Hinb : Zlength (ci_inb data ls ci) = ci_take ci)
    by (unfold ci_inb; rewrite Zlength_sublist; lia).
  unfold DK.strm_at, api_fields. Intros.
  (* main's loads of strm.avail_in, at the law's compspecs *)
  rewrite any_field_cs_avail_in.
  forward. forward.
  set (read' := ls_read ls + z_next_in (dr_z d)).
  assert (Hrd' : Vlong (Int64.add (Int64.repr (ls_read ls))
                   (Int64.sub (Int64.repr (ci_take ci)) (Int64.repr (Int.unsigned (Int.repr (z_avail_in (dr_z d)))))))
                 = vl read').
  { unfold vl, read'. rewrite Int.unsigned_repr by (unfold u32_ok in H3; rep_lia).
    rewrite sub64_repr, add64_repr. do 2 f_equal. lia. }
  rewrite Hrd'.
  forward. forward.
  rewrite <- any_field_cs_avail_in.
  rewrite <- seq_assoc.
  forward_if (temp _t'41 (vi (if ci_flush ci =? 4 then 1 else 0))).
  { (* finishing was set: Z_FINISH was given before, so flush is Z_FINISH *)
    forward. entailer!. destruct (ls_fin ls) eqn:Ef; simpl in *.
    - destruct (Hcfin ltac:(congruence)) as [Ef4 _]. rewrite Ef4. reflexivity.
    - exfalso. match goal with H : ?a <> ?b |- _ => apply H; reflexivity end. }
  { forward. entailer!. destruct (ls_fin ls) eqn:Ef; simpl in *.
    - exfalso. match goal with H : Int.repr 1 = Int.zero |- _ =>
        apply (f_equal Int.unsigned) in H; rewrite Int.unsigned_repr, Int.unsigned_zero in H by rep_lia;
        discriminate H end.
    - destruct (Z.eqb_spec (ci_flush ci) 4) as [E4 | E4]; [ rewrite E4; reflexivity | ].
      unfold bool2val. rewrite Int.eq_false; [ reflexivity | ].
      intro X. apply (f_equal Int.signed) in X. rewrite !Int.signed_repr in X by rep_lia. lia. }
  forward.
  unfold BoundKit.obj.
  forward_call (tarray tuchar (Zlength (ci_inb data ls ci)), ci_piece ci, gv).
  { rewrite if_false by (destruct (ci_piece ci); simpl in *; try contradiction; discriminate). cancel. }
  unfold DK.out_at.
  forward_call (tarray tuchar (ci_room ci), ci_out ci, gv).
  { rewrite if_false by (destruct (ci_out ci); simpl in *; try contradiction; discriminate). cancel. }
  forward_call (tarray tuchar (Zlength (ci_bs ci)), ci_before ci, gv).
  { rewrite if_false by (destruct (ci_before ci); simpl in *; try contradiction; discriminate). cancel. }
  (* [at]'s position is not read any more *)
  sep_apply (AnyAt.any_at_free (c_pos ls ci c) ap).
  unfold T_inv. Exists (dr_code d) (any_next data ls ci d). unfold T_at, J_loc, J_sep.
  cbn [any_next ls_s ls_fin ls_read ls_left ls_tout ls_adler ls_msg ls_msgv] in HJ' |- *.
  fold read'.
  replace (z_total_in (dr_z d)) with read' by (unfold read'; lia).
  unfold DK.shead.
  Exists (offset_val (z_next_in (dr_z d)) (ci_piece ci)) (z_avail_in (dr_z d))
         (offset_val (Zlength (cs_out c ++ z_out (dr_z d))) (ci_out ci)) (z_avail_out (dr_z d)).
  unfold DK.strm_at, api_fields.
  entailer!.
  split; [ split | ].
  - unfold vl. rewrite Int.unsigned_repr by (unfold u32_ok in H3; rep_lia). reflexivity.
  - change Z_FINISH with 4. destruct (ci_flush ci =? 4); reflexivity.
  - unfold u64_ok, read'. pose proof Hsetup as (_ & Hn & _). pose proof H1 as (_ & Hnin & _). rep_lia.
Qed.

Lemma any_check : any_check_stmt.
Proof.
  unfold any_check_stmt. intros.
  apply any_check_code, any_check_unmoved, any_check_bytes, any_check_tail.
Qed.
