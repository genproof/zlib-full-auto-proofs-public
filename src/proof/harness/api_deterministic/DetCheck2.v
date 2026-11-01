(* Law api_deterministic (data of any length): the checks of an iteration, read, and the four frees (DetKit2.det_check_stmt): the two
   streams' codes, adler, avail_in, avail_out and output bytes are the same; the loop invariant again unless
   Z_STREAM_END.  The three checks are proved in DetCheck2a, DetCheck2b and DetCheck2c, each from the assertion
   D_at at its statement to D_at at the next one (each part in a file of its own keeps every file's check short);
   this file proves the rest of the body and puts the parts together. *)
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
Require Import Zlib.proof.harness.api_deterministic.DetCheck2a.
Require Import Zlib.proof.harness.api_deterministic.DetCheck2b.
Require Import Zlib.proof.harness.api_deterministic.DetCheck2c.
Require Import Zlib.harness.api_deterministic.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

(* a stream's pieces after deflate (dstream_sp, the caller's fields, the two halves of the local) as the loop
   head's [shead]: next_in, avail_in, next_out, avail_out are forgotten *)
Lemma det_shead_fold (p : val) (s : dstate) (sp nin : val) (ain tin : Z) (nout : val) (aout tout : Z)
    (msgv : val) (adler : Z) (gv : globals) :
  u32_ok ain -> u64_ok tin -> u32_ok aout -> u64_ok tout -> u64_ok adler ->
  dstream_sp 2 (Some s) p nullval sp gv *
  field_at Ews t_strm (DOT DC._next_in) nin p * field_at Ews t_strm (DOT DC._avail_in) (vi ain) p *
  field_at Ews t_strm (DOT DC._total_in) (vl tin) p * field_at Ews t_strm (DOT DC._next_out) nout p *
  field_at Ews t_strm (DOT DC._avail_out) (vi aout) p * field_at Ews t_strm (DOT DC._total_out) (vl tout) p *
  field_at Ews t_strm (DOT DC._msg) msgv p * field_at Ews t_strm (DOT DC._adler) (vl adler) p *
  BoundKit.strm_pad p * data_at_ BoundKit.Ecomp t_strm p
  |-- shead p s sp tin tout msgv adler gv.
Proof.
  intros. unfold shead. Exists nin ain nout aout. unfold strm_at, api_fields. entailer!.
Qed.

(* the loop head after an iteration: deflate's state, [read] advanced by what deflate consumed, the rest of the
   data as [fin] once Z_FINISH was given, the stream fields deflate left *)
Definition det_next (n : Z) (data : list Z) (ls : lstate) (ci : citer) (d : dres) : lstate :=
  mkLS (dr_s d)
    (if ci_flush ci =? Z_FINISH then Some (sublist (ls_read ls + z_next_in (dr_z d)) n data) else None)
    (ci_offered ci) (ls_read ls + z_next_in (dr_z d)) (ci_flush ci) (z_total_out (dr_z d)) (z_adler (dr_z d))
    (z_msg (dr_z d)) (dr_msgv1 d) (dr_msgv2 d).

(* the loop invariant again after an iteration whose deflate did not return Z_STREAM_END; the gzip header
   stays unset as deflate keeps it (DetGz) *)
Lemma det_next_ok J n data datap ls ci c d :
  J_ok J n data datap ls -> ci_ok n ls ci -> cs_ok J data ls ci c -> dr_ok J data ls ci c d ->
  dr_code d <> Z_STREAM_END -> J_ok J n data datap (det_next n data ls ci d).
Proof.
  intros HJ Hci Hcs Hdr Hend.
  pose proof HJ as (Hsetup & HJs & Hgz0 & Hrd & Hoff & Hfl & Hfin & Htout & Hm1 & Hm2).
  pose proof Hsetup as (Hdf & Hn & Hdl & Hdb & Pdp).
  pose proof Hci as (Hro & Hcfl & Hc4 & Hcfin & Hroom & Pi1 & Pi2 & Po1 & Po2).
  pose proof Hcs as (HJc & Hgzc & Hnin & Hcout & Hcb & Hcfin' & Hctout & Hcm1 & Hcm2).
  pose proof Hdr as (Hcall & Hok & HJd & Hdm1 & Hdm2).
  pose proof Hok as (Hzin & Hni & Hai & Hti & Hao & Hzo & Hto & Hzb).
  specialize (HJd Hend).
  assert (Hinb : Zlength (ci_inb data ls ci) = ci_take ls ci)
    by (unfold ci_inb, ci_take; rewrite Zlength_sublist; lia).
  assert (Htk : ci_take ls ci = Z.min (ci_offered ci - ls_read ls) 4294967295) by reflexivity.
  assert (Hrg : strm_ranges (d_call data ls ci c)).
  { pose proof (df2_adler J Hdf _ _ _ _ HJc) as Had.
    unfold d_call, zcall, strm_ranges, u32_ok, u64_ok, u64r in *; simpl.
    rewrite Hinb. split3; [ lia | lia | ]. split3; [ lia | rep_lia | ]. split3; [ rep_lia | rep_lia | ].
    split3; [ rep_lia | rewrite Zlength_nil; rep_lia | ]. split3; [ rep_lia | rep_lia | ].
    split; [ unfold ci_inb; apply Forall_sublist; exact Hdb | constructor ]. }
  pose proof (det_gz_deflate _ _ _ _ _ _ Hrg Hcall) as Hgz.
  unfold J_ok, det_next; simpl. split; [ exact Hsetup | ]. split.
  { replace (ls_read ls + z_next_in (dr_z d)) with (z_total_in (dr_z d)) at 2 by lia.
    replace (if ci_flush ci =? Z_FINISH then Some (sublist (ls_read ls + z_next_in (dr_z d)) n data) else None)
      with (if ci_flush ci =? Z_FINISH
            then Some (sublist (z_next_in (dr_z d)) (ci_take ls ci) (ci_inb data ls ci)) else None);
      [ exact HJd | ].
    change Z_FINISH with 4. destruct (Z.eqb_spec (ci_flush ci) 4) as [E | E]; [ | reflexivity ].
    f_equal. destruct (Hc4 E) as [Ho Hr].
    (* after Z_FINISH the piece is the whole rest of the data *)
    assert (Htk' : ci_take ls ci = n - ls_read ls) by lia.
    unfold ci_inb. rewrite Htk'. rewrite sublist_sublist by lia. f_equal; lia. }
  split; [ rewrite Hgz; exact Hgzc | ].
  split; [ lia | ]. split; [ lia | ]. split; [ lia | ].
  split.
  { change Z_FINISH with 4. destruct (Z.eqb_spec (ci_flush ci) 4) as [E | E]; auto.
    destruct (Hc4 E) as [Ho Hr]. split3; auto. split; [ reflexivity | lia ]. }
  split; [ rewrite Hto; unfold u64r, u64;
           match goal with |- context [?x mod ?m] => pose proof (Z.mod_pos_bound x m ltac:(lia)) end; lia | ].
  split; auto.
Qed.

(* the end of the loop body: read += take - first.avail_in, the four frees, and the loop test's precondition
   T_inv with the next loop head det_next *)
Lemma det_check_tail {Espec : OracleKind} J n data datap v1 v2 sp1 sp2 gv ls ci c d :
  semax Delta_m (D_at J n data datap v1 v2 sp1 sp2 gv ls ci c d) lsuf16 (Rbody J n data datap v1 v2 sp1 sp2 gv).
Proof.
  pose proof (det_next_ok J n data datap ls ci c d) as HJ'.
  unfold D_at, D_sep, B_loc, lsuf16, Rbody, POST_m, Delta_m, Gmain. simplify_func_tycontext.
  abbreviate_semax. Intros.
  specialize (HJ' H H0 H1 H2).
  pose proof H as (Hsetup & _ & _ & Hrd & _).
  pose proof Hsetup as (_ & _ & Hdl & _).
  pose proof H0 as (Hro & _ & _ & _ & Hroom & Pi1 & Pi2 & Po1 & Po2).
  pose proof H1 as (_ & _ & Hnin & Hcout & _).
  pose proof H2 as (_ & Hok & _).
  pose proof Hok as (_ & Hni & Hai & Hti & Hao & Hzo & _).
  set (z := dr_z d) in *.
  assert (Hinb : Zlength (ci_inb data ls ci) = ci_take ls ci)
    by (unfold ci_inb, ci_take; rewrite Zlength_sublist; lia).
  assert (Hol : Zlength (cs_out c ++ z_out z) = ci_room ci - z_avail_out z)
    by (rewrite Zlength_app; lia).
  rewrite Hol.
  set (read' := ls_read ls + z_next_in z).
  assert (Hti' : z_total_in z = read') by (unfold read'; lia).
  unfold strm_at, api_fields. Intros.
  forward. forward.
  assert (Hrd' : Vlong (Int64.add (Int64.repr (ls_read ls))
                   (Int64.sub (Int64.repr (ci_take ls ci)) (Int64.repr (Int.unsigned (Int.repr (z_avail_in z))))))
                 = vl read').
  { unfold vl, read'. rewrite Int.unsigned_repr by (unfold u32_ok in H3; rep_lia).
    rewrite sub64_repr, add64_repr. do 2 f_equal. lia. }
  rewrite Hrd'.
  unfold BoundKit.obj.
  forward_call (tarray tuchar (Zlength (ci_inb data ls ci)), ci_in1 ci, gv).
  { rewrite if_false by (destruct (ci_in1 ci); simpl in *; try contradiction; discriminate). cancel. }
  forward_call (tarray tuchar (Zlength (ci_inb data ls ci)), ci_in2 ci, gv).
  { rewrite if_false by (destruct (ci_in2 ci); simpl in *; try contradiction; discriminate). cancel. }
  unfold out_at.
  forward_call (tarray tuchar (ci_room ci), ci_out1 ci, gv).
  { rewrite if_false by (destruct (ci_out1 ci); simpl in *; try contradiction; discriminate). cancel. }
  forward_call (tarray tuchar (ci_room ci), ci_out2 ci, gv).
  { rewrite if_false by (destruct (ci_out2 ci); simpl in *; try contradiction; discriminate). cancel. }
  unfold T_inv. Exists (dr_code d) (det_next n data ls ci d). unfold T_at, J_loc, J_sep.
  cbn [det_next ls_s ls_fin ls_offered ls_read ls_flush ls_tout ls_adler ls_msg ls_msgv1 ls_msgv2] in HJ' |- *.
  fold z read' in HJ' |- *.
  rewrite Hti' in *.
  sep_apply (det_shead_fold v1 (dr_s d) sp1 (offset_val (z_next_in z) (ci_in1 ci)) (z_avail_in z) read'
               (offset_val (ci_room ci - z_avail_out z) (ci_out1 ci)) (z_avail_out z) (z_total_out z)
               (dr_msgv1 d) (z_adler z) gv H3 H4 H5 H6 H7).
  sep_apply (det_shead_fold v2 (dr_s d) sp2 (offset_val (z_next_in z) (ci_in2 ci)) (z_avail_in z) read'
               (offset_val (ci_room ci - z_avail_out z) (ci_out2 ci)) (z_avail_out z) (z_total_out z)
               (dr_msgv2 d) (z_adler z) gv H3 H4 H5 H6 H7).
  entailer!.
Qed.

(* the three checks (DetCheck2a, DetCheck2b, DetCheck2c), then the tail *)
Lemma det_check : det_check_stmt.
Proof.
  unfold det_check_stmt. intros.
  apply det_check_code, det_check_avail, det_check_bytes, det_check_tail.
Qed.
