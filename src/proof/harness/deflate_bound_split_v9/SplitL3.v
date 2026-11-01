(* Law deflate_bound_split, main: the two asserts, pos += ain - s.avail_in, the three frees, if (r == Z_STREAM_END) break (statements 16..22 of lbody) (SplitKit.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.harness.x_deflate_bound_split.code.
Require Import Zlib.proof.harness.deflate_bound_split_v9.SplitMain Zlib.proof.harness.deflate_bound_split_v9.SplitKit.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

(* the loop invariant after an iteration that does not break *)
Lemma l3_next Bpre Brun bs b pos fin s f ci s' z' code msgv' :
  ci_ok Bpre Brun bs b pos fin s f ci -> step_ok Brun bs b pos s f ci s' z' code -> msg_ok (z_msg z') msgv' ->
  code <> Z_STREAM_END ->
  J_ok Bpre Brun bs b (pos + Zlength (ci_inb bs pos ci) - z_avail_in z') (ci_fin ci) s' (sf_after ci z' msgv').
Proof.
  intros Hci Hst Hm Hc.
  destruct Hci as (HJ & Hlim & Hff & Hfl & _).
  destruct HJ as (BS & BF & OB & HB & Hgzh & Hmsg & Hpos & Hb).
  destruct Hst as (Hcall & Hgz & _ & Hzain & Htout & Hnext).
  assert (Hinb : Zlength (ci_inb bs pos ci) = ci_lim ci - pos)
    by (unfold ci_inb; rewrite Zlength_sublist; try lia; destruct BS as (_ & Hn & _); lia).
  assert (Hf : (ci_flush ci =? Z_FINISH) = ci_fin ci) by (unfold ci_flush; destruct (ci_fin ci); reflexivity).
  specialize (Hnext Hc). rewrite Hf in Hnext.
  unfold J_ok, sf_after. cbn [sf_tin sf_tout sf_adler sf_msg sf_msgv].
  rewrite Hgz. refine (conj BS (conj BF (conj OB (conj Hnext (conj Hgzh (conj Hm (conj _ Hb))))))). lia.
Qed.

Lemma part_l3 {Espec : OracleKind} Bpre Brun sp hp vosn gv bs b pos fin s f ci s' z' code msgv' :
  semax Delta_m (B2 Bpre Brun sp hp vosn gv bs b pos fin s f ci s' z' code msgv') lsuf16
    (Rbody Bpre Brun sp hp vosn gv bs b).
Proof.
  unfold B2, lsuf16, Rbody, Rm_ret, POST_m, B_locals, loop_locals.
  simpl app.
  Intros.
  abbreviate_semax.
  pose proof H0 as Hst. destruct Hst as (Hcall & Hgz & Hc & Hzain & Htout & Hnext).
  unfold Z_OK, Z_BUF_ERROR, Z_STREAM_END in Hc.
  pose proof H as Hci. destruct Hci as (HJ & Hlim & Hff & Hfl & Haout & Hobs & Hobsb & Pib & Pob & Pq).
  pose proof HJ as HJ'. destruct HJ' as (BS & BF & OB & HB & Hgzh & Hmsg & Hpos & Hb).
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'50 (Vint (if orb (code =? 0) (code =? -5) then Int.one else Int.zero)) :: Q) (SEPx R))) end.
  { forward. entailer!. }
  { forward. entailer!. destruct Hc as [-> | [-> | ->]]; first [contradiction | reflexivity]. }
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'51 (Vint Int.one) :: Q) (SEPx R))) end.
  { forward. entailer!. }
  { forward. entailer!. destruct Hc as [-> | [-> | ->]]; first [discriminate | reflexivity]. }
  forward_call Int.one.
  unfold live, sf_at, api_fields. cbn [sf_nin sf_ain sf_tin sf_nout sf_aout sf_tout sf_msgv sf_adler sf_after]. Intros.
  forward.
  forward_call Int.one.
  { entailer!. unfold u64_ok in *. arg_cmp. }
  forward. forward.
  unfold obj at 1.
  sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength (ci_inb bs pos ci))) (map vi (ci_inb bs pos ci)) (ci_ib ci)).
  forward_call (tarray tuchar (Zlength (ci_inb bs pos ci)), ci_ib ci, gv).
  { rewrite if_false by (intro; subst; destruct (ci_ib ci); try contradiction; discriminate). cancel. }
  sep_apply (data_at_data_at_ Ews (tarray tuchar (ci_aout ci))
      (map vi (z_out z') ++ sublist (Zlength (z_out z')) (ci_aout ci) (map vi (ci_obs ci))) (ci_ob ci)).
  forward_call (tarray tuchar (ci_aout ci), ci_ob ci, gv).
  { rewrite if_false by (intro; subst; destruct (ci_ob ci); try contradiction; discriminate). cancel. }
  forward.
  unfold obj at 1.
  sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength (ci_obs ci))) (map vi (ci_obs ci)) (ci_q ci)).
  forward_call (tarray tuchar (Zlength (ci_obs ci)), ci_q ci, gv).
  { rewrite if_false by (intro; subst; destruct (ci_q ci); try contradiction; discriminate). cancel. }
  assert (Hinb : Zlength (ci_inb bs pos ci) = ci_lim ci - pos)
    by (unfold ci_inb; rewrite Zlength_sublist; try lia; destruct BS as (_ & Hn & _); lia).
  assert (Epos : Vint (Int.add (Int.repr pos) (Int.sub (Int.repr (ci_lim ci - pos)) (Int.repr (z_avail_in z')))) =
                 vi (pos + Zlength (ci_inb bs pos ci) - z_avail_in z')).
  { unfold vi. rewrite sub_repr, add_repr, Hinb. f_equal. f_equal. lia. }
  rewrite Epos. clear Epos.
  forward_if.
  { forward.
    unfold E_inv. Exists s' (sf_after ci z' msgv').
    unfold E, live, sf_at, api_fields, sf_after. cbn [sf_nin sf_ain sf_tin sf_nout sf_aout sf_tout sf_msgv sf_adler].
    rewrite Hgz. entailer!. }
  { assert (Hc1 : code <> Z_STREAM_END) by (unfold Z_STREAM_END; intro; subst; contradiction).
    pose proof (l3_next Bpre Brun bs b pos fin s f ci s' z' code msgv' H H0 H1 Hc1) as HJn.
    forward.
    unfold J_inv. Exists (pos + Zlength (ci_inb bs pos ci) - z_avail_in z') (ci_fin ci) s' (sf_after ci z' msgv').
    unfold J, loop_locals, live, sf_at, api_fields, sf_after. cbn [sf_nin sf_ain sf_tin sf_nout sf_aout sf_tout sf_msgv sf_adler].
    entailer!. }
Qed.
