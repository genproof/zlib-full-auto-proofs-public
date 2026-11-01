(* Law rfc_trailing_bytes, main: the last part of the inflate loop's body (TBLoopKit.tbl_call_stmt),
   code = inflate(&decompressor, (int) nondet_u32()) on the next piece of src and the rest of the output object,
   `if (code == Z_MEM_ERROR) return 0` and gp_assert(code == Z_OK || code == Z_BUF_ERROR || code == Z_STREAM_END)
   (the codes of TBFacts.tl_call); the loop's test is then reached with tbl_cont (TBFacts.tl_call). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Zlib.proof.inflate.Callees.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.harness.clip_streams.CS Zlib.proof.harness.clip_streams.Globals.
Require Import Zlib.proof.harness.clip_streams.DFacts Zlib.proof.harness.clip_streams.IFacts.
Require Import Zlib.proof.harness.clip_streams.TBFacts Zlib.proof.harness.clip_streams.MainDefs.
Require Import Zlib.proof.harness.clip_streams.TBKit Zlib.proof.harness.clip_streams.TBLoopKit.
Require Import Zlib.harness.rfc_trailing_bytes.code.
#[local] Existing Instance CS.CS.
Local Open Scope logic.

Lemma tbl_call : tbl_call_stmt.
Proof.
  intros Espec P wbits n D O src dp op ip vc vd gv pos out z L PF FA.
  destruct FA as (DF & HD & Hn & HO & Hsl & Hsb & Hw & BD & BD' & BO & Pdp & Pop & Pip).
  unfold tbl_st. Intros.
  rename H into HP0. rename H0 into Hsw. rename H1 into H3. rename H2 into H5.
  assert_PROP (isptr vd) as Pvd by entailer!.
  destruct (tl_ok P PF _ _ _ _ _ _ _ _ HP0) as (Hhd & Hpos & rest & Erest).
  assert (Hout: Zlength out <= n) by (rewrite <- HD, Erest, Zlength_app; pose proof (Zlength_nonneg rest); lia).
  unfold max_size in Hn.
  unfold tbl_x34, Delta_tb, POST_B, POST_tb. abbreviate_semax.
  forward_call tt. Intros u.
  assert (Eu: Int.repr u = Int.repr (Int.signed (Int.repr u))) by (rewrite Int.repr_signed; auto).
  rewrite Eu. clear Eu. set (flush := Int.signed (Int.repr u)).
  assert (Hfl: Int.min_signed <= flush <= Int.max_signed) by apply Int.signed_range. clearbody flush.
  set (ai := Z.min (Zlength src - pos) Int.max_unsigned).
  set (ao := Z.min (n - Zlength out) Int.max_unsigned).
  assert (Hai: 0 <= ai <= Zlength src - pos /\ ai <= Int.max_unsigned) by (unfold ai; rep_lia).
  assert (Hao: 0 <= ao <= n - Zlength out /\ ao <= Int.max_unsigned) by (unfold ao; rep_lia).
  clearbody ai ao.
  set (inp := sublist pos (pos + ai) src).
  assert (Hinp: Zlength inp = ai) by (unfold inp; rewrite Zlength_sublist; lia).
  set (ib := tbl_ib ip (Zlength src) pos src). set (o := tbl_ob op n out).
  replace (offset_val pos ip) with (in_ptr ib 0) by (unfold ib, tbl_ib; simpl; rewrite Z.add_0_r; reflexivity).
  replace (offset_val (Zlength out) op) with (out_ptr o 0)
    by (unfold o, tbl_ob; simpl; rewrite Z.add_0_r; reflexivity).
  sep_apply (tbl_offer_fold gv vd z L ib o ai ao); auto; try lia.
  replace (bytes_rep src) with (tbl_oc (Zlength src) src)
    by (unfold tbl_oc; rewrite Z.sub_diag, Zrepeat_0, app_nil_r; reflexivity).
  change (bytes_rep out ++ Zrepeat Vundef (n - Zlength out)) with (tbl_oc n out).
  sep_apply (tbl_bufs_pre vd L ip (Zlength src) pos src op n out); auto; try lia. fold ib o.
  unfold R_tb, R_of, Zlib.proof.deflate.DSpec.deflate_globals. Intros.
  assert (INOK: in_ok ib inp) by (apply tbl_in_ok; auto; lia).
  assert (OUTOK: out_ok o ao) by (apply tbl_out_ok; auto; rep_lia).
  forward_call (gv, Tsh, vd, offer_z z (in_ptr ib 0) ai (out_ptr o 0) ao, Vundef, Some L, ib, inp, Some o,
                flush, Ers, Ers, true, true).
  { split; [exact INOK | simpl; lia]. }
  Intros vret. destruct vret as [[[r z'] st'] ow]. simpl fst in *; simpl snd in *.
  match goal with Hr: inflate_rel _ _ _ _ _ _ _ _ _ _ _ |- _ => rename Hr into REL end.
  pose proof (tbl_ret_range _ _ _ _ _ _ _ _ _ _ _ REL) as Hrr.
  assert_PROP (zf_ok z') as Zo'.
  { sep_apply (tbl_zf_ok gv Tsh vd z' Vundef st'); auto. entailer!. }
  forward.
  forward_if.
  { (* Z_MEM_ERROR ends the run *)
    forward. Exists (Int.repr 0). sep_apply (tbl_a_frame_opt gv Tsh vd z' Vundef st'); auto. entailer!. }
  assert (Hr: r <> Z_MEM_ERROR) by (intro E; subst r; contradiction).
  assert (CP: call_pre src pos z L vd flush ib inp o ao).
  { unfold call_pre.
    refine (conj H5 (conj H3 (conj _ (conj Hfl (conj _ (conj INOK (conj OUTOK (conj _ (conj _ _))))))))).
    - intro E; subst vd; contradiction.
    - unfold ib, tbl_ib; discriminate.
    - unfold umax; rep_lia.
    - unfold umax; rep_lia.
    - rewrite Hinp. reflexivity. }
  assert (REL': inflate_rel flush vd (offer_z z (in_ptr ib 0) (Zlength inp) (out_ptr o 0) ao) (Some L) ib inp
                  (Some o) r z' st' ow) by (rewrite Hinp; exact REL).
  destruct (tl_call P PF wbits D O src pos out z L vd flush ib inp o ao r z' st' ow HP0 CP
              ltac:(lia) REL' Hr Zo')
    as (L' & (Est & Hai' & Hao' & Hni' & Hno' & How) & Hcodes & Hend & HP').
  subst st'.
  rewrite tbl_istreamA_opt_ptr by auto.
  rewrite (tbl_is_live_ptr vd (Some L')) by auto.
  unfold ib, o. sep_apply (tbl_bufs_post vd L ip (Zlength src) pos src op n out ow); auto; try lia. Intros.
  fold ib o.
  assert (Eni: zf_ni z' = offset_val (pos + (Zlength inp - zf_ai z')) ip)
    by (rewrite Hni'; unfold ib, tbl_ib; reflexivity).
  assert (Eno: zf_no z' = offset_val (Zlength (out ++ ow)) op)
    by (rewrite Hno'; unfold o, tbl_ob; simpl; f_equal; rewrite Zlength_app; lia).
  (* gp_assert(code == Z_OK || code == Z_BUF_ERROR || code == Z_STREAM_END): the codes of TBFacts.tl_call *)
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'23 (Vint (if r =? Z_STREAM_END then Int.zero else Int.one)) :: Q)
                  (SEPx R))) end.
  { forward. entailer!. }
  { forward. entailer!.
    destruct Hcodes as [E | [E | E]]; subst r; unfold Z_OK, Z_BUF_ERROR, Z_STREAM_END in *; try lia;
      reflexivity. }
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'24 (Vint Int.one) :: Q) (SEPx R))) end.
  { forward. entailer!. }
  { forward. entailer!.
    destruct Hcodes as [E | [E | E]]; subst r; unfold Z_OK, Z_BUF_ERROR, Z_STREAM_END in *; cbn in *;
      try discriminate; reflexivity. }
  forward_call (Int.one).
  unfold tbl_cont. Exists r (pos + (Zlength inp - zf_ai z')) (out ++ ow) z' L'.
  unfold tbl_oc, R_tb, R_of, Zlib.proof.deflate.DSpec.deflate_globals.
  rewrite Z.sub_diag, Zrepeat_0, app_nil_r. entailer!.
Qed.
