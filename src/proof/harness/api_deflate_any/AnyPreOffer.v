(* Law api_deflate_any: the loop body from the NULL test of the piece and the output space when neither is NULL
   (AnyKit.any_pre_stmt's last part): the copy [before] of the output space (NULL: return 0), then set_buffer of
   the piece and the output space; the stream is then [C_at] with [c0].  (AnyPreTail.v: the NULL case.) *)
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
Require Zlib.proof.deflate.DModel5.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.api_deterministic.DetMem2.
Require Zlib.proof.harness.api_deterministic.DetMem2b.
Require Zlib.proof.harness.api_deterministic.DetKit2.
Require Zlib.proof.harness.api_deterministic.DetPreOffer2.
Require Import Zlib.proof.harness.api_deflate_any.AnyCS.
Require Import Zlib.proof.harness.api_deflate_any.AnyMainStmt.
Require Import Zlib.proof.harness.api_deflate_any.AnyKit.
Require Import Zlib.proof.harness.api_deflate_any.AnyPreTail.
Require Import Zlib.harness.api_deflate_any.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

Ltac rlt_list i L := Zlib.proof.harness.api_deterministic.DetPreOffer2.rlt_list i L.
Local Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u' := rlt_list i L in change (remove_localdef_temp i L) with u' end.

(* the bytes of alloc_any_bytes are bytes of the model *)
Lemma any_is_bytes (l : list Z) : is_bytes l -> bytes l.
Proof. unfold is_bytes, bytes. intros H. eapply Forall_impl; [ | exact H ]. simpl; intros; rep_lia. Qed.

Lemma any_pre_ok {Espec : OracleKind} J n data datap v sp gv ap ls take room fl bs piece out :
  piece <> nullval -> out <> nullval ->
  (forall ci, @semax AnyCS.CS _ Delta_m (C_at J n data datap v sp gv ap ls ci (c0 ls)) lsuf9 (Rbody J n data datap v sp gv ap)) ->
  @semax AnyCS.CS _ Delta_m (M_at J n data datap v sp gv ap ls take room fl bs piece out) lsuf5 (Rbody J n data datap v sp gv ap).
Proof.
  intros E1 E2 HC.
  unfold M_at. Intros.
  unfold lsuf5, Rbody, loop1_ret_assert, POST_m, overridePost, frame_ret_assert. cbv beta iota.
  abbreviate_semax.
  freeze FR := (mem_mgr gv) (deflate_globals gv) (data_at Ews _ _ datap) (DetKit2.shead v _ _ _ _ _ _ _)
    (at_free ap) TT.
  (* floyd's own reassociation elaborates at the local instance DCS.CS, not at the goal's AnyCS.CS *)
  rewrite <- seq_assoc.
  destruct (eq_dec piece nullval); [ contradiction | ]. destruct (eq_dec out nullval); [ contradiction | ].
  Intros.
  forward_if (temp _t'19 (vi 0)); [ any_false | | ]. { forward. entailer!. any_nonnull. }
  match goal with |- semax _ ?P _ _ => apply semax_seq with (Q := P) end.
  { forward_if; [ any_false | ]. forward. entailer!. }
  thaw FR.
  (* the copy of the output space *)
  unfold abbreviate in MORE_COMMANDS; subst MORE_COMMANDS. abbreviate_semax.
  assert_PROP (isptr out) as Pout by entailer!.
  assert (Hcb : cbuf_ok false out Ews out 0 room room (bytes_rep bs) bs).
  { subst room. apply cbuf_ok_whole; auto. }
  forward_call (out, Ews, out, 0, room, bytes_rep bs, room, bs, gv).
  { rewrite DetMem2.det_bytes_cs. cancel. }
  Intros before. rewrite !DetMem2.det_bytes_cs, !DetMem2.det_token_cs.
  destruct (eq_dec before nullval) as [E3|E3].
  { subst before. forward_if; [ | any_false ]. any_ret. }
  Intros.
  match goal with |- semax _ ?P _ _ => apply semax_seq with (Q := P) end.
  { forward_if; [ any_false | ]. forward. entailer!. }
  (* set_buffer leads to C_at; the rest of the body is the hypothesis *)
  unfold abbreviate in MORE_COMMANDS; subst MORE_COMMANDS.
  eapply semax_seq'; [| apply (HC (mkCI take room bs fl piece out before)) ].
  abbreviate_semax.
  sep_apply (DetPreOffer2.det_offer_open v (ls_s ls) sp (ls_read ls) (ls_tout ls) (ls_msgv ls) (ls_adler ls) gv).
  Intros nin ain nout aout.
  remember (gv DC._zcalloc) as zca. remember (gv DC._zcfree) as zcf.
  forward_call (v, Ews, piece, take, out, room, nin, vi ain, vl (ls_read ls), nout, vi aout,
                vl (ls_tout ls), ls_msgv ls, sp, zca, zcf, nullval, DetKit2.det_dt (ls_s ls),
                vl (ls_adler ls), Vundef).
  assert (Hut : u32_ok take) by (unfold u32_ok; rep_lia).
  assert (Hur : u32_ok room) by (unfold u32_ok; rep_lia).
  sep_apply (DetPreOffer2.det_offer_close v (ls_s ls) sp piece take (ls_read ls) out room (ls_tout ls)
               (ls_msgv ls) (ls_adler ls) gv zca zcf Heqzca Heqzcf Hut ltac:(assumption) Hur ltac:(assumption)
               ltac:(assumption)).
  assert_PROP (isptr piece /\ isptr before) as Hptr by entailer!.
  destruct Hptr as [Ppi Pbe].
  unfold C_at, C_sep, B_loc, c0, ci_inb, DetKit2.out_at, BoundKit.obj, ovals.
  cbn [ci_take ci_room ci_bs ci_flush ci_piece ci_out ci_before cs_s cs_nin cs_out cs_tout cs_adler cs_msg cs_msgv].
  rewrite !isptr_offset_val_zero by auto. rewrite Zlength_nil, !Z.sub_0_r, !Z.add_0_r, app_nil_l.
  rewrite (sublist_same 0 (Zlength bs) bs) by lia.
  assert (Hr0 : 0 <= ls_read ls) by (destruct H as [_ [_ [Hr _]]]; lia).
  rewrite Zlength_sublist by (destruct H as [[_ [_ [Hn _]]] _]; lia). rewrite Z.add_simpl_l, H5.
  change (bytes_rep (sublist (ls_read ls) (ls_read ls + take) data))
    with (map vi (sublist (ls_read ls) (ls_read ls + take) data)).
  change (bytes_rep bs) with (map vi bs).
  entailer!.
  split.
  - unfold ci_ok; cbn [ci_take ci_room ci_bs ci_flush ci_piece ci_out ci_before].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [exact H3|]. split; [lia|]. split; [reflexivity|].
    split; [apply any_is_bytes; auto|]. auto.
  - destruct H as [_ [HJ [_ [_ [_ [Ht Hm]]]]]].
    unfold cs_ok; cbn [ci_take ci_room cs_s cs_nin cs_out cs_tout cs_adler cs_msg cs_msgv].
    rewrite Z.add_0_r. split; [exact HJ|]. split; [lia|]. split; [rewrite Zlength_nil; lia|].
    split; [constructor|]. split; [auto|]. split; auto.
Qed.
