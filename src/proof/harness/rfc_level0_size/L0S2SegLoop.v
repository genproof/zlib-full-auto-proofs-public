(* Law rfc_level0_size, main: statement 20, the do-while of deflate() calls (rest = data_len - consumed,
   piece = 65535 * (1 + upto(65530)), flush, avail_in = piece, avail_out = clip(room - produced),
   code = deflate(&strm, flush), while code == Z_OK) (l0_LI -> l0_LB, by Level0CallsFit.ff_range and ff_call; the
   call itself is L0S2LoopCall.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.Rep Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.LawFacts.
Require Import Zlib.proof.deflate.GlobalsInit.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.deflate.Level0CallsFit.
Require Import Zlib.proof.harness.rfc_level0_size.L0S2MainStmt.
Require Import Zlib.proof.harness.rfc_level0_size.L0Kit2.
Require Import Zlib.proof.harness.rfc_level0_size.L0S2Kit.
Require Import Zlib.proof.harness.rfc_level0_size.L0S2LoopCall.
Require Import Zlib.harness.rfc_level0_size.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

Ltac simplify_remove_localdef_temp ::= l0_rlt.

(* [Q] without the binding of the temporary [t] *)
Ltac rm_temp t Q :=
  lazymatch Q with
  | temp t _ :: ?Q' => Q'
  | ?a :: ?Q' => let r := rm_temp t Q' in constr:(a :: r)
  | nil => constr:(@nil localdef)
  end.

(* forward over an [if] after which the temporaries [t] and [t'] are [v] and [v'] *)
Ltac fif2 t v t' v' :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    let Q1 := rm_temp t Q in let Q' := rm_temp t' Q1 in
    forward_if (PROPx P (LOCALx (temp t v :: temp t' v' :: Q') (SEPx R))) end.

(* next - start for next = start + k inside one object: CompCert's pointer difference (Ptrofs.divs of the
   offsets' difference by 1, no overflow check), as a long of the signed value of k, the (size_t) cast then
   gives k back *)
Lemma l0_sub_ptrL (p : val) k : isptr p -> 0 <= k <= Ptrofs.max_unsigned ->
  force_val (sem_binary_operation' Osub (tptr tuchar) (tptr tuchar) (offset_val k p) p) = Vlong (Int64.repr k).
Proof.
  intros Pp Hk. destruct p; try contradiction. simpl.
  unfold sem_sub_pp. simpl. rewrite if_true by auto. simpl.
  f_equal. rewrite Ptrofs.sub_add_l, Ptrofs.sub_idem, Ptrofs.add_zero_l.
  unfold Ptrofs.divs. rewrite (Ptrofs.signed_repr 1) by rep_lia. rewrite Z.quot_1_r, Ptrofs.repr_signed.
  rewrite Vptrofs_unfold_true by reflexivity. unfold Ptrofs.to_int64.
  rewrite Ptrofs.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma l0_sub_pp (p : val) k : isptr p -> 0 <= k <= Ptrofs.max_unsigned ->
  force_val (sem_sub_pp tuchar (offset_val k p) p) = Vlong (Int64.repr k).
Proof. intros. apply (l0_sub_ptrL p k); auto. Qed.

(* m - (size_t) (next - start) *)
Lemma l0_sub_arg (p : val) m k : isptr p -> 0 <= k <= m -> m <= Int64.max_unsigned ->
  force_val (sem_sub_default tulong tulong (Vlong (Int64.repr m)) (force_val (sem_sub_pp tuchar (offset_val k p) p)))
  = Vlong (Int64.repr (m - k)).
Proof.
  intros Pp Hk Hm. rewrite l0_sub_pp by (auto; rep_lia). simpl.
  f_equal. apply Int64.eqm_samerepr. apply Int64.eqm_sub; apply Int64.eqm_sym; apply Int64.eqm_unsigned_repr.
Qed.

Lemma l0_binop_sub (p : val) k : isptr p -> 0 <= k <= Ptrofs.max_unsigned ->
  eval_binop Osub (tptr tuchar) (tptr tuchar) (offset_val k p) p = Vlong (Int64.repr k).
Proof.
  intros Pp Hk. unfold eval_binop. rewrite <- (l0_sub_ptrL p k Pp Hk). unfold force_val2, force_val.
  destruct (sem_binary_operation' _ _ _ _ _); reflexivity.
Qed.

Lemma l0_rest_val (p : val) m k : isptr p -> 0 <= k <= m -> m <= Int64.max_unsigned ->
  force_val (sem_binary_operation' Osub tulong tulong (Vlong (Int64.repr m))
    (eval_cast tlong tulong (eval_binop Osub (tptr tuchar) (tptr tuchar) (offset_val k p) p))) =
  Vlong (Int64.repr (m - k)).
Proof.
  intros Pp Hk Hm. rewrite l0_binop_sub by (auto; rep_lia). simpl.
  f_equal. apply Int64.eqm_samerepr. apply Int64.eqm_sub; apply Int64.eqm_sym; apply Int64.eqm_unsigned_repr.
Qed.

Lemma l0_sameblock (p : val) k : isptr p -> is_true (sameblock (offset_val k p) p).
Proof. intros Pp. destruct p; try contradiction. unfold sameblock; simpl. destruct (peq b b); [reflexivity | congruence]. Qed.

(* one iteration: from the loop head to the state after deflate() *)
Lemma l0_loop_body {Espec : OracleKind} J gv vs n D dp cp wbits room :
  l0_fit_facts l0s_kmax l0s_slack J ->
  semax Delta_l0 (l0_LI gv vs J n D dp cp wbits room) l0_lbody
    (normal_ret_assert (l0_LC gv vs J n D dp cp wbits room)).
Proof.
  intros LF.
  unfold l0_lbody. abbreviate_semax.
  unfold l0_LI. Intros pos O s tin tout adler ai ao msg msgv.
  destruct (ff_range _ _ J LF _ _ _ _ _ _ _ _ _ ltac:(eassumption))
    as (Hpos & Hn & HO & Hb & RD & RO & Hgz & Htin & Htout & Had).
  unfold api_fields. Intros.
  subst n.
  forward.
  forward.
  { entailer!. apply prop_right. apply l0_sameblock; auto. }
  rewrite l0_rest_val by (auto; unfold l0_max_size in *; rep_lia).
  forward_call 65530.
  Intros u.
  forward.
  forward.
  replace (Int64.mul (Int64.repr (Int.signed (Int.repr 65535))) (Int64.add (Int64.repr (Int.signed (Int.repr 1)))
             (Int64.repr u))) with (Int64.repr (65535 * (1 + u)))
    by (rewrite !Int.signed_repr by rep_lia; rewrite add64_repr, mul64_repr; reflexivity).
  set (k := 1 + u).
  assert (Hk : 1 <= k <= 65531) by (unfold k; lia).
  clearbody k.
  fif2 _piece (Vlong (Int64.repr (l0_piece (Zlength D) pos k))) _flush (Vint (Int.repr (l0_flush (Zlength D) pos k))).
  { forward. forward. entailer!.
    unfold Int64.ltu in *. rewrite !Int64.unsigned_repr in * by (unfold l0_max_size in *; rep_lia).
    unfold l0_piece, l0_flush. destruct (zlt _ _); [discriminate|].
    destruct (Z.leb_spec (Zlength D - pos) (65535 * k)); [split; reflexivity | lia]. }
  { forward. entailer!.
    unfold Int64.ltu in *. rewrite !Int64.unsigned_repr in * by (unfold l0_max_size in *; rep_lia).
    unfold l0_piece, l0_flush. destruct (zlt _ _); [|discriminate].
    destruct (Z.leb_spec (Zlength D - pos) (65535 * k)); [lia | split; reflexivity]. }
  forward.
  pose proof (l0_piece_range (Zlength D) pos k ltac:(lia) ltac:(lia)) as Hpr.
  rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia.
  forward.
  forward_call (room - Zlength O).
  { apply prop_right. apply l0_sameblock; auto. }
  { entailer!. simpl. rewrite l0_sub_arg by (auto; unfold l0_max_u64 in *; rep_lia). reflexivity. }
  { unfold l0_max_u64 in *; rep_lia. }
  forward.
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre; [ | apply (l0_loop_call J gv vs D dp cp wbits room k pos O s tin tout adler msg msgv LF) ].
  unfold l0_X1.
  rewrite <- (l0_inb_len D pos k) by lia.
  assert (U1 : u32_ok (Zlength (l0_inb D pos k))) by (rewrite l0_inb_len by lia; unfold u32_ok; rep_lia).
  assert (U2 : u32_ok (l0_clip (room - Zlength O))) by (unfold l0_clip, u32_ok, l0_max_u64 in *; rep_lia).
  change (Z.min (room - Zlength O) Int.max_unsigned) with (l0_clip (room - Zlength O)).
  sep_apply (l0_api_fold vs (offset_val pos dp) (Zlength (l0_inb D pos k)) tin (offset_val (Zlength O) cp)
               (l0_clip (room - Zlength O)) tout msgv adler U1 H3 U2 H5 H6).
  entailer!.
Qed.

Lemma seg_loop_ok : seg_loop_stmt.
Proof.
  intros Espec J gv vs n D dp cp wbits room LF K.
  unfold l0_seg20, POST_B, POST_l0. abbreviate_semax.
  forward_loop (l0_LI gv vs J n D dp cp wbits room) continue: (l0_LC gv vs J n D dp cp wbits room)
    break: (l0_LB gv vs n D dp cp wbits room).
  { apply ENTAIL_refl. }
  { eapply semax_post; [ | | | | apply (l0_loop_body J gv vs n D dp cp wbits room LF) ];
      intros; simpl RA_normal; simpl RA_break; simpl RA_continue; simpl RA_return; normalize. }
  { (* while (code == Z_OK) *)
    unfold l0_LC. Intros code pos O s tin tout adler ai ao msg msgv.
    match goal with Hx : code = Z_OK -> _ |- _ => rename Hx into HOK end.
    match goal with Hx : code <> Z_OK -> _ |- _ => rename Hx into HEND end.
    destruct (Z.eq_dec code Z_OK) as [E | E].
    - specialize (HOK E). subst code.
      forward_if.
      { forward. unfold l0_LI. Exists pos O s tin tout adler ai ao msg msgv. entailer!. }
      { match goal with Hx : Int.repr _ <> Int.repr 0 |- _ => elim Hx; reflexivity end. }
    - destruct (HEND E) as (Ec & Et & HO & RO & HF). subst code tout.
      forward_if.
      { match goal with Hx : Int.repr _ = Int.repr 0 |- _ =>
          apply (f_equal Int.unsigned) in Hx; vm_compute in Hx; discriminate Hx end. }
      forward. unfold l0_LB. Exists O (Some s) (offset_val pos dp) ai tin ao adler msgv.
      entailer!. }
  (* after the loop *)
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  exact K.
Qed.
