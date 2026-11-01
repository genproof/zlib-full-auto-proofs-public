(* Shared pieces of the harness mains (checksum laws; usable by any law): main proved against a core
   specification (memory manager and given global resources R, instead of globvars2pred), and the
   funspec_sub that turns it into harness_safe's main specification; pick of an unsigned long. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Assembly.

Section MainCore.
Context {CS: compspecs}.

(* main with the memory manager and the resources R gv of the program's globals. *)
Definition main_core_spec (R: globals -> mpred) : funspec :=
  WITH gv: globals
  PRE [] PROP () PARAMS () GLOBALS (gv) SEP (mem_mgr gv; R gv)
  POST [ tint ] EX r: int, PROP () RETURN (Vint r) SEP (TT).

(* R out of the program's global variables, at genviron2globals (offset 0 for every global). *)
Lemma main_core_sub (p: QP.program function) (R: globals -> mpred)
  (GL: forall gv, (forall i b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
         globvars2pred gv (QPprog_vars p) |-- R gv * TT):
  funspec_sub (main_core_spec R) (QPmain_spec_ext' p tt main_post_TT).
Proof.
  apply NDsubsume_subsume.
  - intros ts; split; reflexivity.
  - split; [split; reflexivity | ]. intros gv [ge args].
    unfold main_pre. simpl. Exists (initialize.genviron2globals ge) (TT: mpred). simpl. normalize.
    apply andp_right; [ apply prop_right; intros; unfold main_post_TT; apply TT_right | ].
    match goal with |- fold_right sepcon emp (map (globvar2pred ?g) (QPprog_vars p)) * _ |-- _ =>
      change (fold_right sepcon emp (map (globvar2pred g) (QPprog_vars p)))
        with (globvars2pred g (QPprog_vars p)) end.
    sep_apply GL.
    { intros i b o E. unfold initialize.genviron2globals in E. destruct (Map.get ge i); inv E; auto. }
    sep_apply (create_mem_mgr (initialize.genviron2globals ge)).
    unfold PROPx, PARAMSx, GLOBALSx, SEPx, LOCALx. simpl. unfold local, lift1, argsassert2assert; simpl.
    rewrite !prop_true_andp; auto. cancel. split; auto.
    unfold gvars_denote, globals_of_env, initialize.genviron2globals; simpl. reflexivity.
Qed.

(* A body of main proved against main_core_spec R is a body of harness_safe's main. *)
Lemma semax_body_main_core (V: varspecs) (G: funspecs) (p: QP.program function) (i: ident) f R
  (GL: forall gv, (forall i b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
         globvars2pred gv (QPprog_vars p) |-- R gv * TT):
  semax_body V G f (i, main_core_spec R) ->
  compute_list_norepet (map fst (fn_params f) ++ map fst (fn_temps f)) = true ->
  semax_body V G f (i, QPmain_spec_ext' p tt main_post_TT).
Proof.
  intros B LNR. eapply semax_body_funspec_sub; [exact B | apply main_core_sub; auto | ].
  apply compute_list_norepet_e; exact LNR.
Qed.

(* pick(x) on an unsigned long: its 8 bytes for nondet_bytes. *)
Lemma data_at_ulong_bytes sh p: data_at_ sh tulong p |-- data_at_ sh (tarray tuchar 8) p.
Proof.
  rewrite data_at__memory_block. normalize.
  apply memory_block_data_at__tarray_tuchar. rep_lia.
Qed.

Lemma data_at_long_bytes sh p: data_at_ sh tlong p |-- data_at_ sh (tarray tuchar 8) p.
Proof.
  rewrite data_at__memory_block. normalize.
  apply memory_block_data_at__tarray_tuchar. rep_lia.
Qed.

End MainCore.

(* The argument of gp_assume/gp_assert when it is a comparison: the int of a Z boolean. *)
Ltac arg_cmp :=
  simpl;
  try change (Int.shl (Int.repr 1) (Int.repr 20)) with (Int.repr (2 ^ 20));
  try change (Int.unsigned (Int.repr (-1))) with 4294967295;
  unfold Int.ltu, Int64.ltu, Int.eq, Int64.eq;
  try change (Int.unsigned (Int.repr (-1))) with 4294967295;
  rewrite ?Int.unsigned_repr, ?Int64.unsigned_repr by rep_lia;
  repeat match goal with |- context [zlt ?a ?b] => destruct (zlt a b) end;
  repeat match goal with |- context [zeq ?a ?b] => destruct (zeq a b) end;
  repeat match goal with |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b) end;
  repeat match goal with |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec a b) end;
  repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b) end;
  try lia; reflexivity.

(* After gp_assume(Int.repr (if c then 1 else 0)): c holds. *)
Ltac assumed := match goal with H: Int.repr (if ?c then 1 else 0) <> Int.zero |- _ =>
  let E := fresh "E" in destruct c eqn:E; [clear H | contradiction H; reflexivity] end.

Local Transparent denote_tc_test_eq.

(* A malloc'd byte object (any size, also 0) can be compared with NULL. *)
Lemma malloc_test_eq {cs: compspecs} P n q:
  0 <= n ->
  P |-- (malloc_token Ews (tarray tuchar n) q * data_at_ Ews (tarray tuchar n) q * TT)%logic ->
  P |-- denote_tc_test_eq q (Vlong (Int64.repr 0)).
Proof.
  intros Hn H. eapply derives_trans; [exact H | ].
  assert_PROP (isptr q) as Hq by (saturate_local; entailer!).
  destruct q; try contradiction.
  unfold denote_tc_test_eq. cbv [Archi.ptr64].
  apply andp_right; [apply prop_right; reflexivity | ].
  apply sepcon_weak_valid_pointer1.
  destruct (zlt 0 n).
  - apply sepcon_weak_valid_pointer2.
    rewrite data_at__memory_block. normalize.
    simpl sizeof. rewrite Z.max_r by lia. rewrite Z.mul_1_l.
    eapply derives_trans; [apply (memory_block_weak_valid_pointer Ews n (Vptr b i) 0); try lia; auto | ].
    simpl. rewrite ptrofs_add_repr_0_r. auto.
  - assert (n = 0) by lia. subst n.
    apply sepcon_weak_valid_pointer1.
    eapply derives_trans; [apply malloc_token_valid_pointer; simpl; lia | ].
    apply valid_pointer_weak.
Qed.

(* forward_if with the join point: the current assertion plus temp t = v. *)
Ltac ifpost t v := match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_if (PROPx [] (LOCALx (temp t (Vint v) :: Q) (SEPx R))) end.
Ltac ifsame := match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_if (PROPx [] (LOCALx Q (SEPx R))) end.

(* return 0 from main (main_core_spec's postcondition), the local variables given back. *)
Ltac ret0 := forward; Exists (Int.repr 0); entailer!;
  repeat (sep_apply data_at_data_at_); cancel.

(* After forward_call: close the frame entailments it leaves. *)
Ltac frame_close := try (match goal with |- _ |-- _ => cancel end).

(* gp_assert(cond) with cond true: the argument goal, when forward_call leaves one. *)
Ltac assert_true := forward_call (Int.repr 1); [ .. ].
