(** * MainLib.semax_body_main_core with one more fact about the globals main gets

    genviron2globals (what main's precondition gives) is [Vptr b 0] or [Vundef] at every identifier; MainLib's
    lemma passes on only the offset-0 fact.  Programs whose global initialisers take the address of FUNCTIONS
    (deflate.c's configuration_table: deflate_stored / deflate_fast / deflate_slow) also need that these are a
    pointer or undefined: [GL] may assume it for the identifiers [fs]. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.

Section MainCoreCfg.
Context {CS: compspecs}.

Lemma main_core_sub_cfg (p: QP.program function) (fs: list ident) (R: globals -> mpred)
  (GL: forall gv, (forall i b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
         (forall f, In f fs -> gv f = Vundef \/ isptr (gv f)) ->
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
    { intros f _. unfold initialize.genviron2globals. destruct (Map.get ge f); [right; exact I | left; reflexivity]. }
    sep_apply (create_mem_mgr (initialize.genviron2globals ge)).
    unfold PROPx, PARAMSx, GLOBALSx, SEPx, LOCALx. simpl. unfold local, lift1, argsassert2assert; simpl.
    rewrite !prop_true_andp; auto. cancel. split; auto.
    unfold gvars_denote, globals_of_env, initialize.genviron2globals; simpl. reflexivity.
Qed.

Lemma semax_body_main_core_cfg (V: varspecs) (G: funspecs) (p: QP.program function) (fs: list ident)
  (i: ident) f R
  (GL: forall gv, (forall i b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
         (forall f, In f fs -> gv f = Vundef \/ isptr (gv f)) ->
         globvars2pred gv (QPprog_vars p) |-- R gv * TT):
  semax_body V G f (i, main_core_spec R) ->
  compute_list_norepet (map fst (fn_params f) ++ map fst (fn_temps f)) = true ->
  semax_body V G f (i, QPmain_spec_ext' p tt main_post_TT).
Proof.
  intros B LNR. eapply semax_body_funspec_sub; [exact B | apply (main_core_sub_cfg p fs); auto | ].
  apply compute_list_norepet_e; exact LNR.
Qed.

End MainCoreCfg.
