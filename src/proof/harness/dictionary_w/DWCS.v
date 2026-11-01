(* The laws rt_dictionary and api_dict_id (data of any length, a dictionary of up to 2^32 - 1 bytes): their
   programs, their compspecs and the resources of their global variables.

   The two harnesses link the same units as the clip()-stream laws (adler32, crc32, deflate, trees, inflate,
   inffast, inftrees, zutil, libc) and define no struct of their own, so their composites are clip_streams'
   ([dw_comps]): the mains are proved at clip_streams' compspecs CS.CS, with its moves of the shared
   specifications' compspecs and the helper lemmas proved there.  Their global variables are clip_streams'
   list with the harness's own "1.3.2" literal ([dw_globals]: GlobalsOk.clip_vars_globals). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.harness.clip_streams.CS.
Require Import Zlib.proof.harness.clip_streams.Globals.
Require Zlib.proof.harness.clip_streams.GlobalsOk.
Require Zlib.contracts.rt_dictionary.
Require Zlib.contracts.api_dict_id.
Require Zlib.harness.rt_dictionary.code.
Require Zlib.harness.api_dict_id.code.

Definition p_drt := Zlib.contracts.rt_dictionary.whole_prog.
Definition p_dai := Zlib.contracts.api_dict_id.whole_prog.

Lemma dw_comps : prog_composites p_drt = comps /\ prog_composites p_dai = comps.
Proof. split; vm_compute; reflexivity. Qed.

Definition lit_drt : ident := Zlib.harness.rt_dictionary.code.___stringlit_rt_dictionary_1.
Definition lit_dai : ident := Zlib.harness.api_dict_id.code.___stringlit_api_dict_id_1.

Definition R_drt := R_of lit_drt.
Definition R_dai := R_of lit_dai.

Lemma vars_drt : QPprog_vars p_drt =
  GlobalsOk.clip_vars lit_drt Zlib.harness.rt_dictionary.code.v___stringlit_rt_dictionary_1.
Proof. vm_compute; reflexivity. Qed.
(* api_dict_id's literal comes before zutil's ten literals (positions 35-44 of clip_vars): clip_vars up to a
   permutation, which globvars2pred does not see *)
Definition vars_l_dai : list (ident * globvar type) :=
  GlobalsOk.clip_vars lit_dai Zlib.harness.api_dict_id.code.v___stringlit_api_dict_id_1.

Lemma vars_dai : QPprog_vars p_dai =
  firstn 35 vars_l_dai ++ sublist 45 46 vars_l_dai ++ sublist 35 45 vars_l_dai ++ skipn 46 vars_l_dai.
Proof. vm_compute; reflexivity. Qed.

Lemma vars_dai_perm gv : globvars2pred gv (QPprog_vars p_dai) = globvars2pred gv vars_l_dai.
Proof.
  rewrite vars_dai. unfold globvars2pred.
  change (fold_right sepcon emp ?l) with (fold_right_sepcon l).
  apply fold_right_sepcon_permutation.
  apply Permutation.Permutation_map.
  assert (E : vars_l_dai = firstn 35 vars_l_dai ++ sublist 35 45 vars_l_dai ++ sublist 45 46 vars_l_dai ++
                           skipn 46 vars_l_dai) by (vm_compute; reflexivity).
  rewrite E at 5.
  apply Permutation.Permutation_app_head. rewrite !app_assoc. apply Permutation.Permutation_app_tail.
  apply Permutation.Permutation_app_comm.
Qed.

Lemma dw_globals : globals_of p_drt lit_drt /\ globals_of p_dai lit_dai.
Proof.
  unfold globals_of.
  split; intros gv HP HU; [rewrite vars_drt | rewrite vars_dai_perm];
    apply GlobalsOk.clip_vars_globals; auto; reflexivity.
Qed.
