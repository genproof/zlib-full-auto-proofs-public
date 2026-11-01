(* Law api_inflate_deterministic: R_aid (AIDMainDefs.v) out of the program's global variables (as
   api_reset/ARGlobals.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.harness.api_inflate_deterministic.AIDMainDefs.
Require Zlib.harness.api_inflate_deterministic.code.
Require Zlib.inflate.code.
Require Zlib.inffast.code.
Require Zlib.inftrees.code.
Require Zlib.crc32.code.
Require Zlib.zutil.code.
Require Zlib.proof.crc32.Globals.
Require Zlib.proof.harness.inflate_codes.Globals.

Lemma aid_vars : QPprog_vars p = vars_head ++ [] ++
  [(Zlib.harness.api_inflate_deterministic.code.___stringlit_api_inflate_deterministic_1, Zlib.harness.api_inflate_deterministic.code.v___stringlit_api_inflate_deterministic_1)] ++
  vars_zutil ++ vars_tail.
Proof. vm_compute; reflexivity. Qed.

Lemma aid_globals : aid_globals_stmt.
Proof.
  intros gv HP. rewrite aid_vars. unfold globvars2pred, vars_head, vars_zutil, vars_tail. simpl map; simpl fold_right.
  sep_apply (Zlib.proof.crc32.Globals.crc_table_of_globvar gv (HP _)).
  sep_apply (ir_lenfix_g gv (HP _)).
  sep_apply (ir_distfix_g gv (HP _)).
  sep_apply (ir_order_g gv (HP _)).
  sep_apply (ir_lbase_g gv (HP _)).
  sep_apply (ir_lext_g gv (HP _)).
  sep_apply (ir_dbase_g gv (HP _)).
  sep_apply (ir_dext_g gv (HP _)).
  sep_apply (ir_version_g gv (HP _)).
  sep_apply (hversion_g gv Zlib.harness.api_inflate_deterministic.code.___stringlit_api_inflate_deterministic_1
               Zlib.harness.api_inflate_deterministic.code.v___stringlit_api_inflate_deterministic_1 ltac:(vm_compute; reflexivity) (HP _)).
  sep_apply (ir_str_glob gv Zlib.inflate.code.___stringlit_inflate_2 Zlib.inflate.code.v___stringlit_inflate_2 ltac:(vm_compute; reflexivity) (HP _)).
  sep_apply (ir_str_glob gv Zlib.inflate.code.___stringlit_inflate_3 Zlib.inflate.code.v___stringlit_inflate_3 ltac:(vm_compute; reflexivity) (HP _)).
  sep_apply (ir_str_glob gv Zlib.inflate.code.___stringlit_inflate_4 Zlib.inflate.code.v___stringlit_inflate_4 ltac:(vm_compute; reflexivity) (HP _)).
  sep_apply (ir_str_glob gv Zlib.inflate.code.___stringlit_inflate_5 Zlib.inflate.code.v___stringlit_inflate_5 ltac:(vm_compute; reflexivity) (HP _)).
  sep_apply (ir_str_glob gv Zlib.inflate.code.___stringlit_inflate_6 Zlib.inflate.code.v___stringlit_inflate_6 ltac:(vm_compute; reflexivity) (HP _)).
  sep_apply (ir_str_glob gv Zlib.inflate.code.___stringlit_inflate_7 Zlib.inflate.code.v___stringlit_inflate_7 ltac:(vm_compute; reflexivity) (HP _)).
  sep_apply (ir_str_glob gv Zlib.inflate.code.___stringlit_inflate_8 Zlib.inflate.code.v___stringlit_inflate_8 ltac:(vm_compute; reflexivity) (HP _)).
  sep_apply (ir_str_glob gv Zlib.inflate.code.___stringlit_inflate_9 Zlib.inflate.code.v___stringlit_inflate_9 ltac:(vm_compute; reflexivity) (HP _)).
  sep_apply (ir_str_glob gv Zlib.inflate.code.___stringlit_inflate_10 Zlib.inflate.code.v___stringlit_inflate_10 ltac:(vm_compute; reflexivity) (HP _)).
  sep_apply (ir_str_glob gv Zlib.inflate.code.___stringlit_inflate_11 Zlib.inflate.code.v___stringlit_inflate_11 ltac:(vm_compute; reflexivity) (HP _)).
  sep_apply (ir_str_glob gv Zlib.inflate.code.___stringlit_inflate_12 Zlib.inflate.code.v___stringlit_inflate_12 ltac:(vm_compute; reflexivity) (HP _)).
  sep_apply (ir_str_glob gv Zlib.inflate.code.___stringlit_inflate_13 Zlib.inflate.code.v___stringlit_inflate_13 ltac:(vm_compute; reflexivity) (HP _)).
  sep_apply (ir_str_glob gv Zlib.inflate.code.___stringlit_inflate_14 Zlib.inflate.code.v___stringlit_inflate_14 ltac:(vm_compute; reflexivity) (HP _)).
  sep_apply (ir_str_glob gv Zlib.inflate.code.___stringlit_inflate_15 Zlib.inflate.code.v___stringlit_inflate_15 ltac:(vm_compute; reflexivity) (HP _)).
  sep_apply (ir_str_glob gv Zlib.inflate.code.___stringlit_inflate_16 Zlib.inflate.code.v___stringlit_inflate_16 ltac:(vm_compute; reflexivity) (HP _)).
  sep_apply (ir_str_glob gv Zlib.inflate.code.___stringlit_inflate_17 Zlib.inflate.code.v___stringlit_inflate_17 ltac:(vm_compute; reflexivity) (HP _)).
  sep_apply (ir_str_glob gv Zlib.inflate.code.___stringlit_inflate_18 Zlib.inflate.code.v___stringlit_inflate_18 ltac:(vm_compute; reflexivity) (HP _)).
  sep_apply (ir_str_glob gv Zlib.inflate.code.___stringlit_inflate_19 Zlib.inflate.code.v___stringlit_inflate_19 ltac:(vm_compute; reflexivity) (HP _)).
  sep_apply (ir_str_glob gv Zlib.inffast.code.___stringlit_inffast_1 Zlib.inffast.code.v___stringlit_inffast_1 ltac:(vm_compute; reflexivity) (HP _)).
  sep_apply (ir_str_glob gv Zlib.inffast.code.___stringlit_inffast_2 Zlib.inffast.code.v___stringlit_inffast_2 ltac:(vm_compute; reflexivity) (HP _)).
  sep_apply (ir_str_glob gv Zlib.inffast.code.___stringlit_inffast_3 Zlib.inffast.code.v___stringlit_inffast_3 ltac:(vm_compute; reflexivity) (HP _)).
  unfold R_aid, R_of, tables_rep, Zlib.proof.inftrees.spec.itables, ir_msg_lits, ir_all_msgs. cbv [map fold_right msg_ident].
  cancel.
Qed.
