(* Law api_reset: R_ar (ARMainDefs.v) out of the program's global variables (as inflate_reset/IRGlobals.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Assembly.
Require Import Zlib.proof.harness.api_reset.ARMainDefs.
Require Zlib.harness.api_reset.code.
Require Zlib.inflate.code Zlib.inffast.code Zlib.inftrees.code Zlib.crc32.code Zlib.zutil.code.
Require Zlib.proof.crc32.Globals Zlib.proof.harness.inflate_codes.Globals.

Lemma ar_vars : QPprog_vars p = vars_head ++ [] ++
  [(Zlib.harness.api_reset.code.___stringlit_api_reset_1, Zlib.harness.api_reset.code.v___stringlit_api_reset_1)] ++
  vars_zutil ++ vars_tail.
Proof. vm_compute; reflexivity. Qed.

Lemma ar_globals : ar_globals_stmt.
Proof.
  intros gv HP. rewrite ar_vars. unfold globvars2pred, vars_head, vars_zutil, vars_tail. simpl map; simpl fold_right.
  sep_apply (Zlib.proof.crc32.Globals.crc_table_of_globvar gv (HP _)).
  sep_apply (ir_lenfix_g gv (HP _)).
  sep_apply (ir_distfix_g gv (HP _)).
  sep_apply (ir_order_g gv (HP _)).
  sep_apply (ir_lbase_g gv (HP _)).
  sep_apply (ir_lext_g gv (HP _)).
  sep_apply (ir_dbase_g gv (HP _)).
  sep_apply (ir_dext_g gv (HP _)).
  sep_apply (ir_version_g gv (HP _)).
  sep_apply (hversion_g gv Zlib.harness.api_reset.code.___stringlit_api_reset_1
               Zlib.harness.api_reset.code.v___stringlit_api_reset_1 ltac:(vm_compute; reflexivity) (HP _)).
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
  unfold R_ar, R_of, tables_rep, Zlib.proof.inftrees.spec.itables, ir_msg_lits, ir_all_msgs. cbv [map fold_right msg_ident].
  cancel.
Qed.
