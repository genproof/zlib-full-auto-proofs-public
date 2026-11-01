(* Law api_inflate_any: the resources of the program's global variables that its main needs (R_aia), out of
   globvars2pred, as inflate_pieces/Globals.v gives them for the three laws of the same loop: inflate's read-only
   tables, crc32's table, inflate.c's ZLIB_VERSION literal and the harness's own "1.3.2". *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Assembly.
Require Import Zlib.proof.harness.inflate_pieces.Globals.
Require Import Zlib.proof.harness.api_inflate_any.LawCS.
Require Zlib.harness.api_inflate_any.code.

Definition R_aia := @R_of Aia.CS Zlib.harness.api_inflate_any.code.___stringlit_api_inflate_any_1.

(* the program links the same units as the three laws: the same variables but the harness's literal *)
Lemma Aia_vars : QPprog_vars Aia.p =
  vars_head ++ [] ++
  [(Zlib.harness.api_inflate_any.code.___stringlit_api_inflate_any_1,
    Zlib.harness.api_inflate_any.code.v___stringlit_api_inflate_any_1)] ++ vars_zutil ++ vars_tail.
Proof. vm_compute; reflexivity. Qed.

(* R out of globvars2pred (MainLib.semax_body_main_core's hypothesis) *)
Lemma aia_globals gv : (forall i b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
  globvars2pred gv (QPprog_vars Aia.p) |-- R_aia gv * TT.
Proof. intros HP. rewrite Aia_vars. apply globals_of; [vm_compute; reflexivity | exact HP]. Qed.
