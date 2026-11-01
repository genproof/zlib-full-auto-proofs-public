(* The laws rj_any_input, api_counters and api_untouched_output: the resources of each program's global variables
   that its main needs (R), out of globvars2pred: inflate's read-only tables (lenfix, distfix, order,
   inftrees' lbase/lext/dbase/dext), crc32's table, inflate.c's ZLIB_VERSION literal (inflateInit2_ compares
   the caller's version with it) and the harness's own ZLIB_VERSION literal "1.3.2" (passed to inflateInit2_). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Assembly.
Require Import Zlib.proof.inflate_api.Spec5.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.inflate_pieces.LawCS.
Require Zlib.harness.rj_any_input.code Zlib.harness.api_counters.code Zlib.harness.api_untouched_output.code.
Require Zlib.inflate.code Zlib.inffast.code Zlib.inftrees.code Zlib.crc32.code Zlib.zutil.code.
Require Zlib.proof.crc32.Globals Zlib.proof.harness.inflate_codes.Globals.

(* the harness's "1.3.2" at the global i *)
Definition hversion_at {cs: compspecs} (i: ident) (gv: globals) : mpred :=
  data_at Ers (tarray tschar 6) (map (fun c => Vint (Int.repr c)) [49; 46; 51; 46; 50; 0]) (gv i).

Definition R_of {cs: compspecs} (i: ident) (gv: globals) : mpred :=
  (tables_rep Ers gv * crc_table_at Ers gv * version_lit gv * hversion_at i gv)%logic.

Definition R_any := @R_of Any.CS Zlib.harness.rj_any_input.code.___stringlit_rj_any_input_1.
Definition R_cnt := @R_of Cnt.CS Zlib.harness.api_counters.code.___stringlit_api_counters_1.
Definition R_unt := @R_of Unt.CS Zlib.harness.api_untouched_output.code.___stringlit_api_untouched_output_1.

(* ---------------------------------------------------------------------------------------------- *)
(* The three programs link the same zlib units, so their
   global variables are the same list except for the harness's "1.3.2" literal, which sits before or after
   zutil's literals.  The list in three parts: *)
Definition vars_head : list (ident * globvar type) :=
  [(Zlib.inflate.code._order, Zlib.inflate.code.v_order);
   (Zlib.crc32.code._crc_table, Zlib.crc32.code.v_crc_table);
   (Zlib.inftrees.code._inflate_copyright, Zlib.inftrees.code.v_inflate_copyright);
   (Zlib.inflate.code.___stringlit_inflate_8, Zlib.inflate.code.v___stringlit_inflate_8);
   (Zlib.inflate.code.___stringlit_inflate_4, Zlib.inflate.code.v___stringlit_inflate_4);
   (Zlib.inflate.code.___stringlit_inflate_2, Zlib.inflate.code.v___stringlit_inflate_2);
   (Zlib.inflate.code.___stringlit_inflate_6, Zlib.inflate.code.v___stringlit_inflate_6);
   (Zlib.inflate.code.___stringlit_inflate_10, Zlib.inflate.code.v___stringlit_inflate_10);
   (Zlib.inflate.code.___stringlit_inflate_18, Zlib.inflate.code.v___stringlit_inflate_18);
   (Zlib.inflate.code.___stringlit_inflate_14, Zlib.inflate.code.v___stringlit_inflate_14);
   (Zlib.inflate.code.___stringlit_inflate_12, Zlib.inflate.code.v___stringlit_inflate_12);
   (Zlib.inflate.code.___stringlit_inflate_16, Zlib.inflate.code.v___stringlit_inflate_16);
   (Zlib.inflate.code.___stringlit_inflate_1, Zlib.inflate.code.v___stringlit_inflate_1);
   (Zlib.inflate.code.___stringlit_inflate_11, Zlib.inflate.code.v___stringlit_inflate_11);
   (Zlib.inflate.code.___stringlit_inflate_19, Zlib.inflate.code.v___stringlit_inflate_19);
   (Zlib.inflate.code.___stringlit_inflate_15, Zlib.inflate.code.v___stringlit_inflate_15);
   (Zlib.inflate.code.___stringlit_inflate_13, Zlib.inflate.code.v___stringlit_inflate_13);
   (Zlib.inflate.code.___stringlit_inflate_17, Zlib.inflate.code.v___stringlit_inflate_17);
   (Zlib.inflate.code.___stringlit_inflate_9, Zlib.inflate.code.v___stringlit_inflate_9);
   (Zlib.inflate.code.___stringlit_inflate_5, Zlib.inflate.code.v___stringlit_inflate_5);
   (Zlib.inflate.code.___stringlit_inflate_3, Zlib.inflate.code.v___stringlit_inflate_3);
   (Zlib.inflate.code.___stringlit_inflate_7, Zlib.inflate.code.v___stringlit_inflate_7);
   (Zlib.inffast.code.___stringlit_inffast_2, Zlib.inffast.code.v___stringlit_inffast_2);
   (Zlib.inffast.code.___stringlit_inffast_1, Zlib.inffast.code.v___stringlit_inffast_1);
   (Zlib.inffast.code.___stringlit_inffast_3, Zlib.inffast.code.v___stringlit_inffast_3)].

Definition vars_zutil : list (ident * globvar type) :=
  [(Zlib.zutil.code.___stringlit_zutil_8, Zlib.zutil.code.v___stringlit_zutil_8);
   (Zlib.zutil.code.___stringlit_zutil_4, Zlib.zutil.code.v___stringlit_zutil_4);
   (Zlib.zutil.code.___stringlit_zutil_2, Zlib.zutil.code.v___stringlit_zutil_2);
   (Zlib.zutil.code.___stringlit_zutil_6, Zlib.zutil.code.v___stringlit_zutil_6);
   (Zlib.zutil.code.___stringlit_zutil_10, Zlib.zutil.code.v___stringlit_zutil_10);
   (Zlib.zutil.code.___stringlit_zutil_1, Zlib.zutil.code.v___stringlit_zutil_1);
   (Zlib.zutil.code.___stringlit_zutil_9, Zlib.zutil.code.v___stringlit_zutil_9);
   (Zlib.zutil.code.___stringlit_zutil_5, Zlib.zutil.code.v___stringlit_zutil_5);
   (Zlib.zutil.code.___stringlit_zutil_3, Zlib.zutil.code.v___stringlit_zutil_3);
   (Zlib.zutil.code.___stringlit_zutil_7, Zlib.zutil.code.v___stringlit_zutil_7)].

Definition vars_tail : list (ident * globvar type) :=
  [(Zlib.crc32.code._x2n_table, Zlib.crc32.code.v_x2n_table);
   (Zlib.inftrees.code._lext, Zlib.inftrees.code.v_lext);
   (Zlib.inftrees.code._lenfix, Zlib.inftrees.code.v_lenfix);
   (Zlib.inftrees.code._lbase, Zlib.inftrees.code.v_lbase);
   (Zlib.inftrees.code._distfix, Zlib.inftrees.code.v_distfix);
   (Zlib.inftrees.code._dext, Zlib.inftrees.code.v_dext);
   (Zlib.inftrees.code._dbase, Zlib.inftrees.code.v_dbase);
   (Zlib.zutil.code._z_errmsg, Zlib.zutil.code.v_z_errmsg)].

Lemma Any_vars : QPprog_vars Any.p =
  vars_head ++ vars_zutil ++
  [(Zlib.harness.rj_any_input.code.___stringlit_rj_any_input_1,
    Zlib.harness.rj_any_input.code.v___stringlit_rj_any_input_1)] ++ [] ++ vars_tail.
Proof. vm_compute; reflexivity. Qed.

Lemma Cnt_vars : QPprog_vars Cnt.p =
  vars_head ++ [] ++
  [(Zlib.harness.api_counters.code.___stringlit_api_counters_1,
    Zlib.harness.api_counters.code.v___stringlit_api_counters_1)] ++ vars_zutil ++ vars_tail.
Proof. vm_compute; reflexivity. Qed.

Lemma Unt_vars : QPprog_vars Unt.p =
  vars_head ++ [] ++
  [(Zlib.harness.api_untouched_output.code.___stringlit_api_untouched_output_1,
    Zlib.harness.api_untouched_output.code.v___stringlit_api_untouched_output_1)] ++ vars_zutil ++ vars_tail.
Proof. vm_compute; reflexivity. Qed.

(* a global initialised to "1.3.2" is hversion_at *)
Lemma hversion_g {cs: compspecs} gv h vh :
  Zlib.proof.harness.inflate_codes.Globals.int_glob_ok I8 Signed vh 6 [49; 46; 51; 46; 50; 0] = true ->
  (forall b o, gv h = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (h, vh) |-- hversion_at h gv.
Proof.
  intros OK HP. unfold hversion_at.
  exact (Zlib.proof.harness.inflate_codes.Globals.int_glob gv h vh I8 Signed 6 _ I OK HP).
Qed.

(* R out of the variable list, wherever the harness literal sits among the unused globals *)
Lemma globals_of {cs: compspecs} gv h vh pre post :
  Zlib.proof.harness.inflate_codes.Globals.int_glob_ok I8 Signed vh 6 [49; 46; 51; 46; 50; 0] = true ->
  (forall i b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
  globvars2pred gv (vars_head ++ pre ++ [(h, vh)] ++ post ++ vars_tail) |-- R_of h gv * TT.
Proof.
  intros OK HP. unfold globvars2pred. rewrite !map_app, !fold_right_sepcon_app.
  generalize (fold_right_sepcon (map (globvar2pred gv) pre)) (fold_right_sepcon (map (globvar2pred gv) post)).
  intros P Q. unfold vars_head, vars_tail. simpl map; simpl fold_right_sepcon. rewrite !sepcon_emp.
  sep_apply (Zlib.proof.crc32.Globals.crc_table_of_globvar gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.lenfix_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.distfix_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.order_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.lbase_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.lext_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.dbase_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.dext_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.version_g gv (HP _)).
  sep_apply (hversion_g gv h vh OK (HP _)).
  unfold R_of, tables_rep, Zlib.proof.inftrees.spec.itables.
  cancel.
Qed.

(* R out of globvars2pred, for each of the three programs (MainLib.semax_body_main_core's hypothesis) *)
Lemma pieces_globals :
  (forall gv, (forall i b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
     globvars2pred gv (QPprog_vars Any.p) |-- R_any gv * TT) /\
  (forall gv, (forall i b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
     globvars2pred gv (QPprog_vars Cnt.p) |-- R_cnt gv * TT) /\
  (forall gv, (forall i b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
     globvars2pred gv (QPprog_vars Unt.p) |-- R_unt gv * TT).
Proof.
  split; [|split]; intros gv HP.
  - rewrite Any_vars. apply globals_of; [vm_compute; reflexivity | exact HP].
  - rewrite Cnt_vars. apply globals_of; [vm_compute; reflexivity | exact HP].
  - rewrite Unt_vars. apply globals_of; [vm_compute; reflexivity | exact HP].
Qed.
