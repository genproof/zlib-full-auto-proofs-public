(* Laws res_free_inflate and res_memory_inflate: the global variables of each program give main the resources
   [Ri lit] (ResISpecs.v): inflate()'s read-only tables (tables_rep: lenfix, distfix, order, inftrees' lbase,
   lext, dbase, dext), crc32's table, inflate.c's ZLIB_VERSION literal and the harness's own literal [lit]
   (the version argument of inflateInit2). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Assembly.
Require Import Zlib.proof.harness.res_inflate.ResICS Zlib.proof.harness.res_inflate.ResISpecs.
Require Zlib.contracts.res_free_inflate Zlib.contracts.res_memory_inflate.
Require Zlib.harness.res_free_inflate.code Zlib.harness.res_memory_inflate.code.
Require Zlib.proof.harness.inflate_codes.Globals.
Require Zlib.proof.crc32.Globals.
Require Zlib.inflate.code Zlib.inffast.code Zlib.inftrees.code Zlib.crc32.code Zlib.zutil.code.

(* The global variables of a program that links inflate.c, inffast.c, inftrees.c, crc32.c, zutil.c (and
   adler32.c, which has none) with a harness whose only global is its literal [lit]: the same list for both
   laws, up to the harness's literal. *)
Definition inflate_vars (lit : ident) (vlit : globvar type) : list (ident * globvar type) :=
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
   (Zlib.inffast.code.___stringlit_inffast_3, Zlib.inffast.code.v___stringlit_inffast_3);
   (Zlib.zutil.code.___stringlit_zutil_8, Zlib.zutil.code.v___stringlit_zutil_8);
   (Zlib.zutil.code.___stringlit_zutil_4, Zlib.zutil.code.v___stringlit_zutil_4);
   (Zlib.zutil.code.___stringlit_zutil_2, Zlib.zutil.code.v___stringlit_zutil_2);
   (Zlib.zutil.code.___stringlit_zutil_6, Zlib.zutil.code.v___stringlit_zutil_6);
   (Zlib.zutil.code.___stringlit_zutil_10, Zlib.zutil.code.v___stringlit_zutil_10);
   (Zlib.zutil.code.___stringlit_zutil_1, Zlib.zutil.code.v___stringlit_zutil_1);
   (Zlib.zutil.code.___stringlit_zutil_9, Zlib.zutil.code.v___stringlit_zutil_9);
   (Zlib.zutil.code.___stringlit_zutil_5, Zlib.zutil.code.v___stringlit_zutil_5);
   (Zlib.zutil.code.___stringlit_zutil_3, Zlib.zutil.code.v___stringlit_zutil_3);
   (Zlib.zutil.code.___stringlit_zutil_7, Zlib.zutil.code.v___stringlit_zutil_7);
   (lit, vlit);
   (Zlib.crc32.code._x2n_table, Zlib.crc32.code.v_x2n_table);
   (Zlib.inftrees.code._lext, Zlib.inftrees.code.v_lext);
   (Zlib.inftrees.code._lenfix, Zlib.inftrees.code.v_lenfix);
   (Zlib.inftrees.code._lbase, Zlib.inftrees.code.v_lbase);
   (Zlib.inftrees.code._distfix, Zlib.inftrees.code.v_distfix);
   (Zlib.inftrees.code._dext, Zlib.inftrees.code.v_dext);
   (Zlib.inftrees.code._dbase, Zlib.inftrees.code.v_dbase);
   (Zlib.zutil.code._z_errmsg, Zlib.zutil.code.v_z_errmsg)].

Lemma free_vars : QPprog_vars Zlib.contracts.res_free_inflate.whole_prog =
  inflate_vars Zlib.harness.res_free_inflate.code.___stringlit_res_free_inflate_1
    Zlib.harness.res_free_inflate.code.v___stringlit_res_free_inflate_1.
Proof. vm_compute; reflexivity. Qed.

Lemma memory_vars : QPprog_vars Zlib.contracts.res_memory_inflate.whole_prog =
  inflate_vars Zlib.harness.res_memory_inflate.code.___stringlit_res_memory_inflate_1
    Zlib.harness.res_memory_inflate.code.v___stringlit_res_memory_inflate_1.
Proof. vm_compute; reflexivity. Qed.

(* the harness's "1.3.2", from its initialised read-only array *)
Lemma hversion_g gv lit vlit :
  Zlib.proof.harness.inflate_codes.Globals.int_glob_ok I8 Signed vlit 6 [49; 46; 51; 46; 50; 0] = true ->
  (forall b o, gv lit = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (lit, vlit) |-- hversion_lit lit gv.
Proof.
  intros OK HP. unfold hversion_lit, hver_vals.
  exact (Zlib.proof.harness.inflate_codes.Globals.int_glob gv lit vlit I8 Signed 6 _ I OK HP).
Qed.

(* the globals of either program give [Ri lit] *)
Lemma inflate_vars_ok gv lit vlit :
  Zlib.proof.harness.inflate_codes.Globals.int_glob_ok I8 Signed vlit 6 [49; 46; 51; 46; 50; 0] = true ->
  (forall i b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
  globvars2pred gv (inflate_vars lit vlit) |-- Ri lit gv * TT.
Proof.
  intros OK HP. unfold globvars2pred, inflate_vars. simpl map; simpl fold_right.
  sep_apply (Zlib.proof.crc32.Globals.crc_table_of_globvar gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.lenfix_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.distfix_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.order_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.lbase_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.lext_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.dbase_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.dext_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.version_g gv (HP _)).
  sep_apply (hversion_g gv lit vlit OK (HP _)).
  unfold Ri, Zlib.proof.inflate.Rep.tables_rep, Zlib.proof.inftrees.spec.itables.
  cancel.
Qed.


Lemma globals_free gv : (forall i b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
  globvars2pred gv (QPprog_vars Zlib.contracts.res_free_inflate.whole_prog)
  |-- Ri Zlib.harness.res_free_inflate.code.___stringlit_res_free_inflate_1 gv * TT.
Proof.
  intros HP. rewrite free_vars. apply inflate_vars_ok; [vm_compute; reflexivity | exact HP].
Qed.

Lemma globals_memory gv : (forall i b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
  globvars2pred gv (QPprog_vars Zlib.contracts.res_memory_inflate.whole_prog)
  |-- Ri Zlib.harness.res_memory_inflate.code.___stringlit_res_memory_inflate_1 gv * TT.
Proof.
  intros HP. rewrite memory_vars. apply inflate_vars_ok; [vm_compute; reflexivity | exact HP].
Qed.
