(* Law rt_stream_trailing: main's resources [TMainStmt.Rm_t] out of the program's global variables
   ([TMainStmt.trl_globals_stmt]), as rt_stream's Globals.v: the deflate side's tables (deflate/GlobalsKit.v),
   crc32.c's table, inflate's and inftrees' tables and inflate.c's version literal (inflate_codes/Globals.v), and
   the harness's own "1.3.2" literal. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.harness.rt_stream.LawCS.
Require Import Zlib.proof.harness.rt_stream_trailing.TMainStmt.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.GlobalsKit.
Require Zlib.proof.deflate.GlobalsFixed.
Require Zlib.harness.rt_stream_trailing.code.
Require Zlib.deflate.code.
Require Zlib.trees.code.
Require Zlib.crc32.code.
Require Zlib.zutil.code.
Require Zlib.inflate.code.
Require Zlib.inffast.code.
Require Zlib.inftrees.code.
Require Zlib.proof.crc32.Globals.
Require Zlib.proof.harness.inflate_codes.Globals.
Require Zlib.proof.inflate.Rep.
Require Zlib.proof.inflate_api.Spec5.
Require Zlib.proof.inftrees.spec.

(* the program's global variables, in the order of [QPprog_vars] *)
Lemma trl_vars : QPprog_vars p_t =
  [(Zlib.inflate.code._order, Zlib.inflate.code.v_order);
   (Zlib.deflate.code._configuration_table, Zlib.deflate.code.v_configuration_table);
   (Zlib.crc32.code._crc_table, Zlib.crc32.code.v_crc_table);
   (Zlib.trees.code._static_l_desc, Zlib.trees.code.v_static_l_desc);
   (Zlib.trees.code._static_ltree, Zlib.trees.code.v_static_ltree);
   (Zlib.trees.code._static_d_desc, Zlib.trees.code.v_static_d_desc);
   (Zlib.trees.code._static_dtree, Zlib.trees.code.v_static_dtree);
   (Zlib.trees.code._static_bl_desc, Zlib.trees.code.v_static_bl_desc);
   (Zlib.inftrees.code._inflate_copyright, Zlib.inftrees.code.v_inflate_copyright);
   (Zlib.deflate.code._my_version, Zlib.deflate.code.v_my_version);
   (Zlib.trees.code._extra_lbits, Zlib.trees.code.v_extra_lbits);
   (Zlib.trees.code._extra_dbits, Zlib.trees.code.v_extra_dbits);
   (Zlib.trees.code._extra_blbits, Zlib.trees.code.v_extra_blbits);
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
   (Zlib.harness.rt_stream_trailing.code.___stringlit_rt_stream_trailing_1, Zlib.harness.rt_stream_trailing.code.v___stringlit_rt_stream_trailing_1);
   (Zlib.trees.code.__length_code, Zlib.trees.code.v__length_code);
   (Zlib.trees.code.__dist_code, Zlib.trees.code.v__dist_code);
   (Zlib.crc32.code._x2n_table, Zlib.crc32.code.v_x2n_table);
   (Zlib.inftrees.code._lext, Zlib.inftrees.code.v_lext);
   (Zlib.inftrees.code._lenfix, Zlib.inftrees.code.v_lenfix);
   (Zlib.inftrees.code._lbase, Zlib.inftrees.code.v_lbase);
   (Zlib.inftrees.code._distfix, Zlib.inftrees.code.v_distfix);
   (Zlib.inftrees.code._dext, Zlib.inftrees.code.v_dext);
   (Zlib.deflate.code._deflate_copyright, Zlib.deflate.code.v_deflate_copyright);
   (Zlib.inftrees.code._dbase, Zlib.inftrees.code.v_dbase);
   (Zlib.zutil.code._z_errmsg, Zlib.zutil.code.v_z_errmsg);
   (Zlib.trees.code._base_length, Zlib.trees.code.v_base_length);
   (Zlib.trees.code._base_dist, Zlib.trees.code.v_base_dist);
   (Zlib.trees.code._bl_order, Zlib.trees.code.v_bl_order)].
Proof. vm_compute; reflexivity. Qed.

(* the harness's ZLIB_VERSION literal is its initializer *)
Lemma hversion_g gv : (forall b o, gv Zlib.harness.rt_stream_trailing.code.___stringlit_rt_stream_trailing_1 = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (Zlib.harness.rt_stream_trailing.code.___stringlit_rt_stream_trailing_1,
                   Zlib.harness.rt_stream_trailing.code.v___stringlit_rt_stream_trailing_1) |-- hversion_at_t gv.
Proof.
  intros HP. unfold hversion_at_t.
  eapply (@int_glob _ gv _ _ I8 Signed); [exact I | vm_compute; reflexivity | exact HP].
Qed.

Theorem trl_globals : trl_globals_stmt.
Proof.
  intros gv HP HU. rewrite trl_vars. unfold globvars2pred. simpl map; simpl fold_right.
  Zlib.proof.deflate.GlobalsFixed.lit_ptr gv Zlib.zutil.code.___stringlit_zutil_1 Zlib.zutil.code.v___stringlit_zutil_1.
  Zlib.proof.deflate.GlobalsFixed.lit_ptr gv Zlib.zutil.code.___stringlit_zutil_2 Zlib.zutil.code.v___stringlit_zutil_2.
  Zlib.proof.deflate.GlobalsFixed.lit_ptr gv Zlib.zutil.code.___stringlit_zutil_3 Zlib.zutil.code.v___stringlit_zutil_3.
  Zlib.proof.deflate.GlobalsFixed.lit_ptr gv Zlib.zutil.code.___stringlit_zutil_4 Zlib.zutil.code.v___stringlit_zutil_4.
  Zlib.proof.deflate.GlobalsFixed.lit_ptr gv Zlib.zutil.code.___stringlit_zutil_5 Zlib.zutil.code.v___stringlit_zutil_5.
  Zlib.proof.deflate.GlobalsFixed.lit_ptr gv Zlib.zutil.code.___stringlit_zutil_6 Zlib.zutil.code.v___stringlit_zutil_6.
  Zlib.proof.deflate.GlobalsFixed.lit_ptr gv Zlib.zutil.code.___stringlit_zutil_7 Zlib.zutil.code.v___stringlit_zutil_7.
  Zlib.proof.deflate.GlobalsFixed.lit_ptr gv Zlib.zutil.code.___stringlit_zutil_8 Zlib.zutil.code.v___stringlit_zutil_8.
  Zlib.proof.deflate.GlobalsFixed.lit_ptr gv Zlib.zutil.code.___stringlit_zutil_9 Zlib.zutil.code.v___stringlit_zutil_9.
  Zlib.proof.deflate.GlobalsFixed.lit_ptr gv Zlib.zutil.code.___stringlit_zutil_10 Zlib.zutil.code.v___stringlit_zutil_10.
  sep_apply (ltree_g gv (HP _)); Intros.
  sep_apply (dtree_g gv (HP _)); Intros.
  sep_apply (dist_code_g gv (HP _)); Intros.
  sep_apply (length_code_g gv (HP _)); Intros.
  sep_apply (base_length_g gv (HP _)); Intros.
  sep_apply (base_dist_g gv (HP _)); Intros.
  sep_apply (extra_lbits_g gv (HP _)); Intros.
  sep_apply (extra_dbits_g gv (HP _)); Intros.
  sep_apply (extra_blbits_g gv (HP _)); Intros.
  sep_apply (bl_order_g gv (HP _)); Intros.
  sep_apply (my_version_g gv (HP _)); Intros.
  sep_apply (hversion_g gv (HP _)).
  assert (A1 := addr_ok_isptr gv Zlib.trees.code._static_ltree ltac:(assumption)).
  assert (A2 := addr_ok_isptr gv Zlib.trees.code._static_dtree ltac:(assumption)).
  assert (A3 := addr_ok_isptr gv Zlib.trees.code._extra_lbits ltac:(assumption)).
  assert (A4 := addr_ok_isptr gv Zlib.trees.code._extra_dbits ltac:(assumption)).
  assert (A5 := addr_ok_isptr gv Zlib.trees.code._extra_blbits ltac:(assumption)).
  sep_apply (l_desc_g gv A1 A3 (HP _)).
  sep_apply (d_desc_g gv A2 A4 (HP _)).
  sep_apply (bl_desc_g gv A5 (HP _)).
  sep_apply (config_g gv
    (Zlib.proof.deflate.GlobalsFixed.addr_ok_of gv Zlib.deflate.code._deflate_stored
       (HU Zlib.deflate.code._deflate_stored ltac:(simpl; tauto)))
    (Zlib.proof.deflate.GlobalsFixed.addr_ok_of gv Zlib.deflate.code._deflate_fast
       (HU Zlib.deflate.code._deflate_fast ltac:(simpl; tauto)))
    (Zlib.proof.deflate.GlobalsFixed.addr_ok_of gv Zlib.deflate.code._deflate_slow
       (HU Zlib.deflate.code._deflate_slow ltac:(simpl; tauto))) (HP _)).
  assert (AE : Forall (fun s => isptr (gv s)) errmsg_lits) by (unfold errmsg_lits; repeat constructor; assumption).
  sep_apply (errmsg_g gv AE (HP _)).
  sep_apply (Zlib.proof.crc32.Globals.crc_table_of_globvar gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.lenfix_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.distfix_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.order_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.lbase_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.lext_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.dbase_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.dext_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.version_g gv (HP _)).
  unfold Rm_t, deflate_globals, trees_globals, static_trees, trees_tables,
    Zlib.proof.inflate.Rep.tables_rep, Zlib.proof.inftrees.spec.itables.
  cancel.
Qed.
