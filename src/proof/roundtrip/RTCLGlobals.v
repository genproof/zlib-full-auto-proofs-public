(* Law compress_roundtrip, part RT-CL: the resources of the program's global variables that main needs (R),
   out of globvars2pred: deflate's (DSpec.deflate_globals: trees.c's tables, z_errmsg, configuration_table with the
   function pointers, my_version, crc32's table), compress.c's ZLIB_VERSION literal (RTCSpec.cversion_lit),
   inflate's read-only tables (tables_rep), inflate.c's and uncompr.c's ZLIB_VERSION literals.  The rest goes to
   TT.  As deflate/GlobalsFixed.v (globals_tac) and uncompress_any/UAGlobals.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Assembly.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.Rep.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.GlobalsKit.
Require Zlib.proof.crc32.Globals.
Require Zlib.proof.harness.inflate_codes.Globals.
Require Import Zlib.proof.inflate_api.Spec5.
Require Import Zlib.proof.uncompr.USpec5.
Require Zlib.proof.roundtrip.RTCSpec.
Require Import Zlib.proof.roundtrip.RTCLCS.
Require Zlib.units.Compress Zlib.units.Uncompr.
Require Zlib.deflate.code Zlib.trees.code Zlib.compress.code Zlib.crc32.code Zlib.zutil.code Zlib.inflate.code
        Zlib.inffast.code Zlib.inftrees.code Zlib.uncompr.code.

Definition R (gv: globals) : mpred :=
  (deflate_globals gv * Zlib.proof.roundtrip.RTCSpec.cversion_lit gv *
   tables_rep Ers gv * version_lit gv * uversion_lit gv)%logic.

Definition cfg_funs : list ident :=
  [Zlib.deflate.code._deflate_stored; Zlib.deflate.code._deflate_fast; Zlib.deflate.code._deflate_slow].

Lemma W_vars : QPprog_vars p =
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
   (Zlib.compress.code.___stringlit_compress_1, Zlib.compress.code.v___stringlit_compress_1);
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
   (Zlib.uncompr.code.___stringlit_uncompr_1, Zlib.uncompr.code.v___stringlit_uncompr_1);
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

Lemma cversion_g gv : (forall b o, gv Zlib.compress.code.___stringlit_compress_1 = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (Zlib.compress.code.___stringlit_compress_1, Zlib.compress.code.v___stringlit_compress_1)
  |-- Zlib.proof.roundtrip.RTCSpec.cversion_lit gv.
Proof.
  intros HP. unfold Zlib.proof.roundtrip.RTCSpec.cversion_lit.
  eapply (@Zlib.proof.harness.inflate_codes.Globals.int_glob Zlib.units.Compress.CS _ _ _ I8 Signed);
    [exact I | vm_compute; reflexivity | exact HP].
Qed.

Lemma uversion_g gv : (forall b o, gv Zlib.uncompr.code.___stringlit_uncompr_1 = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (Zlib.uncompr.code.___stringlit_uncompr_1, Zlib.uncompr.code.v___stringlit_uncompr_1)
  |-- uversion_lit gv.
Proof.
  intros HP. unfold uversion_lit.
  eapply (Zlib.proof.harness.inflate_codes.Globals.int_glob _ _ _ I8 Signed);
    [exact I | vm_compute; reflexivity | exact HP].
Qed.

Lemma addr_ok_of gv f : gv f = Vundef \/ isptr (gv f) -> addr_ok gv f.
Proof. unfold addr_ok. intros [H|H]; [rewrite H; exact I | destruct (gv f); try contradiction; exact I]. Qed.

Ltac lit_ptr gv i v := sep_apply (glob_isptr gv i v eq_refl); Intros.

Lemma globals_ok gv : (forall i b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
  (forall f, In f cfg_funs -> gv f = Vundef \/ isptr (gv f)) ->
  globvars2pred gv (QPprog_vars p) |-- R gv * TT.
Proof.
  intros HP HU. rewrite W_vars. unfold globvars2pred; simpl map; simpl fold_right.
  lit_ptr gv Zlib.zutil.code.___stringlit_zutil_1 Zlib.zutil.code.v___stringlit_zutil_1.
  lit_ptr gv Zlib.zutil.code.___stringlit_zutil_2 Zlib.zutil.code.v___stringlit_zutil_2.
  lit_ptr gv Zlib.zutil.code.___stringlit_zutil_3 Zlib.zutil.code.v___stringlit_zutil_3.
  lit_ptr gv Zlib.zutil.code.___stringlit_zutil_4 Zlib.zutil.code.v___stringlit_zutil_4.
  lit_ptr gv Zlib.zutil.code.___stringlit_zutil_5 Zlib.zutil.code.v___stringlit_zutil_5.
  lit_ptr gv Zlib.zutil.code.___stringlit_zutil_6 Zlib.zutil.code.v___stringlit_zutil_6.
  lit_ptr gv Zlib.zutil.code.___stringlit_zutil_7 Zlib.zutil.code.v___stringlit_zutil_7.
  lit_ptr gv Zlib.zutil.code.___stringlit_zutil_8 Zlib.zutil.code.v___stringlit_zutil_8.
  lit_ptr gv Zlib.zutil.code.___stringlit_zutil_9 Zlib.zutil.code.v___stringlit_zutil_9.
  lit_ptr gv Zlib.zutil.code.___stringlit_zutil_10 Zlib.zutil.code.v___stringlit_zutil_10.
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
  assert (A1 := addr_ok_isptr gv Zlib.trees.code._static_ltree ltac:(assumption)).
  assert (A2 := addr_ok_isptr gv Zlib.trees.code._static_dtree ltac:(assumption)).
  assert (A3 := addr_ok_isptr gv Zlib.trees.code._extra_lbits ltac:(assumption)).
  assert (A4 := addr_ok_isptr gv Zlib.trees.code._extra_dbits ltac:(assumption)).
  assert (A5 := addr_ok_isptr gv Zlib.trees.code._extra_blbits ltac:(assumption)).
  sep_apply (l_desc_g gv A1 A3 (HP _)).
  sep_apply (d_desc_g gv A2 A4 (HP _)).
  sep_apply (bl_desc_g gv A5 (HP _)).
  sep_apply (config_g gv (addr_ok_of gv Zlib.deflate.code._deflate_stored (HU Zlib.deflate.code._deflate_stored ltac:(simpl; tauto)))
                         (addr_ok_of gv Zlib.deflate.code._deflate_fast (HU Zlib.deflate.code._deflate_fast ltac:(simpl; tauto)))
                         (addr_ok_of gv Zlib.deflate.code._deflate_slow (HU Zlib.deflate.code._deflate_slow ltac:(simpl; tauto))) (HP _)).
  assert (AE : Forall (fun s => isptr (gv s)) errmsg_lits) by (unfold errmsg_lits; repeat constructor; assumption).
  sep_apply (errmsg_g gv AE (HP _)).
  sep_apply (Zlib.proof.crc32.Globals.crc_table_of_globvar gv (HP _)).
  sep_apply (cversion_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.lenfix_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.distfix_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.order_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.lbase_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.lext_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.dbase_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.dext_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.version_g gv (HP _)).
  sep_apply (uversion_g gv (HP _)).
  unfold R, deflate_globals, trees_globals, static_trees, trees_tables, tables_rep,
    Zlib.proof.inftrees.spec.itables.
  cancel.
Qed.
