(** * The globals of the three deflate law programs (deflate_api, deflate_bound, deflate_bound_split), as
    GlobalsInit.globals_of wants them, under one more hypothesis on [gv]: the three functions that
    configuration_table points to (deflate_stored, deflate_fast, deflate_slow) are at a pointer or undefined.

    GlobalsInit.globals_of only assumes offset 0 for every pointer; but those three are functions, not program
    variables, so nothing in globvars2pred excludes e.g. [gv _deflate_stored = Vint 0]: init_data2pred then gives
    [mapsto_] for the pointer member, while [config_vals gv] needs the pointer-or-null value [gv _deflate_stored]
    (value_fits fails for Vint 0): globals_of as stated is false.  genviron2globals (what main gets,
    MainLib.main_core_sub) is [Vptr b 0] or [Vundef], so it satisfies the extra hypothesis.

    This file does not import GlobalsInit (so that GlobalsInit can import it): [version_at] is written out. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Assembly.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.Rep.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.contracts.x_deflate_api Zlib.contracts.x_deflate_bound Zlib.contracts.x_deflate_bound_split.
Require Zlib.harness.x_deflate_api.code Zlib.harness.x_deflate_bound.code Zlib.harness.x_deflate_bound_split.code.

Require Zlib.compress.code Zlib.zutil.code Zlib.crc32.code.
Require Zlib.proof.crc32.Globals.
Require Import Zlib.proof.deflate.GlobalsKit.

Lemma W_vars_api : QPprog_vars Zlib.contracts.x_deflate_api.whole_prog =
  [(Zlib.deflate.code._configuration_table, Zlib.deflate.code.v_configuration_table);
   (Zlib.crc32.code._crc_table, Zlib.crc32.code.v_crc_table);
   (Zlib.trees.code._static_l_desc, Zlib.trees.code.v_static_l_desc);
   (Zlib.trees.code._static_ltree, Zlib.trees.code.v_static_ltree);
   (Zlib.trees.code._static_d_desc, Zlib.trees.code.v_static_d_desc);
   (Zlib.trees.code._static_dtree, Zlib.trees.code.v_static_dtree);
   (Zlib.trees.code._static_bl_desc, Zlib.trees.code.v_static_bl_desc);
   (Zlib.deflate.code._my_version, Zlib.deflate.code.v_my_version);
   (Zlib.trees.code._extra_lbits, Zlib.trees.code.v_extra_lbits);
   (Zlib.trees.code._extra_dbits, Zlib.trees.code.v_extra_dbits);
   (Zlib.trees.code._extra_blbits, Zlib.trees.code.v_extra_blbits);
   (Zlib.harness.x_deflate_api.code.___stringlit_x_deflate_api_1, Zlib.harness.x_deflate_api.code.v___stringlit_x_deflate_api_1);
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
   (Zlib.deflate.code._deflate_copyright, Zlib.deflate.code.v_deflate_copyright);
   (Zlib.zutil.code._z_errmsg, Zlib.zutil.code.v_z_errmsg);
   (Zlib.trees.code._base_length, Zlib.trees.code.v_base_length);
   (Zlib.trees.code._base_dist, Zlib.trees.code.v_base_dist);
   (Zlib.trees.code._bl_order, Zlib.trees.code.v_bl_order)].
Proof. vm_compute; reflexivity. Qed.

Lemma W_vars_bound : QPprog_vars Zlib.contracts.x_deflate_bound.whole_prog =
  [(Zlib.deflate.code._configuration_table, Zlib.deflate.code.v_configuration_table);
   (Zlib.crc32.code._crc_table, Zlib.crc32.code.v_crc_table);
   (Zlib.trees.code._static_l_desc, Zlib.trees.code.v_static_l_desc);
   (Zlib.trees.code._static_ltree, Zlib.trees.code.v_static_ltree);
   (Zlib.trees.code._static_d_desc, Zlib.trees.code.v_static_d_desc);
   (Zlib.trees.code._static_dtree, Zlib.trees.code.v_static_dtree);
   (Zlib.trees.code._static_bl_desc, Zlib.trees.code.v_static_bl_desc);
   (Zlib.deflate.code._my_version, Zlib.deflate.code.v_my_version);
   (Zlib.trees.code._extra_lbits, Zlib.trees.code.v_extra_lbits);
   (Zlib.trees.code._extra_dbits, Zlib.trees.code.v_extra_dbits);
   (Zlib.trees.code._extra_blbits, Zlib.trees.code.v_extra_blbits);
   (Zlib.compress.code.___stringlit_compress_1, Zlib.compress.code.v___stringlit_compress_1);
   (Zlib.harness.x_deflate_bound.code.___stringlit_x_deflate_bound_1, Zlib.harness.x_deflate_bound.code.v___stringlit_x_deflate_bound_1);
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
   (Zlib.deflate.code._deflate_copyright, Zlib.deflate.code.v_deflate_copyright);
   (Zlib.zutil.code._z_errmsg, Zlib.zutil.code.v_z_errmsg);
   (Zlib.trees.code._base_length, Zlib.trees.code.v_base_length);
   (Zlib.trees.code._base_dist, Zlib.trees.code.v_base_dist);
   (Zlib.trees.code._bl_order, Zlib.trees.code.v_bl_order)].
Proof. vm_compute; reflexivity. Qed.

Lemma W_vars_split : QPprog_vars Zlib.contracts.x_deflate_bound_split.whole_prog =
  [(Zlib.deflate.code._configuration_table, Zlib.deflate.code.v_configuration_table);
   (Zlib.crc32.code._crc_table, Zlib.crc32.code.v_crc_table);
   (Zlib.trees.code._static_l_desc, Zlib.trees.code.v_static_l_desc);
   (Zlib.trees.code._static_ltree, Zlib.trees.code.v_static_ltree);
   (Zlib.trees.code._static_d_desc, Zlib.trees.code.v_static_d_desc);
   (Zlib.trees.code._static_dtree, Zlib.trees.code.v_static_dtree);
   (Zlib.trees.code._static_bl_desc, Zlib.trees.code.v_static_bl_desc);
   (Zlib.deflate.code._my_version, Zlib.deflate.code.v_my_version);
   (Zlib.trees.code._extra_lbits, Zlib.trees.code.v_extra_lbits);
   (Zlib.trees.code._extra_dbits, Zlib.trees.code.v_extra_dbits);
   (Zlib.trees.code._extra_blbits, Zlib.trees.code.v_extra_blbits);
   (Zlib.harness.x_deflate_bound_split.code.___stringlit_x_deflate_bound_split_1, Zlib.harness.x_deflate_bound_split.code.v___stringlit_x_deflate_bound_split_1);
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
   (Zlib.deflate.code._deflate_copyright, Zlib.deflate.code.v_deflate_copyright);
   (Zlib.zutil.code._z_errmsg, Zlib.zutil.code.v_z_errmsg);
   (Zlib.trees.code._base_length, Zlib.trees.code.v_base_length);
   (Zlib.trees.code._base_dist, Zlib.trees.code.v_base_dist);
   (Zlib.trees.code._bl_order, Zlib.trees.code.v_bl_order)].
Proof. vm_compute; reflexivity. Qed.


Definition cfg_funs : list ident :=
  [Zlib.deflate.code._deflate_stored; Zlib.deflate.code._deflate_fast; Zlib.deflate.code._deflate_slow].

(** GlobalsInit.globals_of with the extra hypothesis on the functions of configuration_table. *)
Definition globals_of_fixed (p : QP.program Clight.function) (lit : ident) : Prop :=
  forall gv, (forall i b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
  (forall f, In f cfg_funs -> gv f = Vundef \/ isptr (gv f)) ->
  globvars2pred gv (QPprog_vars p) |--
  deflate_globals gv * @data_at DCS.CS Ers (tarray tschar 6) (map vi [49; 46; 51; 46; 50; 0]) (gv lit) * TT.

Lemma addr_ok_of gv f : gv f = Vundef \/ isptr (gv f) -> addr_ok gv f.
Proof. unfold addr_ok. intros [H|H]; [rewrite H; exact I | destruct (gv f); try contradiction; exact I]. Qed.

Ltac lit_ptr gv i v := sep_apply (glob_isptr gv i v eq_refl); Intros.

Ltac globals_tac W lit vlit :=
  let gv := fresh "gv" in let HP := fresh "HP" in let HU := fresh "HU" in
  intros gv HP HU; rewrite W; unfold globvars2pred; simpl map; simpl fold_right;
  lit_ptr gv Zlib.zutil.code.___stringlit_zutil_1 Zlib.zutil.code.v___stringlit_zutil_1;
  lit_ptr gv Zlib.zutil.code.___stringlit_zutil_2 Zlib.zutil.code.v___stringlit_zutil_2;
  lit_ptr gv Zlib.zutil.code.___stringlit_zutil_3 Zlib.zutil.code.v___stringlit_zutil_3;
  lit_ptr gv Zlib.zutil.code.___stringlit_zutil_4 Zlib.zutil.code.v___stringlit_zutil_4;
  lit_ptr gv Zlib.zutil.code.___stringlit_zutil_5 Zlib.zutil.code.v___stringlit_zutil_5;
  lit_ptr gv Zlib.zutil.code.___stringlit_zutil_6 Zlib.zutil.code.v___stringlit_zutil_6;
  lit_ptr gv Zlib.zutil.code.___stringlit_zutil_7 Zlib.zutil.code.v___stringlit_zutil_7;
  lit_ptr gv Zlib.zutil.code.___stringlit_zutil_8 Zlib.zutil.code.v___stringlit_zutil_8;
  lit_ptr gv Zlib.zutil.code.___stringlit_zutil_9 Zlib.zutil.code.v___stringlit_zutil_9;
  lit_ptr gv Zlib.zutil.code.___stringlit_zutil_10 Zlib.zutil.code.v___stringlit_zutil_10;
  sep_apply (ltree_g gv (HP _)); Intros;
  sep_apply (dtree_g gv (HP _)); Intros;
  sep_apply (dist_code_g gv (HP _)); Intros;
  sep_apply (length_code_g gv (HP _)); Intros;
  sep_apply (base_length_g gv (HP _)); Intros;
  sep_apply (base_dist_g gv (HP _)); Intros;
  sep_apply (extra_lbits_g gv (HP _)); Intros;
  sep_apply (extra_dbits_g gv (HP _)); Intros;
  sep_apply (extra_blbits_g gv (HP _)); Intros;
  sep_apply (bl_order_g gv (HP _)); Intros;
  sep_apply (my_version_g gv (HP _)); Intros;
  sep_apply (version_lit_g gv lit vlit eq_refl (HP _)); Intros;
  assert (A1 := addr_ok_isptr gv Zlib.trees.code._static_ltree ltac:(assumption));
  assert (A2 := addr_ok_isptr gv Zlib.trees.code._static_dtree ltac:(assumption));
  assert (A3 := addr_ok_isptr gv Zlib.trees.code._extra_lbits ltac:(assumption));
  assert (A4 := addr_ok_isptr gv Zlib.trees.code._extra_dbits ltac:(assumption));
  assert (A5 := addr_ok_isptr gv Zlib.trees.code._extra_blbits ltac:(assumption));
  sep_apply (l_desc_g gv A1 A3 (HP _));
  sep_apply (d_desc_g gv A2 A4 (HP _));
  sep_apply (bl_desc_g gv A5 (HP _));
  sep_apply (config_g gv (addr_ok_of gv Zlib.deflate.code._deflate_stored (HU Zlib.deflate.code._deflate_stored ltac:(simpl; tauto)))
                         (addr_ok_of gv Zlib.deflate.code._deflate_fast (HU Zlib.deflate.code._deflate_fast ltac:(simpl; tauto)))
                         (addr_ok_of gv Zlib.deflate.code._deflate_slow (HU Zlib.deflate.code._deflate_slow ltac:(simpl; tauto))) (HP _));
  assert (AE : Forall (fun s => isptr (gv s)) errmsg_lits) by (unfold errmsg_lits; repeat constructor; assumption);
  sep_apply (errmsg_g gv AE (HP _));
  sep_apply (Zlib.proof.crc32.Globals.crc_table_of_globvar gv (HP _));
  unfold deflate_globals, trees_globals, static_trees, trees_tables; cancel.

Lemma globals_api_fixed :
  globals_of_fixed Zlib.contracts.x_deflate_api.whole_prog Zlib.harness.x_deflate_api.code.___stringlit_x_deflate_api_1.
Proof.
  globals_tac W_vars_api Zlib.harness.x_deflate_api.code.___stringlit_x_deflate_api_1
    Zlib.harness.x_deflate_api.code.v___stringlit_x_deflate_api_1.
Qed.

Lemma globals_bound_fixed :
  globals_of_fixed Zlib.contracts.x_deflate_bound.whole_prog Zlib.harness.x_deflate_bound.code.___stringlit_x_deflate_bound_1.
Proof.
  globals_tac W_vars_bound Zlib.harness.x_deflate_bound.code.___stringlit_x_deflate_bound_1
    Zlib.harness.x_deflate_bound.code.v___stringlit_x_deflate_bound_1.
Qed.

Lemma globals_split_fixed :
  globals_of_fixed Zlib.contracts.x_deflate_bound_split.whole_prog
    Zlib.harness.x_deflate_bound_split.code.___stringlit_x_deflate_bound_split_1.
Proof.
  globals_tac W_vars_split Zlib.harness.x_deflate_bound_split.code.___stringlit_x_deflate_bound_split_1
    Zlib.harness.x_deflate_bound_split.code.v___stringlit_x_deflate_bound_split_1.
Qed.

