(* Law res_memory_deflate: the global variables of its program give main deflate.c's globals and the harness's
   ZLIB_VERSION literal (as GlobalsFixed.v does for the three deflate laws). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Assembly.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.Rep Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.GlobalsKit Zlib.proof.deflate.GlobalsFixed.
Require Zlib.contracts.res_memory_deflate Zlib.harness.res_memory_deflate.code.
Require Zlib.deflate.code Zlib.trees.code Zlib.zutil.code Zlib.crc32.code.
Require Zlib.proof.crc32.Globals.

Lemma W_vars_memory : QPprog_vars Zlib.contracts.res_memory_deflate.whole_prog =
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
   (Zlib.harness.res_memory_deflate.code.___stringlit_res_memory_deflate_1, Zlib.harness.res_memory_deflate.code.v___stringlit_res_memory_deflate_1);
   (Zlib.trees.code.__length_code, Zlib.trees.code.v__length_code);
   (Zlib.trees.code.__dist_code, Zlib.trees.code.v__dist_code);
   (Zlib.crc32.code._x2n_table, Zlib.crc32.code.v_x2n_table);
   (Zlib.deflate.code._deflate_copyright, Zlib.deflate.code.v_deflate_copyright);
   (Zlib.zutil.code._z_errmsg, Zlib.zutil.code.v_z_errmsg);
   (Zlib.trees.code._base_length, Zlib.trees.code.v_base_length);
   (Zlib.trees.code._base_dist, Zlib.trees.code.v_base_dist);
   (Zlib.trees.code._bl_order, Zlib.trees.code.v_bl_order)].
Proof. vm_compute; reflexivity. Qed.

Lemma globals_memory_fixed :
  globals_of_fixed Zlib.contracts.res_memory_deflate.whole_prog
    Zlib.harness.res_memory_deflate.code.___stringlit_res_memory_deflate_1.
Proof.
  globals_tac W_vars_memory Zlib.harness.res_memory_deflate.code.___stringlit_res_memory_deflate_1
    Zlib.harness.res_memory_deflate.code.v___stringlit_res_memory_deflate_1.
Qed.
