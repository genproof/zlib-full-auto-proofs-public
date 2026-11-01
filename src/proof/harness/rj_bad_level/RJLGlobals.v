(* Law rj_bad_level: the resources of the program's global variables that main needs (R), out of globvars2pred:
   deflate's (DSpec.deflate_globals: trees.c's tables, z_errmsg, configuration_table with the function pointers,
   my_version, crc32's table) and compress.c's ZLIB_VERSION literal (RTCSpec.cversion_lit), which compress2 needs.
   The rest goes to TT.  As roundtrip/RTCLGlobals.v, with deflate/GlobalsFixed.v's globals_tac. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Assembly.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.Rep.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.GlobalsKit Zlib.proof.deflate.GlobalsFixed.
Require Zlib.proof.crc32.Globals.
Require Zlib.proof.roundtrip.RTCSpec.
Require Import Zlib.proof.harness.rj_bad_level.RJLCS.
Require Zlib.units.Compress.
Require Zlib.deflate.code Zlib.trees.code Zlib.compress.code Zlib.crc32.code Zlib.zutil.code.

Definition R (gv: globals) : mpred :=
  (deflate_globals gv * Zlib.proof.roundtrip.RTCSpec.cversion_lit gv)%logic.

Lemma W_vars : QPprog_vars p =
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

(* compress.c's literal as deflate.c's version literal is given (DCS.CS): an array of chars, the same at every
   compspecs *)
Lemma rjl_cversion gv :
  @data_at DCS.CS Ers (tarray tschar 6) (map vi [49; 46; 51; 46; 50; 0]) (gv Zlib.compress.code.___stringlit_compress_1)
  |-- Zlib.proof.roundtrip.RTCSpec.cversion_lit gv.
Proof.
  unfold Zlib.proof.roundtrip.RTCSpec.cversion_lit.
  erewrite (@data_at_change_composite _ _ CC_dcs Ers (tarray tschar 6)); [ | apply JMeq_refl | reflexivity].
  erewrite (@data_at_change_composite _ _ CC_compress Ers (tarray tschar 6)); [ | apply JMeq_refl | reflexivity].
  apply derives_refl.
Qed.

Lemma globals_ok gv : (forall i b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
  (forall f, In f cfg_funs -> gv f = Vundef \/ isptr (gv f)) ->
  globvars2pred gv (QPprog_vars p) |-- R gv * TT.
Proof.
  intros HP HU.
  assert (G : globals_of_fixed p Zlib.compress.code.___stringlit_compress_1).
  { globals_tac W_vars Zlib.compress.code.___stringlit_compress_1 Zlib.compress.code.v___stringlit_compress_1. }
  sep_apply (G gv HP HU). unfold R. sep_apply (rjl_cversion gv). cancel.
Qed.
