(* The laws rj_bad_block and rj_far_back: the resources of each program's global variables that its main needs
   (R), out of globvars2pred: inflate's read-only tables (tables_rep: lenfix, distfix, order, inftrees' tables),
   crc32's table, inflate.c's ZLIB_VERSION literal (inflateInit2_ compares the caller's version with it) and the
   harness's own ZLIB_VERSION literal "1.3.2" (passed to inflateInit2_). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Assembly.
Require Import Zlib.proof.inflate_api.Spec5.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.bit_writer.BWLawCS.
Require Zlib.harness.rj_bad_block.code Zlib.harness.rj_far_back.code.
Require Zlib.inflate.code Zlib.inffast.code Zlib.inftrees.code Zlib.crc32.code Zlib.zutil.code.
Require Zlib.proof.crc32.Globals Zlib.proof.harness.inflate_codes.Globals.

(* the harness's "1.3.2" at the global i *)
Definition bw_hversion_at {cs: compspecs} (i: ident) (gv: globals) : mpred :=
  data_at Ers (tarray tschar 6) (map (fun c => Vint (Int.repr c)) [49; 46; 51; 46; 50; 0]) (gv i).

Definition bw_R {cs: compspecs} (i: ident) (gv: globals) : mpred :=
  (tables_rep Ers gv * crc_table_at Ers gv * version_lit gv * bw_hversion_at i gv)%logic.

Definition R_bb := @bw_R BB.CS Zlib.harness.rj_bad_block.code.___stringlit_rj_bad_block_1.
Definition R_fb := @bw_R FB.CS Zlib.harness.rj_far_back.code.___stringlit_rj_far_back_1.

(* Both programs link the same zlib units, so their global variables are the same list except for the
   harness's "1.3.2" literal, which sits between zutil's literals and the tables.  The list in three parts: *)
Definition bw_vars_head : list (ident * globvar type) :=
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

Definition bw_vars_zutil : list (ident * globvar type) :=
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

Definition bw_vars_tail : list (ident * globvar type) :=
  [(Zlib.crc32.code._x2n_table, Zlib.crc32.code.v_x2n_table);
   (Zlib.inftrees.code._lext, Zlib.inftrees.code.v_lext);
   (Zlib.inftrees.code._lenfix, Zlib.inftrees.code.v_lenfix);
   (Zlib.inftrees.code._lbase, Zlib.inftrees.code.v_lbase);
   (Zlib.inftrees.code._distfix, Zlib.inftrees.code.v_distfix);
   (Zlib.inftrees.code._dext, Zlib.inftrees.code.v_dext);
   (Zlib.inftrees.code._dbase, Zlib.inftrees.code.v_dbase);
   (Zlib.zutil.code._z_errmsg, Zlib.zutil.code.v_z_errmsg)].

Lemma BB_vars : QPprog_vars BB.p =
  bw_vars_head ++ bw_vars_zutil ++
  [(Zlib.harness.rj_bad_block.code.___stringlit_rj_bad_block_1,
    Zlib.harness.rj_bad_block.code.v___stringlit_rj_bad_block_1)] ++ bw_vars_tail.
Proof. vm_compute; reflexivity. Qed.

Lemma FB_vars : QPprog_vars FB.p =
  bw_vars_head ++ bw_vars_zutil ++
  [(Zlib.harness.rj_far_back.code.___stringlit_rj_far_back_1,
    Zlib.harness.rj_far_back.code.v___stringlit_rj_far_back_1)] ++ bw_vars_tail.
Proof. vm_compute; reflexivity. Qed.

(* R out of the variable list, for any global h initialised to "1.3.2" placed after zutil's literals *)
Lemma bw_globals_of {cs: compspecs} gv h vh :
  Zlib.proof.harness.inflate_codes.Globals.int_glob_ok I8 Signed vh 6 [49; 46; 51; 46; 50; 0] = true ->
  (forall i b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
  globvars2pred gv (bw_vars_head ++ bw_vars_zutil ++ [(h, vh)] ++ bw_vars_tail) |-- bw_R h gv * TT.
Proof.
  intros OK HP. unfold globvars2pred. rewrite !map_app, !fold_right_sepcon_app.
  generalize (fold_right_sepcon (map (globvar2pred gv) bw_vars_zutil)). intros Z.
  unfold bw_vars_head, bw_vars_tail. simpl map; simpl fold_right_sepcon. rewrite !sepcon_emp.
  sep_apply (Zlib.proof.crc32.Globals.crc_table_of_globvar gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.lenfix_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.distfix_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.order_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.lbase_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.lext_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.dbase_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.dext_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.version_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.int_glob gv h vh I8 Signed 6 _ I OK (HP _)).
  unfold bw_R, bw_hversion_at, tables_rep, Zlib.proof.inftrees.spec.itables.
  cancel.
Qed.

Lemma globals_ok_bb gv : (forall i b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
  globvars2pred gv (QPprog_vars BB.p) |-- R_bb gv * TT.
Proof. intros HP. rewrite BB_vars. apply bw_globals_of; [vm_compute; reflexivity | exact HP]. Qed.

Lemma globals_ok_fb gv : (forall i b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
  globvars2pred gv (QPprog_vars FB.p) |-- R_fb gv * TT.
Proof. intros HP. rewrite FB_vars. apply bw_globals_of; [vm_compute; reflexivity | exact HP]. Qed.
