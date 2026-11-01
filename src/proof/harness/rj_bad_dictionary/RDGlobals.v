(* Law rj_bad_dictionary: the resources of the program's global variables that main needs (R), out of
   globvars2pred (as inflate_check/IKGlobals.v): inflate's read-only tables (lenfix, distfix, order, inftrees'
   lbase/lext/dbase/dext), crc32's table, inflate.c's ZLIB_VERSION literal (inflateInit2_) and the harness's
   ZLIB_VERSION literal (the macro inflateInit2 passes it to inflateInit2_).  The rest (inflate's message
   literals, ...) goes to TT. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.inflate_api.Spec5.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.rj_bad_dictionary.RDLawCS.
Require Zlib.harness.rj_bad_dictionary.code.
Require Zlib.units.Inflate.
Require Zlib.inflate.code.
Require Zlib.inffast.code.
Require Zlib.inftrees.code.
Require Zlib.crc32.code.
Require Zlib.zutil.code.
Require Zlib.proof.crc32.Globals.
Require Zlib.proof.harness.inflate_codes.Globals.

(* the harness's "1.3.2" *)
Definition rbd_hversion_lit (gv: globals) : mpred :=
  data_at Ers (tarray tschar 6) (map (fun c => Vint (Int.repr c)) [49; 46; 51; 46; 50; 0])
    (gv Zlib.harness.rj_bad_dictionary.code.___stringlit_rj_bad_dictionary_1).

Definition R (gv: globals) : mpred :=
  (tables_rep Ers gv * crc_table_at Ers gv * version_lit gv * rbd_hversion_lit gv)%logic.

Lemma rbd_hversion_g gv :
  (forall b o, gv Zlib.harness.rj_bad_dictionary.code.___stringlit_rj_bad_dictionary_1 = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (Zlib.harness.rj_bad_dictionary.code.___stringlit_rj_bad_dictionary_1,
                   Zlib.harness.rj_bad_dictionary.code.v___stringlit_rj_bad_dictionary_1) |-- rbd_hversion_lit gv.
Proof.
  intros HP. unfold rbd_hversion_lit.
  eapply (Zlib.proof.harness.inflate_codes.Globals.int_glob _ _ _ I8 Signed); [exact I | vm_compute; reflexivity | exact HP].
Qed.

Lemma rbd_W_vars : QPprog_vars p =
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
   (Zlib.harness.rj_bad_dictionary.code.___stringlit_rj_bad_dictionary_1, Zlib.harness.rj_bad_dictionary.code.v___stringlit_rj_bad_dictionary_1);
   (Zlib.crc32.code._x2n_table, Zlib.crc32.code.v_x2n_table);
   (Zlib.inftrees.code._lext, Zlib.inftrees.code.v_lext);
   (Zlib.inftrees.code._lenfix, Zlib.inftrees.code.v_lenfix);
   (Zlib.inftrees.code._lbase, Zlib.inftrees.code.v_lbase);
   (Zlib.inftrees.code._distfix, Zlib.inftrees.code.v_distfix);
   (Zlib.inftrees.code._dext, Zlib.inftrees.code.v_dext);
   (Zlib.inftrees.code._dbase, Zlib.inftrees.code.v_dbase);
   (Zlib.zutil.code._z_errmsg, Zlib.zutil.code.v_z_errmsg)].
Proof. vm_compute; reflexivity. Qed.

Lemma globals_ok gv : (forall i b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
  globvars2pred gv (QPprog_vars p) |-- R gv * TT.
Proof.
  intros HP.
  rewrite rbd_W_vars. unfold globvars2pred. simpl map; simpl fold_right.
  sep_apply (Zlib.proof.crc32.Globals.crc_table_of_globvar gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.lenfix_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.distfix_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.order_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.lbase_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.lext_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.dbase_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.dext_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_codes.Globals.version_g gv (HP _)).
  sep_apply (rbd_hversion_g gv (HP _)).
  unfold R, tables_rep, Zlib.proof.inftrees.spec.itables.
  cancel.
Qed.
