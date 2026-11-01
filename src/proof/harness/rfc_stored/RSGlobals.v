(* Law rfc_stored: the resources of the program's global variables that main needs (R), out of globvars2pred:
   inflate's read-only tables (lenfix, distfix, order, inftrees' lbase/lext/dbase/dext), crc32's table (crc32_z
   for the gzip trailer, inflate's CRC-32 check), inflate.c's ZLIB_VERSION literal (inflateInit2_ compares
   the caller's with it) and the harness's ZLIB_VERSION literal (the macro inflateInit2 passes it).  The rest
   (inflate's message literals, ...) goes to TT. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Assembly.
Require Import Zlib.proof.inflate_api.Spec5.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.rfc_stored.RSLawCS.
Require Zlib.harness.rfc_stored.code.
Require Zlib.units.Inflate.
Require Zlib.inflate.code Zlib.inftrees.code Zlib.crc32.code.
Require Zlib.proof.crc32.Globals.
Require Zlib.proof.harness.inflate_reset.IRGlobals.

(* the harness's "1.3.2", at the inflate unit's compspecs (as inflateInit2__spec takes the caller's version) *)
Definition rs_hver_vals : list val := map (fun c => Vint (Int.repr c)) [49; 46; 51; 46; 50; 0].

Definition rs_hversion_lit (gv: globals) : mpred :=
  @data_at Zlib.units.Inflate.CS Ers (tarray tschar (Zlength rs_hver_vals)) rs_hver_vals
    (gv Zlib.harness.rfc_stored.code.___stringlit_rfc_stored_1).

Definition R (gv: globals) : mpred :=
  (tables_rep Ers gv * crc_table_at Ers gv * version_lit gv * rs_hversion_lit gv)%logic.

Lemma rs_hversion_g gv :
  (forall b o, gv Zlib.harness.rfc_stored.code.___stringlit_rfc_stored_1 = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (Zlib.harness.rfc_stored.code.___stringlit_rfc_stored_1,
                   Zlib.harness.rfc_stored.code.v___stringlit_rfc_stored_1) |-- rs_hversion_lit gv.
Proof.
  intros HP. unfold rs_hversion_lit, rs_hver_vals. change (Zlength _) with 6.
  eapply (@Zlib.proof.harness.inflate_reset.IRGlobals.ir_int_glob Zlib.units.Inflate.CS _ _ _ I8 Signed);
    [exact I | vm_compute; reflexivity | exact HP].
Qed.

(* the elements of a separating list that satisfy keep, the rest forgotten *)
Lemma rs_fold_filter {A} (f: A -> mpred) (keep: A -> bool) : forall l,
  fold_right sepcon emp (map f l) |-- fold_right sepcon emp (map f (filter keep l)) * TT.
Proof.
  induction l as [|a l IH]; simpl.
  - cancel.
  - destruct (keep a); simpl; sep_apply IH; cancel.
Qed.

(* the global variables R is made of *)
Definition rs_R_ids : list ident :=
  [Zlib.inflate.code._order; Zlib.crc32.code._crc_table; Zlib.inflate.code.___stringlit_inflate_1;
   Zlib.harness.rfc_stored.code.___stringlit_rfc_stored_1;
   Zlib.inftrees.code._lext; Zlib.inftrees.code._lenfix; Zlib.inftrees.code._lbase;
   Zlib.inftrees.code._distfix; Zlib.inftrees.code._dext; Zlib.inftrees.code._dbase].

Lemma globals_ok gv : (forall i b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
  globvars2pred gv (QPprog_vars p) |-- R gv * TT.
Proof.
  intros HP. unfold globvars2pred.
  sep_apply (rs_fold_filter (globvar2pred gv) (fun x => existsb (Pos.eqb (fst x)) rs_R_ids) (QPprog_vars p)).
  replace (filter _ (QPprog_vars p)) with
    [(Zlib.inflate.code._order, Zlib.inflate.code.v_order);
     (Zlib.crc32.code._crc_table, Zlib.crc32.code.v_crc_table);
     (Zlib.inflate.code.___stringlit_inflate_1, Zlib.inflate.code.v___stringlit_inflate_1);
     (Zlib.harness.rfc_stored.code.___stringlit_rfc_stored_1, Zlib.harness.rfc_stored.code.v___stringlit_rfc_stored_1);
     (Zlib.inftrees.code._lext, Zlib.inftrees.code.v_lext);
     (Zlib.inftrees.code._lenfix, Zlib.inftrees.code.v_lenfix);
     (Zlib.inftrees.code._lbase, Zlib.inftrees.code.v_lbase);
     (Zlib.inftrees.code._distfix, Zlib.inftrees.code.v_distfix);
     (Zlib.inftrees.code._dext, Zlib.inftrees.code.v_dext);
     (Zlib.inftrees.code._dbase, Zlib.inftrees.code.v_dbase)]
    by (vm_compute; reflexivity).
  simpl map; simpl fold_right.
  sep_apply (Zlib.proof.crc32.Globals.crc_table_of_globvar gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_reset.IRGlobals.ir_lenfix_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_reset.IRGlobals.ir_distfix_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_reset.IRGlobals.ir_order_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_reset.IRGlobals.ir_lbase_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_reset.IRGlobals.ir_lext_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_reset.IRGlobals.ir_dbase_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_reset.IRGlobals.ir_dext_g gv (HP _)).
  sep_apply (Zlib.proof.harness.inflate_reset.IRGlobals.ir_version_g gv (HP _)).
  sep_apply (rs_hversion_g gv (HP _)).
  unfold R, tables_rep, Zlib.proof.inftrees.spec.itables.
  cancel.
Qed.
