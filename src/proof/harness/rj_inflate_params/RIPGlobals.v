(* Law rj_inflate_params: the resources of the program's global variables that main needs (R), out of
   globvars2pred: inflate.c's ZLIB_VERSION literal (inflateInit2_ compares the caller's version with it) and the
   harness's own ZLIB_VERSION literal (the argument of inflateInit2).  The conversions of initialised read-only
   arrays are inflate_reset's (IRGlobals.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Assembly.
Require Import Zlib.proof.inflate_api.Spec5.
Require Import Zlib.proof.harness.rj_inflate_params.RIPLawCS.
Require Zlib.harness.rj_inflate_params.code.
Require Zlib.proof.harness.inflate_reset.IRGlobals.
Require Zlib.inflate.code.

(* the harness's "1.3.2", at the inflate unit's compspecs (as inflateInit2__spec takes the caller's version) *)
Definition rip_hver_vals : list val := map (fun c => Vint (Int.repr c)) [49; 46; 51; 46; 50; 0].

Definition rip_hversion_lit (gv: globals) : mpred :=
  @data_at Zlib.units.Inflate.CS Ers (tarray tschar (Zlength rip_hver_vals)) rip_hver_vals
    (gv Zlib.harness.rj_inflate_params.code.___stringlit_rj_inflate_params_1).

Definition R (gv: globals) : mpred := (version_lit gv * rip_hversion_lit gv)%logic.

Lemma rip_hversion_g gv :
  (forall b o, gv Zlib.harness.rj_inflate_params.code.___stringlit_rj_inflate_params_1 = Vptr b o -> o = Ptrofs.zero) ->
  globvar2pred gv (Zlib.harness.rj_inflate_params.code.___stringlit_rj_inflate_params_1,
                   Zlib.harness.rj_inflate_params.code.v___stringlit_rj_inflate_params_1) |-- rip_hversion_lit gv.
Proof.
  intros HP. unfold rip_hversion_lit, rip_hver_vals. change (Zlength _) with 6.
  eapply (@Zlib.proof.harness.inflate_reset.IRGlobals.ir_int_glob Zlib.units.Inflate.CS _ _ _ I8 Signed);
    [exact I | vm_compute; reflexivity | exact HP].
Qed.

(* two distinct elements of a separating list, the rest forgotten *)
Lemma rip_fold_pick {A} (f: A -> mpred) : forall l k d, (k < length l)%nat ->
  fold_right sepcon emp (map f l) |-- f (nth k l d) * TT.
Proof.
  induction l as [|a l IH]; intros k d H; simpl in H; [lia|].
  destruct k as [|k]; simpl.
  - cancel.
  - sep_apply (IH k d ltac:(lia)). cancel.
Qed.

Lemma rip_fold_pick2 {A} (f: A -> mpred) : forall l j k d, (j < k < length l)%nat ->
  fold_right sepcon emp (map f l) |-- f (nth j l d) * f (nth k l d) * TT.
Proof.
  induction l as [|a l IH]; intros j k d H; simpl in H; [lia|].
  destruct j as [|j], k as [|k]; try lia; simpl.
  - sep_apply (rip_fold_pick f l k d ltac:(lia)). cancel.
  - sep_apply (IH j k d ltac:(lia)). cancel.
Qed.

Lemma globals_ok gv : (forall i b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
  globvars2pred gv (QPprog_vars p) |-- R gv * TT.
Proof.
  intros HP. unfold globvars2pred.
  sep_apply (rip_fold_pick2 (globvar2pred gv) (QPprog_vars p) 12 35
               (Zlib.inflate.code.___stringlit_inflate_1, Zlib.inflate.code.v___stringlit_inflate_1)
               ltac:(vm_compute; lia)).
  replace (nth 12 (QPprog_vars p) _)
    with (Zlib.inflate.code.___stringlit_inflate_1, Zlib.inflate.code.v___stringlit_inflate_1)
    by (vm_compute; reflexivity).
  replace (nth 35 (QPprog_vars p) _)
    with (Zlib.harness.rj_inflate_params.code.___stringlit_rj_inflate_params_1,
          Zlib.harness.rj_inflate_params.code.v___stringlit_rj_inflate_params_1)
    by (vm_compute; reflexivity).
  sep_apply (Zlib.proof.harness.inflate_reset.IRGlobals.ir_version_g gv (HP _)).
  sep_apply (rip_hversion_g gv (HP _)).
  unfold R. cancel.
Qed.
