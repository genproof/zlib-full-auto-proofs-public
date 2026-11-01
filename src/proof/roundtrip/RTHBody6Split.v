(* RT-H: inflate_spec6 from Spec5's inflate_spec and inflate_spec6h (RTHBody6Kit.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTHBody6Kit.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Lemma semax_orp6 {Espec: OracleKind}: forall Delta P1 P2 c Q,
  semax Delta P1 c Q -> semax Delta P2 c Q -> semax Delta (P1 || P2) c Q.
Proof.
  intros.
  eapply semax_pre with (EX b: bool, if b then P1 else P2).
  + apply andp_left2. apply orp_left.
    - apply (exp_right true), derives_refl.
    - apply (exp_right false), derives_refl.
  + apply semax_extract_exists. intros b. destruct b; auto.
Qed.

Lemma close_pre_orp: forall ids (P Q R: argsEnviron -> mpred),
  (forall ae, P ae |-- Q ae || R ae) ->
  forall rho, close_precondition ids P rho |-- close_precondition ids Q rho || close_precondition ids R rho.
Proof.
  intros ids P Q R H rho. unfold close_precondition.
  apply exp_left; intros vals. normalize.
  eapply derives_trans; [apply H | ].
  apply orp_left; [apply orp_right1 | apply orp_right2]; apply (exp_right vals); normalize.
Qed.

Lemma rth_split {Espec: OracleKind}:
  semax_body Vprog_inflate Gprog_inflate3 f_inflate inflate_spec ->
  semax_body Vprog_inflate Gprog_inflate3 f_inflate inflate_spec6h ->
  semax_body Vprog_inflate Gprog_inflate3 f_inflate inflate_spec6.
Proof.
  intros [A1 [A2 A]] [B1 [B2 B]].
  split; [exact A1 | split; [exact A2 | ]].
  intros Es ts x.
  specialize (A Es ts x). specialize (B Es ts x).
  destruct x as [[[[[[[[[[[[gv shs] strmp] z] st] ib] inp] ob] flush] gsh] tsh] itok] otok].
  set (body := fn_body f_inflate) in *. clearbody body.
  set (sf := stackframe_of f_inflate) in *. clearbody sf.
  set (Dl := func_tycontext f_inflate Vprog_inflate Gprog_inflate3 []) in *.
  simpl in A, B |- *.
  clear A1 A2 B1 B2.
  eapply semax_pre; [ | apply semax_orp6; [ eapply semax_post; [ | | | | exact A] | exact B] ]; clear A B.
  - apply andp_left2. intros rho. simpl. rewrite <- distrib_orp_sepcon.
    apply sepcon_derives; [ | apply derives_refl].
    apply close_pre_orp. intros ae.
    unfold PROPx, PARAMSx, GLOBALSx, SEPx, LOCALx. simpl. normalize.
    unfold argsassert2assert. rewrite !prop_true_andp by tauto.
    set (Lc := local _ _).
    eapply derives_trans; [apply andp_derives; [apply derives_refl | ] | ].
    { rewrite <- !sepcon_assoc. rewrite (sepcon_comm (istream_opt _ _ _ _ _)). rewrite !sepcon_assoc.
      apply sepcon_derives; [apply head_opt6_split | apply derives_refl]. }
    rewrite distrib_orp_sepcon. rewrite andp_comm, distrib_orp_andp.
    apply orp_derives; rewrite andp_comm; apply andp_derives; auto; cancel.
  - apply andp_left2. apply derives_refl.
  - apply andp_left2. apply derives_refl.
  - apply andp_left2. apply derives_refl.
  - intros vl. apply andp_left2. intros rho. simpl.
    apply sepcon_derives; [ | apply derives_refl].
    assert (HO: forall s, head_opt s |-- head_opt6 s) by (intros [L|]; [apply head_mem_6 | apply derives_refl]).
    destruct vl; unfold bind_ret; simpl; [ | apply derives_refl].
    apply andp_derives; [apply derives_refl | ].
    apply exp_left; intros r; apply exp_left; intros z'; apply exp_left; intros st'; apply exp_left; intros ow.
    apply (exp_right r); apply (exp_right z'); apply (exp_right st'); apply (exp_right ow).
    unfold PROPx, LOCALx, SEPx; simpl.
    apply andp_derives; [apply derives_refl | ]. apply andp_derives; [apply derives_refl | ].
    apply sepcon_derives; [apply derives_refl | ]. apply sepcon_derives; [apply HO | apply derives_refl].
Qed.
