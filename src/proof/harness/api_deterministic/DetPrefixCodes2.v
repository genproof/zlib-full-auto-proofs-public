(* Law api_deterministic (data of any length): main's body from the Z_MEM_ERROR test to offered = 0
   (DetPrefixKit2.det_codes_stmt): the checks of the codes of the two deflateInit2_ calls (the same code on both
   streams, DetFacts2.df2_init); unless both are Z_OK main returns 0. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Rep.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.deflate.DetFacts2.
Require Zlib.proof.deflate.DModel5.
Require Import Zlib.proof.deflate.DetGz.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.api_deterministic.DetCS2.
Require Import Zlib.proof.harness.api_deterministic.DetMainStmt2.
Require Import Zlib.proof.harness.api_deterministic.DetKit2.
Require Import Zlib.proof.harness.api_deterministic.DetPrefixKit2.
Require Import Zlib.harness.api_deterministic.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

(* after_forward_call builds [remove_localdef_temp] syntactically (DetPrefixKit2.rlt_list) *)
Local Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u' := rlt_list i L in change (remove_localdef_temp i L) with u' end.

(* [Q] without the binding of the temporary [t] *)
Ltac rm_temp t Q :=
  lazymatch Q with
  | temp t _ :: ?Q' => Q'
  | ?a :: ?Q' => let r := rm_temp t Q' in constr:(a :: r)
  | nil => constr:(@nil localdef)
  end.

(* forward over an [if] after which the temporary [t] is [v] *)
Ltac fif1 t v :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    let Q' := rm_temp t Q in forward_if (PROPx P (LOCALx (temp t v :: Q') (SEPx R))) end.

(* a goal on the codes of the two deflateInit2_ calls, by cases on them ([Hc], [Hc2]: each is Z_OK,
   Z_STREAM_ERROR or Z_MEM_ERROR) *)
Ltac ccase Hc Hc2 :=
  unfold Z_OK, Z_STREAM_ERROR, Z_MEM_ERROR in *;
  destruct Hc as [-> | [-> | ->]]; destruct Hc2 as [-> | [-> | ->]];
  try match goal with H : Int.repr _ = Int.repr _ |- _ => apply repr_inj_signed in H; [lia | rep_lia | rep_lia] end;
  try match goal with H : Int.repr _ <> Int.repr _ |- _ => exfalso; apply H; reflexivity end;
  try reflexivity.

(* the two halves of a local back together *)
Lemma det_join (p : val) :
  data_at_ Ews t_strm p * data_at_ BoundKit.Ecomp t_strm p |-- data_at_ Tsh t_strm p.
Proof. rewrite (BoundKit.data_at__Tsh_split t_strm p). apply derives_refl. Qed.

Lemma det_codes : det_codes_stmt.
Proof.
  intros Espec v1 v2 gv J JF level wbits mem strategy n bs datap os z' code msgv1 os2 z2 code2 msgv2 K.
  unfold P12, P_loc, init_res, version_at, msuf12, Delta_m, Gmain, POST_m. simplify_func_tycontext.
  abbreviate_semax. Intros.
  rename H into Hpre, H0 into Hv, H1 into Hr1, H2 into Hr2, H3 into H7, H4 into H8.
  pose proof Hpre as (H3 & H4 & H5 & H6 & H & H0 & H1 & Pdp).
  assert (H2 : datap <> nullval) by (intros ->; exact Pdp).
  destruct Hr1 as (a1 & a2 & a3 & a4 & a5 & HI). destruct Hr2 as (b1 & b2 & b3 & b4 & b5 & HI2).
  unfold init_msg in *.
  assert (S : s32 level /\ s32 wbits /\ s32 mem /\ s32 strategy) by (unfold s32; rep_lia).
  destruct S as (S1 & S3 & S4 & S5).
  pose proof (fun a1 a2 a3 a4 a5 => df2_init _ JF level wbits mem strategy a1 a2 a3 a4 a5 zrst0
                S1 S3 S4 S5) as FIN.
  destruct (proj2 (FIN a1 a2 a3 a4 a5) _ _ _ HI) as (Hc & Hse & Hok).
  destruct (proj2 (FIN b1 b2 b3 b4 b5) _ _ _ HI2) as (Hc2 & Hse2 & Hok2).
  (* Z_MEM_ERROR on either stream: return 0 *)
  fif1 _t'10 (Val.of_bool ((code =? -4) || (code2 =? -4))%bool).
  { forward. entailer!. ccase Hc Hc2. }
  { forward. entailer!. ccase Hc Hc2. }
  forward_if.
  { (* the streams back to the locals *)
    sep_apply (det_init_back os code v1 gv). sep_apply (det_init_back os2 code2 v2 gv).
    sep_apply (det_join v1). sep_apply (det_join v2).
    forward. Exists (Int.repr 0). entailer!. }
  clear FIN.
  assert (Hm : code <> Z_MEM_ERROR /\ code2 <> Z_MEM_ERROR).
  { unfold Z_MEM_ERROR. destruct (Z.eqb_spec code (-4)), (Z.eqb_spec code2 (-4)); simpl in H9;
      try (inversion H9; fail); lia. }
  (* the parameters are valid (gp_assume): neither call returns Z_STREAM_ERROR, so both return Z_OK *)
  assert (Hcc : code = Z_OK /\ code2 = Z_OK).
  { destruct Hm.
    assert (code <> Z_STREAM_ERROR) by (intro X; apply Hse in X; congruence).
    assert (code2 <> Z_STREAM_ERROR) by (intro X; apply Hse2 in X; congruence).
    destruct Hc as [?|[?|?]], Hc2 as [?|[?|?]]; try contradiction; split; assumption. }
  destruct Hcc as [-> ->].
  (* gp_assert(code_first == Z_OK && code_second == Z_OK) *)
  forward_if (temp _t'11 (vi 1)).
  { forward. entailer!. }
  { exfalso. auto. }
  forward_call (Int.one).
  (* both Z_OK: the same state on both streams *)
  clear H9 Hm Hc Hc2 Hse Hse2.
  destruct (Hok eq_refl) as [(s & -> & Htin & Htout & HJ) _].
  destruct (proj2 (Hok2 eq_refl) _ _ _ _ _ _ _ _ HI eq_refl) as [E1 E2]. subst os2 z2.
  clear Hok Hok2 HI2.
  pose proof (det_gz_init _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HI) as Hgz.
  pose proof (df2_adler _ JF _ _ _ _ HJ) as Had.
  change (Z_OK =? Z_VERSION_ERROR) with false in H7, H8. change (Z_OK =? Z_OK) with true. unfold rfv.
  rewrite Htin, Htout in *.
  rewrite !dstream_sp_eq. Intros sp2 sp1.
  (* the state at offered = 0 *)
  eapply semax_pre; [| apply (K s z' msgv1 msgv2 sp1 sp2)].
  unfold P14, P_loc, version_at. entailer!.
Qed.
