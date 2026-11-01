(* Law api_deterministic (data of any length): main's body up to the loop (DetKit2.det_prefix_stmt): the parameters
   and their check (deflate_params_ok, gp_assume), the data and new_stream on both streams here, then the parts of
   DetPrefixKit2.v: deflateInit2_ on both streams (DetPrefixInit2.v), the checks of their codes
   (DetPrefixCodes2.v), offered, read, flush and the loop invariant J_at (DetPrefixEnter2.v). *)
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
Require Import Zlib.proof.harness.laws_session.Spec.
Require Zlib.proof.harness.laws_session.Facts.
Require Import Zlib.proof.harness.api_deterministic.DetCS2.
Require Import Zlib.proof.harness.api_deterministic.DetMainStmt2.
Require Import Zlib.proof.harness.api_deterministic.DetKit2.
Require Import Zlib.proof.harness.api_deterministic.DetPrefixKit2.
Require Import Zlib.proof.harness.api_deterministic.DetPrefixInit2.
Require Import Zlib.proof.harness.api_deterministic.DetPrefixCodes2.
Require Import Zlib.proof.harness.api_deterministic.DetPrefixEnter2.
Require Import Zlib.harness.api_deterministic.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

(* VST's after_forward_call simplifies [remove_localdef_temp i L] with [simpl], which can take minutes on main's
   LOCAL list; the same list built syntactically, comparing the identifiers by vm_compute *)
Ltac rlt_list i L :=
  lazymatch L with
  | temp ?j ?v :: ?L' =>
      let r := rlt_list i L' in
      let b := eval vm_compute in (Pos.eqb i j) in
      lazymatch b with true => r | false => constr:(temp j v :: r) end
  | ?d :: ?L' => let r := rlt_list i L' in constr:(d :: r)
  | nil => constr:(@nil localdef)
  end.
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

Lemma det_prefix : det_prefix_stmt.
Proof.
  intros Espec v1 v2 gv [J JF] K.
  unfold PRE0, main_body, Delta_m, Gmain, POST_m. simplify_func_tycontext. abbreviate_semax.
  forward_call tt. Intros n1.
  forward_call tt. Intros n2.
  forward_call tt. Intros n3.
  forward_call tt. Intros n4.
  (* the four (int) casts: each parameter is the signed value of the drawn u32 *)
  rewrite <- (Int.repr_signed (Int.repr n1)), <- (Int.repr_signed (Int.repr n2)),
    <- (Int.repr_signed (Int.repr n3)), <- (Int.repr_signed (Int.repr n4)).
  pose proof (Int.signed_range (Int.repr n1)). pose proof (Int.signed_range (Int.repr n2)).
  pose proof (Int.signed_range (Int.repr n3)). pose proof (Int.signed_range (Int.repr n4)).
  forget (Int.signed (Int.repr n1)) as level. forget (Int.signed (Int.repr n2)) as wbits.
  forget (Int.signed (Int.repr n3)) as mem. forget (Int.signed (Int.repr n4)) as strategy.
  clear n1 n2 n3 n4 H H0 H1 H2.
  (* gp_assume(deflate_params_ok(level, window_bits, mem_level, strategy)): the parameters are in zlib.h's ranges,
     the ones for which deflateInit2_ returns Z_OK or Z_MEM_ERROR (DetFacts2.df2_init) *)
  forward_call (level, wbits, mem, strategy).
  forward_call (if deflate_params_valid level wbits mem strategy then Int.one else Int.zero).
  { destruct (deflate_params_valid level wbits mem strategy); entailer!. }
  Intros.
  assert (Hv : params_ok level 8 wbits mem strategy = true).
  { rewrite <- Zlib.proof.harness.laws_session.Facts.deflate_params_valid_ok.
    destruct (deflate_params_valid level wbits mem strategy); [reflexivity | contradiction]. }
  forward_call 9223372036854775807.
  Intros n.
  forward_call (n, gv).
  Intros vret. destruct vret as [datap bs]. cbn [fst snd] in *.
  rewrite det_token_cs, det_bytes_cs.
  destruct (eq_dec datap nullval) as [Pd | Pd].
  { subst datap. forward_if.
    { forward. Exists (Int.repr 0). entailer!. }
    { contradiction. } }
  forward_if.
  { subst datap. contradiction. }
  assert_PROP (isptr datap) as Pdp by entailer!.
  (* new_stream(&first), new_stream(&second) on the Ews halves of the locals *)
  rewrite (BoundKit.data_at__Tsh_split t_strm v1), (BoundKit.data_at__Tsh_split t_strm v2).
  sep_apply (det_strm_undef v1). sep_apply (det_strm_undef v2).
  forward_call (v1, Ews, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef,
                Vundef, Vundef, Vundef, Vundef).
  forward_call (v2, Ews, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef,
                Vundef, Vundef, Vundef, Vundef).
  (* the rest: the parts, chained *)
  pose proof (fun os z' code msgv1 os2 z2 code2 msgv2 =>
    det_codes _ v1 v2 gv J JF level wbits mem strategy n bs datap os z' code msgv1 os2 z2 code2 msgv2
      (fun s z' msgv1 msgv2 sp1 sp2 =>
         det_enter _ v1 v2 gv J JF level wbits mem strategy n bs datap s z' msgv1 msgv2 sp1 sp2 K)) as K11.
  assert (Hpre : pre_ok level wbits mem strategy n bs datap) by (unfold pre_ok; tauto).
  eapply semax_pre; [| apply (det_init _ v1 v2 gv J JF level wbits mem strategy n bs datap K11)].
  unfold P10, P_loc, new_strm. entailer!.
Qed.
