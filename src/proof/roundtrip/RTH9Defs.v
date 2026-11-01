(* The contexts and the headless switch cases of inflate()'s body against RTH9Spec.inflate_spec9 (calls of any uInt
   size).

   inflate_body9_stmt proves inflate()'s body in RTH8Spec.Gprog_inflate8 fast: Spec5's callees (updatewindow_spec3,
   inflateStateCheck_spec, zlib's allocator zcalloc / zcfree) with a specification [fast] of inflate_fast of our
   choice.  Two kinds of proofs meet in it:
   - the proofs of src/proof/inflate*, src/proof/hl and src/proof/roundtrip, for calls of up to 2^31 - 1 bytes
     (machine invariant Inv3.mwf3), in the contexts Delta_cases5 / Delta_inflate5 / Delta_inflate5_hl, which are
     sub-contexts of [Delta_inflate9 fast] as soon as [fast] is stronger than their inflate_fast specification;
   - the switch cases for calls of any uInt size (machine invariant InvW.mwf3W), from the wide port src/proof/za
     at zlib's allocator.
   [fast9_stmt]: some specification of inflate_fast, with calling convention cc_default, proved of its body, stronger
   than the headless one of the port src/proof/hl (hence than Spec5's), under which the headless switch cases of the
   modes after the header (DICTID .. SYNC, labels 9 .. 31) hold for wide machines ([cases_nh9]). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTH8Spec.
Require Export Zlib.proof.inflate.InvW.
Require Export Zlib.proof.hl.inflate.HlCaseKit5.
Require Export Zlib.proof.hl.inflate.HlLoop2.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Module IM := Zlib.proof.inflate.Model.

(* ---------------------------------------------------------------------------------------------- *)
(* the contexts with the specification [fast] of inflate_fast                                     *)

(* Spec5's callees of the switch cases with [fast] for inflate_fast *)
Definition Gprog_cases9 (fast : funspec) : funspecs :=
  map (fun f : ident * funspec => if ident_eq (fst f) _inflate_fast then (_inflate_fast, fast) else f)
    Gprog_cases3.

Definition Delta_cases9 (fast : funspec) : tycontext :=
  func_tycontext f_inflate Vprog_inflate (Gprog_cases9 fast) nil.

(* the context of inflate()'s body in inflate_body9_stmt *)
Definition Delta_inflate9 (fast : funspec) : tycontext :=
  func_tycontext f_inflate Vprog_inflate (Gprog_inflate8 fast) nil.

(* ---------------------------------------------------------------------------------------------- *)
(* the headless switch cases of the modes after the header, for wide machines                    *)

(* HlCaseKit5.case_ok5_hl with the wide machine invariant InvW.mwf3W and the context [Delta_cases9 fast] *)
Definition case_ok_nh9 {Espec: OracleKind} (fast : funspec) (F: frame) (Y: Z) (i: nat) : Prop :=
  forall m, m_mode m = Y -> m_leave m = 0 -> mwf3W m ->
    semax (Delta_cases9 fast) (loop_state_hl F m) (seq_of_labeled_statement (ls_drop i inflate_LS))
      (switch_ret_assert (case_post2_hl F m)).

(* every mode after the header: DICTID .. SYNC, the switch's labels 9 .. 31 *)
Definition cases_nh9 (fast : funspec) : Prop :=
  forall {Espec: OracleKind} (F: frame), frame_ok5 F ->
    forall i, (9 <= i < 32)%nat -> case_ok_nh9 fast F (IM.HEAD + Z.of_nat i) i.

Definition fast9_stmt : Prop :=
  exists fast : funspec,
    callingconvention_of_funspec fast = cc_default /\
    (forall {Espec: OracleKind},
       semax_body Vprog_fast Gprog_fast Zlib.inffast.code.f_inflate_fast (_inflate_fast, fast)) /\
    funspec_sub fast (snd inflate_fast_spec3_hl) /\
    cases_nh9 fast.
