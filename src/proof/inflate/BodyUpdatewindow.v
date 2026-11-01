(* The function specifications for the body of updatewindow (inflate.c).  The body is proved (Qed) in
   BodyUw5.v (body_updatewindow5, against Callees3.v's updatewindow_spec3, the specification the proof
   uses). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.CaseCommon.
Require Zlib.proof.zutil.Spec Zlib.proof.zutil.Libc.
#[local] Existing Instance Zlib.units.Inflate.CS.

Definition Gprog_updatewindow : funspecs :=
  [Zlib.proof.zutil.Spec.zcalloc_spec; (_memcpy, snd (@Zlib.proof.zutil.Libc.memcpy_spec Zlib.units.Inflate.CS))].
