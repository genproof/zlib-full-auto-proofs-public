(* The run of inflate's machine where it does not read the header model (RTH8W.hind) is the same with any header
   model (RTH8W.sim_stmt).  The pass, the loop, the exit and the run are RTH8SimKit's hs_step, hs_loop, hs_leave
   and hs_run (hind is RTH8SimKit.hk, out_h is out_hk, res_h is rh). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTH8Spec.
Require Import Zlib.proof.roundtrip.RTH8W.
Require Zlib.proof.roundtrip.RTH8SimKit.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Module K := Zlib.proof.roundtrip.RTH8SimKit.

Lemma rth8_sim : sim_stmt.
Proof.
  unfold sim_stmt. split; [|split; [|split]].
  - intros flush m h H. exact (K.hs_step flush lenfix_list distfix_list m h H).
  - intros flush m h o H L. exact (K.hs_loop flush lenfix_list distfix_list m h o H L).
  - intros flush m h res H L. exact (K.hs_leave flush m h res H L).
  - intros flush m h res H L. exact (K.hs_run flush lenfix_list distfix_list m h res H L).
Qed.
