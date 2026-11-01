(* RT-H: mechanical port of inflate/ModeKit5.v to the header-external loop state (RTHLoop.v); identifiers whose meaning changes carry the suffix H. *)
(* ModeKit.v's semax_store_modeH in Delta_cases5 *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.roundtrip.RTHModeKit.
Require Export Zlib.proof.inflate.Callees5.
Require Export Zlib.proof.roundtrip.RTHCaseCommon.
Require Export Zlib.proof.inflate.ModeKit5.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Lemma semax_store_mode5H {Espec: OracleKind} (F: frame) (m: mst) (md: Z):
  semax Delta_cases5 (loop_stateH F m)
    (Sassign (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                       (Tstruct _inflate_state noattr)) _mode tint)
       (Econst_int (Int.repr md) tint))
    (normal_ret_assert (loop_stateH F (set_mode m md))).
Proof.
  rewrite loop_state_set_modeH, loop_state_splitH. unfold loop_state_mH.
  abbreviate_semax.
  forward.
  entailer!.
Qed.
