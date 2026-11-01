(* ModeKit.v's semax_store_mode in Delta_cases5 *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.inflate.ModeKit.
Require Export Zlib.proof.inflate.Callees5.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Lemma semax_store_mode5 {Espec: OracleKind} (F: frame) (m: mst) (md: Z):
  semax Delta_cases5 (loop_state F m)
    (Sassign (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                       (Tstruct _inflate_state noattr)) _mode tint)
       (Econst_int (Int.repr md) tint))
    (normal_ret_assert (loop_state F (set_mode m md))).
Proof.
  rewrite loop_state_set_mode, loop_state_split. unfold loop_state_m.
  abbreviate_semax.
  forward.
  entailer!.
Qed.
