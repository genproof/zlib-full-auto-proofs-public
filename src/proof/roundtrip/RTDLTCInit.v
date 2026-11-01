(** * Core part of the deflate law theory: deflateInit2_ (deflateReset, lm_init, _tr_init) establishes W
    Statement: RTDLTCSpecs.v; invariant: RTDLTCW.v; shared lemmas: RTDLTCLib.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDLTCLib.
Require Import Zlib.proof.roundtrip.RTDLTCInitKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Theorem init_ok : init_spec.
Proof.
  intros level method wbits mem strategy z H.
  pose proof (init_eq _ _ _ _ _ z H) as E. rewrite fin_eq in E.
  destruct (params_bounds _ _ _ _ _ H) as (B1 & B2 & B3 & B4 & B5).
  set (lv := if level =? -1 then 6 else level) in *.
  set (wb := Z.max 9 (wb_of wbits)) in *.
  set (wrap := wrap_of wbits) in *.
  eexists _, _. split; [exact E|].
  assert (Hw : Z.shiftl 1 wb = 2 ^ wb) by (apply Z.shiftl_1_l).
  assert (Hhs : Z.shiftl 1 (mem + 7) = 2 ^ (mem + 7)) by (apply Z.shiftl_1_l).
  assert (HL : Z.shiftl 1 (mem + 6) = 2 ^ (mem + 7 - 1)) by (rewrite Z.shiftl_1_l; f_equal; lia).
  split; [apply sG_W; assumption || lia|].
  split; [apply sG_outok; assumption || lia|].
  unfold sG, d_pending, d_bi_valid, d_sym_next, d_level, d_strategy;
    cbn [d_status d_wrap d_gzhead d_gzindex d_last_flush d_po d_tr tr_out o_pending o_bi_valid d_strstart
         d_lookahead d_block_start tr_sym_next tr_level tr_strategy d_w_bits d_hash_bits].
  do 16 (split; [reflexivity|]).
  destruct z; reflexivity.
Qed.
